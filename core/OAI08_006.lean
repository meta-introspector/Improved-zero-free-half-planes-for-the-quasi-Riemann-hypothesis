        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,n,hn,hchoice⟩ := canonical_probe_exists_cube (ι:=RayQuotient.Characters M H)
    K e δ a b B ζ saving τ he he' hδ hδ' hζ hζ' hτ ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,n,hn,?_⟩
  filter_upwards [source_cube_height_eventually τ hτ,
    ProbeRayCharacterFamily.large_supported_twists_eventually M (1/100) (by norm_num)]
    with Z hZ hlarge
  intro η T hT hdis length hl0 hl hpool W hWS hWB
  obtain ⟨idx,grid,hlabel,hbins,herror⟩ := hchoice η Z hZ.1 hZ.2 T hT hdis length hl0 hl hpool W hWS hWB
    (rayCubeFamily M H hH)
  refine ⟨idx,grid,hlabel,hbins,?_,herror⟩
  intro u hu hcal
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hcal
  have hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1 :=
    hlarge u (mem_rowBand.mp hu).2.1 hs H hH
  refine ⟨hnp,?_,?_⟩
  · exact ProbeRayCharacterFamily.raw_twisted_conductor M H hH u
  · intro hnp'
    exact (ProbeRayCharacterFamily.source_nonprincipal_maximum_dominates S hS.prime η u
      (rayCubeFamily M H hH u) hnp' _).trans_lt (hbins u).2.2.2.2.1

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2650

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorMomentData
Source SHA256: 78e5f7704f09deaa4410cbac7a793ce00d82c0ef43e2c8412aad713128ece0a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2651



namespace OAI

noncomputable section
open scoped Classical ComplexConjugate
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeRowClosure ProbePhysical
local notation "O" => HeckeFamily.O

theorem momentData_product_raw (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((momentData χ).character (momentElement u)) I=
      idealCoeff (χ.product (rawRow u)) I := by
  have he : idealCoeff ((momentData χ).character (momentElement u))=
      idealCoeff (χ.product (rawRow u)) := by
    apply hom_eq_of_primes
    intro P
    rw [momentData_coeff,idealCoeff_product,rawRow_coeff,fixedSourcePrincipal_prime]
    simp
  exact congrArg (fun f : Ideal O→*₀ℂ=>f I) he

theorem inverse_row_twist_moment_coeff (χ : Character) (u : FreeRow) (I : Ideal O) :
    idealCoeff ((rawRow u).inverse.product χ) I=
      conj (idealCoeff ((momentData χ.inverse).character (momentElement u)) I) := by
  rw [momentData_product_raw,idealCoeff_product,idealCoeff_product,
    idealCoeff_inverse_conj,idealCoeff_inverse_conj,map_mul]
  simp only [starRingEnd_self_apply]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentData (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→RowData :=
  Sum.elim (fun b=>if b then momentData (fixedSourcePrincipal S hS)
    else momentData (η.inverse.excludePrimes S hS))
    (fun θ=>momentData (HeckeRayQuotient.character M H hH θ).inverse)

def sourceMomentReverse : Sum Bool (RayQuotient.Characters M H)→Bool :=
  Sum.elim (fun b=>!b) (fun _=>true)

theorem source_family_moment_coeff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (η : Character)
    (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) (I : Ideal O) :
    idealCoeff (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) I=
      if sourceMomentReverse M H j then
        conj (idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I)
      else idealCoeff ((sourceMomentData M H hH S hS η j).character (momentElement u)) I := by
  rcases j with b|θ
  · cases b
    · simpa [sourceMomentReverse,sourceMomentData] using denominator_moment_coeff S hS hbad η u I
    · simpa [sourceMomentReverse,sourceMomentData] using numerator_moment_coeff S hS hbad u I
  · exact inverse_row_twist_moment_coeff (HeckeRayQuotient.character M H hH θ) u I
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2651

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorBatch
Source SHA256: 1b10930a0dba429879c4ee3e48b94f502ca1cc6a28d3bd3ef89a896982366d45
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2652



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorSupportedWitness ProbePhysical
local notation "O" => HeckeFamily.O

def retainedProjection (R : Finset FreeRow) (u0 : FreeRow) (u : FreeRow) : FreeRow :=
  if u∈R then u else u0

@[simp] theorem retainedProjection_of_mem (R : Finset FreeRow) (u0 u : FreeRow) (hu : u∈R) :
    retainedProjection R u0 u=u := by simp [retainedProjection,hu]

theorem retainedProjection_mem (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R) (u : FreeRow) :
    retainedProjection R u0 u∈R := by
  unfold retainedProjection
  split_ifs with hu
  · exact hu
  · exact h0

variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def retainedSourceBatch {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character)
    (R : Finset FreeRow) (u0 : FreeRow) (h0 : u0∈R)
    (U a ε tstar T allowance : ℝ) (i : ℕ)
    (hw : ∀u∈R,SupportedWitness
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) U a ε tstar T allowance i)
    (hrow : ∀u∈R,rowNorm u≤U)
    (slots : Finset Slot) (profile : Slot→ℝ→ℂ) (upper widths : Slot→ℝ) (external : Slot→ℂ)
    (mesh binWidth : ℝ) (hm : 0≤mesh) (hb : 0<binWidth)
    (hwpos : ∀s∈slots,0<widths s) (hwmesh : ∀s∈slots,widths s≤mesh)
    (hsupply : 7/37≤∑s∈slots,widths s) :
    Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i where
  rows := R
  family := fun u=>sourceDetectorFamily S hS.prime η (retainedProjection R u0 u)
    (rayCubeFamily M H hH (retainedProjection R u0 u))
  witness := fun u=>hw (retainedProjection R u0 u) (retainedProjection_mem R u0 h0 u)
  row_norm := hrow
  data := sourceMomentData M H hH S hS.prime η
  reverse := sourceMomentReverse M H
  row_coeff := by
    intro u hu j I
    rw [retainedProjection_of_mem R u0 u hu]
    exact source_family_moment_coeff M H hH S hS.prime hS.bad η u j I
  slots := slots
  profile := profile
  upper := upper
  widths := widths
  external := external
  mesh := mesh
  binWidth := binWidth
  mesh_nonneg := hm
  binWidth_pos := hb
  widths_pos := hwpos
  widths_mesh := hwmesh
  supply := hsupply

lemma physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0<dmin) (hd : dmin≤d) (hdtop : d≤37/42)
    (hell : ∀j,0<ell j) (hsmall : ∀j,ell j≤dmin*mesh)
    (hsum : ∑j,ell j=1/6) :
    (∀j,0<ell j/d) ∧ (∀j,ell j/d≤mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0<d := hdmin.trans_le hd
  have hm : 0≤mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    rw [hsum] at hn
    norm_num at hn
  refine ⟨fun j=>div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div,hsum]
    apply (le_div_iff₀ hd0).mpr
    nlinarith

lemma physical_slot_scale {N : ℕ} (ell : Fin N→ℝ) (Z d : ℝ) (hZ : 0<Z) (hd : d≠0) (j : Fin N) :
    (Z^d)^(ell j/d)=Z^(ell j) := by
  rw [←Real.rpow_mul hZ.le]
  congr 1
  field_simp
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2652

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorMomentGates
Source SHA256: e14ccde841c8d8d70ced51d66d5089c41a9d1ab93e56961a9aaf419e6937a88f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2653





namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open CanonicalCoefficientClass InverseInitialExcludedPeriod CanonicalQuadraticSieve
open InverseInitialRayAttachment CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

def sourceMomentPeriod (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℕ:=
  ∏j:Sum Bool (RayQuotient.Characters M H),
    (baseCharacter (sourceMomentData M H hH S hS η j)).period

def sourceMomentConductorBound (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):ℝ:=
  1+∑j:Sum Bool (RayQuotient.Characters M H),
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)

theorem sourceMomentPeriod_ne_zero (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    sourceMomentPeriod M H hH S hS η≠0:=by
  exact Finset.prod_ne_zero_iff.mpr (fun j _=>Nat.ne_of_gt (Character.period_pos _))

theorem sourceMomentPeriod_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    Ideal.span {(sourceMomentPeriod M H hH S hS η:O)}≤
      (baseCharacter (sourceMomentData M H hH S hS η j)).modulus:=by
  apply Ideal.span_le.mpr
  intro x hx
  rcases Set.mem_singleton_iff.mp hx with rfl
  have hd:(baseCharacter (sourceMomentData M H hH S hS η j)).period∣
      sourceMomentPeriod M H hH S hS η:=Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  obtain ⟨n,hn⟩:=hd
  rw [hn,Nat.cast_mul]
  exact Ideal.mul_mem_right _ _ (Character.period_mem _)

theorem sourceMomentConductorBound_pos (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    0<sourceMomentConductorBound M H hH S hS η:=by
  unfold sourceMomentConductorBound
  positivity

theorem sourceMomentConductor_le (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    (j:Sum Bool (RayQuotient.Characters M H)):
    ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
      sourceMomentConductorBound M H hH S hS η:=by
  have hh:=Finset.single_le_sum (fun k (_:k∈(Finset.univ:Finset (Sum Bool (RayQuotient.Characters M H))))=>
    (Nat.cast_nonneg (α:=ℝ) (baseCharacter (sourceMomentData M H hH S hS η k)).modulus.absNorm))
      (Finset.mem_univ j)
  unfold sourceMomentConductorBound
  linarith

theorem sourceMoment_deleted_base_gates (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character):
    let q:=sourceMomentPeriod M H hH S hS η
    deletedPeriod q≠0 ∧ reflectionExcludedPrimes (deletedPeriod q)=reflectionExcludedPrimes q ∧
    ∀j:Sum Bool (RayQuotient.Characters M H),
      let χ:=(baseCharacter (sourceMomentData M H hH S hS η j)).excludePrimes
        (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (∀x,‖elementCharacter (idealCoeff χ).toMonoidHom x‖≤1) ∧
      FactorsModulo (fixedBaseConductor (deletedPeriod q))
        (elementCharacter (idealCoeff χ).toMonoidHom):=by
  dsimp only
  let q:=sourceMomentPeriod M H hH S hS η
  have hq:q≠0:=sourceMomentPeriod_ne_zero M H hH S hS η
  refine ⟨deletedPeriod_ne_zero q hq,deleted_excluded_eq q hq,?_⟩
  intro j
  exact (deleted_physical_base_gates _ q hq (sourceMomentPeriod_le M H hH S hS η j)).2.2

theorem sourceMoment_large_eventually (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀j:Sum Bool (RayQuotient.Characters M H),∀s:Slot,
        ((baseCharacter (sourceMomentData M H hH S hS η j)).modulus.absNorm:ℝ)<
          (Z^d)^(ell s/d):=by
  have ht:∀ᶠZ:ℝ in atTop,∀s:Slot,sourceMomentConductorBound M H hH S hS η<Z^(ell s):=by
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact (sourceMomentConductor_le M H hH S hS η j).trans (ht s)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2653

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRows
Source SHA256: 20771a0225cec462b6d272954974b400ff7bb43444f2d780a6a4cfa74d437b27
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2654



namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem source_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ψ : Character) (m u : O) (reverse : Bool)
    (hrow : ∀n,elementCoeff ψ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (1*u) n)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then conj (idealCoeff ψ I) else idealCoeff ψ I)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hMm : M≤Ideal.span {m})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η m 1 u
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  rw [positiveSlotRow_eq_product η ψ m 1 u hrow _ _ _ _ P _ _ _ _ hX₁ hX₂ hP]
  simp only [norm_mul,norm_prod]
  rw [norm_of_oriented_coefficients χ ψ reverse hc false W₁ X₁ σ t hX₁,
    norm_of_oriented_coefficients χ ψ reverse hc false W₂ X₂ σ t hX₂]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  rw [physical_slot_conj M H η m u hmLam hMm (V i) (b i) (P i) (external i) (hP i) (hη i),RCLike.norm_conj]

theorem momentData_plain_pair_norm
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O,idealCoeff χ I=if reverse then
      conj (idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
      else idealCoeff ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u)) I)
    (hMm : M≤Ideal.span {ProbeHighRowFamily.rowMaskElement})
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P : ι→ℝ) (external : ι→ℂ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i)
    (hη : ∀i,∀J∈primePool M H (b i) (P i),V i ((J.absNorm:ℝ)/(P i))≠0→IsCoprime J η.modulus) :
    ‖polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
      ∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (P i) (external i)‖ =
    ‖positiveSlotRow η ProbeHighRowFamily.rowMaskElement 1 u.val
      (twistProfile (orientedProfile reverse W₁) σ (orientedFrequency reverse t))
      (twistProfile (orientedProfile reverse W₂) σ (orientedFrequency reverse t))
      (fun i=>primePool M H (b i) (P i))
      (fun i=>physicalSlotCoefficient η (V i) (P i) (external i)) P 0 X₁ X₂‖ := by
  apply source_plain_pair_norm M H η χ
    ((ProbeHighRowFamily.momentData η).character (ProbeHighRowFamily.momentElement u))
    ProbeHighRowFamily.rowMaskElement u.val reverse _ hc (dvd_mul_left _ _) hMm
    W₁ W₂ V b P external X₁ X₂ σ t hX₁ hX₂ hP hη
  intro n
  simpa only [ProbeHighRowFamily.momentData,ProbeHighRowFamily.momentElement,one_mul] using
    (ProbeHighRowFamily.momentData η).character_spec (ProbeHighRowFamily.momentElement u) n

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2654

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryFiber
Source SHA256: 329b8f98e7c80578bf2e1d9a5d6a7887af508f69c0b9e55e89493b57b668d5bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2655



namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open HeckeDetectorCoefficientTransfer HeckeDetectorRawFiber HeckeDetectorRowwisePolynomial
open HeckeDetectorDyadicProfiles CenteredMomentRetainedEnergy
open CenteredMomentPrimeSlot ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

def detectorPositiveRow (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) : ℂ :=
  positiveSlotRow η rowMaskElement 1 u.val
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (fun s : selected=>physicalSlotCoefficient η (F.profile s.val) (U^(F.widths s.val)) (F.external s.val))
    (fun s : selected=>U^(F.widths s.val)) 0 (U^F.m) (U^F.m)

theorem fiber_plain_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2 := by
  apply Finset.sum_congr rfl
  intro u hu
  congr 1
  have hc := F.row_coeff u hu
  rw [hdata] at hc
  have he := momentData_plain_pair_norm M H η (F.family u F.label) u F.reverse hc hMm
    ((logProfile^[j]) positiveAnnular) ((logProfile^[k]) positiveAnnular)
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    (U^F.m) (U^F.m) σ t (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
    (fun s=>Real.rpow_pos_of_pos hU _) (fun s=>hη s.val s.property)
  have hprod := Finset.prod_coe_sort selected (fun s=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val
    (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s))
  rw [hprod] at he
  simpa only [detectorPositiveRow,Fiber.physicalProduct,HeckeDetectorPhysicalSelection.physical,
    Finset.prod_coe_sort] using he

theorem fiber_plain_unmarked_energy_eq (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (j k : ℕ) (σ t : ℝ) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t‖^2)=
      ∑u∈F.rows,‖detectorPositiveRow F η ∅ j k σ t u‖^2 := by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    fiber_plain_energy_eq F η hdata hMm hU ∅ j k σ t (by simp)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2655

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySource
Source SHA256: b8f6d1f292e243d21ee2a48e3c7d0033e27055d1fad16953881064ed1b1e7391
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2656




namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open ProbePhysical CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma source_product_le_rowMask (S : Finset (Ideal O))
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) :
    (∏P∈S,P)≤Ideal.span {rowMaskElement} := by
  apply Ideal.dvd_iff_le.mp
  have hne : (Ideal.span {ConcretePrimeRowBridge.goodLambda}:Ideal O)≠Ideal.span {(2:O)} := by
    intro he
    have hh : CanonicalQuadraticSieve.badPrime false=CanonicalQuadraticSieve.badPrime true := he
    have hh := CanonicalQuadraticSieve.badPrime_injective hh
    cases hh
  have hd := Finset.prod_dvd_prod_of_subset CanonicalQuadraticSieve.fixedBadPrimes S (fun P : Ideal O=>P) hbad
  have he : (∏P∈CanonicalQuadraticSieve.fixedBadPrimes,P)=Ideal.span {rowMaskElement} := by
    change (∏P∈({Ideal.span {ConcretePrimeRowBridge.goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O)),P)=_
    rw [Finset.prod_pair hne]
    unfold rowMaskElement
    rw [←Ideal.span_singleton_mul_span_singleton]
    exact mul_comm _ _
  rwa [he] at hd

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceMomentBase (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) :
    Sum Bool (RayQuotient.Characters M H)→Character :=
  Sum.elim (fun b=>if b then fixedSourcePrincipal S hS else η.inverse.excludePrimes S hS)
    (fun θ=>(HeckeRayQuotient.character M H hH θ).inverse)

lemma sourceMomentData_base (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (j : Sum Bool (RayQuotient.Characters M H)) :
    sourceMomentData M H hH S hS η j=momentData (sourceMomentBase M H hH S hS η j) := by
  rcases j with b|θ
  · cases b <;> rfl
  · rfl

theorem eventually_source_slots_coprime {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (ell : Fin N→ℝ) (hell : ∀i,0<ell i) (a : ℝ) (ha : 0<a) :
    ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀d : ℝ,d≠0→∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b ((Z^d)^(ell i/d)),
        W ((P.absNorm:ℝ)/((Z^d)^(ell i/d)))≠0→
          IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
  have he : ∀ᶠZ : ℝ in atTop,∀j : Sum Bool (RayQuotient.Characters M H),∀i : Fin N,
      ∀(W : ℝ→ℂ)(b : ℝ),Function.support W⊆Set.Ici a→
      ∀P∈primePool M H b (Z^(ell i)),W ((P.absNorm:ℝ)/(Z^(ell i)))≠0→
        IsCoprime P (sourceMomentBase M H hH S hS η j).modulus := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro i
    filter_upwards [eventually_primePool_power_coprime (sourceMomentBase M H hH S hS η j)
      a (ell i) ha (hell i)] with Z hz
    exact hz M H
  filter_upwards [he,eventually_ge_atTop (0:ℝ)] with Z hz hZ
  intro j i d hd W b hs
  have heq : (Z^d)^(ell i/d)=Z^(ell i) := by
    rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]
  rw [heq]
  exact hz j i W b hs

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2656

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFiber
Source SHA256: 4cffd09d689f283fe1c122c150e8f65292175804a6991aa2e12fb9b01a1cd64d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2657



namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary CenteredMomentRetainedEnergy CenteredMomentHeckeSlots
open CenteredMomentHeckeHeight CenteredMomentPrimeSlot HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open ProbeHighRowFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma rowMaskElement_eq_fixed : rowMaskElement=fixedBadMask := by
  unfold rowMaskElement fixedBadMask
  exact mul_comm _ _

lemma excluded_one_ideal (χ : Character) (I : Ideal O) :
    idealCoeff (excluded χ 1) I=idealCoeff χ I := by
  simp only [excluded_ideal χ 1 one_ne_zero,isCoprime_one_right,ite_true]

lemma natural_unit_mask_coefficient {η : Character} {z : O} (F : NaturalRow η z) (I : Ideal O) :
    idealCoeff η I*CanonicalRowCompletion.idealRowHom ((fixedBadMask*idealGenerator 1)^6*z) I=
      idealCoeff η I*CanonicalRowCompletion.idealRowHom (fixedBadMask^6*z) I := by
  rw [←F.masked_ideal 1 one_ne_zero,excluded_one_ideal,F.ideal]

lemma natural_unit_mask_positive {ι : Type*} [Fintype ι] [DecidableEq ι]
    {η : Character} {z : O} (F : NaturalRow η z) (W₁ W₂ : ℝ→ℂ)
    (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ) (t X₁ X₂ : ℝ) :
    positiveSlotRow η (fixedBadMask*idealGenerator 1) 1 z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η fixedBadMask 1 z W₁ W₂ S β P t X₁ X₂ := by
  simp only [positiveSlotRow,rowTwistedSum,rowSlot,one_mul,natural_unit_mask_coefficient F]

variable {M : Ideal O} [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable {H : Subgroup (O⧸M)ˣ} (hH : RayOrthogonality.globalUnits M≤H)
variable {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}

def fiberSector (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (θ : selected→RayQuotient.Characters M H) (u : FreeRow) : ℂ :=
  sectorValue M H hH (naturalRow η u.val u.property.1).character η 1
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>fun y=>conj (F.profile s.val y)) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>1-(F.external s.val).re)
    (fun s : selected=>-(F.external s.val).im) 0 (U^F.m) (U^F.m) θ

theorem detectorPositiveRow_sector {Slot : Type*}
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (η : Character)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ) (u : FreeRow) (hU : 0<U) :
    detectorPositiveRow F η selected j k σ t u=
      averageWeight (ι:=selected) M H*∑θ : selected→RayQuotient.Characters M H,
        fiberSector hH F η selected j k σ t θ u := by
  have he:=natural_physical_product M H hH (naturalRow η u.val u.property.1) η 1 one_ne_zero
    (twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (twistProfile (orientedProfile F.reverse ((logProfile^[k]) positiveAnnular)) σ (orientedFrequency F.reverse t))
    (fun s : selected=>F.profile s.val) (fun s : selected=>F.upper s.val)
    (fun s : selected=>U^(F.widths s.val)) (fun s : selected=>F.external s.val)
    0 (U^F.m) (U^F.m) (by positivity) (fun _=>Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (naturalRow η u.val u.property.1)] at he
  simpa only [detectorPositiveRow,rowMaskElement_eq_fixed,fiberSector] using he

theorem fiber_plain_sector_energy (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η)
    (hMm : M≤Ideal.span {rowMaskElement}) (hU : 0<U)
    (selected : Finset Slot) (j k : ℕ) (σ t : ℝ)
    (hη : ∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus) :
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) (U^F.m) σ t*
      polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) (U^F.m) σ t*
        F.physicalProduct selected u‖^2)≤
      ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
        ∑u∈F.rows,‖fiberSector hH F η selected j k σ t θ u‖^2 := by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  calc
    _≤∑u∈F.rows,∑θ : selected→RayQuotient.Characters M H,
        ‖averageWeight (ι:=selected) M H‖*‖fiberSector hH F η selected j k σ t θ u‖^2 := by
      apply Finset.sum_le_sum
      intro u hu
      rw [detectorPositiveRow_sector hH F η selected j k σ t u hU]
      exact sector_average_energy M H _
    _= _ := by rw [Finset.sum_comm]; simp only [Finset.mul_sum]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2657

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeCalibration
Source SHA256: badf6f3e00ef5de00c14ce06e14e4d71dc1fdc5ba6dcc105fb8a032b0496073e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2658


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma centralCubeIntegral_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=0 := by
  simp [centralCubeIntegral,continuedRowOnLines,continuedPhysicalRowKernel,hc]

lemma cubeWeightedRow_calibration_zero {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (hc : (calibrationForSet S hmax).residueMonoid u.val=0)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z a e H : ℝ) :
    cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H=0 := by
  funext t
  simp [cubeWeightedRow,weightedRowOnLines,calibratedTupleValue,hc]

theorem finiteCentralCubeRows_filter_calibration {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (a H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η (R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0))
      T hT W Yp W0 W1 X Y Z e a H=
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H := by
  unfold finiteCentralCubeRows
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp [hc,centralCubeIntegral_calibration_zero S hS hmax _ _ η u hc]
  · simp [hc]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2658

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralSupportedSplit
Source SHA256: 972925f42f9e96c7e7bc7ad424c45537751e35b7819ee287648667ae830ab9b5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2659


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def supportedFloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) : Finset FreeRow :=
  R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u=0)

def supportedNonfloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) : Finset FreeRow :=
  R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u≠0)

@[simp] lemma mem_supportedFloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow) :
    u∈supportedFloorRows S hmax R grid ↔ u∈R ∧ (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u=0 :=
  Finset.mem_filter

@[simp] lemma mem_supportedNonfloorRows (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow) :
    u∈supportedNonfloorRows S hmax R grid ↔ u∈R ∧ (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ grid u≠0 :=
  Finset.mem_filter

lemma nonfloor_grid_positive (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (R : Finset FreeRow) (grid : FreeRow→ℕ) (u : FreeRow)
    (hu : u∈supportedNonfloorRows S hmax R grid) (e : ℝ) (he : 0<e) :
    51/100<(51/100:ℝ)+e*grid u := by
  have hg : 0<(grid u:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero ((mem_supportedNonfloorRows S hmax R grid u).mp hu).2.2
  linarith [mul_pos he hg]

theorem finiteCentralCubeRows_supported_split {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e : ℝ) (grid : FreeRow→ℕ) (H : FreeRow→ℝ) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H=
      finiteCentralCubeRows S hS hmax η (supportedFloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun _=>51/100) H+
      finiteCentralCubeRows S hS hmax η (supportedNonfloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H := by
  have hfilter := finiteCentralCubeRows_filter_calibration S hS hmax η R T hT W Yp W0 W1 X Y Z e
    (fun u=>51/100+e*grid u) H
  refine hfilter.symm.trans ?_
  let Rs := R.filter (fun u=>(calibrationForSet S hmax).residueMonoid u.val≠0)
  have hfloor : Rs.filter (fun u=>grid u=0)=supportedFloorRows S hmax R grid := by
    simp only [Rs, Finset.filter_filter, supportedFloorRows]
  have hn : Rs.filter (fun u=>¬grid u=0)=supportedNonfloorRows S hmax R grid := by
    simp only [Rs, Finset.filter_filter, supportedNonfloorRows]
  have hsplit : finiteCentralCubeRows S hS hmax η Rs T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H=
      finiteCentralCubeRows S hS hmax η (supportedFloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H+
      finiteCentralCubeRows S hS hmax η (supportedNonfloorRows S hmax R grid) T hT W Yp W0 W1 X Y Z e (fun u=>51/100+e*grid u) H := by
    unfold finiteCentralCubeRows
    rw [←hfloor,←hn]
    exact (Finset.sum_filter_add_sum_filter_not Rs (fun u=>grid u=0) _).symm
  refine hsplit.trans ?_
  refine congrArg₂ (fun x y : ℂ => x + y) ?_ rfl
  unfold finiteCentralCubeRows
  apply Finset.sum_congr rfl
  intro u hu
  have hg := ((mem_supportedFloorRows S hmax R grid u).mp hu).2.2
  simp only [hg,Nat.cast_zero,mul_zero,add_zero]

lemma normalized_nonfloor_error (A F Cfloor Cnon N : ℂ) (E B : ℝ)
    (hE : ‖A/N-F-(Cfloor+Cnon)/N‖≤E) (hB : ‖Cfloor/N‖≤B) :
    ‖A/N-F-Cnon/N‖≤E+B := by
  calc
    _ = ‖(A/N-F-(Cfloor+Cnon)/N)+Cfloor/N‖ := by congr 1;ring
    _ ≤ ‖A/N-F-(Cfloor+Cnon)/N‖+‖Cfloor/N‖ := norm_add_le _ _
    _ ≤ E+B := add_le_add hE hB

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2659

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeBinPartition
Source SHA256: f8df56cd7678abc578b9b4b92e18009b6f57793ad81b7e69ba47a588615df618
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2660


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) : Finset FreeRow :=
  R.filter (fun u=>idx u=i ∧ grid u=k)

@[simp] lemma mem_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (i k : ℕ) (u : FreeRow) :
    u∈cubeBinRows R idx grid i k ↔ u∈R ∧ idx u=i ∧ grid u=k := by simp [cubeBinRows]

lemma sum_cubeBinRows (R : Finset FreeRow) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) (f : FreeRow→ℂ) :
    (∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),∑u∈cubeBinRows R idx grid i k,f u)=∑u∈R,f u := by
  have hm : ∀u∈R,(idx u,grid u)∈(Finset.range (n+1)).product (Finset.range (m+1)) := by
    intro u hu
    simpa only [Finset.product_eq_sprod,Finset.mem_product,Finset.mem_range] using
      And.intro (Nat.lt_succ_of_le (hlabel u hu).1) (Nat.lt_succ_of_le (hlabel u hu).2)
  have hs := Finset.sum_fiberwise_of_maps_to hm f
  simpa only [Finset.product_eq_sprod,Finset.sum_product,Prod.mk.injEq,cubeBinRows] using hs

theorem finiteCentralCubeRows_bin_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z e B : ℝ) (idx grid : FreeRow→ℕ) (n m : ℕ)
    (hlabel : ∀u∈R,idx u≤n ∧ grid u≤m) :
    finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e
      (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*B)=
    ∑i∈Finset.range (n+1),∑k∈Finset.range (m+1),
      finiteCentralCubeRows S hS hmax η (cubeBinRows R idx grid i k) T hT W Yp W0 W1 X Y Z e
        (fun _=>51/100+e*k) (fun _=>(3*i+1:ℕ)*B) := by
  unfold finiteCentralCubeRows
  rw [←sum_cubeBinRows R idx grid n m hlabel]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro u hu
  rcases (mem_cubeBinRows R idx grid i k u).mp hu with ⟨hu,hi,hk⟩
  simp only [hi,hk]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2660

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeCommonProfile
Source SHA256: 949febab3c7afb9e6cbcf316464e3a76e5b10075d1de0e9ee60c63ffd2e6e9e7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2661


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def cubeArithmeticSum {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace) : ℂ :=
  ∑u∈R,frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)

theorem cube_sum_eq_common_profile {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) (t : HeightSpace) :
    (∑u∈R,∑P:(∀i,T i),cubeWeightedRow S hS hmax (fun i=>(P i).val)
      (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z a e H t)=
    {v : HeightSpace | (|v.1.1|≤H ∧ |v.2|≤H) ∧ |v.1.2|≤H}.indicator
      (fun v=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+v.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+v.2*Complex.I)
        ((17/50:ℂ)+v.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e v) t := by
  by_cases ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H
  · simp [cubeWeightedRow,ht,weightedRowOnLines,cubeArithmeticSum,
      Finset.mul_sum,mul_assoc]
  · simp [cubeWeightedRow,ht]

theorem cube_common_profile_integral {K : ℕ} {ι : Type*} [Fintype ι]
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1' : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
      (fun t=>sourceMellinWeight W0 W1 X Y Z
        (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
        ((17/50:ℂ)+t.1.2*Complex.I)*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  have hh := finiteCentralCubeRows_eq_integral e he he' S hS hmax hfirst η R hR T hT
    (fun _=>a) (fun _=>B) (fun _=>H) (fun _=>i) ψ
    (fun u hu=>⟨ha,ha1,hB,hH,hbin u hu⟩) W Yp W0 W1 a0 b0 a1 b1 ha0 ha1' hW0 hW1 X Y Z hX hY hZ
  dsimp only at hh ⊢
  simpa only [cube_sum_eq_common_profile] using hh

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2661

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralCubeNorm
Source SHA256: ff41bad5e590181d0cb346745f56f6a32f69cfe9f018f0d5a72baec8261dedd2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2662




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma cubeArithmeticSum_norm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (a e : ℝ) (t : HeightSpace)
    (A : FreeRow→ℝ)
    (hA : ∀u∈R,‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=>hT j _ (P j).property) W Yp
      (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)‖≤A u) :
    ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤
      ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u := by
  unfold cubeArithmeticSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun u hu=>?_)
  rw [norm_mul,frequencyWeight_ideal_norm]
  have hz : (((17/50:ℂ)+t.1.2*Complex.I).re:ℝ)=17/50 := by simp
  rw [hz]
  exact mul_le_mul_of_nonneg_left (hA u hu) (Real.rpow_nonneg (by positivity) _)

theorem actual_common_cube_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : FreeRow→ℝ,(∀u∈R,0≤A u) →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H → ∀u∈R,
        ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>hT j _ (P j).property) W Yp
          (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
          ((17/50:ℂ)+t.1.2*Complex.I)‖≤A u) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          (∑u∈R,rowNorm u^(-(17/50:ℝ))*A u) := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := ∑u∈R,rowNorm u^(-(17/50:ℝ))*A u
  have hm : 0≤mass := Finset.sum_nonneg fun u hu=>mul_nonneg (Real.rpow_nonneg (by unfold rowNorm;positivity) _) (hA u hu)
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (cubeArithmeticSum_norm S hS hmax η R T hT W Yp a e t A (hb t ht)) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring

theorem actual_common_cube_aggregate_norm (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀{K : ℕ} {ι : Type*} [Fintype ι]
      (e a B H : ℝ) (i : ℕ),0<e → e<1/1000 → 51/100≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
    ∀(S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal),
    FirstTail (4*e) S → ∀(η : Character) (R : Finset FreeRow), (∀u∈R,u.val≠1) →
    ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→P.val∉S)
      (ψ : FreeRow→ι→Character),
      (∀u∈R,detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(i+1:ℕ)*B)<a+2*e) →
    ∀(W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (X Y Z : ℝ),0<X → 0<Y → 0<Z →
    ∀A : ℝ,0≤A →
      (∀t : HeightSpace,(|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H →
        ‖cubeArithmeticSum S hS hmax η R T hT W Yp a e t‖≤A) →
      ‖finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e (fun _=>a) (fun _=>H)‖≤
        C*(X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e))*
          A := by
  obtain ⟨D,hD,hprofile⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    0 2 (17/50) (17/50) (-1) 1 (by norm_num) 0
  refine ⟨‖((1/(2*Real.pi):ℝ):ℂ)^3‖*D,mul_pos (norm_pos_iff.mpr (by
    apply pow_ne_zero
    exact_mod_cast (div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero)))) hD,?_⟩
  intro K ι _ e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR T hT ψ hbin W Yp X Y Z hX hY hZ A hA hb
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let V : HeightSpace→ℂ := fun t=>sourceMellinWeight W0 W1 X Y Z
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
    ((17/50:ℂ)+t.1.2*Complex.I)
  let F := E.indicator (fun t=>V t*cubeArithmeticSum S hS hmax η R T hT W Yp a e t)
  let mass : ℝ := A
  have hm : 0≤mass := hA
  let scale : ℝ := X^(4/25:ℝ)*Z^(a+16*e-33/50)*Y^(-a-6*e)
  have hs : 0≤scale := by dsimp [scale];positivity
  have hv (t : HeightSpace) : ‖V t‖=scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ := by
    have hxre : (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I).re=a+16*e := by simp
    have hwre : (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I).re=1-a-6*e := by simp
    have hzre : ((17/50:ℂ)+t.1.2*Complex.I).re=17/50 := by simp
    dsimp [V]
    rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ,hxre,hwre,hzre]
    have hs0 : X^(1/2-(17/50:ℝ))*Z^((a+16*e)+17/50-1)*Y^((1-a-6*e)-1)=scale := by
      rw [show (1/2-17/50:ℝ)=4/25 by norm_num,
        show (a+16*e)+17/50-1=a+16*e-33/50 by ring,
        show (1-a-6*e)-1=-a-6*e by ring]
    rw [hs0]
    simp [onLines]
  have hp := hprofile (a+16*e) (by constructor <;> linarith) (17/50) ⟨le_rfl,le_rfl⟩
    (1-a-6*e) (by constructor <;> linarith)
  simp only [pow_zero,one_mul] at hp
  have hg : Integrable (fun t=>scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass) heightMeasure :=
    (hp.1.const_mul scale).mul_const mass
  have hf := cube_common_profile_integral e a B H i he he' ha ha' hB hH S hS hmax hfirst η R hR
    T hT ψ hbin W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  change Integrable F heightMeasure ∧ _ at hf
  have hb' (t : HeightSpace) : ‖F t‖≤scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass := by
    by_cases ht : t∈E
    · dsimp only [F]
      rw [Set.indicator_of_mem ht,norm_mul,hv]
      exact mul_le_mul_of_nonneg_left (hb t ht) (by positivity)
    · dsimp only [F]
      rw [Set.indicator_of_notMem ht,norm_zero]
      positivity
  rw [hf.2,norm_mul]
  calc
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(∫t,scale*‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖*mass ∂heightMeasure) :=
      mul_le_mul_of_nonneg_left ((norm_integral_le_integral_norm _).trans (integral_mono hf.1.norm hg hb')) (norm_nonneg _)
    _ = ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*(∫t,‖onLines W0 W1 (a+16*e) (17/50) (1-a-6*e) t‖ ∂heightMeasure)*mass) := by
      rw [integral_mul_const,integral_const_mul]
    _ ≤ ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*(scale*D*mass) := by gcongr;exact hp.2
    _ = _ := by dsimp [scale,mass];ring
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2662

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralDyadicWeight
Source SHA256: 731176a3f226ff14ad0eea1ab1f73c8cd8c81d870dd6672676298e1abcdd0f22
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2663



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma dyadic_weighted_rows_card (α r C U B : ℝ) (hC : 0≤C) (hU : 0<U)
    (R : Finset FreeRow) (hcard : (R.card:ℝ)≤B)
    (hR : ∀u∈R,U≤rowNorm u ∧ rowNorm u≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*rowNorm u^α)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      B*C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (α-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<rowNorm u := hU.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      change rowNorm u^(-r)*F u≤_
      calc
        _ ≤ rowNorm u^(-r)*(C*rowNorm u^α) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*rowNorm u^(α-r) := by
          rw [show α-r=(-r)+α by ring,Real.rpow_add hN]; ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U (rowNorm u) (α-r)
            (by norm_num) (by norm_num) hU (by simpa using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) := by simp
    _ ≤ B*(C*ProbeSelectedPrimeSums.annularPower 1 2 (α-r)*U^(α-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

lemma annular_power_uniform (p pmax : ℝ) (hp : p≤pmax) :
    ProbeSelectedPrimeSums.annularPower 1 2 p≤max 1 ((2:ℝ)^pmax) := by
  unfold ProbeSelectedPrimeSums.annularPower
  rw [Real.one_rpow]
  exact max_le_max le_rfl (Real.rpow_le_rpow_of_exponent_le (by norm_num) hp)

def mixedSourceExponent (a v d R q : ℝ) : ℝ :=
  ProbeCentralExponent.sourceExponent a v R q+(d-v)*R

lemma mixed_physical_exponent (Z a v d R q e eps loss mesh : ℝ) (N : ℕ)
    (hZ : 0<Z) :
    ((Z^(17/48:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(23/48:ℝ))^(-a-6*e))*
      ((Z^d)^R*(Z^v)^(a-1/2+12*e+eps*(N+8)-17/50)*Z^(-2/75+q/6+mesh/6+loss))=
    Z^(mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

lemma mixed_source_slack (a v d R q μ Rmax : ℝ)
    (hR : 0≤R) (hRmax : R≤Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedSourceExponent a v d R q≤ProbeCentralExponent.sourceExponent a v R q+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedSourceExponent
  linarith

lemma dyad_conductor_margin (Z v margin : ℝ) (hZ : 0<Z) (hmargin : 2≤Z^margin)
    (R : Finset FreeRow) (hR : ∀u∈R,rowNorm u≤2*Z^v) :
    ∀u∈R,rowNorm u≤Z^((v+2*margin)-margin) := by
  intro u hu
  calc
    rowNorm u≤2*Z^v := hR u hu
    _ ≤ Z^margin*Z^v := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ.le _)
    _ = _ := by rw [←Real.rpow_add hZ]; congr 1; ring
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2663

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins
Source SHA256: 635ed51704661906d6c751bed052cfbacde4d5d9207179be65d328877f7d034d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2664


namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorRowCount ProbeCentralExponent

lemma balanced_count_range (δ x Δ loss : ℝ) (hδ : 0≤δ) (hd : δ≤5/6)
    (hx : 0≤x) (hx' : x≤1/2) (hΔ : 0≤Δ) (hΔ' : Δ≤1/8)
    (hl : 0≤loss) (hl' : loss≤1/32) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    1-δ≤R ∧ R≤3/2 := by
  have ht := balanced_cutoff_bounds hδ hd hx hx'
  have hp0 := mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤Endpoint.balancedCutoff δ (1/2-x)-1 by linarith)
  have hp1 := mul_le_mul_of_nonneg_left ht.2 (show 0≤5/6-δ by linarith)
  dsimp only
  unfold Endpoint.balancedRowCount
  constructor <;> nlinarith

lemma balanced_mixed_margin (δ x Δ loss ζ μ v d : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
    mixedSourceExponent ((1+δ)/2) v d R (δ*x)-(3/16+Δ)≤
      -49/440640-(51/64)*Δ+(13/16)*loss+2*ζ+(3/2)*μ := by
  dsimp only
  let R := Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss
  have hr := balanced_count_range δ x Δ loss hδ hd hx hx' hΔ hΔ' hl hl'
  have hlo : 0≤R+δ/2-17/50 := by dsimp [R]; linarith [hr.1]
  have hhi : R+δ/2-17/50≤2 := by dsimp [R]; linarith [hr.2]
  have hm := balanced_source_margin δ x R Δ loss ζ v hδ hd hx hx' le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d R (δ*x) μ (3/2)
    (by dsimp [R];linarith [hr.1]) hr.2 hμ hdv
  linarith

lemma high_mixed_margin (δ q Δ loss ζ μ v d : ℝ)
    (hδ : 5/6≤δ) (hd : δ≤1) (hq : q≤δ/2)
    (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ) :
    mixedSourceExponent ((1+δ)/2) v d (1-δ+loss) q-(3/16+Δ)≤
      -1/48-δ/16-Δ+(13/16)*loss+2*ζ+μ := by
  have hlo : 0≤(1-δ+loss)+δ/2-17/50 := by linarith
  have hhi : (1-δ+loss)+δ/2-17/50≤2 := by linarith
  have hm := high_source_margin δ (1-δ+loss) q Δ loss ζ v hq le_rfl hζ hv hlo hhi
  have hs := mixed_source_slack ((1+δ)/2) v d (1-δ+loss) q μ 1
    (by linarith) (by linarith) hμ hdv
  linarith

lemma balanced_mixed_saving (δ x Δ loss ζ μ v d other saving : ℝ)
    (hδ : 0≤δ) (hd : δ≤5/6) (hx : 0≤x) (hx' : x≤1/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hl : 0≤loss) (hl' : loss≤1/32)
    (hζ : 0≤ζ) (hv : v≤13/16+ζ) (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : (13/16)*loss+2*ζ+(3/2)*μ+other+saving≤49/440640) :
    mixedSourceExponent ((1+δ)/2) v d
      (Endpoint.balancedRowCount δ (1/2-x)+Δ/4+loss) (δ*x)+other≤3/16+Δ-saving := by
  have hm := balanced_mixed_margin δ x Δ loss ζ μ v d hδ hd hx hx' hΔ hΔ' hl hl' hζ hv hμ hdv
  linarith
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2664

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeScale
Source SHA256: 8455534043a275bbc802b7e6f3f5435a833dfabd40d63c5ab66ea439503bdab2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2665



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification
local notation "O" => HeckeFamily.O

theorem cube_height_budget_eventually (n : ℕ) (τ dmin cost : ℝ)
    (hτ : 0<τ) (hc : 0≤cost) (hgap : 2*τ<dmin*cost) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → ∀d : ℝ,dmin≤d →
      (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost := by
  have habs := HeckeDyadic.constant_absorbed_eventually
    ((3*(n:ℝ)+5)^2) (dmin*cost-2*τ) (by linarith)
  filter_upwards [habs,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi d hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by
    push_cast
    nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^2 := by
      apply sq_le_sq₀ (by positivity) (by positivity) |>.mpr hx
    _ = (3*(n:ℝ)+5)^2*Z^(2*τ) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_two,←Real.rpow_mul hZp.le]
      congr 1
      ring
    _ ≤ Z^(dmin*cost-2*τ)*Z^(2*τ) :=
      mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^(dmin*cost) := by rw [←Real.rpow_add hZp];congr 1;ring
    _ ≤ (Z^d)^cost := by
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (mul_le_mul_of_nonneg_right hd hc)

theorem ray_cube_conductor_eventually (M : Ideal O) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually
    ((conductorConstant*M.absNorm:ℕ):ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu
  calc
    _ = ((conductorConstant*M.absNorm:ℕ):ℝ)*rowNorm u := by simp [rowNorm]
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2665

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralHeightCost
Source SHA256: f707a9e752921c6a6fd7dfbb36a4b1edb1633ed90393cd7fe86f28fe9164f1c3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2666



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem cube_height_power_eventually (n : ℕ) (τ p loss : ℝ)
    (hτ : 0<τ) (hp : 0≤p) (hgap : τ*p<loss) :
    ∀ᶠ Z : ℝ in atTop,∀i : ℕ,i≤n → (3+(3*i+2:ℕ)*Z^τ)^p≤Z^loss := by
  have hh := HeckeDyadic.constant_absorbed_eventually ((3*(n:ℝ)+5)^p)
    (loss-τ*p) (by linarith)
  filter_upwards [hh,eventually_ge_atTop (1:ℝ)] with Z hC hZ
  intro i hi
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hpow : 1≤Z^τ := Real.one_le_rpow hZ hτ.le
  have hi' : (i:ℝ)≤n := by exact_mod_cast hi
  have hx : 3+(3*i+2:ℕ)*Z^τ≤(3*(n:ℝ)+5)*Z^τ := by push_cast;nlinarith
  calc
    _ ≤ ((3*(n:ℝ)+5)*Z^τ)^p := Real.rpow_le_rpow (by positivity) hx hp
    _ = (3*(n:ℝ)+5)^p*Z^(τ*p) := by
      rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
    _ ≤ Z^(loss-τ*p)*Z^(τ*p) := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hZp.le _)
    _ = Z^loss := by rw [←Real.rpow_add hZp];congr 1;ring

theorem central_remaining_rowCost_scale (e eps τ loss : ℝ) (n : ℕ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) (hτ : 0<τ)
    (hgap : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,∀(η : Character) (u : FreeRow)
      {ι : Type*} [Fintype ι] (ψ : ι→Character) (a : ℝ) (i : ℕ),i≤n →
      51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤(3*i+2:ℕ)*Z^τ →
      ‖centralRemainingScalar S hS η u x w z‖*
        ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*Z^τ)≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := central_remaining_rowCost_bound e eps he he' heps S hS hfirst
  refine ⟨C,hC,?_⟩
  filter_upwards [cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hgap,
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hheight hZ
  intro η u ι _ ψ a i hi ha ha1 hbin x w z hx hw hz hxi
  have hb := hbound η u ψ (Z^τ) a ((3*i+2:ℕ)*Z^τ) i hZ ha ha1 le_rfl hbin x w z hx hw hz hxi
  exact hb.trans (mul_le_mul_of_nonneg_left (hheight i hi) (by unfold rowNorm;positivity))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2666

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubePhaseBins
Source SHA256: c09694944039cd83fefea60beb77ac553d3779cf9814d736f38d3963ddd413c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2667



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins_on_cube (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hmax : ∀P∈S,P.IsMaximal)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh δ ν : ℝ) (n : ℕ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hν : 0<ν) (hheight : 2*τ<dmin*cost) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤rowNorm u →
      (ProbePhysical.calibrationForSet S hmax).residueMonoid u.val≠0 →
      rowNorm u≤Z^(d-ν) →
    ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (t : ProbeMellinBoundary.HeightSpace),rmin≤r → r≤R →
      ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
    let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := ProbeRayPhaseBins.actual_phase_bins M H hH S hS hbad W A B hA hAB hWs hW
    R dmin dmax rmin τ ε e κ cost mesh (33/50) (33/50) δ
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hδ hbudget hgap
  filter_upwards [hb,cube_height_budget_eventually n τ dmin cost hτ hcost hheight,
    ray_cube_conductor_eventually M ν hν,eventually_gt_atTop (0:ℝ)] with Z hb hh hc hZ
  intro d hd hd' hU hT η u hu hcal hrow a i hi ha ha' hbin r t hr hr' ht
  have hs := calibration_nonzero_supported S hmax hbad u.val hcal
  have hpow : 0≤Z^τ := Real.rpow_nonneg hZ.le _
  have hbuffer : ((3*i+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*i+2:ℕ)*Z^τ := by
    push_cast
    nlinarith
  have hfreq := (cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht hpow hbuffer).2.2
  have hb' := hb d hd hd' hU hT η u hu hs (hc u d hrow) a i ha ha' hbin r
    ((17/50:ℂ)+t.1.2*Complex.I) hr hr'
    (by norm_num) (by norm_num) (by simpa using hfreq) (hh i hi d hd)
  exact hb'

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2667

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeBound
Source SHA256: e5608bd6e9fe2c79895cd36e7556b7bd34064d57f270eafefa76cc7f050318f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2668





namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem poolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_cube_prime_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      ∀r : Fin N→ℝ,(∀j,rmin≤r j) → (∀j,r j≤R) →
      let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q : Fin N→ℂ := fun j=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z
      let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh (Q j)
      (∀j,0≤g j ∧ g j≤a-1/2 ∧ g j∈labels (a-1/2) mesh ∧
        ‖Q j‖≤(Y j)^(g j+mesh) ∧ (0<g j → (Z^d)^(2*r j*g j)≤‖Q j‖^2)) ∧
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>poolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh)) := by
  have hb (j : Fin N) := actual_phase_bins_on_cube M H hH S hS.prime hS.bad hmax (W j) c b hc hcb
    (hWs j) (hW j) R dmin dmax rmin τ ε e κ cost mesh δ margin n
    hR hdmin hdmax hrmin hτ hε he he1 hκ hcost hmesh hδ hbudget hgap hmargin hheight
  have hbAll := Filter.eventually_all.mpr hb
  obtain ⟨C,hC,hbound⟩ := ProbeCentralPrimeSum.actual_central_prime_sum N e eps c b A
    he he1 heps hc (hc.trans_le hcb) hA S hS hfirst hmax
  refine ⟨C,hC,?_⟩
  intro η
  have hscale := HeckeDetectorDyadicGeometry.uniform_scale_threshold dmin 2 hdmin
  filter_upwards [hbAll,central_pool_good_eventually η e c b dmin rmin he hc hcb hdmin hrmin,
    cube_height_power_eventually n τ (2+4*eps) loss hτ (by positivity) hloss,
    hscale,source_cube_height_eventually τ hτ] with Z hb hg hheightZ hscaleZ hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin r hr hr'
  dsimp only
  intro hdis t ht
  let Y : Fin N→ℝ := fun j=>(Z^d)^(r j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh
    (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
  have hU : 2≤Z^d := hscaleZ d hd
  have hUp : 0<Z^d := by linarith
  have hY (j : Fin N) : 1≤Y j := Real.one_le_rpow (by linarith) (hrmin.trans_le (hr j)).le
  have hYp (j : Fin N) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hphase (j : Fin N) := hb j d hd hd' hU hZ.2 η u hulo hcal huhi a i hi ha ha1 hbin (r j) t (hr j) (hr' j) ht
  refine ⟨fun j=>⟨(hphase j).1,(hphase j).2.1,(hphase j).2.2.1,(hphase j).2.2.2.1,(hphase j).2.2.2.2.1⟩,?_⟩
  let p : Fin N→ℝ := fun j=>(Y j)^(g j+mesh)
  have hp (j : Fin N) : 1≤p j := Real.one_le_rpow (hY j) (by have := (hphase j).1;dsimp [g];linarith)
  have hph (j : Fin N) : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j := by
    have hj := (hphase j).2.2.2.2.2
    have hsum : phaseSlot u (T j) (W j) (Y j) z=
        ∑P∈T j,W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val)) :=
      Finset.sum_coe_sort (T j) (fun P=>W j ((P.val.absNorm:ℝ)/Y j)*(P.val.absNorm:ℂ)^(z-1)*
        (-star (CanonicalRowCompletion.idealRowHom u.val P.val)))
    have hj' : ‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ)+g j+mesh) := by
      rw [hsum]
      convert hj using 1
      simp only [Y,g,z]
      congr 1
      norm_num
    apply hj'.trans_eq
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  have hgood (j : Fin N) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P∈T j) := hg (RayQuotient.identityClass M H) S d (r j) hd (hr j) P hP
  have hfreq := cube_buffered_heights t ((3*i+1:ℕ)*Z^τ) (Z^τ) i ht
    (Real.rpow_nonneg (zero_le_one.trans hZ.1) _) (by push_cast;have hh : 0≤Z^τ := Real.rpow_nonneg (zero_le_one.trans hZ.1) _;nlinarith)
  have hbound' := hbound u hu η (rayCubeFamily M H hH u) (Z^τ) a i hZ.2 ha ha1 hbin T
    (poolOutside M H S N c b Y) hdis (fun j P hP=>(hgood j P hP).2.1)
    (fun j P hP=>(hgood j P hP).2.2.1) (fun j P hP=>(hgood j P hP).2.2.2)
    W Y hY (fun j=>(hWs j).trans Ioo_subset_Icc_self) hWB
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z
    (by simp) (by simp) (by simp [z]) (by simpa using hfreq.1) (by simpa using hfreq.2.1) p hp hph
  have hprod : (∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)=∏j,(Y j)^(-(4/25:ℝ)+g j+mesh) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    dsimp only [p]
    rw [←Real.rpow_add (hYp j)]
    congr 1
    ring
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*Z^τ)^(2+4*eps)*((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      exact hbound'.trans_eq (by ring)
    _ ≤ C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
        ((∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by
      apply mul_le_mul_of_nonneg_right _ (mul_nonneg
        (Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hYp j).le _))
        (Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))))
      exact mul_le_mul_of_nonneg_left (hheightZ i hi) (by unfold rowNorm;positivity)
    _ = _ := by rw [hprod]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2668

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFixedPrimes
Source SHA256: f6fe5e084a764b4732fe2c6a67b80ee898c493c1451e3ea6100c348ddecd2857
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2669



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots ProbeCentralAllSlots HeckePrimeAmplitudeBins
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem fixedPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_fixed_cube_prime_bound (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (_hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(u : FreeRow),u.val≠1 → Z^δ≤rowNorm u →
      (calibrationForSet S hmax).residueMonoid u.val≠0 → rowNorm u≤Z^(d-margin) →
      ∀(a : ℝ) (i : ℕ),i≤n → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let x : ℂ := (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I)
      let w : ℂ := (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I)
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      let Q : Fin N→ℂ := fun j=>HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z
      let g : Fin N→ℝ := fun j=>amplitude (Y j) (a-1/2) mesh (Q j)
      (∀j,0≤g j ∧ g j≤a-1/2 ∧ g j∈labels (a-1/2) mesh ∧
        ‖Q j‖≤(Y j)^(g j+mesh) ∧ (0<g j → (Z^d)^(2*(ell j/d)*g j)≤‖Q j‖^2)) ∧
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
          (fun j=>fixedPoolOutside M H S N c b Y j (P j).val (P j).property) W Y x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*Z^loss*
          (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh)) := by
  obtain ⟨C,hC,hbound⟩ := actual_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax W hWs hW hWB
  have hdj := power_pools_eventually_disjoint (RayQuotient.identityClass M H) S
    (fun _ : Fin N=>c) (fun _=>b) ell (fun _=>hc) (fun _=>hcb) hell
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,hdj,eventually_ge_atTop (1:ℝ)] with Z hbound hdis hZ
  intro d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin
  dsimp only
  intro t ht
  have hd0 : 0<d := hdmin.trans_le hd
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hr (j : Fin N) : rmin≤ell j/d := by
    apply (le_div_iff₀ hd0).mpr
    exact (by nlinarith [mul_le_mul_of_nonneg_right hd' hrmin.le] : rmin*d≤dmax*rmin).trans (hello j)
  have hr' (j : Fin N) : ell j/d≤R := by
    apply (div_le_iff₀ hd0).mpr
    exact (hellhi j).trans (by nlinarith [mul_le_mul_of_nonneg_right hd hR])
  have heq (j : Fin N) : (Z^d)^(ell j/d)=Z^(ell j) := by
    rw [←Real.rpow_mul hZp.le,mul_div_cancel₀ _ hd0.ne']
  have hb := hbound d hd hd' u hu hulo hcal huhi a i hi ha ha1 hbin (fun j=>ell j/d) hr hr'
  have hfun : (fun j : Fin N => (Z^d)^(ell j/d)) = (fun j => Z^(ell j)) := funext heq
  rw [hfun] at hb
  exact hb hdis t ht

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2669

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeSlotExponent
Source SHA256: fcbf599c51475455f27ccc157f023268cf927aa8617e5a8a04d1f87c962e387e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2670



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorPhysicalSelection

lemma source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=1/6) :
    (∑j∈slots,ell j/d)=1/(6*d) := by
  rw [←Finset.sum_div,hell]
  ring

lemma source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    weightedMean slots (fun j=>ell j/d) g=6*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0<Z) (hd : d≠0) (hell : ∑j∈slots,ell j=1/6) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(2/75:ℝ)+weightedMean slots (fun j=>ell j/d) g/6+mesh/6) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  ring

lemma source_slot_spike_scale (Z d ell g : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(2*(ell/d)*g)=Z^(2*ell*g) := by
  rw [←Real.rpow_mul hZ]
  congr 1
  field_simp

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2670

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralClassArithmetic
Source SHA256: f58267253e1b165a56047c50f88e68e1ce7a71db7d038ee9d9a19e74ccab568f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2671



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem classPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_class_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a q D Rcount : ℝ),0≤v → 51/100≤a → a≤1 → 0≤D → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      (rows.card:ℝ)≤D*(Z^d)^Rcount →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      (∀u∈rows,weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) ((17/50:ℂ)+t.1.2*Complex.I)))=q) →
      ‖cubeArithmeticSum S hS hmax η rows T (classPoolOutside M H S N c b Y) W Y a e t‖≤
        C*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let AA : ℝ := max 1 ((2:ℝ)^(4/25+12*e+eps*(N+8)))
  have hAA : 0<AA := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C*AA,mul_pos hC hAA,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v a q D Rcount hv ha ha' hD rows hrows hnorm hcard i hi hbin
  dsimp only
  intro t ht hq
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let α : ℝ := a-1/2+12*e+eps*(N+8)
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=>classPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let E : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-2/75+q/6+mesh/6)
  have hE : 0≤E := by dsimp [E];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤E*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha' (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=Z^(-2/75+q/6+mesh/6) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(2/75:ℝ)+weightedMean Finset.univ (fun j=>ell j/d) g/6+mesh/6) from
        source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      rw [show weightedMean Finset.univ (fun j=>ell j/d) g=q from hq u hu]
      congr 1 ; ring
    have hh' := hh.2
    rw [hp] at hh'
    convert hh' using 1 ; dsimp [F,E,α,Y,z,g] ; ring
  have hh := dyadic_weighted_rows_card α (17/50) E (Z^v) (D*(Z^d)^Rcount) hE
    (Real.rpow_pos_of_pos hZp _) rows hcard hnorm F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (classPoolOutside M H S N c b Y) W Y a e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  have hAp : ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)≤AA :=
    annular_power_uniform _ _ (by dsimp [α];linarith)
  apply (hsum.trans hh).trans
  have hpow : (Z^d)^Rcount*Z^loss*Z^(-2/75+q/6+mesh/6)*(Z^v)^(α-17/50)=
      Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) := by
    simp_rw [←Real.rpow_mul hZp.le]
    rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ (D*(Z^d)^Rcount)*E*AA*(Z^v)^(α-17/50) := by gcongr
    _ = _ := by
      dsimp [E]
      calc
        _ = (C*AA)*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          ((Z^d)^Rcount*Z^loss*Z^(-2/75+q/6+mesh/6)*(Z^v)^(α-17/50)) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2671

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralClassPartition
Source SHA256: da2a07d3a4197a63bdb33874785ac439f6e9e15e029acd328726b62077bf21d2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2672




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition

lemma sum_amplitudeRows {Slot : Type*} (rows : Finset FreeRow) (slots : Finset Slot)
    (U cap mesh : ℝ) (hm : 0<mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (f : FreeRow→ℂ) :
    (∑u∈rows,f u)=∑bin : BinLabel slots cap mesh,
      ∑u∈amplitudeRows rows slots U cap mesh hm widths Q bin,f u := by
  have hmap : ∀u∈rows,amplitudeLabel slots U cap mesh hm widths Q u∈
      (Finset.univ : Finset (BinLabel slots cap mesh)) := by simp
  exact (Finset.sum_fiberwise_of_maps_to hmap f).symm

lemma cubeArithmeticSum_amplitude_partition {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ) :
    cubeArithmeticSum S hS hmax η rows T hT W Yp a e t=
      ∑bin : BinLabel slots cap mesh,cubeArithmeticSum S hS hmax η
        (amplitudeRows rows slots U cap mesh hm widths Q bin) T hT W Yp a e t := by
  unfold cubeArithmeticSum
  exact sum_amplitudeRows rows slots U cap mesh hm widths Q _

theorem cubeArithmeticSum_class_uniform {N : ℕ} {Slot : Type*}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (rows : Finset FreeRow) (T : Fin N→Finset ProbePhysical.PrimeIdeal)
    (hT : ∀j P,P∈T j→P.val∉S) (W : Fin N→ℝ→ℂ) (Yp : Fin N→ℝ)
    (a e : ℝ) (t : HeightSpace) (slots : Finset Slot) (U cap mesh : ℝ)
    (hm : 0<mesh) (hcap : cap≤1/2) (widths : Slot→ℝ) (Q : FreeRow→Slot→ℂ)
    (A : ℝ) (hA : 0≤A)
    (hclass : ∀bin : BinLabel slots cap mesh,
      (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty →
      ‖cubeArithmeticSum S hS hmax η (amplitudeRows rows slots U cap mesh hm widths Q bin)
        T hT W Yp a e t‖≤A) :
    ‖cubeArithmeticSum S hS hmax η rows T hT W Yp a e t‖≤
      (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^slots.card*A := by
  rw [cubeArithmeticSum_amplitude_partition S hS hmax η rows T hT W Yp a e t slots U cap mesh hm widths Q]
  calc
    _ ≤ ∑bin : BinLabel slots cap mesh,A := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro bin _
      by_cases hn : (amplitudeRows rows slots U cap mesh hm widths Q bin).Nonempty
      · exact hclass bin hn
      · have he := Finset.not_nonempty_iff_eq_empty.mp hn
        simpa only [he,cubeArithmeticSum,Finset.sum_empty,norm_zero] using hA
    _ = (Fintype.card (BinLabel slots cap mesh):ℝ)*A := by simp
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ hA
      exact_mod_cast HeckeDetectorClassBudget.bin_card_le slots cap mesh hcap hm
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2672

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorArithmetic
Source SHA256: fa1776b3b1e481c0d2ca8a3d512ee6d21f70067c54406825bbc0b500637260f8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2673



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem floorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let α : ℝ := 1/100+12*e+eps*(N+8)
  let AA := ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)
  have hAA : 0≤AA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 _ (by norm_num)
  refine ⟨256*C*(AA+1),by positivity,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=>floorPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-1/40+mesh/6)
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤D*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi (51/100) i hi le_rfl (by norm_num) (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=>HeckePrimeAmplitudeBins.amplitude (Y j) ((51/100:ℝ)-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hellpos (j : Fin N) : 0≤ell j := by
      exact (mul_nonneg hdmax hrmin.le).trans (hello j)
    have hq := weightedMean_bounds Finset.univ (fun j=>ell j/d) g (1/50)
      (fun j _=>div_nonneg (hellpos j) hd0.le)
      (by rw [source_slot_length_sum _ _ _ hellsum];positivity)
      (fun j _=>⟨(hh.1 j).1,by have hhj := (hh.1 j).2.1;dsimp [g,Y,z];norm_num at hhj ⊢;exact hhj⟩)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))≤Z^(-1/40+mesh/6) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(2/75:ℝ)+weightedMean Finset.univ (fun j=>ell j/d) g/6+mesh/6) from
        source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      apply Real.rpow_le_rpow_of_exponent_le hZ
      linarith [hq.2]
    have hN : 0≤rowNorm u := (rowNorm_ge_one u).trans' (by norm_num)
    have h := hh.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
    convert h using 1 ; dsimp [F,D,α,Y,z,g] ; norm_num ; ring
  have hh := dyadic_weighted_rows α (17/50) D (Z^v) hD (Real.one_le_rpow hZ hv) rows hnorm
    F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (floorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  apply (hsum.trans hh).trans
  have hpow : Z^loss*Z^(-1/40+mesh/6)*(Z^v)^(1+α-17/50)=
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6) := by
    rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ 256*D*(AA+1)*(Z^v)^(1+α-17/50) := by change 256*D*AA*_≤_;gcongr;linarith
    _ = _ := by
      dsimp [D]
      calc
        _ = (256*C*(AA+1))*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^loss*Z^(-1/40+mesh/6)*(Z^v)^(1+α-17/50)) := by ring
        _ = _ := by rw [hpow]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2673

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobal
Source SHA256: 939c8135a734160ac57b378794270e10f569d4fe9557553da8da78a22b865271
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2674



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem globalFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_global_floor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      ‖cubeArithmeticSum S hS hmax η rows T (globalFloorPoolOutside M H S N c b Y) W Y (51/100) e t‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6) := by
  obtain ⟨C,hC,hbound⟩ := actual_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  let θ : ℝ := 67/100+12*e+eps*(N+8)
  have hθ : 0<θ := by dsimp [θ];positivity
  obtain ⟨Cg,hCg,hgeom⟩ := bounded_dyadic_power_sum θ hθ
  refine ⟨C*Cg,mul_pos hC hCg,?_⟩
  intro η
  filter_upwards [hbound η,eventually_gt_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  intro t ht
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Rn : ℕ→Finset FreeRow := fun k=>rows∩dyadicRows 1 k
  let term : FreeRow→ℂ := fun u=>frequencyWeight ((17/50:ℂ)+t.1.2*Complex.I) ⟨u.val,u.property.1⟩*
    ∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
      (fun j=>globalFloorPoolOutside M H S N c b Y j _ (P j).property) W Y
      (((51/100+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-51/100-6*e:ℝ):ℂ)+t.2*Complex.I)
      ((17/50:ℂ)+t.1.2*Complex.I)
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(loss-1/40+mesh/6)
  have hD : 0≤D := by dsimp [D];positivity
  have hdyad (k : ℕ) : ‖∑u∈Rn k,term u‖≤D*((2:ℝ)^k)^θ := by
    let vk := Real.logb Z ((2:ℝ)^k)
    have hvk : 0≤vk := Real.logb_nonneg hZ (one_le_pow₀ (by norm_num))
    have heq : Z^vk=(2:ℝ)^k := Real.rpow_logb hZp hZ.ne' (by positivity)
    have hsub : Rn k⊆rows := Finset.inter_subset_left
    have hn : ∀u∈Rn k,Z^vk≤rowNorm u ∧ rowNorm u≤2*Z^vk := by
      intro u hu
      have h := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [heq,one_mul] using And.intro h.1 h.2.le
    have hh := hb d hd hd' vk hvk (Rn k) (fun u hu=>hrows u (hsub hu)) hn i hi
      (fun u hu=>hbin u (hsub hu)) t ht
    change ‖∑u∈Rn k,term u‖≤_ at hh
    apply hh.trans_eq
    have hp : Z^(vk*θ+loss-1/40+mesh/6)=Z^(loss-1/40+mesh/6)*((2:ℝ)^k)^θ := by
      rw [show vk*θ+loss-1/40+mesh/6=(loss-1/40+mesh/6)+vk*θ by ring,Real.rpow_add hZp,
        Real.rpow_mul hZp.le,heq]
    change C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(vk*θ+loss-1/40+mesh/6)=_
    rw [hp]
    dsimp [D]
    ring
  have hpart := retained_dyadic_sum rows (Z^v) (fun u hu=>⟨(hrows u hu).1,hnorm u hu⟩) term
  change ‖∑u∈rows,term u‖≤_
  rw [hpart]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^v),‖∑u∈Rn k,term u‖ := norm_sum_le _ _
    _ ≤ ∑k∈smallDyadicIndices (Z^v),D*((2:ℝ)^k)^θ := Finset.sum_le_sum (fun k _=>hdyad k)
    _ = D*∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^θ := (Finset.mul_sum _ _ _).symm
    _ ≤ D*(Cg*(Z^v)^θ) := mul_le_mul_of_nonneg_left
      (hgeom (Z^v) (by positivity) (smallDyadicIndices (Z^v)) (fun k hk=>mem_smallDyadicIndices.mp hk)) hD
    _ = _ := by
      have hp : Z^(loss-1/40+mesh/6)*(Z^v)^θ=Z^(v*θ+loss-1/40+mesh/6) := by
        rw [←Real.rpow_mul hZp.le,←Real.rpow_add hZp]
        congr 1
        ring
      dsimp [D]
      calc
        _ = (C*Cg)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^(loss-1/40+mesh/6)*(Z^v)^θ) := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2674

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorGlobalIntegral
Source SHA256: c236312c955034a729457dbdb77a547bde73b3e156d1de423f41f1e54869dccb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2675



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem globalFloorIntegralPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_global_floor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      ‖finiteCentralCubeRows S hS hmax η rows T (globalFloorIntegralPoolOutside M H S N c b Yp) W Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
            ProbeCentralExponent.realLoss N v e eps loss mesh) := by
  obtain ⟨Ca,hCa,hbound⟩ := actual_global_floor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  obtain ⟨Cp,hCp,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cp*Ca,mul_pos hCp hCa,?_⟩
  intro η
  filter_upwards [hbound η,source_cube_height_eventually τ hτ] with Z hb hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only
  have hZp : 0<Z := zero_lt_one.trans_le hZ.1
  let Yp : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
  have hheight : (3*i+1:ℕ)*Z^τ≤(3*i+2:ℕ)*Z^τ := by
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZp.le _)
    exact_mod_cast (show 3*i+1≤3*i+2 by omega)
  let mass : ℝ := Ca*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)
  have hp := hprofile e (51/100) (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 le_rfl (by norm_num)
    hZ.2 hheight S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1) T
    (globalFloorIntegralPoolOutside M H S N c b Yp) (rayCubeFamily M H hH) hbin W Yp
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp mass (by dsimp [mass];positivity)
    (hb d hd hd' v hv rows hrows hnorm i hi hbin)
  apply hp.trans_eq
  rw [ProbeCentralExponent.physical_scale_identity Z (51/100) e hZp]
  have hpowers : Z^((25/48)*(51/100)-181/300+(105/8)*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)=
      Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
        ProbeCentralExponent.realLoss N v e eps loss mesh) := by
    rw [←Real.rpow_add hZp]
    congr 1
    unfold ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
    ring
  dsimp [mass]
  calc
    _ = (Cp*Ca)*(η.modulus.absNorm:ℝ)^(2*eps)*(Z^((25/48)*(51/100)-181/300+(105/8)*e)*
      Z^(v*(67/100+12*e+eps*(N+8))+loss-1/40+mesh/6)) := by ring
    _ = _ := by rw [hpowers]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2675

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorNormalized
Source SHA256: d7a307e8cc59fb06c5ac86406fdb396e8152c625f2fc1229951026d52baef90c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2676



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem normalizedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_floor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (normalizedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
            ProbeCentralExponent.realLoss N v e eps loss mesh+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨Cg,hCg,hbound⟩ := actual_global_floor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨Cg*Cn,mul_pos hCg hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v hv rows hrows hnorm i hi hbin
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (ProbeCentralExponent.sourceExponent (51/100) v 1 (1/100)+
    ProbeCentralExponent.realLoss N v e eps loss mesh) nu]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2676

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorSaving
Source SHA256: c042e664a6afb7241320106edd6ceb2d9a8f90b963101219d778fe39f6338974
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2677


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem savingFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_cube_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu)
    (ζ saving : ℝ) (hζ : 0≤ζ) (hζhi : ζ≤3/16) (_hsaving : 0<saving)
    (htotal : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+saving≤7/1200) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → v≤13/16+ζ → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (savingFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(3/16-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := actual_normalized_floor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C,hC,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v hv hvhi rows hrows hnorm i hi hbin
  dsimp only
  have hh := hb d hd hd' v hv rows hrows hnorm i hi hbin
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hm := ProbeCentralExponent.floor_source_margin (1/100) 0 ζ v le_rfl hζ hvhi
  have hl := ProbeCentralExponent.realLoss_bound N v e eps loss mesh (by linarith) he.le heps.le
  apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
  linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2677

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorCollected
Source SHA256: 3184f79b178efe97235a325683c5a677b6b8e15bbc65a46714aa26fdfc1b1089
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2678



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem collectedFloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_floor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu)
    (ζ saving : ℝ) (hζ : 0≤ζ) (hζhi : ζ≤3/16) (hsaving : 0<saving)
    (htotal : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+saving≤7/1200) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v : ℝ),0≤v → v≤13/16+ζ → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,rowNorm u≤Z^v) →
      ∀idx : FreeRow→ℕ,(∀u∈rows,idx u≤n) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e) →
      let Yp : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (collectedFloorPoolOutside M H S N c b Yp) (fun j y=>(W j y:ℂ)) Yp
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(3/16-saving) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := actual_floor_cube_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ζ saving hζ hζhi hsaving htotal
  refine ⟨(n+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η] with Z hb
  intro d hd hd' v hv hvhi rows hrows hnorm idx hidx hbin
  dsimp only
  let Yp : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
  let hT := collectedFloorPoolOutside M H S N c b Yp
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Yp)) : ℂ)
  let Ri : ℕ→Finset FreeRow := fun i=>rows.filter (fun u=>idx u=i)
  have hnormer := (hb d hd hd' v hv hvhi ∅ (by simp) (by simp) 0 (Nat.zero_le n) (by simp)).1
  refine ⟨hnormer,?_⟩
  have hpart := finiteCentralCubeRows_bin_partition S hS hmax η rows T hT WC Yp W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (Z^τ) idx (fun _=>0) n 0 (fun u hu=>⟨hidx u hu,le_rfl⟩)
  have heq : finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑i∈Finset.range (n+1),finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ) := by
    simpa [cubeBinRows,Ri] using hpart
  change ‖finiteCentralCubeRows S hS hmax η rows T hT WC Yp W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [heq,Finset.sum_div]
  apply (norm_sum_le _ _).trans
  have hboundi (i : ℕ) (hi : i∈Finset.range (n+1)) :
      ‖finiteCentralCubeRows S hS hmax η (Ri i) T hT WC Yp W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>51/100) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving) := by
    have hsub : Ri i⊆rows := Finset.filter_subset _ _
    have hbi : ∀u∈Ri i,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<51/100+2*e := by
      intro u hu
      have hh := hbin u (hsub hu)
      rwa [(Finset.mem_filter.mp hu).2] at hh
    exact (hb d hd hd' v hv hvhi (Ri i) (fun u hu=>hrows u (hsub hu))
      (fun u hu=>hnorm u (hsub hu)) i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hbi).2
  calc
    _ ≤ ∑i∈Finset.range (n+1),C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16-saving) := Finset.sum_le_sum hboundi
    _ = _ := by simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2678

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCount
Source SHA256: a52ccf6c3e635d3305336b6ede7b6b82271c0b8606178e410be3110e632734af
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2679




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff

theorem balanced_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorFixedAmplitudeCount.fixed_amplitude_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ ν C height q i hU ha hd hε hε' hΔ hΔ' hν hC hh hf Label Slot _ B hne hq hmom
  have hδ : 0<2*a-1 := by linarith
  have hqb := HeckeDetectorFixedAmplitudeCount.batch_mean_bounds B hne (by linarith) q hq
  have hx : 0≤q/(2*a-1) := div_nonneg hqb.1 hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith [hqb.2])
  have ht := cutoff_bounds (2*a-1) q hδ.le
  have hc' := hcount a ε (cutoff (2*a-1) q) T allowance Δ ν C height q i
    hU ha hd hε hε' ht.1 ht.2 hΔ hΔ' hν hC hh hf B hq hmom
  have he : max (shortExponent (2*a-1) (q/(2*a-1)) (cutoff (2*a-1) q))
      (longExponent (2*a-1) (cutoff (2*a-1) q)) =
      Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1)) := by
    rw [cutoff_eq_balanced (2*a-1) q hδ hd hqb.1 hqb.2]
    exact HeckeDetectorRowCount.balanced_count_identity hδ.le hd hx hx'
  rw [he] at hc'
  exact hc'

theorem high_adaptive_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀ y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀ y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    ∃ c κ K₀ : ℝ,0<c ∧ c≤1 ∧ 0<κ ∧ 0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type*} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ c κ C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨c,κ,K₀,hc,hc1,hκ,hK,hcount⟩ :=
    HeckeDetectorHighBatchCount.high_batch_count_from_raw_moments
      M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  refine ⟨c,κ,K₀,hc,hc1,hκ,hK,?_⟩
  filter_upwards [hcount] with U hcount
  intro a ε T allowance Δ C height q i hU ha ha' hε hε' hC hh hf
  rw [cutoff_eq_high (2*a-1) q ha]
  exact hcount a ε T allowance Δ C height i hU ha.le ha' hε hε' hC hh hf

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2679

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCountParameters
Source SHA256: 88b1a01167a672f116f0285f9384ed5c888cc456a55da7dbc71c90498632a968
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2680


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

structure CountParameters (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ) (εm : ℝ) where
  cB : ℝ
  kB : ℝ
  cH : ℝ
  kH : ℝ
  cB_pos : 0<cB
  cB_one : cB≤1
  kB_pos : 0<kB
  cH_pos : 0<cH
  cH_one : cH≤1
  kH_pos : 0<kH
  balanced : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠU : ℝ in atTop,
      ∀(a ε T allowance Δ ν C height q : ℝ) (i : ℕ),
      1<U → 51/100<a → 2*a-1≤5/6 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i:ℕ)*T≤height →
      ∀{Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots U ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external U) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cB kB C height εm) →
      (B.rows.card:ℝ)≤(Fintype.card Label:ℝ)*(dyadicLength U:ℝ)^2* fiberConstant C height K₀*
        (Fintype.card B.Bin:ℝ)*
        U^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+
          Δ/4+159*ε+εm+B.mesh+7*ν)
  high : ∃K₀ : ℝ,0≤K₀ ∧ ∀ᶠ U : ℝ in atTop,
      ∀ (a ε T allowance Δ C height q : ℝ) (i : ℕ),
      1<U → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C → 0≤height →
      2*Real.pi*allowance+(3*i : ℕ)*T≤height →
      ∀ {Label Slot : Type} [Fintype Label] (B : Batch M H Label Slot U a ε (cutoff (2*a-1) q) T allowance i),
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ cH kH C height εm) →
      (B.rows.card : ℝ)≤(Fintype.card Label:ℝ)*(HeckeDetectorWitnessRows.dyadicLength U:ℝ)^2*
        fiberConstant C height K₀*(Fintype.card B.Bin:ℝ)*U^(1-(2*a-1)+78*ε+εm)

theorem exists_count_parameters
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm) :
    Nonempty (CountParameters M H εm) := by
  obtain ⟨cB,kB,KB,hcB,hcB1,hkB,hKB,hbalanced⟩ := balanced_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  obtain ⟨cH,kH,KH,hcH,hcH1,hkH,hKH,hhigh⟩ := high_adaptive_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
  exact ⟨⟨cB,kB,cH,kH,hcB,hcB1,hkB,hcH,hcH1,hkH,⟨KB,hKB,hbalanced⟩,⟨KH,hKH,hhigh⟩⟩⟩

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2680

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorInverseRawField
Source SHA256: 405a368337f3dbf5ce14ce525de5c67a6949edffa9f193654c3832958c95e869
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2681





namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.ProbeDetectorInverseRawField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open HeckeDetectorInverseFiberCount DetectorDictionaryInverseClippedUniform
open ProbeHighRowFamily ProbeFinalAssembly

private theorem raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro H D hH hD hcap rows hrows
  apply (h H D hH hD hcap rows hrows).trans
  gcongr

theorem fixed_raw_profiles (c κ:ℝ)(hc:0<c)(hκ:0<κ):
    ∃J:ℕ,∀data:RowData,∃C:ℝ,0<C ∧
      ∀reverse:Bool,∀n:ℕ,n≤2→∀U:ℝ,0<U→∀tstar r:ℝ,
      ∀s∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height→t∈Set.Icc (-height) height→
      let W:=twistProfile (logTest (orientedProfile reverse (inverseTest U tstar r)) n) s t;
      RawMoment data W c κ (C*(1+height)^J) ∧
      RawMoment data (scaleProfile W) c κ (C*(1+height)^J):=by
  obtain ⟨J,hreference⟩:=DetectorDictionaryInverseRawReference.raw_reference_moment
    referenceWindow (1/18) (13/4) c κ (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) hc hκ
  obtain ⟨K,C,hC,hfamily⟩:=DetectorDictionaryInverseRawUniform.raw_pair_height_uniform J
  refine ⟨K,?_⟩
  intro data
  obtain ⟨A,hA,href⟩:=hreference data
  exact ⟨A*C,mul_pos hA hC,hfamily data c κ A hA.le href⟩

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_raw
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(εm:ℝ)(counts:CountParameters M H εm):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧
    ∀{Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ},0<U→
    ∀(B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height→∀n:ℕ,n≤2→∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J):=by
  obtain ⟨JB,hB⟩:=fixed_raw_profiles counts.cB counts.kB counts.cB_pos counts.kB_pos
  obtain ⟨JH,hHraw⟩:=fixed_raw_profiles counts.cH counts.kH counts.cH_pos counts.kH_pos
  refine ⟨JB+JH,?_⟩
  intro η
  let data:=sourceMomentData M H hH S hS η
  choose CB hCB hb using (fun label=>hB (data label))
  choose CH hCH hh using (fun label=>hHraw (data label))
  let C:ℝ:=1+(∑label,CB label)+(∑label,CH label)
  have hsumB:0≤∑label,CB label:=Finset.sum_nonneg (fun j _=>(hCB j).le)
  have hsumH:0≤∑label,CH label:=Finset.sum_nonneg (fun j _=>(hCH j).le)
  have hC:0<C:=by dsimp [C];linarith
  have hCBound (label):CB label≤C:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hCB j).le) (Finset.mem_univ label)
    dsimp [C];linarith
  have hCHound (label):CH label≤C:=by
    have he:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hCH j).le) (Finset.mem_univ label)
    dsimp [C];linarith
  refine ⟨C,hC,?_⟩
  intro Slot U a ε tstar T allowance i hU B hdata bin label left right hne height hheight n hn s hs t ht F W
  have hd:F.rowData=data label:=by
    change B.data label=data label
    rw [hdata]
  have hbase:1≤1+height:=by linarith
  by_cases hbranch:2*a-1≤5/6
  · simp only [hbranch,ite_true]
    have hpair:=hb label F.reverse n hn U hU tstar F.r s hs height t hheight ht
    have hconstant:CB label*(1+height)^JB≤C*(1+height)^(JB+JH):=
      mul_le_mul (hCBound label) (pow_le_pow_right₀ hbase (Nat.le_add_right _ _))
        (by positivity) hC.le
    rw [hd]
    exact ⟨raw_mono _ _ _ _ _ _ hconstant hpair.1,raw_mono _ _ _ _ _ _ hconstant hpair.2⟩
  · simp only [hbranch,ite_false]
    have hpair:=hh label F.reverse n hn U hU tstar F.r s hs height t hheight ht
    have hconstant:CH label*(1+height)^JH≤C*(1+height)^(JB+JH):=
      mul_le_mul (hCHound label) (pow_le_pow_right₀ hbase (Nat.le_add_left _ _))
        (by positivity) hC.le
    rw [hd]
    exact ⟨raw_mono _ _ _ _ _ _ hconstant hpair.1,raw_mono _ _ _ _ _ _ hconstant hpair.2⟩

end SevenEighths.ProbeDetectorInverseRawField

end

end OAI
end OAIOriginalModule2681

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyData
Source SHA256: 40177414737797476aa62242da6bbe91bd42c505887517be6d1ab19a6cef1628
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2682




namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure SourceData {Δ : ℝ} (D : HighData Δ) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal : ∀P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ→ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded : ∀x,0≤w x ∧ w x≤1
  nonzero : w≠0
  complex_eq : ∀x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real : ∀x,(W x).im=0
  nonnegative : ∀x,0≤(W x).re

theorem exists_source_data {Δ : ℝ} (D : HighData Δ) : Nonempty (SourceData D) := by
  obtain ⟨S,_,hS,hfirst,hmax⟩ := exists_fixed_source D.e D.e_pos ∅ (by simp)
  obtain ⟨w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩ := exists_fixed_probe_window
  exact ⟨⟨S,hS,hmax,hfirst,w,W,hw,hc,hs,hp,hb,hn,he,hWn,hWs,hr,hWpos⟩⟩

def SourceData.modulus {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Ideal O := ∏P∈F.S,P

instance {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : NeZero F.modulus :=
  ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩

instance {Δ : ℝ} {D : HighData Δ} (F : SourceData D) : Finite (O ⧸ F.modulus) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne F.modulus)

theorem source_count_parameters {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (CountParameters F.modulus ⊤ D.t) := by
  exact exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

def SourceData.probe {Δ : ℝ} {D : HighData Δ} (F : SourceData D) (η : Character) : ℝ→ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  normalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=>F.w) F.W F.W η

theorem SourceData.probe_low {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (loss : ℝ) (hloss : 0<loss) (η : Character) :
    F.probe η=O[atTop](fun Z : ℝ=>Z^(3/16+loss)) := by
  exact normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j=>(D.slots_bounds j).1) D.slots_injective D.slots_sum
    (fun _=>F.w) (fun _=>F.smooth) (fun _=>F.compact) (fun _=>F.support)
    (fun _=>F.bounded) (fun _=>F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2682

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorMomentFiberGates
Source SHA256: 6e5374af596fc8f2ba7daf95b8ed1b024df28d5955c86fae1d4b95431451f1b9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2683



namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem sourceMoment_fiber_large_eventually
    (S:Finset (Ideal O))(hS:∀P∈S,Prime P)(η:Character)
    {Slot:Type*}[Fintype Slot](ell:Slot→ℝ)(hell:∀s,0<ell s):
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→
      ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→
      ∀bin j J K,∀hne:(B.fiberRows bin j J K).Nonempty,∀s:Slot,
        ((baseCharacter (B.fiber bin j J K hne).rowData).modulus.absNorm:ℝ)<
          1*(Z^d)^((B.fiber bin j J K hne).widths s):=by
  filter_upwards [sourceMoment_large_eventually M H hH S hS η ell hell] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hw bin j J K hne s
  change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s)
  rw [hdata,hw,one_mul]
  exact hZ.2 d hd j s

theorem sourceMoment_fiber_support {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)
    {Slot:Type*}{U a ε tstar T allowance:ℝ}{i:ℕ}
    (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) Slot U a ε tstar T allowance i)
    (hprofile:B.profile=(fun _=>(F.W:ℝ→ℂ)))(hupper:B.upper=(fun _=>2))
    (bin:B.Bin)(j:Sum Bool (RayQuotient.Characters M H))
    (J K:Fin (HeckeDetectorWitnessRows.dyadicLength U))
    (hne:(B.fiberRows bin j J K).Nonempty):
    ∀s x,(B.fiber bin j J K hne).profile s x≠0→
      x∈Set.Icc 1 ((B.fiber bin j J K hne).upper s):=by
  intro s x hx
  change B.profile s x≠0 at hx
  change x∈Set.Icc 1 (B.upper s)
  rw [hprofile] at hx
  rw [hupper]
  exact F.complex_support hx

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2683

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorMomentPrimeGeometry
Source SHA256: d56137ee520fdc699bb8a3990fe0a876fbf007094000bdb7cd5b5c392332ab03
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2684




namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O

theorem sourceMoment_physical_scale (Z d ell : ℝ) (hZ : 0≤Z) (hd : d≠0) :
    (Z^d)^(ell/d)=Z^ell := by
  rw [←Real.rpow_mul hZ,mul_div_cancel₀ _ hd]

theorem sourceMoment_separation_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hinj : Function.Injective ell) :
    ∀ᶠ Z : ℝ in atTop, 1≤Z ∧ ∀d : ℝ,0<d→∀s t : Slot,s≠t→
      2*(Z^d)^(ell s/d)<1*(Z^d)^(ell t/d) ∨
      2*(Z^d)^(ell t/d)<1*(Z^d)^(ell s/d) := by
  have hs : ∀ᶠ Z : ℝ in atTop,∀s t : Slot,s≠t→
      2*Z^(ell s)<1*Z^(ell t) ∨ 2*Z^(ell t)<1*Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro s
    apply Filter.eventually_all.mpr
    intro t
    by_cases he : s=t
    · exact Filter.Eventually.of_forall (fun _ h=>False.elim (h he))
    rcases lt_or_gt_of_ne (fun h=>he (hinj h)) with hlt|hlt
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell s) (ell t)
        (by norm_num) hlt] with Z hZ _
      exact Or.inl hZ
    · filter_upwards [ProbeRaySlots.annular_power_separation 1 2 (ell t) (ell s)
        (by norm_num) hlt] with Z hZ _
      exact Or.inr hZ
  filter_upwards [hs,eventually_ge_atTop (1:ℝ)] with Z hs hZ
  refine ⟨hZ,?_⟩
  intro d hd s t hst
  simp only [sourceMoment_physical_scale Z d _ (by linarith) hd.ne']
  exact hs s t hst

theorem sourceMoment_fixedBase_norm_one (data : RowData) (P : Ideal O) (hP : Prime P)
    (hlarge : ((baseCharacter data).modulus.absNorm:ℝ)<(P.absNorm:ℝ)) :
    ‖fixedBase data.η data.m data.f P‖=1 := by
  rw [←baseCharacter_coeff]
  exact PrincipalSignalComparison.idealCoeff_norm_one_of_coprime
    (baseCharacter data) P hP.ne_zero
    (ProbeRaySlots.prime_coprime_of_norm_gt (baseCharacter data) ⟨P,hP⟩ hlarge)

theorem sourceMoment_primeProfile_norm {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re≤1)
    (P : Ideal O) : ‖primeProfile F.W X ζ P‖≤1 := by
  by_cases hw : F.W ((P.absNorm:ℝ)/X)=0
  · simp [primeProfile,hw]
  have hx := F.complex_support hw
  have hp : 0<(P.absNorm:ℝ)/X := lt_of_lt_of_le (by norm_num) hx.1
  have hnorm : ‖F.W ((P.absNorm:ℝ)/X)‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded _).1]
    exact (F.bounded _).2
  rw [primeProfile,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hp]
  have hr : ((P.absNorm:ℝ)/X)^((ζ-1).re)≤1 :=
    (Real.rpow_le_rpow_of_exponent_le hx.1
      (show (ζ-1).re≤0 by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
        (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hnorm hr (Real.rpow_nonneg hp.le _) (by norm_num : (0:ℝ)≤1)

theorem sourceMoment_tuple_quotient {ι : Type*} [Fintype ι]
    (data : RowData) (A : ι→ℂ) (p : ι→Ideal O) :
    star (∏s,A s)/fixedBase data.η data.m data.f (∏s,p s)=
      ∏s,star (A s)/fixedBase data.η data.m data.f (p s) := by
  rw [map_prod,star_prod,Finset.prod_div_distrib]

section Live
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem sourceMoment_live_disjoint {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} (ell : ι→ℝ)
    (U : ℝ) (hU : 0<U) (s t : ι)
    (hsep : 2*U^(ell s)<1*U^(ell t) ∨ 2*U^(ell t)<1*U^(ell s)) :
    Disjoint (livePrimes M H F.W 2 (U^(ell s))) (livePrimes M H F.W 2 (U^(ell t))) := by
  apply Finset.disjoint_left.mpr
  intro P hs ht
  have hs' := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support P hs
  have ht' := livePrime_data M H F.W 1 2 (U^(ell t))
    (Real.rpow_pos_of_pos hU _) F.complex_support P ht
  rcases hsep with hsep|hsep <;> linarith [hs'.2.2.1,hs'.2.2.2,ht'.2.2.1,ht'.2.2.2]

theorem sourceMoment_live_denominator {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (hU : 0<U)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖fixedBase data.η data.m data.f (∏s,p s)‖=1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro s _
  have hs := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support (p s) (Fintype.mem_piFinset.mp hp s)
  exact sourceMoment_fixedBase_norm_one data (p s) hs.1 ((hlarge s).trans_le hs.2.2.1)

theorem sourceMoment_live_quotient_norm {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (ζ : ι→ℂ) (hU : 0<U)
    (hz : ∀s,(ζ s).re=17/50)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=>livePrimes M H F.W 2 (U^(ell s)))) :
    ‖star (∏s,primeProfile F.W (U^(ell s)) (ζ s) (p s))/
      fixedBase data.η data.m data.f (∏s,p s)‖≤1 := by
  rw [norm_div,norm_star,sourceMoment_live_denominator M H F data U ell hU hlarge p hp,
    div_one,norm_prod]
  exact Finset.prod_le_one₀ (fun s _=>norm_nonneg _)
    (fun s _=>sourceMoment_primeProfile_norm F _ _ (by rw [hz s];norm_num) _)
end Live

theorem sourceMoment_capacity_eventually {Slot : Type*} [Fintype Slot]
    (ell : Slot→ℝ) (hell : ∀s,0≤ell s) (ε : ℝ) (hε : 0<ε) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ ∀d : ℝ,1/200≤d→
      (∀s,1≤2*(Z^d)^(ell s/d)) ∧ ∀selected : Finset Slot,
      (∏s:selected,2*(Z^d)^(ell s/d))≤
        (Z^d)^((∑s:selected,ell s/d)+ε) := by
  have ht := (tendsto_rpow_atTop (show 0<ε/200 by positivity)).eventually
    (eventually_ge_atTop ((2:ℝ)^Fintype.card Slot))
  filter_upwards [ht,eventually_ge_atTop (1:ℝ)] with Z ht hZ
  refine ⟨hZ,?_⟩
  intro d hd
  have hd0 : 0<d := by linarith
  have hz0 : 0<Z := zero_lt_one.trans_le hZ
  have hu0 : 0<Z^d := Real.rpow_pos_of_pos hz0 _
  have hu1 : 1≤Z^d := Real.one_le_rpow hZ hd0.le
  refine ⟨?_,?_⟩
  · intro s
    have hh : 1≤(Z^d)^(ell s/d) := Real.one_le_rpow hu1 (div_nonneg (hell s) hd0.le)
    linarith
  · intro selected
    have hf : (2:ℝ)^selected.card≤(2:ℝ)^Fintype.card Slot :=
      pow_le_pow_right₀ (by norm_num) (Finset.card_le_univ selected)
    have hp : (2:ℝ)^selected.card≤(Z^d)^ε := by
      rw [←Real.rpow_mul hz0.le]
      exact (hf.trans ht).trans (Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith))
    rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
      ←Real.rpow_sum_of_pos hu0,Real.rpow_add hu0]
    calc
      _ ≤ (Z^d)^ε*(Z^d)^(∑s:selected,ell s/d) :=
        mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hu0.le _)
      _ = _ := mul_comm _ _

section Source
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem sourceMoment_fiber_prime_geometry_eventually
    {Δ : ℝ} {D : Parameters.HighData Δ} (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (εg : ℝ) (hεg : 0<εg) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ ∀d : ℝ,1/200≤d→
      ∀(a ε tstar T allowance : ℝ)(i : ℕ)
      (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH F.S F.exclusions.prime η→
      B.profile=(fun _ x=>(F.w x:ℂ))→B.upper=(fun _=>2)→
      B.widths=(fun s=>D.ell s/d)→(∀s,(B.external s).re=17/50)→
      ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      let f:=B.fiber bin j J K hne
      (∀s t,s≠t→Disjoint
        (livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))
        (livePrimes M H (f.profile t) (f.upper t) ((Z^d)^(f.widths t)))) ∧
      ∀selected : Finset (Fin D.N),
        (∀s:selected,1≤2*(Z^d)^(f.widths s)) ∧
        (∏s:selected,2*(Z^d)^(f.widths s))≤
          (Z^d)^((∑s:selected,f.widths s)+εg) ∧
        ∀p : selected→Ideal O,
        p∈Fintype.piFinset (fun s:selected=>
          livePrimes M H (f.profile s) (f.upper s) ((Z^d)^(f.widths s)))→
        Function.Injective p ∧ CanonicalQuadraticSieve.Admissible (∏s:selected,p s) ∧
        (∀s:selected,((p s).absNorm:ℝ)≤2*(Z^d)^(f.widths s)) ∧
        ‖fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖=1 ∧
        ‖star (∏s:selected,primeProfile (f.profile s) ((Z^d)^(f.widths s)) (f.external s) (p s))/
          fixedBase f.rowData.η f.rowData.m f.rowData.f (∏s:selected,p s)‖≤1 := by
  filter_upwards [sourceMoment_separation_eventually D.ell D.slots_injective,
    sourceMoment_capacity_eventually D.ell (fun s=>(D.slots_bounds s).1.le) εg hεg,
    sourceMoment_fiber_large_eventually M H hH F.S F.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1)] with Z hsep hcap hlarge
  refine ⟨hsep.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin j J K hne
  have hprofile : B.profile=(fun _=>(F.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext s x
    exact (F.complex_eq x).symm
  have hd0 : 0<d := by linarith
  have hu : 0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
  have hs := hsep.2 d hd0
  have hc := hcap.2 d hd
  have hl := hlarge.2 d hd0 a ε tstar T allowance i B hdata hwidths bin j J K hne
  dsimp only
  change (∀s t,s≠t→Disjoint
      (livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s)))
      (livePrimes M H (B.profile t) (B.upper t) ((Z^d)^(B.widths t)))) ∧ _
  refine ⟨?_,?_⟩
  · intro s t hst
    rw [hprofile,hupper,hwidths]
    exact sourceMoment_live_disjoint M H F (fun s=>D.ell s/d) (Z^d) hu s t (hs s t hst)
  · intro selected
    change (∀s:selected,1≤2*(Z^d)^(B.widths s)) ∧
      (∏s:selected,2*(Z^d)^(B.widths s))≤(Z^d)^((∑s:selected,B.widths s)+εg) ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [hwidths]
      exact fun s=>hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p∈Fintype.piFinset (fun s:selected=>livePrimes M H F.W 2 ((Z^d)^(D.ell s/d))) := by
        change p∈Fintype.piFinset (fun s:selected=>livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s))) at hp
        simpa only [hprofile,hupper,hwidths] using hp
      have hl' : ∀s:selected,((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(D.ell s/d) := by
        intro s
        have hh:=hl s
        change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t:selected,s≠t→2*(Z^d)^(D.ell s/d)<1*(Z^d)^(D.ell t/d) ∨
          2*(Z^d)^(D.ell t/d)<1*(Z^d)^(D.ell s/d) := by
        intro s t hst
        exact hs s t (fun he=>hst (Subtype.ext he))
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact live_tuple_injective M H (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible M H (B.data j) (fun _=>F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=>D.ell s/d) (Z^d) hu (fun _=>F.complex_support) hl' hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm:ℝ)≤2*(Z^d)^(B.widths s)
        rw [hwidths]
        exact (livePrime_data M H F.W 1 2 ((Z^d)^(D.ell s/d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s) (Fintype.mem_piFinset.mp (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact sourceMoment_live_denominator M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) hu hl' p (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s:selected,primeProfile (B.profile s) ((Z^d)^(B.widths s)) (B.external s) (p s))/
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s:selected,p s)‖≤1
        rw [hprofile,hwidths]
        exact sourceMoment_live_quotient_norm M H F (B.data j) (Z^d)
          (fun s:selected=>D.ell s/d) (fun s:selected=>B.external s) hu (fun s=>hz s) hl' p (by simpa only [Fintype.mem_piFinset] using hp')

end Source
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2684

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePrimeGates
Source SHA256: aed901c0afa3c508a1ca3f907ef07e2143c4489f7c5635785d2b75a4a9faa2a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2685



namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open InverseInitialExcludedPool InverseInitialExcludedOverlap Filter CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O

theorem deleted_large_eventually {Label Slot:Type*}[Fintype Label][Fintype Slot]
    (data:Label→RowData)(ell:Slot→ℝ)(hell:∀s,0<ell s) :
    ∀ᶠZ:ℝ in atTop,1≤Z ∧ ∀d:ℝ,0<d→∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<(Z^d)^(ell s/d) := by
  have ht:∀ᶠZ:ℝ in atTop,∀j:Label,∀s:Slot,
      ((deletedBase (data j)).modulus.absNorm:ℝ)<Z^(ell s) := by
    apply Filter.eventually_all.mpr
    intro j
    apply Filter.eventually_all.mpr
    intro s
    exact (tendsto_rpow_atTop (hell s)).eventually (eventually_gt_atTop _)
  filter_upwards [eventually_ge_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro d hd j s
  rw [←Real.rpow_mul (by linarith:0≤Z),mul_div_cancel₀ _ hd.ne']
  exact ht j s

theorem deletedBase_supported (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) : CanonicalQuadraticSieve.Supported I := by
  by_contra hn
  exact hI (deletedBase_zero_unsupported data I hn)

theorem deleted_source_live_prime {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)(data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
    (X:ℝ)(hX:0<X)(ζ:ℂ)(hζ:ζ.re≤1)
    (hlarge:((deletedBase data).modulus.absNorm:ℝ)<X)
    (P:Ideal O)(hP:P∈livePrimes M H F.W 2 X) :
    Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖star (primeProfile F.W X ζ P)/idealCoeff (deletedBase data) P‖≤1 := by
  have hd:=livePrime_data M H F.W 1 2 X hX F.complex_support P hP
  have hcop:=ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨P,hd.1⟩
    (hlarge.trans_le (by simpa only [one_mul] using hd.2.2.1))
  have hn:=PrincipalSignalComparison.idealCoeff_norm_one_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hne:=HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime (deletedBase data) P hd.1.ne_zero hcop
  have hout:outside (excluded data) P := by
    by_contra hh
    exact hne (deleted_zero_outside (baseCharacter data) (excluded data)
      (reflectionExcludedPrimes_prime (basePeriod data)) P hh)
  refine ⟨hd.1,hout,hne,hn,?_⟩
  rw [norm_div,norm_star,hn,div_one]
  exact ProbeHighRowFamily.sourceMoment_primeProfile_norm F X ζ hζ P

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2685

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeletedEnergy
Source SHA256: 863a349427c1d7aef0d480a89ee40abd6708c4e9add6cec8fe00f3426e3199d7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2686




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic CanonicalQuadraticSieve
open CanonicalRowCompletion ConcretePrimeRowBridge ConcreteTraceCRT
open InverseInitialDetectorSource
open InverseMoment InverseInitialProfile InverseInitialRawDictionary InverseInitialPhysicalSlots
open InverseInitialConjugateEnergy InverseInitialEnergyCallerWindow InverseInitialExcludedPeriod
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseRawConjugateGates
open IdealMobiusDivisorSum Filter
local notation "O"=>HeckeFamily.O

theorem deletedSelectedSource_tuple {ι:Type*}[Fintype ι](data:RowData)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (U r bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O):
    deletedSelectedSource data M H W V U r 0 0 bW b ell ζ u=
      ∑x:Tuple (fun i=>livePrimes M H (V i) (b i) (U^(ell i))),
        (∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i).val)/
          idealCoeff (deletedBase data) (x i).val)*
        originalTotalPolynomial (originalSource U r bW) (∏i,(x i).val)
          (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u := by
  rw [sum_tuple_original (fun i=>livePrimes M H (V i) (b i) (U^(ell i)))
    (fun x=>(∏i,star (primeProfile (V i) (U^(ell i)) (ζ i) (x i))/
      idealCoeff (deletedBase data) (x i))*
      originalTotalPolynomial (originalSource U r bW) (∏i,x i)
        (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1) W U r (∑i,ell i) u)]
  unfold deletedSelectedSource
  apply Finset.sum_congr rfl
  intro x hx
  simp only [star_prod,map_prod,Finset.prod_div_distrib]
  have ht:twistedProfile W 0 0=W:=by
    funext t
    simp [twistedProfile,HeckeDyadic.shift]
  rw [ht]
  rfl

theorem deleted_source_energy {Δ:ℝ}{D:Parameters.HighData Δ}
    (F:ProbeFinalAssembly.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι],Fintype.card ι≤K →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(ell:ι→ℝ)(ζ:ι→ℂ),
      (∀i,0≤ell i) → (∀i,(ζ i).re≤1) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint
        (fun i=>livePrimes M H F.W 2 (U^(ell i)))) →
      (∀i,((deletedBase data).modulus.absNorm:ℝ)<U^(ell i)) →
    ∀r:ℝ,0≤r → r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀j∈idealDivisors (∏P∈excluded data,P),
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖deletedSelectedSource data M H (childLogTest W θ) (fun _=>F.W)
        U (shiftedExponent data U r j) 0 0 bo (fun _=>2) ell ζ u‖^2)≤
        C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨eta,heta,degree,henergy⟩:=padded_source_energy W ao bo hao hab hsW hW εm hεm K
  refine ⟨degree,?_⟩
  intro data
  obtain ⟨hq,hqset,hn,hperiod⟩:=raw_conjugate_base_gates data
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy (deletedPeriod (basePeriod data)) hq
  obtain ⟨Ushift,hshift⟩:=eventually_atTop.mp (marked_shift_eventually data eta heta)
  refine ⟨C,max U₀ Ushift,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst hK M neM H ell ζ hell hζ hdis hlarge r hr hfirst hsecond j hj rows hrows θ
  have hU0:U₀≤U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hUp:0<U:=zero_lt_one.trans hUone
  have hjshift: r-eta≤shiftedExponent data U r j ∧ shiftedExponent data U r j≤r ∧
      U^(shiftedExponent data U r j)=U^r/(j.absNorm:ℝ):=
    (hshift U ((le_max_right _ _).trans hU)).2 j hj r
  let L:ι→Finset (Ideal O):=fun i=>livePrimes M H F.W 2 (U^(ell i))
  let coeff:ι→Ideal O→ℂ:=fun i P=>star (primeProfile F.W (U^(ell i)) (ζ i) P)/
    idealCoeff (deletedBase data) P
  have hg (i:ι)(P:Ideal O)(hP:P∈L i):
      Prime P ∧ InverseInitialExcludedPool.outside (excluded data) P ∧
      idealCoeff (deletedBase data) P≠0 ∧ ‖idealCoeff (deletedBase data) P‖=1 ∧
      ‖coeff i P‖≤1:=
    deleted_source_live_prime F data M H _ (Real.rpow_pos_of_pos hUp _) (ζ i) (hζ i) (hlarge i) P hP
  have hratio (i:ι)(P:Ideal O)(hP:P∈L i):((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2:=
    F.complex_support (Finset.mem_filter.mp hP).2
  have hh:=henergy U hU0 hK L ell coeff hell
    (fun i P hP=>(hg i P hP).1)
    (fun i P hP=>deletedBase_supported data P (hg i P hP).2.2.1)
    hdis hratio (fun i P hP=>(hg i P hP).2.2.2.2)
    (fun i P hP=>by rw [hqset];exact (hg i P hP).2.1)
    (fun _=>F.W) (fun _=>F.complex_support)
    (fun i P hP=>(Finset.mem_filter.mp hP).2)
    (idealCoeff (deletedBase data)).toMonoidHom (idealCoeff_norm_le_one (deletedBase data))
    hperiod (fun I hI=>raw_conjugate_zero_outside data I (by simpa [hqset] using hI))
    r (shiftedExponent data U r j) hr hjshift.1 hjshift.2.1 hfirst hsecond rows hrows θ
  simpa only [deletedSelectedSource_tuple,L,coeff] using hh

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2686

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiberEnergy
Source SHA256: 43703afe82fd36fc057045e279bd09ff907bf607712b2581b39bf40e52d9a16c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2687



namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeInverseAmplification HeckeDyadic HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer InverseMoment InverseInitialProfile
open ConcreteTraceCRT ConcretePrimeRowBridge CanonicalRowCompletion
open DetectorDictionaryInverseRawInitialGates DetectorDictionaryInverseMarkedPhysicalRows
open InverseInitialPhysicalSlots IdealMobiusDivisorSum
local notation "O"=>HeckeFamily.O

theorem fiber_reference_energy {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:ProbeFinalAssembly.SourceData D)
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃degree:ℕ,∀data:RowData,∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀(M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)
      {Label Slot:Type}{a ε tstar T allowance:ℝ}{i:ℕ}
      (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot),
      F.rowData=data → selected.card≤K →
      (∀s∈selected,F.profile s=S.W) → (∀s∈selected,F.upper s=2) →
      (∀s∈selected,0≤F.widths s) → (∀s∈selected,(F.external s).re≤1) →
      (((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected)) →
      (∀s∈selected,((deletedBase data).modulus.absNorm:ℝ)<U^(F.widths s)) →
      0≤F.r → F.r+2*(∑s∈selected,F.widths s)<1 →
      2*F.r+8*(∑s∈selected,F.widths s)<3 → ∀v:ℝ,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
        F.physicalProduct selected u‖^2)≤C*U^(1+εm)*((1+‖v‖)^degree)^2 := by
  have hsor (b:Bool):Function.support (orientedProfile b W)⊆Set.Icc ao bo := by
    cases b
    · exact hsW
    · intro x hx
      apply hsW
      simpa [orientedProfile] using hx
  have hWor (b:Bool):ContDiff ℝ ∞ (orientedProfile b W) := by
    cases b
    · exact hW
    · exact Complex.conjCLE.contDiff.comp hW
  choose J hj using fun b:Bool=>deleted_source_energy S (orientedProfile b W) ao bo hao hab
    (hsor b) (hWor b) εm hεm K
  refine ⟨∑b:Bool,J b,?_⟩
  intro data
  choose C U₀ hC hU₀ hb using fun b:Bool=>hj b data
  let Tbad:=idealDivisors (∏P∈excluded data,P)
  let Ctotal:ℝ:=((Tbad.card:ℝ)+1)^2*(∑b:Bool,C b)
  have hCsum:0<∑b:Bool,C b:=Finset.sum_pos (fun b _=>hC b) Finset.univ_nonempty
  refine ⟨Ctotal,max (U₀ false) (U₀ true),by dsimp [Ctotal];positivity,
    lt_max_of_lt_left (hU₀ false),?_⟩
  intro U hU M neM H Label Slot a ε tstar T allowance i F selected hdata hK hprofile hupper
    hell hext hdis hlarge hr hfirst hsecond v
  have hUb (b:Bool):U₀ b≤U:=by cases b <;> exact le_trans (by simp) hU
  have hUone:1<U:=(hU₀ false).trans_le (hUb false)
  have hpr (s:selected):F.profile s=S.W:=hprofile s s.property
  have hup (s:selected):F.upper s=2:=hupper s s.property
  have hprof:(fun s:selected=>F.profile s)=(fun _=>(S.W:ℝ→ℂ)):=funext hpr
  have hups:(fun s:selected=>F.upper s)=(fun _=>2):=funext hup
  have hslots:∀s∈selected,∀x,F.profile s x≠0 → x∈Set.Icc (1:ℝ) (F.upper s) := by
    intro s hs x hx
    rw [hprofile s hs] at hx
    rw [hupper s hs]
    exact S.complex_support hx
  have hlarge':∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<1*U^(F.widths s):=by
    simpa only [hdata,one_mul] using hlarge
  have hphys:=fiber_child_rows_le_deleted_sources F selected W v bo (fun _=>1) hUone
    (fun x hx=>(hsW hx).2) hslots hlarge'
  rw [hdata] at hphys
  let rows:Finset O:=F.rows.image (fun u=>u.val)
  have hsum (f:O→ℝ):(∑u∈rows,f u)=∑u∈F.rows,f u.val:=
    Finset.sum_image (fun u _ w _ he=>Subtype.ext he)
  have hrows:∀u∈rows,‖eisEmbedding u‖^2≤U := by
    intro u hu
    obtain ⟨w,hw,rfl⟩:=Finset.mem_image.mp hu
    rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    exact F.row_norm w hw
  have hpow (b:Bool):((1+‖orientedFrequency b v‖)^(J b))^2≤
      ((1+‖v‖)^(∑b:Bool,J b))^2 := by
    have hn:‖orientedFrequency b v‖=‖v‖:=by cases b <;> simp [orientedFrequency]
    rw [hn]
    apply pow_le_pow_left₀ (by positivity)
    apply pow_le_pow_right₀ (by linarith [norm_nonneg v])
    exact Finset.single_le_sum (fun b _=>Nat.zero_le _) (Finset.mem_univ b)
  have hterm (j:Ideal O)(hj:j∈Tbad):
      (∑u∈F.rows,‖deletedSelectedSource data M H
        (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
        (fun s:selected=>F.profile s) U (shiftedExponent data U F.r j)
        0 0 bo (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
        (fun s:selected=>F.external s) u.val‖^2)≤
      (∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2 := by
    rw [hprof,hups]
    have hdis':((Finset.univ:Finset selected):Set selected).PairwiseDisjoint
        (fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
      have heL:fiberLists F selected=(fun s:selected=>livePrimes M H S.W 2 (U^(F.widths s))) := by
        funext s
        dsimp only [fiberLists]
        rw [hpr s,hup s]
      rwa [heL] at hdis
    have hh:=hb F.reverse U (hUb F.reverse) (by simpa using hK)
      M H (fun s:selected=>F.widths s) (fun s:selected=>F.external s)
      (fun s=>hell s s.property) (fun s=>hext s s.property) hdis'
      (fun s=>hlarge s s.property) F.r hr
      (by simpa only [Finset.sum_coe_sort] using hfirst)
      (by simpa only [Finset.sum_coe_sort] using hsecond) j hj rows hrows (orientedFrequency F.reverse v)
    rw [hsum] at hh
    refine hh.trans ?_
    apply mul_le_mul _ (hpow F.reverse) (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by linarith) _)
    exact Finset.single_le_sum (fun b _=>(hC b).le) (Finset.mem_univ F.reverse)
  refine hphys.trans ?_
  change (Tbad.card:ℝ)*(∑j∈Tbad,_)≤_
  calc
    _≤(Tbad.card:ℝ)*(∑j∈Tbad,(∑b:Bool,C b)*U^(1+εm)*
        ((1+‖v‖)^(∑b:Bool,J b))^2):=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum hterm) (by positivity)
    _=(Tbad.card:ℝ)^2*(∑b:Bool,C b)*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      simp only [Finset.sum_const,nsmul_eq_mul];ring
    _≤Ctotal*U^(1+εm)*((1+‖v‖)^(∑b:Bool,J b))^2:=by
      dsimp [Ctotal]
      gcongr
      nlinarith [show 0≤(Tbad.card:ℝ) by positivity]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2687

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorInverseMarkedField
Source SHA256: 8d973abff1f405a970f9c5eb126df21c6fac48c55598f183eb47350deabc0120
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2688




namespace OAI

noncomputable section

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.ProbeDetectorInverseMarkedField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
local notation "O"=>HeckeFamily.O

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_marked {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀d:ℝ,(1/200:ℝ)≤d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=>D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height →
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
    ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
        ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t) := by
  obtain ⟨Jref,hreference⟩:=fiber_reference_energy S referenceWindow (1/18) (13/4)
    (by norm_num) (by norm_num)
    (fun x hx=>referenceWindow_support (subset_tsupport _ hx)) (referenceWindow.smooth ⊤)
    D.t D.t_pos D.N
  obtain ⟨J,Cfourier,hCfourier,hfourier⟩:=DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform Jref
  refine ⟨J,?_⟩
  intro η
  let data:=sourceMomentData M H hH S.S S.exclusions.prime η
  choose C U₀ hC hU₀ hb using fun label=>hreference (data label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0<Csum:=by
    have hh:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤Csum:=by
    have hh:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le) (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤d → U₀ label≤Z^d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  refine ⟨Cfourier*Csum,mul_pos hCfourier hCsum,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hscale,
    deleted_large_eventually data D.ell (fun s=>(D.slots_bounds s).1),
    sourceMoment_fiber_prime_geometry_eventually M H hH S η D.t D.t_pos] with Z hZ hscale hlarge hgeom
  refine ⟨hZ,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin label left right hne
    height hheight F selected hselected hfirst hsecond n hn s hs t ht
  have hd0:0<d:=by linarith
  have hUone:1<Z^d:=Real.one_lt_rpow hZ hd0
  have hUp:0<Z^d:=zero_lt_one.trans hUone
  have hprofile:B.profile=(fun _=>(S.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext j x
    exact (S.complex_eq x).symm
  have hfd:F.rowData=data label:=by change B.data label=data label;rw [hdata]
  have hfp (j):F.profile j=S.W:=by change B.profile j=S.W;rw [hprofile]
  have hfu (j):F.upper j=2:=by change B.upper j=2;rw [hupper]
  have hfw (j):F.widths j=D.ell j/d:=by change B.widths j=_;rw [hwidths]
  have hfe (j):(F.external j).re≤1:=by change (B.external j).re≤1;rw [hz j];norm_num
  have hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
    intro j hj k hk hjk
    exact (hgeom.2 d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz
      bin label left right hne).1 j k (fun he=>hjk (Subtype.ext he))
  have hlargeF:∀j∈selected,((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm:ℝ)<
      (Z^d)^(F.widths j) := by
    intro j hj
    rw [hfw]
    exact hlarge.2 d hd0 label j
  have hr:0≤F.r:=Real.logb_nonneg hUone (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have href (v:ℝ):
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest referenceWindow v)
        ((Z^d)^F.r) 0 0*F.physicalProduct selected u‖^2)≤
      (Csum*(Z^d)^(1+D.t))*(1+‖v‖)^(2*Jref) := by
    have hh:=hb label (Z^d) (hscale label d hd) M H F selected hfd
      (by simpa using Finset.card_le_univ selected) (fun j _=>hfp j) (fun j _=>hfu j)
      (fun j hj=>(F.widths_pos j (hselected hj)).le) (fun j _=>hfe j) hdis hlargeF hr hfirst hsecond v
    rw [(show 2*Jref=Jref*2 by omega),pow_mul]

    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hClabel label) (Real.rpow_nonneg hUp.le _)
  have hh:=hfourier F selected hUp (Csum*(Z^d)^(1+D.t)) (by positivity) href
    n hn s hs height t hheight ht
  convert hh using 1 ; ring

end SevenEighths.ProbeDetectorInverseMarkedField

end

end OAI
end OAIOriginalModule2688

/-! Original module: OAI.NumberTheory.DirichletL.Detector.DetectorInverseFields
Source SHA256: d7fae27ae3bfef14c06778fd5e83f528ea146a7b800c9f3cec5f668e474e8d43
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2689



namespace OAI

noncomputable section

open scoped Classical BigOperators Topology
namespace SevenEighths.ProbeDetectorInverseFields
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
local notation "O"=>HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

private lemma raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

theorem source_batch_inverse_fields {Δ:ℝ}{D:Parameters.HighData Δ}
    (S:SourceData D)(counts:CountParameters M H D.t):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
    1<Z ∧ ∀d:ℝ,(1/200:ℝ)≤d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=>D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤height →
    let F:=B.fiber bin label left right hne;
    (∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
          (C*(1+height)^J)*(Z^d)^(1+D.t)) := by
  obtain ⟨Jr,hr⟩ := ProbeDetectorInverseRawField.source_batch_inverse_raw
    M H hH S.S S.exclusions.prime D.t counts
  obtain ⟨Jm,hm⟩ := ProbeDetectorInverseMarkedField.source_batch_inverse_marked M H hH S
  refine ⟨Jr+Jm,?_⟩
  intro η
  obtain ⟨Cr,hCr,hr⟩ := hr η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  refine ⟨Cr+Cm,add_pos hCr hCm,?_⟩
  filter_upwards [hm] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
    bin label left right hne height hheight F
  have hU:0<Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  have hscale:1≤1+height := by linarith
  have hraw:Cr*(1+height)^Jr≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_right _ _)
    · positivity
    · positivity
  have hmarked:Cm*(1+height)^Jm≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_left _ _)
    · positivity
    · positivity
  constructor
  · intro n hn s hs t ht
    have hh:=hr hU B hdata bin label left right hne height hheight n hn s hs t ht
    exact ⟨raw_mono _ _ _ _ _ _ hraw hh.1,raw_mono _ _ _ _ _ _ hraw hh.2⟩
  · intro selected hselected hfirst hsecond n hn s hs t ht
    have hh:=hZ.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
      bin label left right hne height hheight selected hselected hfirst hsecond n hn s hs t ht
    exact hh.trans (mul_le_mul_of_nonneg_right hmarked (Real.rpow_nonneg hU.le _))

end SevenEighths.ProbeDetectorInverseFields

end

end OAI
end OAIOriginalModule2689

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorPlainSlotProfile
Source SHA256: 8dec7619e802c34454f7f0ffc14a94429712cbb0f15fb91baad2e6e0229f369d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2690





namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorPlainSlotProfile
open HeckeFamily HeckeInverseAmplification HeckeDyadic CenteredMomentDetectorDictionary
open CenteredMomentRetainedEnergy
local notation "O"=>HeckeFamily.O
variable {Δ:ℝ}{D:Parameters.HighData Δ}

lemma conjugate_source_support (F:ProbeFinalAssembly.SourceData D):
    Function.support (fun x=>conj (F.W x))⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  exact F.complex_support (by simpa using hx)

private lemma conjugate_source_smooth (F : ProbeFinalAssembly.SourceData D) :
    ContDiff ℝ ∞ (fun x => conj (F.W x)) := by
  exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)

def slotSchwartz (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):𝓢(ℝ,ℂ):=
  interpolatedProfile (fun x=>conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F)
    (1-ζ.re) (-ζ.im)

theorem slotSchwartz_apply (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ)(x:ℝ):
    slotSchwartz F ζ x=conj (F.W x*(x:ℂ)^(ζ-1)) := by
  rw [slotSchwartz,interpolatedProfile_apply]
  unfold twistProfile
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:0<x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) (F.complex_support hw).1
  rw [map_mul,conj_positive_cpow _ hx]
  congr 1
  congr 1
  apply Complex.ext <;> simp [HeckeDyadic.shift]

theorem slotSchwartz_support (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):
    Function.support (slotSchwartz F ζ:ℝ→ℂ)⊆Set.Icc (1:ℝ) 2 := by
  intro x hx
  apply F.complex_support
  intro hw
  exact hx (by rw [slotSchwartz_apply,hw,zero_mul,map_zero])

theorem slotSchwartz_smooth (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ):
    ContDiff ℝ ∞ (slotSchwartz F ζ:ℝ→ℂ):=(slotSchwartz F ζ).smooth ⊤

theorem slotSchwartz_norm (F:ProbeFinalAssembly.SourceData D)(ζ:ℂ)(hζ:ζ.re≤1)(x:ℝ):
    ‖slotSchwartz F ζ x‖≤1 := by
  rw [slotSchwartz_apply,RCLike.norm_conj]
  by_cases hw:F.W x=0
  · simp [hw]
  have hx:=F.complex_support hw
  have hxpos:0<x:=lt_of_lt_of_le (by norm_num : (0:ℝ)<1) hx.1
  have hW:‖F.W x‖≤1 := by
    rw [F.complex_eq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (F.bounded x).1]
    exact (F.bounded x).2
  rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hxpos]
  have hp:x^((ζ-1).re)≤1:=
    (Real.rpow_le_rpow_of_exponent_le hx.1 (by simp only [Complex.sub_re,Complex.one_re];linarith)).trans_eq
      (Real.rpow_zero _)
  simpa only [one_mul] using mul_le_mul hW hp (Real.rpow_nonneg hxpos.le _) zero_le_one

theorem physical_coefficient (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η F.W P ζ I=
      idealCoeff η.inverse I*slotSchwartz F ζ ((I.absNorm:ℝ)/P) := by
  rw [slotSchwartz_apply]
  rfl

theorem physical_coefficient_norm (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (P:ℝ)(ζ:ℂ)(hζ:ζ.re≤1)(I:Ideal O):
    ‖physicalSlotCoefficient η F.W P ζ I‖≤1 := by
  rw [physical_coefficient,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η.inverse I)).trans (slotSchwartz_norm F ζ hζ _)

theorem slotSchwartz_uniform (F:ProbeFinalAssembly.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀ζ:ℂ,ζ.re∈Set.Icc (0:ℝ) 1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F ζ)≤C*(1+‖ζ.im‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=interpolatedProfile_uniform (fun x=>conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F) S
  refine ⟨J,C,hC,?_⟩
  intro ζ hζ
  have hh:=hbound (1-ζ.re) ⟨by linarith [hζ.2],by linarith [hζ.1]⟩ (-ζ.im)
  simpa only [slotSchwartz,norm_neg] using hh

theorem slotSchwartz_height_uniform (F:ProbeFinalAssembly.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤height →
      (∀i,(ζ i).re=17/50) → (∀i,|(ζ i).im|≤height) → ∀i,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F (ζ i))≤C*(1+height)^J := by
  obtain ⟨J,C,hC,hbound⟩:=slotSchwartz_uniform F S
  refine ⟨J,C,hC,?_⟩
  intro ι ζ height hheight hreal him i
  refine (hbound (ζ i) (by rw [hreal i];norm_num)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith [him i]) J

theorem physical_positive_row {ι:Type*}[Fintype ι][DecidableEq ι]
    (F:ProbeFinalAssembly.SourceData D)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(S:ι→Finset (Ideal O))(P:ι→ℝ)(ζ:ι→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ S (fun i=>physicalSlotCoefficient η₀ F.W (P i) (ζ i)) P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S
        (fun i I=>idealCoeff η₀.inverse I*slotSchwartz F (ζ i) ((I.absNorm:ℝ)/P i)) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_coefficient F η₀ (P i) (ζ i) I

end SevenEighths.CenteredMomentDetectorPlainSlotProfile

end

end OAI
end OAIOriginalModule2690

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorPlainFiberSource
Source SHA256: 1cb0a9327547863fb153a83b806f8716c3a421dbbd009fad0f04eee32f0e5a80
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2691





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def plainProfile (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (j:ℕ)(σ t:ℝ):ℝ→ℂ:=
  twistProfile (orientedProfile F.reverse ((logProfile^[j]) positiveAnnular)) σ
    (orientedFrequency F.reverse t)

def slotWindow (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)(x:ℝ):ℂ:=
  conj (F.profile s x*(x:ℂ)^(F.external s-1))

def fiberPool (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot):
    Finset (CenteredMomentAddedZeroUniform.Tuple selected):=
  completePool (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val)))
    (9/4) (9/4) (U^F.m) (U^F.m)

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ):Ideal O→ℂ:=
  finiteColumnCoefficient (fiberPool F selected)
    (uncenteredProfileCoefficient 1 (fun _:selected=>idealCoeff η.inverse)
      (fun s:selected=>slotWindow F s.val) (fun s:selected=>U^(F.widths s.val))
      (plainProfile F j σ t) (plainProfile F k σ t) (U^F.m) (U^F.m) 1 1 1)

def fiberSourceEnergy (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy (fun _=>True) (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem detector_row_eq_source (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(u:FreeRow)(hU:0<U):
    detectorPositiveRow F η selected j k σ t u=
      (Real.sqrt ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):ℂ)⁻¹*
      ∑I∈finiteColumns (fiberPool F selected),fiberCoefficient F η selected j k σ t I*
        CenteredMomentHeckeExpansion.rowWeight η fixedBadMask 1 u.val 0 I:=by
  have he:=positiveSlotRow_eq_complete_source η fixedBadMask 1 u.val 0
    (dvd_mul_right _ _) (dvd_mul_left _ _)
    (fun s:selected=>primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _)
  rw [natural_unit_mask_positive (CenteredMomentNaturalRowSource.naturalRow η u.val u.property.1)] at he
  unfold detectorPositiveRow
  rw [rowMaskElement_eq_fixed]
  exact he

theorem detector_positive_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0<U):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  let Q:=finiteColumns (fiberPool F selected)
  let c:=fun I:supportedColumns Q=>fiberCoefficient F η selected j k σ t I*heightCoeff η 0 I
  let rows:Finset O:=F.rows.image Subtype.val
  have ht:0<(U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val):=
    mul_pos (mul_pos (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _))
      (Finset.prod_pos (fun _ _=>Real.rpow_pos_of_pos hU _))
  have he (u:FreeRow):
      ‖detectorPositiveRow F η selected j k σ t u‖^2=
      ‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
    rw [detector_row_eq_source F η selected j k σ t u hU,
      CenteredMomentDivisorRawEnergy.normalized_norm_sq _ ht]
    congr 1
    exact congrArg (fun w : ℂ=>‖w‖^2)
      (height_source_row η 0 Q (fiberCoefficient F η selected j k σ t) u.val).symm
  have hb:=finite_energy_le_restricted (fun _ : O=>True) Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
