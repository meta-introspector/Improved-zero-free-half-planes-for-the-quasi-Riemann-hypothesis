    (by simp) (fun z=>hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.val_injective hxy)]
    _≤_:=div_le_div_of_nonneg_right hb ht.le

theorem fiber_plain_energy_le_source
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t Φ:=by
  rw [fiber_plain_energy_eq F η hdata hMm hU selected j k σ t hη]
  exact detector_positive_energy_le_source Φ hΦ hone F η selected j k σ t hU

def radialMajorant : 𝓢(ℝ,ℂ):=
  Classical.choose DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant

lemma radialMajorant_compact : HasCompactSupport (radialMajorant:ℝ→ℂ):=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).1

lemma radialMajorant_nonneg (x:ℝ):0≤(radialMajorant x).re:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.1 x

lemma radialMajorant_one (x:ℝ)(hx:x∈Set.Icc (0:ℝ) 1):radialMajorant x=1:=
  (Classical.choose_spec DetectorDictionaryInverseRawRealRadial.exists_real_raw_radial_majorant).2.2.2 x hx

theorem actual_fiber_plain_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)
    (hη:∀s∈selected,∀J∈primePool M H (F.upper s) (U^(F.widths s)),
      F.profile s ((J.absNorm:ℝ)/(U^(F.widths s)))≠0→IsCoprime J η.modulus):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t*F.physicalProduct selected u‖^2)≤
      fiberSourceEnergy F η selected j k σ t radialMajorant:=
  fiber_plain_energy_le_source radialMajorant radialMajorant_nonneg radialMajorant_one
    F η hdata hMm hU selected j k σ t hη

theorem actual_fiber_unmarked_energy_le_source
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (hdata:F.rowData=momentData η)(hMm:M≤Ideal.span {rowMaskElement})(hU:0<U)
    (j k:ℕ)(σ t:ℝ):
    (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
      (U^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
      (U^F.m) σ t‖^2)≤fiberSourceEnergy F η ∅ j k σ t radialMajorant:=by
  simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one] using
    actual_fiber_plain_energy_le_source F η hdata hMm hU ∅ j k σ t (by simp)

end SevenEighths.CenteredMomentDetectorPlainFiberSource

end

end OAI
end OAIOriginalModule2691

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceBatch
Source SHA256: bcabe2864432eeaa7817d5a7481164b2ddb0e856c8b8cf0fde37c6c870b53783
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2692



namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open ProbeHighRowFamily HeckeDetectorDyadicProfiles CenteredMomentPrimeSlot HeckeDetectorRowwisePolynomial
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem eventually_source_batch_plain_sectors {N : ℕ}
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (hM : M=∏P∈S,P)
    (η : Character) (ell : Fin N→ℝ) (hell : ∀s,0<ell s)
    (W : Fin N→ℝ→ℂ) (hW : ∀s,Function.support (W s)⊆Set.Ici 1) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N) (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData M H hH S hS η→B.widths=(fun s=>ell s/d)→B.profile=W→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin N),∀j k : ℕ,∀σ t : ℝ,
      let F:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase M H hH S hS η label
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^F.m) σ t*
        polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^F.m) σ t*
          F.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters M H,‖averageWeight (ι:=selected) M H‖*
          ∑u∈F.rows,‖fiberSector hH F η₀ selected j k σ t θ u‖^2 := by
  have hMm : M≤Ideal.span {rowMaskElement} := by
    rw [hM]
    exact source_product_le_rowMask S hbad
  filter_upwards [eventually_source_slots_coprime M H hH S hS η ell hell 1 (by norm_num),
    eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro d hd a ε tstar T allowance i B hdata hwidth hprofile bin label J K hne selected j k σ t
  dsimp only
  convert fiber_plain_sector_energy hH (B.fiber bin label J K hne)
    (sourceMomentBase M H hH S hS η label) ?_ hMm (Real.rpow_pos_of_pos hZ _) selected j k σ t ?_ using 1
  · congr 2 ; apply Subsingleton.elim
  · change B.data label=momentData (sourceMomentBase M H hH S hS η label)
    rw [hdata,sourceMomentData_base]
  · intro s hs P hP hp
    change P∈primePool M H (B.upper s) ((Z^d)^(B.widths s)) at hP
    change B.profile s ((P.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hp
    rw [hwidth] at hP
    rw [hwidth,hprofile] at hp
    exact hz label s d hd (W s) (B.upper s) (hW s) P hP hp

theorem sourceData_batch_gate {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,d≠0→∀a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : Batch F.modulus ⊤ (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      B.data=sourceMomentData F.modulus ⊤ le_top F.S F.exclusions.prime η→
      B.widths=(fun s=>D.ell s/d)→B.profile=(fun _ y=>(F.w y:ℂ))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀selected : Finset (Fin D.N),∀j k : ℕ,∀σ t : ℝ,
      let Bf:=B.fiber bin label J K hne
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      (∑u∈Bf.rows,‖polynomial (Bf.family u Bf.label) false ((logProfile^[j]) positiveAnnular) ((Z^d)^Bf.m) σ t*
        polynomial (Bf.family u Bf.label) false ((logProfile^[k]) positiveAnnular) ((Z^d)^Bf.m) σ t*
          Bf.physicalProduct selected u‖^2)≤
        ∑θ : selected→RayQuotient.Characters F.modulus ⊤,‖averageWeight (ι:=selected) F.modulus ⊤‖*
          ∑u∈Bf.rows,‖fiberSector le_top Bf η₀ selected j k σ t θ u‖^2 := by
  apply eventually_source_batch_plain_sectors F.modulus ⊤ le_top F.S F.exclusions.prime
    F.exclusions.bad rfl η D.ell (fun s=>(D.slots_bounds s).1) (fun _ y=>(F.w y:ℂ))
  intro s y hy
  have hn : F.w y≠0 := by
    intro h
    apply hy
    simp only [h,Complex.ofReal_zero]
  exact (F.support hn).1.le

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2692

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceCapacity
Source SHA256: bf703b5908f202dcd9765215dfce6950c8e0be9907c1c31d078f434969a83894
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2693


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckePrimeScale HeckeInverseAmplification
open CenteredMomentNaturalRowSource CenteredMomentDetectorDictionary
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sectorConductorFactor (η₀ : Character) : ℕ :=
  η₀.modulus.absNorm*fixedConductorFactor*(M.absNorm*η₀.modulus.absNorm)

lemma initial_sector_modulus (η₀ : Character) (u : FreeRow) (θ : RayQuotient.Characters M H) :
    ((naturalRow η₀ u.val u.property.1).character.product (relativeCharacter M H hH η₀ θ)).modulus.absNorm≤
      sectorConductorFactor M η₀*(Ideal.span {u.val}).absNorm := by
  have hn:=(naturalRow η₀ u.val u.property.1).natural_modulus_bound
  have hs:=relativeCharacter_modulus M H hH η₀ θ
  apply (product_modulus_bound _ _).trans
  apply (Nat.mul_le_mul hn hs).trans_eq
  unfold sectorConductorFactor
  ring

theorem eventually_source_sector_capacity
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character)
    (margin : ℝ) (hmargin : 0<margin) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),∀d : ℝ,∀u : FreeRow,
      ((Ideal.span {u.val}).absNorm:ℝ)≤Z^(d-margin)→
      ∀θ : RayQuotient.Characters M H,
      (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
        (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters M H),
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)≤Z^margin := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (0:ℝ)] with Z hz hZ
  intro label d u hu θ
  have hb : (((naturalRow (sourceMomentBase M H hH S hS η label) u.val u.property.1).character.product
      (relativeCharacter M H hH (sourceMomentBase M H hH S hS η label) θ)).modulus.absNorm:ℝ)≤
      (sectorConductorFactor M (sourceMomentBase M H hH S hS η label):ℝ)*((Ideal.span {u.val}).absNorm:ℝ) := by
    exact_mod_cast initial_sector_modulus M H hH (sourceMomentBase M H hH S hS η label) u θ
  apply hb.trans
  calc
    _≤Z^margin*Z^(d-margin) := mul_le_mul (hz label) hu (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

theorem sourceData_fiber_sector_capacity {Δ : ℝ} {D : Parameters.HighData Δ}
    (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀d a ε tstar T allowance : ℝ,∀i : ℕ,
      ∀B : HeckeDetectorBatch.Batch F.modulus ⊤
        (Sum Bool (RayQuotient.Characters F.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i,
      (∀u∈B.rows,ProbeHighRowFamily.rowNorm u≤Z^(d-D.t))→
      ∀bin label J K,∀hne : (B.fiberRows bin label J K).Nonempty,
      ∀u∈(B.fiber bin label J K hne).rows,∀θ : RayQuotient.Characters F.modulus ⊤,
      (((naturalRow (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
        u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top
          (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) θ)).modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_sector_capacity F.modulus ⊤ le_top
    F.S F.exclusions.prime η D.t D.t_pos] with Z hz
  intro d a ε tstar T allowance i B hcap bin label J K hne u hu θ
  apply hz label d u ?_ θ
  simp only [HeckeDetectorBatch.Batch.fiber, HeckeDetectorFiberPartition.toFiber,
    HeckeDetectorFiberPartition.fiber, Finset.mem_filter] at hu
  have hmem : u∈B.rows := hu.1
  exact hcap u hmem

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2693

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceSupport
Source SHA256: 72ae3a2f82c6ac5072e7e0529c3160df42f10f213ffbed66668abf7589214806
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2694



namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary HeckeDetectorRawFiber ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma oriented_moment_nonzero_base (η χ : Character) (u : FreeRow) (reverse : Bool)
    (hc : ∀I : Ideal O, idealCoeff χ I=if reverse then
      conj (idealCoeff ((momentData η).character (momentElement u)) I)
      else idealCoeff ((momentData η).character (momentElement u)) I)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff η I≠0 := by
  intro he
  have hh:=hc I
  rw [momentData_product_raw,idealCoeff_product,he,zero_mul] at hh
  cases reverse <;> simp only [Bool.false_eq_true,ite_false,ite_true,map_zero] at hh
  · exact hI hh
  · exact hI hh

lemma fiber_nonzero_initial {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0) : idealCoeff η I≠0 := by
  apply oriented_moment_nonzero_base η (F.family u F.label) u F.reverse ?_ I hI
  simpa only [hdata,momentElement] using F.row_coeff u hu

lemma ideal_nonzero_forcing_coprime (η : Character) (I P : Ideal O)
    (hI : idealCoeff η I≠0) (hP : P∣I) : IsCoprime η.modulus P := by
  have hI0 : I≠0 := by intro h; apply hI; rw [h,map_zero]
  have he : elementCoeff η (idealGenerator I)≠0 := by
    rw [←idealCoeff_span η (idealGenerator_ne_zero I hI0),span_idealGenerator]
    exact hI
  exact CenteredMomentChildRows.old_coefficient_prime_coprime η (idealGenerator I) he P
    (by rwa [span_idealGenerator])

theorem fiber_internal_forcing {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (I Q P : Ideal O) (hI : idealCoeff (F.family u F.label) I≠0)
    (hP : P∣I) (hQP : IsCoprime Q P) : IsCoprime (internalQ Q η) P :=
  internalQ_coprime Q P η hQP
    (ideal_nonzero_forcing_coprime η I P (fiber_nonzero_initial F η hdata u hu I hI) hP)

theorem fiber_initial_support_filter {M : Ideal O} {H : Subgroup (O⧸M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    (F : Fiber M H Label Slot U a ε tstar T allowance i)
    (η : Character) (hdata : F.rowData=momentData η) (u : FreeRow) (hu : u∈F.rows)
    (s : Finset (Ideal O)) (weight : Ideal O→ℂ) :
    (∑I∈s,idealCoeff (F.family u F.label) I*weight I)=
      ∑I∈s.filter (fun I=>idealCoeff η I≠0),idealCoeff (F.family u F.label) I*weight I := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro I hIs hnot
  have hzero : idealCoeff (F.family u F.label) I=0 := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨hIs,fiber_nonzero_initial F η hdata u hu I hn⟩)
  rw [hzero,zero_mul]

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2694

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFixedIdeal
Source SHA256: 7814f20f7dae39272b939a7ea392bc6022abcc0757582560c77571a40c21ad22
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2695


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceFixedIdeal (F : ProbeFinalAssembly.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma sourceFixedIdeal_ne_zero (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=>P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤Ideal.span {goodLambda})))

lemma sourceFixedIdeal_le_modulus (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤F.modulus := inf_le_left
lemma sourceFixedIdeal_le_72 (F : ProbeFinalAssembly.SourceData D) : sourceFixedIdeal F≤Ideal.span {(72:O)} := inf_le_right

def sourceExceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) (u : FreeRow) : Prop :=
  FixedInducingRow η (internalQ (sourceFixedIdeal F) η)
    (fixedBadMask*idealGenerator 1) 1 u.val

theorem source_retained_sector_nonprincipal (F : ProbeFinalAssembly.SourceData D)
    (η : Character) (u : FreeRow) (hu : ¬sourceExceptional F η u)
    (θ : RayQuotient.Characters F.modulus ⊤) :
    ((naturalRow η u.val u.property.1).character.product
      (relativeCharacter F.modulus ⊤ le_top η θ)).residue≠1 :=
  internal_sector_nonprincipal F.modulus ⊤ le_top (naturalRow η u.val u.property.1)
    η θ (sourceFixedIdeal F) 1 (sourceFixedIdeal_le_modulus F) one_ne_zero u.property.1 hu

theorem source_energy_split (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (rows : Finset FreeRow) (f : FreeRow→ℂ) :
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>¬sourceExceptional F η u),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2 := by
  simpa only [not_not] using
    (Finset.sum_filter_add_sum_filter_not rows (fun u=>¬sourceExceptional F η u)
      (fun u=>‖f u‖^2)).symm

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2695

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorEnergyInitialState
Source SHA256: 26bd054133aae433f3bf5bce5a3348b610017ebebb5e970a48eefc476931f8ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2696





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorEnergyInitialState
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentEnergyState CenteredMomentRadialEligibleEnergy
open CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentNaturalFixedRaySource ConcretePrimeRowBridge
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def initialKeep (η:Character)(Q:Ideal O)(z:O):Prop:=
  z≠0 ∧ ¬FixedInducingRow η Q (fixedBadMask*idealGenerator 1) 1 z

def initialState (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):NaturalState U 0 bΦ where
  character:=η
  fixedModulus:=Q
  puncture:=1
  radial := {
    keep := initialKeep η Q
    profile := Φ
    scale := U
    scale_pos := zero_lt_one.trans_le hU
    nonneg := fun z => hp _ }
  rowWidth:=1
  characterWidth:=δ
  base_ge_one:=hU
  row_nonneg:=by norm_num
  character_nonneg:=hδ
  scale_eq:=by simp
  modulus_bound:=hη
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=hs
  row_ne_zero:=fun _ h=>h.1
  nonexceptional:=fun _ h=>h.2

lemma initialState_width (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ U δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ):
    (initialState η Q Φ bΦ U δ hU hδ hs hp hη).width=1+δ:=rfl

def detectorProfiles (reverse:Bool)(j k:ℕ)(σ t:ℝ):Profiles (1/4) (9/4) where
  profile:=fun n=>detectorSchwartz reverse (if n=0 then j else k) σ t
  support:=by
    intro n x hx
    have he:(detectorSchwartz reverse (if n=0 then j else k) σ t:ℝ→ℂ)=
      HeckeInverseAmplification.twistProfile
        (HeckeDetectorCoefficientTransfer.orientedProfile reverse
          ((HeckeDetectorRowwisePolynomial.logProfile^[if n=0 then j else k])
            HeckeDetectorDyadicProfiles.positiveAnnular)) σ
          (HeckeDetectorCoefficientTransfer.orientedFrequency reverse t):=by
      funext y;exact detectorSchwartz_apply _ _ _ _ _
    rw [he] at hx
    exact detector_profile_support _ _ _ _ hx

theorem radialMajorant_support_bound:
    ∃bΦ:ℝ,0<bΦ ∧ Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic bΦ:=by
  obtain ⟨b,hb⟩:=radialMajorant_compact.isCompact.bddAbove
  refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left _ _),?_⟩
  intro x hx
  exact (hb (subset_tsupport _ hx)).trans (le_max_right _ _)

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_label_modulus_eventually (F:ProbeFinalAssembly.SourceData D)
    (η:Character)(δ:ℝ)(hδ:0<δ):
    ∀ᶠZ:ℝ in atTop,1<Z ∧
      ∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤d→
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^δ:=by
  have hc:∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ((sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤Z^((1/200)*δ):=by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (mul_pos (by norm_num) hδ)).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  intro label d hd
  apply (hz label).trans
  rw [←Real.rpow_mul (zero_lt_one.trans hZ).le]
  exact Real.rpow_le_rpow_of_exponent_le hZ.le (mul_le_mul_of_nonneg_right hd hδ.le)

lemma source_keep_iff (F:ProbeFinalAssembly.SourceData D)(η:Character)(u:FreeRow):
    initialKeep η (internalQ (sourceFixedIdeal F) η) u.val↔¬sourceExceptional F η u:=by
  exact and_iff_right u.property.1

lemma source_fixed_gates (F:ProbeFinalAssembly.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal F) η≠0 ∧
    internalQ (sourceFixedIdeal F) η≤F.modulus ∧
    internalQ (sourceFixedIdeal F) η≤η.modulus ∧
    internalQ (sourceFixedIdeal F) η≤Ideal.span {(72:O)}:=
  ⟨internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η,
    inf_le_left.trans (sourceFixedIdeal_le_modulus F),inf_le_right,
    inf_le_left.trans (sourceFixedIdeal_le_72 F)⟩

theorem source_energy_split_state (F:ProbeFinalAssembly.SourceData D)(η:Character)
    (rows:Finset FreeRow)(f:FreeRow→ℂ):
    (∑u∈rows,‖f u‖^2)=
      (∑u∈rows.filter (fun u=>initialKeep η (internalQ (sourceFixedIdeal F) η) u.val),‖f u‖^2)+
      ∑u∈rows.filter (sourceExceptional F η),‖f u‖^2:=by
  simpa only [source_keep_iff] using source_energy_split F η rows f

theorem source_initial_states (F:ProbeFinalAssembly.SourceData D):
    ∃bΦ:ℝ,0<bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,∀label:Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d:ℝ,(1/200:ℝ)≤d→
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label;
      ∃s:NaturalState (Z^d) 0 bΦ,
        s.character=η₀ ∧ s.fixedModulus=internalQ (sourceFixedIdeal F) η₀ ∧
        s.puncture=1 ∧ s.radial.profile=radialMajorant ∧ s.radial.scale=Z^d ∧
        s.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal F) η₀) ∧
        s.rowWidth=1 ∧ s.characterWidth=δ ∧ s.width=1+δ:=by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually F η δ hδ] with Z hz
  intro label d hd
  have hd0:0<d:=by linarith
  have hU:1≤Z^d:=(Real.one_lt_rpow hz.1 hd0).le
  dsimp only
  refine ⟨initialState (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label)
    (internalQ (sourceFixedIdeal F) (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label))
    radialMajorant bΦ (Z^d) δ hU hδ.le hs
    radialMajorant_nonneg (hz.2 label d hd),?_⟩
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end SevenEighths.CenteredMomentDetectorEnergyInitialState

end

end OAI
end OAIOriginalModule2696

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorPlainProfileControl
Source SHA256: 1923a4772b9923c847fb50da048a200f85f67c3984cd580da9c4038e33b840ab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2697


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainProfileControl
open CenteredMomentDetectorEnergyInitialState CenteredMomentDetectorDictionary
open CenteredMomentFiniteProfileExceptional

theorem paired_control (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀t:ℝ,
      (detectorProfiles reverse j k σ t).control S ^2≤C*(1+‖t‖)^J:=by
  obtain ⟨J,C,hC,h⟩:=detectorSchwartz_uniform S
  refine ⟨4*J,C^4,by positivity,?_⟩
  intro reverse j k hjk σ hσ t
  have hj:=h reverse j (by omega) σ hσ t
  have hk:=h reverse k (by omega) σ hσ t
  have hp:(detectorProfiles reverse j k σ t).control S≤(C*(1+‖t‖)^J)^2:=by
    simpa only [detectorProfiles,Profiles.control,sourceControl,Fin.zero_eta,ite_true,
      show ¬((1:Fin 2)=0) by decide,ite_false,pow_two] using
      mul_le_mul hj hk (sourceControl_nonneg S (detectorSchwartz reverse k σ t)) (by positivity)
  have hs:=pow_le_pow_left₀ (Profiles.control_nonneg _ _) hp 2
  calc
    _≤((C*(1+‖t‖)^J)^2)^2:=hs
    _=C^4*(1+‖t‖)^(4*J):=by
      rw [←pow_mul,mul_pow,←pow_mul]
      congr 2 ; omega

theorem source_height_factor (S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0<C ∧ ∀degree:ℕ,∀reverse:Bool,∀j k:ℕ,j+k≤2 →
      ∀σ∈Set.Icc (0:ℝ) 1,∀height t:ℝ,0≤height → |t|≤height →
      (detectorProfiles reverse j k σ t).control S ^2*(1+|(0:ℝ)|+height)^degree
        ≤C*(1+height)^(J+degree):=by
  obtain ⟨J,C,hC,h⟩:=paired_control S
  refine ⟨J,C,hC,?_⟩
  intro degree reverse j k hjk σ hσ height t hh ht
  have hb:(detectorProfiles reverse j k σ t).control S ^2≤C*(1+height)^J:=by
    apply (h reverse j k hjk σ hσ t).trans
    apply mul_le_mul_of_nonneg_left _ hC.le
    apply pow_le_pow_left₀ (by positivity)
    simpa only [Real.norm_eq_abs] using add_le_add le_rfl ht
  simpa only [abs_zero,add_zero,pow_add,mul_assoc] using
    mul_le_mul_of_nonneg_right hb (pow_nonneg (by linarith:0≤1+height) degree)

end SevenEighths.CenteredMomentDetectorPlainProfileControl

end

end OAI
end OAIOriginalModule2697

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceFreeExceptional
Source SHA256: 4dbb1822fa52e5743cd4a43d77baa773d9c299e554d13496f5a1c9d6d4318b35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2698



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily UniqueFactorizationMonoid
open CenteredMomentDetectorDictionary CenteredExceptionalProfile CenteredExceptionalCount
open ConcretePrimeRowBridge CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

theorem fixed_inducing_free_support (η : Character) (Q : Ideal O)
    (hQ0 : Q≠0) (hQ : Q≠⊤) (hQ72 : Q≤Ideal.span {(72:O)}) (hQη : Q≤η.modulus)
    (m : O) (hm : m≠0) (hml : goodLambda∣m) (hm2 : (2:O)∣m)
    (u : FreeRow) (hu : FixedInducingRow η Q m 1 u.val) :
    u.val∈HeckeExceptionalRows.rows (normalizedFactors Q).toFinset := by
  obtain ⟨χ,ψ,hprim,hind,hψ,hχ⟩:=hu
  refine ⟨u.property.1,?_⟩
  intro P hP
  refine ⟨?_,u.property.2 P⟩
  by_contra hout
  have hp : Prime P:=prime_of_normalized_factor P hP
  let : P.IsMaximal:=(Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  obtain ⟨hl,h2,hQP⟩:=outside_fixed_support Q hQ0 hQ72 P hp hout
  have hηP : IsCoprime η.modulus P:=hQP.of_isCoprime_of_dvd_left (Ideal.dvd_iff_le.mpr hQη)
  have hz:=actual_row_numerator_valuation_zero η χ ψ hind Q hQ hQ72 hψ
    m 1 u.val hm one_ne_zero u.property.1 hml hm2
    (by simpa only [one_mul] using hχ) P hl h2 hQP hηP
  simp only [one_pow,one_mul,valuation] at hz
  have hpos:=Multiset.count_pos.mpr hP
  have hlt:=u.property.2 P
  omega

variable {Δ : ℝ} {D : Parameters.HighData Δ}

def sourceExceptionalBound (F : ProbeFinalAssembly.SourceData D) (η : Character) : ℕ :=
  HeckeExceptionalRows.bound (normalizedFactors (internalQ (sourceFixedIdeal F) η)).toFinset

lemma source_exceptional_norm (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : sourceExceptional F η u) :
    (Ideal.span {u.val}).absNorm≤sourceExceptionalBound F η := by
  apply HeckeExceptionalRows.row_norm_bound _
    (fun P hP=>prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP))
  apply fixed_inducing_free_support η (internalQ (sourceFixedIdeal F) η)
    (internalQ_ne_zero _ (sourceFixedIdeal_ne_zero F) η)
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η)
    (inf_le_left.trans (sourceFixedIdeal_le_72 F)) inf_le_right
    (fixedBadMask*idealGenerator 1)
    (mul_ne_zero fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero))
    ((dvd_mul_right _ _).trans (dvd_mul_right _ _))
    ((dvd_mul_left _ _).trans (dvd_mul_right _ _)) u hu

theorem eventually_source_no_exceptional (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀u : FreeRow,
      Z^(1/100:ℝ)≤rowNorm u →
      ¬sourceExceptional F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u := by
  have hh : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sourceExceptionalBound F (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)<Z^(1/100:ℝ) := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/100)).eventually (eventually_gt_atTop _)
  filter_upwards [hh] with Z hz
  intro label u hu hex
  have hb : rowNorm u≤(sourceExceptionalBound F
      (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ) := by
    change ((Ideal.span {u.val}).absNorm:ℝ)≤_
    exact_mod_cast source_exceptional_norm F _ u hex
  exact (not_lt_of_ge (hu.trans hb)) (hz label)

theorem eventually_source_sector_gate (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u→ rowNorm u≤Z^(d-D.t) →
      ∀θ : RayQuotient.Characters F.modulus ⊤,
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      let χ:=(CenteredMomentNaturalRowSource.naturalRow η₀ u.val u.property.1).character.product
        (relativeCharacter F.modulus ⊤ le_top η₀ θ)
      χ.residue≠1 ∧ (χ.modulus.absNorm:ℝ)≤Z^d := by
  filter_upwards [eventually_source_no_exceptional F η,
    eventually_source_sector_capacity F.modulus ⊤ le_top F.S F.exclusions.prime η D.t D.t_pos]
    with Z hn hc
  intro label d u hlo hhi θ
  exact ⟨source_retained_sector_nonprincipal F _ u (hn label u hlo) θ,hc label d u hhi θ⟩

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2698

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorPlainExceptional
Source SHA256: 25bada8e125a2286b8c73b49a8c278bb79c6318a120e62ab8137b64199fd8b19
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2699




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap Topology
open Filter

namespace SevenEighths.CenteredMomentDetectorPlainExceptional
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeRowClosure
open CenteredMomentDetectorDictionary CenteredMomentDetectorPlainSource
open CenteredMomentDetectorPlainFiberSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentRetainedEnergy CenteredMomentSourceRow CenteredMomentSourceMass
open CenteredMomentUncenteredTerminal CenteredMomentHeckeColumnWindow
open CenteredMomentSourceRectangleEnergy CenteredMomentRestrictedSource CenteredMomentRestrictedEnergy
open CenteredMomentNaturalFixedRaySource ProbeHighRowFamily HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentPrimeSlot CanonicalQuadraticSieve CenteredMomentRowNorm
open CenteredMomentSecondHeightFamily ConcreteTraceCRT ActualEisensteinCubic
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

def retainedSourceEnergy (keep:O→Prop)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ)):ℝ:=
  sourceRestrictedEnergy keep (finiteColumns (fiberPool F selected))
    (fiberCoefficient F η selected j k σ t) (heightCoeff η 0) Φ U /
    ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val))

theorem retained_positive_energy_le_source
    (keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(η:Character)
    (selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(hU:0<U)
    (hkeep:∀u∈F.rows,keep u.val):
    (∑u∈F.rows,‖detectorPositiveRow F η selected j k σ t u‖^2)≤
      retainedSourceEnergy keep F η selected j k σ t Φ:=by
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
  have hb:=finite_energy_le_restricted keep Finset.univ
    (sourceGenerator Q) (sourceGenerator_supported Q) c Φ U hU rows
    (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      exact hkeep u hu) (fun z=>hΦ _) (by
      intro z hz
      obtain ⟨u,hu,rfl⟩:=Finset.mem_image.mp hz
      have hn:‖eisEmbedding u.val‖^2/U∈Set.Icc (0:ℝ) 1:=by
        refine ⟨div_nonneg (sq_nonneg _) hU.le,(div_le_one hU).mpr ?_⟩
        rw [eisEmbedding_norm_sq_eq_absNorm_span]
        exact F.row_norm u hu
      rw [hone _ hn,Complex.one_re])
  calc
    _=(∑u∈F.rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c u.val‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      simp_rw [he]
      rw [Finset.sum_div]
    _=(∑z∈rows,‖rowPolynomial Finset.univ (sourceGenerator Q) c z‖^2)/
        ((U^F.m)*(U^F.m)*∏s:selected,U^(F.widths s.val)):=by
      rw [Finset.sum_image (fun x _ y _ hxy=>Subtype.val_injective hxy)]
    _≤_:=div_le_div_of_nonneg_right hb ht.le

variable {Δ:ℝ}{D:Parameters.HighData Δ}

theorem source_fibers_eventually_retained (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀(d a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∀u∈(B.fiber bin label J K hne).rows,
        initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val) ∧
      ((B.fiber bin label J K hne).rows.filter (sourceExceptional S η₀))=∅:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows d a ε tstar T allowance i B hB bin label J K hne η₀
  have hk:∀u∈(B.fiber bin label J K hne).rows,
      initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) u.val:=by
    intro u hu
    apply (source_keep_iff S η₀ u).mpr
    apply hz label u
    apply hrows u
    apply hB
    simp only [Batch.fiber,HeckeDetectorFiberPartition.toFiber,
      HeckeDetectorFiberPartition.fiber,Finset.mem_filter] at hu
    exact hu.1
  refine ⟨hk,?_⟩
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact ((source_keep_iff S η₀ u).mp (hk u hu)) hex

theorem source_exceptional_energy_eventually_zero (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀f:FreeRow→ℂ,
      (∑u∈rows.filter (sourceExceptional S
        (sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label)),‖f u‖^2)=0:=by
  filter_upwards [eventually_source_no_exceptional S η] with Z hz
  intro rows hrows label f
  apply Finset.sum_eq_zero
  intro u hu
  obtain ⟨hu,hex⟩:=Finset.mem_filter.mp hu
  exact False.elim ((hz label u (hrows u hu)) hex)

theorem source_batch_plain_retained (S:ProbeFinalAssembly.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤rowNorm u)→
      ∀d:ℝ,d≠0→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=>D.ell s/d)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),∀j k:ℕ,∀σ t:ℝ,
      let F:=B.fiber bin label J K hne;
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        retainedSourceEnergy (initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀))
          F η₀ selected j k σ t radialMajorant:=by
  filter_upwards [source_fibers_eventually_retained S η,
    eventually_source_slots_coprime S.modulus ⊤ le_top S.S S.exclusions.prime η
      D.ell (fun s=>(D.slots_bounds s).1) 1 (by norm_num),eventually_gt_atTop (1:ℝ)] with Z hret hcop hZ
  refine ⟨hZ,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth
    bin label J K hne selected j k σ t F η₀
  have hU:0<Z^d:=Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have hdataF:F.rowData=momentData η₀:=by
    change B.data label=momentData η₀
    rw [hdata,sourceMomentData_base]
  have hMm:S.modulus≤Ideal.span {rowMaskElement}:=source_product_le_rowMask S.S S.exclusions.bad
  have hη:∀s∈selected,∀I∈primePool S.modulus ⊤ (F.upper s) ((Z^d)^(F.widths s)),
      F.profile s ((I.absNorm:ℝ)/((Z^d)^(F.widths s)))≠0→IsCoprime I η₀.modulus:=by
    intro s hs I hI hn
    change I∈primePool S.modulus ⊤ (B.upper s) ((Z^d)^(B.widths s)) at hI
    change B.profile s ((I.absNorm:ℝ)/((Z^d)^(B.widths s)))≠0 at hn
    rw [hwidth] at hI
    rw [hwidth,hprofile] at hn
    exact hcop label s d hd (fun x=>(S.w x:ℂ)) (B.upper s)
      (by
        intro x hx
        have hn:S.w x≠0:=by simpa using hx
        exact (S.support hn).1.le) I hI hn
  rw [fiber_plain_energy_eq F η₀ hdataF hMm hU selected j k σ t hη]
  exact retained_positive_energy_le_source _ radialMajorant radialMajorant_nonneg radialMajorant_one
    F η₀ selected j k σ t hU (hret rows hrows d a ε tstar T allowance i B hB bin label J K hne).1

end SevenEighths.CenteredMomentDetectorPlainExceptional

end

end OAI
end OAIOriginalModule2699

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorPlainStateDictionary
Source SHA256: 04ab65cb07f92260b30b84f48cf168fc8ac8b458f562cfd752ea62a0e424c9aa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2700


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentDetectorPlainStateDictionary
open HeckeFamily HeckeDetectorRawFiber HeckePrimeAnnular
open CenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainFiberSource
open CenteredMomentDetectorPlainSource CenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}

lemma plainProfile_eq_detectorSchwartz
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(j:ℕ)(σ t:ℝ):
    plainProfile F j σ t=(detectorSchwartz F.reverse j σ t:ℝ→ℂ):=by
  funext x
  exact (detectorSchwartz_apply F.reverse j σ t x).symm

theorem retainedSourceEnergy_eq_energy
    (keep:O→Prop)(F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(selected:Finset Slot)(j k:ℕ)(σ t:ℝ)(Φ:𝓢(ℝ,ℂ))(hU:0<U):
    retainedSourceEnergy keep F η selected j k σ t Φ=
      energy η (fixedBadMask*idealGenerator 1) 1 0
        (plainProfile F j σ t) (plainProfile F k σ t)
        (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val)))
        (fun (s:selected) I=>idealCoeff η.inverse I*slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))
        (fun s:selected=>U^(F.widths s.val)) (U^F.m) (U^F.m) keep Φ U:=by
  exact (positive_energy_eq_complete_source η 0 keep
    (fun s:selected=>CenteredMomentPrimeSlot.primePool M H (F.upper s.val) (U^(F.widths s.val))) 1
    (fun _:selected=>idealCoeff η.inverse) (fun s:selected=>slotWindow F s.val)
    (fun s:selected=>U^(F.widths s.val)) (fun _=>Real.rpow_pos_of_pos hU _)
    (plainProfile F j σ t) (plainProfile F k σ t)
    (1/4) (9/4) (1/4) (9/4) (U^F.m) (U^F.m) (by norm_num) (by norm_num)
    (detector_profile_support F.reverse j σ _) (detector_profile_support F.reverse k σ _)
    (Real.rpow_pos_of_pos hU _) (Real.rpow_pos_of_pos hU _) Φ U).symm

theorem retainedSourceEnergy_empty_eq_plainEnergy
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)
    (hU:1≤U)(hδ:0≤δ)(hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)
    (hp:∀x,0≤(Φ x).re)(hη:(η.modulus.absNorm:ℝ)≤U^δ)
    (j k:ℕ)(σ t:ℝ):
    retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t Φ=
      (initialState η Q Φ bΦ U δ hU hδ hs hp hη).plainEnergy
        (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m):=by
  rw [retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  simp only [plainProfile_eq_detectorSchwartz]
  unfold NaturalState.plainEnergy energy
  apply tsum_congr
  intro z
  simp [initialState,NaturalState.mask,detectorProfiles,positiveSlotRow]

end SevenEighths.CenteredMomentDetectorPlainStateDictionary

end

end OAI
end OAIOriginalModule2700

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeGate
Source SHA256: 0daa7ed2ef4a8cf0f87966eebbe5c99cf6cdbe6e61948735110c75877515f836
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2701



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRowMask CenteredMomentFixedRayInducingTransport
local notation "O" => HeckeFamily.O

def relativeBase (η : Character) (u : FreeRow) : Character :=
  (naturalRow η u.val u.property.1).character.product η.inverse

variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem source_relativeBase_twists (F : ProbeFinalAssembly.SourceData D) (η : Character)
    (u : FreeRow) (hu : ¬sourceExceptional F η u) :
    ∀θ : RayQuotient.Characters F.modulus ⊤,
      (twistedFamily F.modulus ⊤ le_top (relativeBase η u) θ).residue≠1 := by
  have hn : ¬FixedInducingRow η (internalQ (sourceFixedIdeal F) η) fixedBadMask 1 u.val := by
    intro h
    apply hu
    exact (fixedInducingRow_mul_mask_iff η _ fixedBadMask (idealGenerator 1) 1 u.val
      fixedBadMask_ne_zero (idealGenerator_ne_zero _ one_ne_zero) one_ne_zero u.property.1
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr h
  have hn' : ¬FixedInducingRow (η.product η.inverse) (internalQ (sourceFixedIdeal F) η)
      fixedBadMask 1 u.val :=
    (not_fixedInducingRow_product_iff η η.inverse _ fixedBadMask 1 u.val inf_le_right
      fixedBadMask_ne_zero one_ne_zero u.property.1 (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hn
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal F.modulus ⊤ le_top
    (η.product η.inverse) (relativeBase η u) (internalQ (sourceFixedIdeal F) η)
    fixedBadMask 1 u.val ?_ (inf_le_left.trans (sourceFixedIdeal_le_modulus F)) hn'
  exact product_row_presentation η (naturalRow η u.val u.property.1).character η.inverse
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η u.val u.property.1).element)

lemma relativeBase_modulus (M : Ideal O) [NeZero M] (η : Character) (u : FreeRow) :
    (relativeBase η u).modulus.absNorm≤sectorConductorFactor M η*(Ideal.span {u.val}).absNorm := by
  have hb:=(HeckePrimeScale.product_modulus_bound (naturalRow η u.val u.property.1).character η.inverse).trans
    (Nat.mul_le_mul_right η.modulus.absNorm (naturalRow η u.val u.property.1).natural_modulus_bound)
  have hM : 1≤M.absNorm := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (NeZero.ne M))
  have hm : η.modulus.absNorm≤M.absNorm*η.modulus.absNorm := by nlinarith
  change (relativeBase η u).modulus.absNorm≤_
  apply hb.trans
  unfold sectorConductorFactor
  calc
    _=(η.modulus.absNorm*fixedConductorFactor*η.modulus.absNorm)*(Ideal.span {u.val}).absNorm := by ring
    _≤_ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hm)

theorem eventually_source_relativeBase_gate (F : ProbeFinalAssembly.SourceData D) (η : Character) :
    ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      ∀d : ℝ,∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u → rowNorm u≤Z^(d-D.t) →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ((relativeBase η₀ u).modulus.absNorm:ℝ)≤Z^d ∧
        ∀θ : RayQuotient.Characters F.modulus ⊤,
          (twistedFamily F.modulus ⊤ le_top (relativeBase η₀ u) θ).residue≠1 := by
  have hc : ∀ᶠZ : ℝ in atTop,∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)≤Z^D.t := by
    apply Filter.eventually_all.mpr
    intro label
    exact (tendsto_rpow_atTop D.t_pos).eventually (eventually_ge_atTop _)
  filter_upwards [hc,eventually_source_no_exceptional F η,eventually_gt_atTop (0:ℝ)] with Z hc hn hZ
  intro label d u hlo hhi
  refine ⟨?_,source_relativeBase_twists F _ u (hn label u hlo)⟩
  have hb : ((relativeBase (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label) u).modulus.absNorm:ℝ)≤
      (sectorConductorFactor F.modulus (sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label):ℝ)*rowNorm u := by
    change _≤_*((Ideal.span {u.val}).absNorm:ℝ)
    exact_mod_cast relativeBase_modulus F.modulus _ u
  apply hb.trans
  calc
    _≤Z^D.t*Z^(d-D.t) := mul_le_mul (hc label) hhi (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
    _=Z^d := by rw [←Real.rpow_add hZ]; congr 1; ring

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2701

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourcePrimeBound
Source SHA256: e78551a3707b9a0570397c4c6d4d9338a990d57aaaac539eca4ef46ebece70fd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2702


namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily HeckePrimeRay
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredMomentSecondHeightFamily ConcretePrimeRowBridge CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot HeckeZeroSupremum
local notation "O" => HeckeFamily.O
variable {Δ : ℝ} {D : Parameters.HighData Δ}

theorem source_physical_slot_bound (F : ProbeFinalAssembly.SourceData D)
    (loss lo hi κ : ℝ) (hloss : 0<loss) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀label : Sum Bool (RayQuotient.Characters F.modulus ⊤),∀d : ℝ,d≤1 →
      ∀u : FreeRow,Z^(1/100:ℝ)≤rowNorm u → rowNorm u≤Z^(d-D.t) →
      ∀P t : ℝ,1≤P → P≤Z → ∀z : ℂ,lo≤1-z.re → 1-z.re≤hi →
      let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
      ‖normalizedSlot η₀ fixedBadMask 1 u.val (primePool F.modulus ⊤ 2 P)
        (physicalSlotCoefficient η₀ F.W P z) t P‖^2≤
        C*(1+|t|+|z.im|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    F.modulus ⊤ le_top F.W 1 2 (by norm_num) F.complex_support (F.W.smooth ⊤)
    1 1 loss lo hi κ (by norm_num) (by norm_num) hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η
  filter_upwards [eventually_source_relativeBase_gate F η,eventually_ge_atTop Z₀,
    eventually_ge_atTop (1:ℝ)] with Z hgate hZ0 hZ
  intro label d hd u hlo hhi P t hP hPZ z hzlo hzhi
  let η₀:=sourceMomentBase F.modulus ⊤ le_top F.S F.exclusions.prime η label
  obtain ⟨hc,hn⟩:=hgate label d u hlo hhi
  have hc' : ((relativeBase η₀ u).modulus.absNorm:ℝ)≤Z^(1:ℝ) :=
    hc.trans (Real.rpow_le_rpow_of_exponent_le hZ hd)
  have hb:=hbound Z P hZ0 hP (by simpa only [Real.rpow_one] using hPZ)
    (relativeBase η₀ u) hc' hn (1-z.re) (t-z.im) hzlo hzhi
  have hconj : (fun y=>conj (F.W y))=(F.W:ℝ→ℂ) := by
    funext y
    rw [F.complex_eq]
    simp
  dsimp only
  rw [physicalSlot_eq_relativeRay F.modulus ⊤ η₀ (naturalRow η₀ u.val u.property.1).character
    fixedBadMask 1 u.val (by simpa only [one_mul] using (naturalRow η₀ u.val u.property.1).element)
    F.W 2 P t z (zero_lt_one.trans_le hP),hconj,norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  have habs : |t-z.im|≤|t|+|z.im| := by simpa using (abs_sub_le t 0 z.im)
  exact pow_le_pow_left₀ (by positivity) (by linarith) degree

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2702

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceNaturalPrime
Source SHA256: 042bee61a3aefbb0c7931dc36d11e692bec7a738df7e8d5e18b29c04831ffd3c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2703


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckeZeroSupremum
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
open CenteredMomentFixedRayInducingTransport CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

lemma natural_relative_twists {η : Character} {z : O} (F : NaturalRow η z) (hz : z≠0)
    (η₀ : Character) (Q : Ideal O) (hQM : Q≤M)
    (hex : ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) :
    ∀θ : RayQuotient.Characters M H,
      (twistedFamily M H hH (F.character.product η₀.inverse) θ).residue≠1 := by
  have hn : ¬FixedInducingRow (η.product η₀.inverse) (internalQ Q η₀) fixedBadMask 1 z :=
    (not_fixedInducingRow_product_iff η η₀.inverse _ fixedBadMask 1 z inf_le_right
      fixedBadMask_ne_zero one_ne_zero hz (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hex
  apply CenteredMomentRayNonprincipal.all_ray_twists_nonprincipal M H hH
    (η.product η₀.inverse) (F.character.product η₀.inverse) (internalQ Q η₀)
    fixedBadMask 1 z ?_ (inf_le_left.trans hQM) hn
  exact product_row_presentation η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element)

include hH

theorem natural_relative_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff η₀.inverse I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW (Lmod+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  filter_upwards [eventually_ge_atTop Z₀,eventually_ge_atTop (η₀.modulus.absNorm:ℝ),
    eventually_gt_atTop (0:ℝ)] with Z hZ0 hη₀ hZ
  intro P hP hPcap η z hz F hcond Q hQM hex σ t v hσ hσhi
  have hc : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤Z^(Lmod+1) := by
    have hb : ((F.character.product η₀.inverse).modulus.absNorm:ℝ)≤
        (F.character.modulus.absNorm:ℝ)*(η₀.modulus.absNorm:ℝ) := by
      exact_mod_cast HeckePrimeScale.product_modulus_bound F.character η₀.inverse
    apply hb.trans
    calc
      _≤Z^Lmod*Z := mul_le_mul hcond hη₀ (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)
      _=Z^(Lmod+1) := by rw [Real.rpow_add hZ,Real.rpow_one]
  have hb:=hbound Z P hZ0 hP hPcap (F.character.product η₀.inverse) hc
    (natural_relative_twists M H hH F hz η₀ Q hQM hex) σ (t+v) hσ hσhi
  rw [relative_normalizedSlot_eq_ray M H η F.character η₀.inverse fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W b P σ t v (zero_lt_one.trans_le hP),norm_mul,
    CenteredMomentTwist.norm_real_imaginary_power P t (zero_lt_one.trans_le hP),one_mul]
  apply hb.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) degree

theorem natural_character_slot_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀ν : Character,∀ᶠZ : ℝ in atTop,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → Q≤ν.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff ν I*HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_relative_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro ν
  filter_upwards [hbound ν.inverse] with Z hz
  intro P hP hPcap η z hz0 F hcond Q hQM hQν hex σ t v hσ hσhi
  have hQeq : internalQ Q ν.inverse=Q := inf_eq_left.mpr hQν
  have he:=hz P hP hPcap η z hz0 F hcond Q hQM (by simpa only [hQeq] using hex) σ t v hσ hσhi
  simpa only [idealCoeff_inverse_conj,starRingEnd_self_apply] using he

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2703

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalFixedRaySourceRayPrime
Source SHA256: e48ee1d132df8f94e972e45e43521a3033e2b6bbbd5301a41fa1ea59a1f7ee9f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2704


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff Topology
open Filter

namespace SevenEighths.CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_ray_slots_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
      ∀θ : RayQuotient.Characters M H,
      ∀P : ℝ,1≤P → P≤Z^Lslot → ∀η : Character,∀z : O,z≠0 →
      ∀F : NaturalRow η z,(F.character.modulus.absNorm:ℝ)≤Z^Lmod →
      ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
      ∀σ t v : ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η fixedBadMask 1 z (primePool M H b P)
        (fun I=>idealCoeff (relativeCharacter M H hH η₀ θ) I*
          HeckePrimeAnnular.annularWeight W P σ v I) t P‖^2≤
        C*(1+|t|+|v|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,hC,hbound⟩:=natural_character_slot_bound M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  have hall:=Filter.eventually_all.mpr (fun θ : RayQuotient.Characters M H=>
    hbound (relativeCharacter M H hH η₀ θ))
  filter_upwards [hall] with Z hz
  intro θ P hP hPcap η z hz0 F hcond Q hQM hex σ t v hσ hσhi
  exact hz θ P hP hPcap η z hz0 F hcond (internalQ Q η₀)
    (inf_le_left.trans hQM)
    (relativeCharacter_fixedQ M H hH η₀ θ (internalQ Q η₀) (inf_le_left.trans hQM) inf_le_right)
    hex σ t v hσ hσhi

end SevenEighths.CenteredMomentNaturalFixedRaySource

end

end OAI
end OAIOriginalModule2704

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSlots
Source SHA256: 58d5aec6a4f46360e4d2139835df8e87188c5483cc52b9fad93598a0f8be6314
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2705



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum CenteredMomentNaturalFixedRaySource
open CenteredMomentNaturalRowSource CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentHeckeSlots CenteredMomentPrimeSlot CenteredExceptionalProfile
open CenteredMomentSecondHeightFamily
local notation "O" => HeckeFamily.O

lemma natural_slot_eq {η : Character} {z : O} (F : NaturalRow η z)
    (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P t : ℝ) :
    naturalSlot F.character pool (heightCoefficient β t) P=
      normalizedSlot η fixedBadMask 1 z pool β t P := by
  unfold naturalSlot normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  rw [F.ideal]
  simp only [heightCoefficient,one_mul]
  ring

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_slot_product {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃C : ℝ,0<C ∧ ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(z : O),z≠0 → ∀N : NaturalRow η z,
      (N.character.modulus.absNorm:ℝ)≤Z^Lmod →
    ∀Q : Ideal O,Q≤M → ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z →
    ∀A : Finset α,A⊆F →
      ‖∏i∈A,naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      C*(1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  let el : ℝ := loss/(F.card+1)
  have hel : 0<el := div_pos hloss (by positivity)
  obtain ⟨J,C,hC,hbound⟩ := natural_ray_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot el lo hi κ hLm hLs hel hbeta hκ
  let C₀ := max 1 C
  have hC₀ : 1≤C₀ := le_max_left _ _
  refine ⟨J*F.card,C₀^F.card,pow_pos (zero_lt_one.trans_le hC₀) _,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (1:ℝ)] with Z hz hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η z hz0 N hmod Q hQM hex A hAF
  have hZ0 : 0<Z := zero_lt_one.trans hZ
  have hk : 0≤κ := by linarith
  have hh : 1≤1+|t|+T := by linarith [abs_nonneg t]
  have hslot (i : α) (hi : i∈A) :
      ‖naturalSlot N.character (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖^2 ≤
      (C₀*(1+|t|+T)^J)*Z^(el+κ*w i) := by
    rw [natural_slot_eq N]
    have he := hz (θ i) (Z^(w i)) (Real.one_le_rpow hZ.le (hw i (hAF hi)))
      (Real.rpow_le_rpow_of_exponent_le hZ.le (hwL i (hAF hi))) η z hz0 N hmod Q hQM hex
      (σ i) t (v i) (hσlo i (hAF hi)) (hσhi i (hAF hi))
    apply he.trans
    rw [←Real.rpow_mul hZ0.le]
    calc
      _ ≤ (C₀*(1+|t|+T)^J)*Z^el*Z^(w i*κ) := by
        gcongr
        · exact le_max_right 1 C
        · exact hv i (hAF hi)
      _ = _ := by rw [mul_assoc,←Real.rpow_add hZ0]; congr 2 ; ring
  rw [norm_prod,←Finset.prod_pow]
  apply (Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot).trans
  rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hZ0]
  have hexp : (∑i∈A,(el+κ*w i))≤loss+κ*(∑i∈F,w i) := by
    rw [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,←Finset.mul_sum]
    have hc : (A.card:ℝ)≤F.card+1 := by exact_mod_cast (Finset.card_le_card hAF).trans (Nat.le_succ _)
    have he : (A.card:ℝ)*el≤loss := by
      calc
        _ ≤ (F.card+1)*el := mul_le_mul_of_nonneg_right hc hel.le
        _ = _ := by dsimp [el]; field_simp
    have hs := Finset.sum_le_sum_of_subset_of_nonneg hAF (fun i hi _=>hw i hi)
    nlinarith
  have hp : 1≤C₀*(1+|t|+T)^J := one_le_mul_of_one_le_of_one_le hC₀ (one_le_pow₀ hh)
  apply (mul_le_mul (pow_le_pow_right₀ hp (Finset.card_le_card hAF))
    (Real.rpow_le_rpow_of_exponent_le hZ.le hexp) (by positivity) (by positivity)).trans_eq
  rw [mul_pow,←pow_mul]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end OAIOriginalModule2705

/-! Original module: OAI.NumberTheory.DirichletL.Energy.AllocatedChildren
Source SHA256: 4e5de51d8260988b9fa03df021978469a2886c00f7ac20b0c2d1a3d44435d4d8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2706






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentNaturalRowSource CenteredMomentNaturalFixedRaySource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentDetectorDictionary CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion
open CenteredMomentSecondHeightFamily CenteredMomentHeckeHeight
open CenteredMomentOriginalRadialComparison CenteredMomentInductionEnergy
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma natural_product_eq_positive {η:Character}{z:O}(F:NaturalRow η z)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    polynomial F.character false W₁ X₁ 0 0*polynomial F.character false W₂ X₂ 0 0*
      ∏i,naturalSlot F.character (pool i) (β i) (P i)=
      CenteredMomentRetainedEnergy.positiveSlotRow η
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 z
        W₁ W₂ pool β P 0 X₁ X₂:=by
  rw [natural_unit_mask_positive F]
  have hh:=positiveSlotRow_eq_product η F.character fixedBadMask 1 z
    (by simpa only [one_mul] using F.element) W₁ W₂ pool β P X₁ X₂ 0 0 hX₁ hX₂ hP
  rw [twistProfile_zero,twistProfile_zero] at hh
  rw [hh]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hs:=CenteredMomentRayMaskedFloor.natural_slot_eq F (pool i) (β i) (P i) 0
  have he:heightCoefficient (β i) 0=β i:=by
    funext I
    simp only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one]
  rw [he] at hs
  exact hs

lemma natural_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂ pool β P
      X₁ X₂ r.keep r.profile r.scale:=by
  unfold radialEnergy CenteredMomentInductionEnergy.energy
  apply tsum_congr
  intro z
  by_cases hk:r.keep z
  · simp only [ite_eq_left hk,naturalCharacter_eq η z (hz z hk)]
    rw [natural_product_eq_positive (naturalRow η z (hz z hk)) W₁ W₂ pool β P X₁ X₂ hX₁ hX₂ hP]
  · simp only [ite_eq_right hk]

omit [Fintype α] in
lemma natural_subset_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (F:Finset α)(W₁ W₂:ℝ→ℂ)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
      polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
      r.keep r.profile r.scale=
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0 W₁ W₂
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ r.keep r.profile r.scale:=by
  have hh:=natural_radial_eq_energy (α:=F) η r hz W₁ W₂
    (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂ hX₁ hX₂
    (fun i=>hP i i.property)
  have hp (z:O):(∏i:F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))=
      ∏i∈F,naturalSlot (naturalCharacter η z) (pool i) (β i) (P i):=
    Finset.prod_coe_sort F (fun i:α=>naturalSlot (naturalCharacter η z) (pool i) (β i) (P i))
  simp_rw [hp] at hh
  exact hh

open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentRetainedProfile CenteredMomentCommonAllocationSum

def allocatedEnergy (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α):ℝ:=
  CenteredMomentInductionEnergy.energy (ι := ↥(liveIndices D a\J)) η
    (fixedBadMask*ConcretePrimeRowBridge.idealGenerator (1:Ideal O)) 1 0
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    (fun i:↥(liveIndices D a\J)=>pool i) (fun i:↥(liveIndices D a\J)=>heightCoefficient (β i) t)
    (fun i:↥(liveIndices D a\J)=>P i)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    r.keep r.profile r.scale

lemma child_radial_eq_energy (η:Character)(r:Radial)(hz:∀z,r.keep z→z≠0)
    (D:Ideal O)(a:Allocation D (Finset.univ:Finset (α⊕Fin 2))) (V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)(hP:∀i,0<P i)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))(J:Finset α)
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>child (α:=α) (naturalCharacter η z) D a V₁ V₂ pool β P
      t X₁ X₂ hX₁ hX₂ D₁ D₂ J) r.keep r.profile r.scale=
      allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ J:=by
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  exact natural_subset_radial_eq_energy η r hz (liveIndices D a\J)
    (V₁.profile (rawScale D a X₁ 0) (rawScale_pos D a X₁ hX₁ 0) t)
    (V₂.profile (rawScale D a X₂ 1) (rawScale_pos D a X₂ hX₂ 1) t)
    pool (fun i=>heightCoefficient (β i) t) P
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂) (fun i _=>hP i)

def commonAllocatedEnergy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val)):ℝ:=
  let d:=commonData (withHeight s τ v) C R B
  if left then allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J
  else allocatedEnergy τ r D a V₁ V₂ d.slots d.coefficient d.P
    v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J

lemma commonChild_energy (s:Input α)(τ:Character)(v:ℝ)(C R:Ideal O)
    (B:actualAllocations s.pools C)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2)))
    (V₁ V₂:Plain)(r:Radial)(hz:∀z,r.keep z→z≠0)(left:Bool)(D₁ D₂:Finset (Ideal O))
    (J:Finset (CenteredMomentCommonProfile.liveIndices B.val))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0):
    radialEnergy (fun z=>commonChild s τ v C R B D a V₁ V₂ left z D₁ D₂ J)
      r.keep r.profile r.scale=commonAllocatedEnergy s τ v C R B D a V₁ V₂ r left D₁ D₂ J:=by
  let d:=commonData (withHeight s τ v) C R B
  cases left
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.Y₁ d.Y₂ d.Y₁_pos d.Y₂_pos D₁ D₂ J hD₁ hD₂
  · exact child_radial_eq_energy τ r hz D a V₁ V₂ d.slots d.coefficient d.P d.P_pos
      v d.X₁ d.X₂ d.X₁_pos d.X₂_pos D₁ D₂ J hD₁ hD₂

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI
end OAIOriginalModule2706

/-! Original module: OAI.NumberTheory.DirichletL.Energy.AllocatedBound
Source SHA256: 94936519cab549b89f05979b9efa635c3c7b02beb6d264983c040df502a8140b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2707


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedChildren
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial
open CenteredMomentCommonRadialData CenteredMomentCommonHeightEnvelope
open CenteredMomentCommonAllocationSum CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentNaturalRowSource CenteredMomentRadialEligibleEnergy
local notation "O"=>HeckeFamily.O
variable {α:Type*}[Fintype α][DecidableEq α]

theorem actual_common_from_energy (b M:α→ℝ)(hM:∀i,0≤M i)(ε:ℝ)(hε:0<ε):
    ∃C₀:ℝ,0<C₀ ∧ ∀s:Input α,(∀i,s.hi i≤b i)→(∀i,s.M i≤M i)→
    ∀(τ:Character)(v:ℝ)(C R:Ideal O),R≠0→∀B:actualAllocations s.pools C,
    ∀(L:Ideal O)(a:Allocation L (Finset.univ:Finset (CenteredMomentCommonProfile.liveIndices B.val⊕Fin 2))),
    ∀V₁ V₂:Plain,V₁.W=s.W₁→V₂.W=s.W₂→∀r:Radial,(∀z,r.keep z→z≠0)→
    ∀E₁ E₂:ℝ,0≤E₁→0≤E₂→
    (∀left:Bool,∀D₁∈(CompletedGauss.primeSupport (R*C)).powerset,
      ∀D₂∈(CompletedGauss.primeSupport (R*C)).powerset,∀J∈(liveIndices L a).powerset,
      commonAllocatedEnergy s τ v C R B L a V₁ V₂ r left D₁ D₂ J≤(if left then E₁ else E₂))→
    childEnergy (commonData (withHeight s τ v) C R B) r L a≤
      C₀*(Ideal.absNorm (R*C).radical:ℝ)^ε*(E₁+E₂):=by
  obtain ⟨C₀,hC₀,hbound⟩:=actual_common_radial_energy b M hM ε hε
  refine ⟨C₀,hC₀,?_⟩
  intro s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂ he
  apply hbound s hhi hMs τ v C R hR B L a V₁ V₂ hV₁ hV₂ r hz E₁ E₂ hE₁ hE₂
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz true D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he true D₁ hD₁ D₂ hD₂ J hJ
  · intro D₁ hD₁ D₂ hD₂ J hJ
    rw [commonChild_energy s τ v C R B L a V₁ V₂ r hz false D₁ D₂ J
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₁) hi)).ne_zero)
      (fun I hi=>(support_prime (R*C) I ((Finset.mem_powerset.mp hD₂) hi)).ne_zero)]
    exact he false D₁ hD₁ D₂ hD₂ J hJ

end SevenEighths.CenteredMomentEnergyAllocatedChildren

end

end OAI
end OAIOriginalModule2707

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorCoefficients
Source SHA256: de7c2ac7511c1a50f24d0b253deef640784a05eb5ad453057ef04276af713617
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2708


namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckePrimeAnnular CenteredMomentCommonMaskEnergy
local notation "O" => HeckeFamily.O

 theorem slot_coefficient_bounds (W : ℝ→ℂ) (a b lo hi : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : Continuous W) :
    ∃B : ℝ,0<B ∧ ∀(ν : Character)(P σ v t : ℝ),0<P → lo≤σ → σ≤hi →
    ∀I : Ideal O,I≠0 →
      ‖heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I‖≤B ∧
      (heightCoefficient (fun I=>idealCoeff ν I*annularWeight W P σ v I) t I≠0 →
        (I.absNorm:ℝ)≤b*P) := by
  obtain ⟨B,hB,hprofile⟩ := fixed_profile_norm_bound W hW a b lo hi ha
  refine ⟨B,hB,?_⟩
  intro ν P σ v t hP hσlo hσhi I hI
  rw [heightCoefficient_norm _ _ _ hI]
  constructor
  · apply (show ‖idealCoeff ν I*annularWeight W P σ v I‖≤‖annularWeight W P σ v I‖ by
      rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one ν I)).trans
    by_cases hz : W ((I.absNorm:ℝ)/P)=0
    · simp [annularWeight,hz,hB.le]
    · have hs := hWs hz
      rw [annularWeight,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (ha.trans_le hs.1)]
      simpa only [Complex.neg_re,shift_re] using hprofile σ ⟨hσlo,hσhi⟩ _ hs
  · intro hn
    have hw : W ((I.absNorm:ℝ)/P)≠0 := by
      intro hh
      exact hn (by simp [heightCoefficient,annularWeight,hh])
    exact (div_le_iff₀ hP).mp (hWs hw).2

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end OAIOriginalModule2708

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowError
Source SHA256: 38cfc29d5984d912be9349db7caecec4da1fb73712a46ab6b48ddafca9a1c7bc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2709



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowError
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyReferenceHomogeneousError QuadraticInitialBound
local notation "O"=>HeckeFamily.O

theorem relative_slot_error {α:Type*}(F:Finset α)
    (Wslot:ℝ→ℂ)(aslot bslot lo hi bshort:ℝ)(ha:0<aslot)
    (hs:Function.support Wslot⊆Set.Icc aslot bslot)(hc:Continuous Wslot):
    ∃C:ℝ,0<C ∧ ∀T:Finset α,T⊆F → ∀W:𝓢(ℝ,ℂ),
      Function.support (W:ℝ→ℂ)⊆Set.Iic bshort →
      ∀(χ:O→Character)(ν:α→Character)(pool:α→Finset (Ideal O))
        (P σ freq:α→ℝ)(t X K:ℝ)(Φ:𝓢(ℝ,ℂ))(keep:O→Prop),
      0<X → 0<K → (∀i∈T,0<P i) → (∀i∈T,lo≤σ i) → (∀i∈T,σ i≤hi) →
      (∀i∈T,∀I∈pool i,Prime I) → (∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) →
      radialEnergy (fun z=>polynomial (χ z) false W X 0 t *
        ∏i∈T,naturalSlot (χ z) (pool i)
          (heightCoefficient (fun I=>idealCoeff (ν i) I*
            HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I) t) (P i)) keep Φ K≤
        C*((schwartzSeminormFamily ℝ ℝ ℂ (0,0)) W)^2*
          diagonalControl Φ*max 1 K*X*∏i∈T,P i:=by
  obtain ⟨B,hB,hslot⟩:=CenteredMomentRayMaskedFloor.slot_coefficient_bounds
    Wslot aslot bslot lo hi ha hs hc
  obtain ⟨C,hC,he⟩:=natural_reference_error_homogeneous F bshort
    (fun _=>bslot) (fun _=>B) (fun _ _=>hB.le)
  refine ⟨C,hC,?_⟩
  intro T hT W hW χ ν pool P σ freq t X K Φ keep hX hK hP hlo hhi hp hΦ
  apply he T hT W hW χ pool
    (fun i I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight Wslot (P i) (σ i) (freq i) I)
    P t X K Φ keep hX hK hP hp
  · intro i hi I hI
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).1
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hb
  · intro i hi I hI hn
    have hb:=(hslot (ν i) (P i) (σ i) (freq i) 0 (hP i hi) (hlo i hi) (hhi i hi)
      I (hp i hi I hI).ne_zero).2
    apply hb
    simpa only [heightCoefficient,Complex.ofReal_zero,mul_zero,Complex.cpow_zero,mul_one] using hn
  · exact hΦ

end SevenEighths.CenteredMomentEnergyReferenceLowError

end

end OAI
end OAIOriginalModule2709

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorNatural
Source SHA256: 3052492c63a843f8495c3ab12572dcc689c86e7f29c8c8033968723c34491d50
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2710




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ),Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ → ∀A : Finset α,A⊆F →
      radialEnergy (fun z=>polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,Cs,hCs,hslot⟩ := natural_slot_product M H hH F W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨S,Cp,hCp,hplain⟩ := global_positive_scale a₀ b₀ ha₀
  refine ⟨J,S,Cp^4*3^8*Cs,by positivity,?_⟩
  intro η₀
  filter_upwards [hslot η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂ A hAF
  let E := Cs*(1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hE : 0≤E := by dsimp [E]; positivity
  let B₁ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂ := S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁ : 0≤B₁ := apply_nonneg _ _
  have hB₂ : 0≤B₂ := apply_nonneg _ _
  let B := Cp^2*(B₁*B₂)*Qbound^2*3^4*Real.sqrt E
  have hB : 0≤B := by dsimp [B]; positivity
  have hpoint (z : O) (hkeep : r.keep z) :
      ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0*
        polynomial (naturalCharacter η z) false W₂ X₂ 0 0*
        ∏i∈A,naturalSlot (naturalCharacter η z) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i))‖≤B := by
    have hn := hz z hkeep
    have heq := naturalCharacter_eq η z hn
    have hnon : (naturalCharacter η z).residue≠1 := by
      rw [heq]
      exact CenteredMomentNonprincipalGate.actual_row_nonprincipal η
        (naturalRow η z hn).character (internalQ Q η₀) fixedBadMask 1 z
        (by simpa only [one_mul] using (naturalRow η z hn).element) (hex z hkeep)
    have h₁ : ‖polynomial (naturalCharacter η z) false W₁ X₁ 0 0‖≤Cp*B₁*Qbound*3^2 := by
      have he := hplain W₁ hs₁ _ hnon X₁ 0 hX₁
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₁)) (show (0:ℝ)≤9 by norm_num))
    have h₂ : ‖polynomial (naturalCharacter η z) false W₂ X₂ 0 0‖≤Cp*B₂*Qbound*3^2 := by
      have he := hplain W₂ hs₂ _ hnon X₂ 0 hX₂
      norm_num only [abs_zero,add_zero] at he
      apply he.trans
      simpa only [show (3:ℝ)^2=9 by norm_num] using (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hQ z hkeep) (mul_nonneg hCp.le hB₂)) (show (0:ℝ)≤9 by norm_num))
    have hs := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η z hn (naturalRow η z hn)
      (by simpa only [heq] using hmod z hkeep) Q hQM (hex z hkeep) A hAF
    rw [←heq] at hs
    have hsroot := (Real.le_sqrt (norm_nonneg _) hE).mpr hs
    rw [norm_mul,norm_mul]
    apply (mul_le_mul (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity))
      hsroot (norm_nonneg _) (by positivity)).trans_eq
    dsimp [B,B₁,B₂]
    norm_num only [abs_zero,add_zero]
    ring
  have he := radial_bound_on_keep _ r B hB hpoint
  apply he.trans_eq
  dsimp [B,E,B₁,B₂]
  rw [mul_pow,mul_pow,mul_pow,mul_pow,Real.sq_sqrt hE]
  ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end OAIOriginalModule2710

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorShared
Source SHA256: b1e89fd7b41c636c99b1fd83a1546fddb81092be65b77666dfe20483ba8ded90
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2711





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem masked_natural_pair_slots {α : Type*} [DecidableEq α]
    (F : Finset α) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i∈F,0≤w i) → (∀i∈F,w i≤Lslot) →
      (∀i∈F,lo≤σ i) → (∀i∈F,σ i≤hi) → 0≤T → (∀i∈F,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false W₁ X₁ 0 0*
        polynomial (excluded (naturalCharacter η z) R) false W₂ X₂ 0 0*
        ∏i∈F,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
          (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
            HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
        r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i∈F,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := natural_pair_slots M H hH F W a b ha hWs hW a₀ b₀ ha₀
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨B,hB,hcoeff⟩ := slot_coefficient_bounds W a b lo hi ha hWs hW.continuous
  obtain ⟨Cd,hCd,hdelete⟩ := CenteredMomentCommonMaskRadialEnergy.actual_radial_shared_energy
    F (fun _=>b) (fun _=>B) (fun _ _=>hB.le) ε hε
  refine ⟨J,S,Cd*C,mul_pos hCd hC,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  let E := C*diagonalControl r.profile*max 1 r.scale*
    ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
      (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i∈F,w i))
  have hd := diagonalControl_nonneg r.profile
  have hE : 0≤E := by dsimp [E]; positivity
  have hp (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) : Prime I :=
    (Finset.mem_filter.mp hI).2.1
  have hc (i : α) (hi : i∈F) (I : Ideal O) (hI : I∈primePool M H b (Z^(w i))) :=
    hcoeff (relativeCharacter M H hH η₀ (θ i)) (Z^(w i)) (σ i) (v i) t
      (Real.rpow_pos_of_pos hZ0 _) (hσlo i hi) (hσhi i hi) I (hp i hi I hI).ne_zero
  have he := hdelete (CompletedGauss.primeSupport R) (support_prime R) (naturalCharacter η)
    W₁ W₂ X₁ X₂ a₀ b₀ a₀ b₀ (fun i=>primePool M H b (Z^(w i)))
    (fun i=>heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
      HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t)
    (fun i=>Z^(w i)) r.keep r.profile r.scale E hX₁ hX₂ hb₀ hb₀ hs₁ hs₂ hp
    (fun _ _=>Real.rpow_pos_of_pos hZ0 _) (fun i hi I hI=>(hc i hi I hI).1)
    (fun i hi I hI=>(hc i hi I hI).2) r.scale_pos r.nonneg hE ?_
  · rw [primeSupport_product_radical R hR] at he
    exact he.trans_eq (by dsimp [E]; ring)
  · intro D₁ hD₁ D₂ hD₂ A hA
    have hn (D : Finset (Ideal O)) (hD : D∈(CompletedGauss.primeSupport R).powerset) :
        0<(Ideal.absNorm (∏I∈D,I):ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Finset.prod_ne_zero_iff.mpr (fun I hi=>(support_prime R I (Finset.mem_powerset.mp hD hi)).ne_zero)))
    exact hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound hQM hQbound hz hex hmod hQ
      W₁ W₂ hs₁ hs₂ _ _ (div_pos hX₁ (hn D₁ hD₁)) (div_pos hX₂ (hn D₂ hD₂))
      (F\A) Finset.sdiff_subset

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end OAIOriginalModule2711

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorSource
Source SHA256: d7b505fbb626c2bc1ad81892b580693d31d02a6decdfa8b6f7a1d90bb5e5a90e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2712




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem original_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (Lmod Lslot loss lo hi κ : ℝ) (hLm : 0≤Lmod) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(Qbound : ℝ)(R : Ideal O),R≠0 → Q≤M → 0≤Qbound →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^Lmod) →
      (∀z,r.keep z→((naturalCharacter η z).modulus.absNorm:ℝ)≤Qbound) →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*Qbound^4*
         (1+|t|+T)^degree*Z^(loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := masked_natural_pair_slots M H hH (Finset.univ : Finset α)
    W a b ha hWs hW a₀ b₀ ε ha₀ hb₀ hε Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  obtain ⟨n,T₀,Ct,hCt,ht⟩ :=
    CenteredMomentFiniteProfileExceptional.normPowerProfile_source_control a₀ b₀ ha₀ S
  refine ⟨4*n+J,T₀,C*Ct^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_gt_atTop (0:ℝ)] with Z hZ hZ0
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r Qbound R hR hQM hQbound hz hex hmod hQ
    W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hexbase (z : O) (hk : r.keep z) :
      ¬FixedInducingRow η (internalQ Q η₀) fixedBadMask 1 z := by
    intro hh
    apply hex z hk
    exact (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff η (internalQ Q η₀)
      fixedBadMask (ConcretePrimeRowBridge.idealGenerator R) 1 z fixedBadMask_ne_zero
      (ConcretePrimeRowBridge.idealGenerator_ne_zero R hR) one_ne_zero (hz z hk)
      (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hh
  let V₁ := CenteredMomentLattice.normPowerProfile W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t
  let V₂ := CenteredMomentLattice.normPowerProfile W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t
  have hv₁ : Function.support (V₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₁ a₀ b₀ ha₀ hs₁ (W₁.smooth ⊤) t).trans hs₁
  have hv₂ : Function.support (V₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ :=
    (CenteredMomentTwist.normPowerProfile_support W₂ a₀ b₀ ha₀ hs₂ (W₂.smooth ⊤) t).trans hs₂
  have he := hZ θ w σ v t T (fun i _=>hw i) (fun i _=>hwL i)
    (fun i _=>hσlo i) (fun i _=>hσhi i) hT (fun i _=>hv i)
    η Q r Qbound R hR hQM hQbound hz hexbase hmod hQ V₁ V₂ hv₁ hv₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale =
    radialEnergy (fun z=>polynomial (excluded (naturalCharacter η z) R) false V₁ X₁ 0 0*
      polynomial (excluded (naturalCharacter η z) R) false V₂ X₂ 0 0*
      ∏i,naturalSlot (excluded (naturalCharacter η z) R) (primePool M H b (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I) t) (Z^(w i)))
      r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy radialEnergy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · simp only [hk,ite_true]
      rw [original_positive_normalized (naturalRow η z (hz z hk)) R hR W₁ W₂
        a₀ b₀ a₀ b₀ ha₀ ha₀ hs₁ hs₂ (W₁.smooth ⊤) (W₂.smooth ⊤)
        _ _ _ (fun i=>Real.rpow_pos_of_pos hZ0 _) t X₁ X₂ hX₁ hX₂]
      rw [norm_mul,norm_mul,positive_height_phase_norm X₁ t hX₁,
        positive_height_phase_norm X₂ t hX₂,one_mul,one_mul,naturalCharacter_eq η z (hz z hk)]
    · simp only [hk,ite_false]
  rw [hid]
  apply he.trans
  have hB₁ := ht W₁ hs₁ t
  have hB₂ := ht W₂ hs₂ t
  have hprod : (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₁ *
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) V₂)^2 ≤
      (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n) := by
    have hh := pow_le_pow_left₀ (mul_nonneg (apply_nonneg _ _) (apply_nonneg _ _))
      (mul_le_mul hB₁ hB₂ (apply_nonneg _ _) (by positivity)) 2
    have hheight : (1+‖t‖)^(4*n)≤(1+|t|+T)^(4*n) := by
      apply pow_le_pow_left₀ (by positivity)
      rw [Real.norm_eq_abs]
      linarith
    calc
      _ ≤ (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(1+‖t‖)^n*
        (Ct*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)*(1+‖t‖)^n))^2 := hh
      _ = (Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+‖t‖)^(4*n) := by
          rw [Nat.mul_comm 4 n,pow_mul]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hheight (by positivity)
  have hd := diagonalControl_nonneg r.profile
  calc
    _ ≤ C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*max 1 r.scale*
      ((Ct^4*(T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁*
        T₀.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂)^2)*(1+|t|+T)^(4*n))*Qbound^4*
      (1+|t|+T)^J*Z^(loss+κ*(∑i,w i)) := by gcongr
    _ = _ := by rw [pow_add]; ring

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end OAIOriginalModule2712

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayMaskedFloor
Source SHA256: 69eab25845a0e57d2bb465b616def835953a1fecb61249a6f83ab6e52e29cfc7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2713


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeDyadic HeckeZeroSupremum QuadraticInitialBound ConcreteTraceCRT
open CenteredMomentNaturalFixedRaySource CenteredMomentNaturalRowSource
open CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedNaturalRadial CenteredMomentPrimeSlot
open CenteredMomentPlainPositiveScale CenteredMomentOriginalRadialComparison
open CenteredMomentPlainGlobalEnergy CenteredMomentSecondHeightFamily CenteredExceptionalProfile
open CenteredMomentRadialEligibleEnergy (Radial)
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem natural_masked_positive_floor {α : Type*} [Fintype α] [DecidableEq α] (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ ε : ℝ) (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hε : 0<ε)
    (L Lslot loss lo hi κ bΦ : ℝ) (hL : 0≤L) (hbΦ : 0≤bΦ) (hLs : 0≤Lslot) (hloss : 0<loss)
    (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) →
      (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤T → (∀i,|v i|≤T) →
    ∀(η : Character)(Q : Ideal O)(r : Radial)(R : Ideal O),R≠0 → Q≤M →
      (∀z,r.keep z→z≠0) →
      (∀z,r.keep z→¬FixedInducingRow η (internalQ Q η₀) (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z) →
      Function.support (r.profile:ℝ→ℂ)⊆Set.Iic bΦ →
    ∀(m q ρ : ℝ),0≤m → 0≤q → m+q≤ρ → ρ≤L → r.scale=Z^m →
      (η.modulus.absNorm:ℝ)≤Z^q →
    ∀(W₁ W₂ : 𝓢(ℝ,ℂ)),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a₀ b₀ →
    ∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      CenteredMomentInductionEnergy.energy η (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t
        W₁ W₂ (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale ≤
      C*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
         (1+|t|+T)^degree*Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
  obtain ⟨J,S,C,hC,hbound⟩ := original_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ ε ha₀ hb₀ hε (L+1) Lslot loss lo hi κ (by linarith) hLs hloss hbeta hκ
  let Fc : ℝ := fixedConductorFactor
  have hFc : 0<Fc := by
    unfold Fc fixedConductorFactor
    norm_cast
    apply Nat.mul_pos
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr fixedBadMask_ne_zero))
    · exact Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
        (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0)))
  refine ⟨J,S,C*Fc^4,by positivity,?_⟩
  intro η₀
  filter_upwards [hbound η₀,eventually_ge_atTop (Fc*bΦ),eventually_ge_atTop (1:ℝ)] with Z hZ hconst hZ1
  intro θ w σ v t T hw hwL hσlo hσhi hT hv η Q r R hR hQM hz hex hsΦ
    m q ρ hm hq hρ hρL hscale hη W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  let r' : Radial := {r with keep := fun z=>r.keep z ∧ r.profile (‖eisEmbedding z‖^2/r.scale)≠0}
  have hmod (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Fc*bΦ*Z^ρ := by
    have hn := hz z hk.1
    rw [naturalCharacter_eq η z hn]
    have hrow : ((Ideal.span {z}).absNorm:ℝ)≤bΦ*Z^m := by
      rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,←hscale]
      exact (div_le_iff₀ r.scale_pos).mp (hsΦ hk.2)
    have he := (naturalRow η z hn).modulus_power_bound Z q m bΦ hZ0 hbΦ hη hrow
    apply he.trans
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg hFc.le hbΦ)
    exact Real.rpow_le_rpow_of_exponent_le hZ1 (by linarith)
  have hcap (z : O) (hk : r'.keep z) :
      ((naturalCharacter η z).modulus.absNorm:ℝ)≤Z^(L+1) := by
    apply (hmod z hk).trans
    calc
      _ ≤ Z*Z^L := mul_le_mul hconst (Real.rpow_le_rpow_of_exponent_le hZ1 hρL)
        (Real.rpow_nonneg hZ0.le _) hZ0.le
      _ = _ := by rw [Real.rpow_add hZ0,Real.rpow_one]; ring
  have he := hZ θ w σ v t T hw hwL hσlo hσhi hT hv η Q r'
    (Fc*bΦ*Z^ρ) R hR hQM (by positivity) (fun z hk=>hz z hk.1)
    (fun z hk=>hex z hk.1) hcap hmod W₁ W₂ hs₁ hs₂ X₁ X₂ hX₁ hX₂
  have hid : CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r'.keep r'.profile r'.scale =
    CenteredMomentInductionEnergy.energy η
      (fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 t W₁ W₂
      (fun i=>primePool M H b (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ r.keep r.profile r.scale := by
    unfold CenteredMomentInductionEnergy.energy
    apply tsum_congr
    intro z
    by_cases hk : r.keep z
    · by_cases hp : r.profile (‖eisEmbedding z‖^2/r.scale)=0
      · simp [r',hk,hp]
      · simp [r',hk,hp]
    · simp [r',hk]
  rw [hid] at he
  dsimp only [r'] at he
  rw [hscale,max_eq_right (Real.one_le_rpow hZ1 hm)] at he
  rw [hscale]
  apply he.trans_eq
  have hzpow : Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))=Z^(m+4*ρ+loss+κ*(∑i,w i)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le,←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    congr 1
    norm_num
    ring
  calc
    _ = (C*Fc^4*(R.radical.absNorm:ℝ)^ε*diagonalControl r.profile*bΦ^4*
      ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*
      (1+|t|+T)^J)*(Z^m*(Z^ρ)^4*Z^(loss+κ*(∑i,w i))) := by ring
    _ = _ := by rw [hzpow]

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end OAIOriginalModule2713

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RayMaskedFloorState
Source SHA256: d92e43317ba957bfacda742d91ce8447be88e3245535ee5ad3a8a00ffa539927
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2714



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentRayMaskedFloor
open HeckeFamily HeckeZeroSupremum QuadraticInitialBound
open CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentSecondHeightFamily
open CenteredMomentPrimeSlot CenteredMomentInductionEnergy
local notation "O" => HeckeFamily.O

variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem exists_positive_floor {α : Type*} [Fintype α] [DecidableEq α]
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (a₀ b₀ bΦ Bmask ε Lslot lo hi κ : ℝ)
    (ha₀ : 0<a₀) (hb₀ : 0≤b₀) (hbΦ : 0<bΦ) (hmask : 0≤Bmask)
    (hε : 0<ε) (hLs : 0≤Lslot) (hbeta : (51/100:ℝ)≤beta) (hκ : 2*beta-1≤κ) :
    ∃degree : ℕ,∃S : Finset (ℕ×ℕ),∃C : ℝ,0<C ∧
    ∀η₀ : Character,∀ᶠZ : ℝ in atTop,
    ∀(θ : α→RayQuotient.Characters M H)(w σ v : α→ℝ)(t T : ℝ),
      (∀i,0≤w i) → (∀i,w i≤Lslot) → (∀i,lo≤σ i) → (∀i,σ i≤hi) →
      0≤T → (∀i,|v i|≤T) →
    ∀(Q : Ideal O),Q≤M → ∀s : NaturalState Z Bmask bΦ,
      s.fixedModulus=internalQ Q η₀ → s.width≤ε/16 → 6*κ*(∑i,w i)≤s.width →
    ∀p : Profiles a₀ b₀,∀X₁ X₂ : ℝ,0<X₁ → 0<X₂ →
      energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
        (fun i=>primePool M H b (Z^(w i)))
        (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
        (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale ≤
      C*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^degree*Z^(s.width+ε) := by
  let e : ℝ := ε/(4*(Bmask+1))
  have he : 0<e := div_pos hε (by positivity)
  have hcost : Bmask*e≤ε/4 := by
    have hh := mul_le_mul_of_nonneg_left (show Bmask≤Bmask+1 by linarith) he.le
    have hid : e*(Bmask+1)=ε/4 := by dsimp [e]; field_simp
    rw [hid] at hh
    linarith
  obtain ⟨J,S,C,hC,hfloor⟩ := natural_masked_positive_floor (α:=α) M H hH W a b ha hWs hW
    a₀ b₀ e ha₀ hb₀ he (ε/16) Lslot (ε/4) lo hi κ bΦ (by positivity) hbΦ.le hLs
    (by positivity) hbeta hκ
  refine ⟨J,S,C*bΦ^4,mul_pos hC (pow_pos hbΦ _),?_⟩
  intro η₀
  filter_upwards [hfloor η₀] with Z hZ
  intro θ w σ v t T hw hwL hσlo hσhi hT hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hZ1 := s.base_ge_one
  have hZ0 : 0<Z := zero_lt_one.trans_le hZ1
  have hrad : (s.puncture.radical.absNorm:ℝ)^e≤Z^(Bmask*e) := by
    rw [Real.rpow_mul hZ0.le]
    exact Real.rpow_le_rpow (by positivity) s.radical_bound he.le
  have hex (z : O) (hz : s.radial.keep z) :
      ¬CenteredExceptionalProfile.FixedInducingRow s.character (internalQ Q η₀)
        (fixedBadMask*ConcretePrimeRowBridge.idealGenerator s.puncture) 1 z := by
    rw [←hQ]
    exact s.nonexceptional z hz
  have hh := hZ θ w σ v t T hw hwL hσlo hσhi hT hv s.character Q s.radial s.puncture
    s.puncture_ne_zero hQM s.row_ne_zero hex s.radial_support s.rowWidth s.characterWidth
    (ε/16) s.row_nonneg s.character_nonneg hs le_rfl s.scale_eq s.modulus_bound
    (p.profile 0) (p.profile 1) (p.support 0) (p.support 1) X₁ X₂ hX₁ hX₂
  have hwidth : s.rowWidth≤s.width := by dsimp [NaturalState.width]; linarith [s.character_nonneg]
  have hbudget : Bmask*e+(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤s.width+ε := by
    linarith
  have hpow : Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤Z^(s.width+ε) := by
    rw [←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ1 hbudget
  have hd := diagonalControl_nonneg s.radial.profile
  have hc := p.control_nonneg S
  apply hh.trans
  change C*(s.puncture.radical.absNorm:ℝ)^e*diagonalControl s.radial.profile*bΦ^4*
    (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))≤_
  calc
    _ ≤ C*Z^(Bmask*e)*diagonalControl s.radial.profile*bΦ^4*
      (p.control S)^2*(1+|t|+T)^J*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i)) := by gcongr
    _ = (C*bΦ^4*diagonalControl s.radial.profile*(p.control S)^2*(1+|t|+T)^J)*
      (Z^(Bmask*e)*Z^(s.rowWidth+4*(ε/16)+ε/4+κ*(∑i,w i))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)

end SevenEighths.CenteredMomentRayMaskedFloor

end

end OAI
end OAIOriginalModule2714

/-! Original module: OAI.NumberTheory.DirichletL.Energy.Bands
Source SHA256: a61844ac79dfb06cdbce70a09bdc62671b15ad25ded96a3069fc657909e20324
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2715



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentEnergyBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentFiniteProfileExceptional
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def length (Z X:ℝ):ℝ:=Real.logb Z (max 1 X)

lemma length_nonneg (Z X:ℝ)(hZ:1<Z):0≤length Z X:=
  Real.logb_nonneg hZ (le_max_left _ _)

def ZeroAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

lemma zeroAt_of_zeroBound (Q:Ideal O)(a b bΦ Bmask L M ε Z Z₀:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (h:ZeroBound Q a b bΦ Bmask M ε degree S C Z₀)(hZ:Z₀≤Z):
    ZeroAt Q a b bΦ Bmask L M ε Z degree S C:=by
  intro s hQ hs p t X₁ X₂ hX₁ hX₂ _ _
  exact h Z hZ s hQ hs p t X₁ X₂ hX₁ hX₂

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

theorem exists_positive_bottom (W:ℝ→ℂ)(aslot bslot:ℝ)(haslot:0<aslot)
    (hWs:Function.support W⊆Set.Icc aslot bslot)(hW:ContDiff ℝ ∞ W)
    (a b bΦ Bmask L Lslot lo hi ε κ:ℝ)
    (ha:0<a)(hb:0≤b)(hbΦ:0<bΦ)(hmask:0≤Bmask)(hε:0<ε)(hLs:0≤Lslot)
    (hbeta:(51/100:ℝ)≤HeckeZeroSupremum.beta)(hκ:2*HeckeZeroSupremum.beta-1≤κ):
    ∃degree:ℕ,∃S:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀η₀:Character,∀ᶠZ:ℝ in atTop,1<Z ∧ ∀Q:Ideal O,Q≤M→
        PositiveAt (α:=α) M H hH W bslot a b bΦ Bmask L Lslot lo hi
          (ε/16) ε κ Z η₀ Q degree S C:=by
  have hs (T:Finset α):=CenteredMomentRayMaskedFloor.exists_positive_floor (α:=T)
    M H hH W aslot bslot haslot hWs hW a b bΦ Bmask ε Lslot lo hi κ
    ha hb hbΦ hmask hε hLs hbeta hκ
  choose J S C hC hbound using hs
  let S₀:Finset (ℕ×ℕ):=Finset.univ.biUnion S
  let C₀:ℝ:=1+∑T:Finset α,C T
  have hC₀:0<C₀:=by
    have hh:=Finset.sum_nonneg (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
    dsimp [C₀];linarith
  refine ⟨∑T:Finset α,J T,S₀,C₀,hC₀,?_⟩
  intro η₀
  have hall:∀ᶠZ:ℝ in atTop,∀T:Finset α,_:=Filter.eventually_all.mpr (fun T=>hbound T η₀)
  filter_upwards [hall,eventually_gt_atTop (1:ℝ)] with Z hZ hZ1
  refine ⟨hZ1,?_⟩
  intro Q hQM T θ w σ v t height hw hwL hσlo hσhi hheight hv s hQ hs p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hslots:6*κ*(∑i,w i)≤s.width:=by
    linarith [length_nonneg Z X₁ hZ1,length_nonneg Z X₂ hZ1]
  have hh:=hZ T θ w σ v t height hw hwL hσlo hσhi hheight hv Q hQM s hQ hs hslots p X₁ X₂ hX₁ hX₂
  have hsub:S T⊆S₀:=by
    intro x hx
    exact Finset.mem_biUnion.mpr ⟨T,Finset.mem_univ _,hx⟩
  have hpc:p.control (S T)≤p.control S₀:=by
    unfold Profiles.control
    exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 0))
      (Seminorm.le_def.mp (Finset.sup_mono hsub) (p.profile 1))
      (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)
  have hc:C T≤C₀:=by
    have hh:=Finset.single_le_sum (fun T (_:T∈(Finset.univ:Finset (Finset α)))=>(hC T).le)
      (Finset.mem_univ T)
    dsimp [C₀];linarith
  have hj:J T≤∑T:Finset α,J T:=Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ T)
  have hpow:(1+|t|+height)^(J T)≤(1+|t|+height)^(∑T:Finset α,J T):=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hj
  have hd:=diagonalControl_nonneg s.radial.profile
  have hp:=p.control_nonneg S₀
  have hpt:=p.control_nonneg (S T)
  apply hh.trans
  gcongr
end SevenEighths.CenteredMomentEnergyBands

end

end OAI
end OAIOriginalModule2715

/-! Original module: OAI.NumberTheory.DirichletL.Energy.AllocatedZero
Source SHA256: c8616e37629c3f7a6f34a3cdf489a3f41aff96621ca6c50ae4eda3cd8c507dd3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2716




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergyAllocatedZero
open HeckeFamily CenteredMomentEnergyAllocatedChildren CenteredMomentEnergyAllocatedProfiles
open CenteredMomentAllocatedNaturalSource CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentRetainedProfile CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentRadialEligibleEnergy (Radial)
open QuadraticInitialBound
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α][DecidableEq α]

lemma allocatedScale_le (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(X:ℝ)(hX:0<X)
    (j:Fin 2)(F:Finset (Ideal O))(hF:∀I∈F,I≠0):
    clippedScale (rawScale D a X j)/(Ideal.absNorm (∏I∈F,I):ℝ)≤max 1 X:=by
  have hn:1≤(Ideal.absNorm (CenteredMomentDivisorRectangle.selectedPlain D a j):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (CenteredMomentDivisorExtraction.selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hf:1≤(Ideal.absNorm (∏I∈F,I):ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Finset.prod_ne_zero_iff.mpr hF))
  have hx:rawScale D a X j≤X:=div_le_self hX.le hn
  exact (div_le_self (by unfold clippedScale;positivity) hf).trans
    (max_le_max_left 1 hx)

lemma allocated_empty (η:Character)(r:Radial)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))(V₁ V₂:Plain)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O)):
    allocatedEnergy η r D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)=
      CenteredMomentCoreFloor.zeroEnergy η
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator 1) 1 0
        (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
        (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
        (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
        (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) r:=by
  let : IsEmpty ↥(liveIndices D a\liveIndices D a):=⟨fun i=>by
    have hi:=Finset.mem_sdiff.mp i.property
    exact hi.2 hi.1⟩
  simp only [allocatedEnergy,energy,CenteredMomentCoreFloor.zeroEnergy,
    CenteredMomentCoreFloor.zeroRow,positiveSlotRow,Fintype.prod_empty,mul_one]

theorem empty_from_zeroAt (lo hi Z Bmask bΦ L Mcap ε:ℝ)(hlo:0<lo)(hL:0≤L)
    (Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hz:ZeroAt Q (lo/max 1 hi) hi bΦ Bmask L Mcap ε Z degree S C)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=Q)(hwidth:s.width≤Mcap)
    (hunit:s.puncture=1)(p:Profiles lo hi)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (α⊕Fin 2)))
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(D₁ D₂:Finset (Ideal O))
    (hD₁:∀I∈D₁,I≠0)(hD₂:∀I∈D₂,I≠0)
    (hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L):
    let V₁:=sourcePlain lo hi hlo (p.profile 0) (p.support 0)
    let V₂:=sourcePlain lo hi hlo (p.profile 1) (p.support 1)
    let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
    let hU:∀i,0<U i:=by intro i;fin_cases i;exact rawScale_pos D a X₁ hX₁ 0;exact rawScale_pos D a X₂ hX₂ 1
    allocatedEnergy s.character s.radial D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ D₁ D₂ (liveIndices D a)≤
      C*diagonalControl s.radial.profile*((retainedPair lo hi hlo p U hU t).control S)^2*
        Z^(s.width+ε):=by
  dsimp only
  rw [allocated_empty]
  have hd₁:0<(Ideal.absNorm (∏I∈D₁,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₁))
  have hd₂:0<(Ideal.absNorm (∏I∈D₂,I):ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (Finset.prod_ne_zero_iff.mpr hD₂))
  let U:Fin 2→ℝ:=![rawScale D a X₁ 0,rawScale D a X₂ 1]
  have hU:∀i,0<U i:=by
    intro i;fin_cases i
    · exact rawScale_pos D a X₁ hX₁ 0
    · exact rawScale_pos D a X₂ hX₂ 1
  have hh:=hz s hQ hwidth (retainedPair lo hi hlo p U hU t) 0
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ))
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ))
    (div_pos (by unfold clippedScale;positivity) hd₁)
    (div_pos (by unfold clippedScale;positivity) hd₂)
    ((allocatedScale_le D a X₁ hX₁ 0 D₁ hD₁).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₁))
    ((allocatedScale_le D a X₂ hX₂ 1 D₂ hD₂).trans
      (max_le (Real.one_le_rpow s.base_ge_one hL) hc₂))
  rw [NaturalState.plainEnergy_eq_zero] at hh
  simpa only [NaturalState.mask,hunit,retainedPair,U,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.head_cons,norm_zero,zero_add,abs_zero,add_zero,one_pow,mul_one] using hh

end SevenEighths.CenteredMomentEnergyAllocatedZero

end

end OAI
end OAIOriginalModule2716

/-! Original module: OAI.NumberTheory.DirichletL.Energy.BandMonotonicity
Source SHA256: 15102fee699c6a156a62a86e7480d4afdc67153fc0c613964aa7f68e1b793465
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2717


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyBandMonotonicity
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentFiniteProfileExceptional CenteredMomentInductionEnergy QuadraticInitialBound
local notation "O"=>HeckeFamily.O

def widenState {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    NaturalState Z B' b':=
  {s with
    puncture_bound:=s.puncture_bound.trans (Real.rpow_le_rpow_of_exponent_le s.base_ge_one hB)
    radial_support:=fun _x hx=>le_trans (s.radial_support hx) hb}

def widenProfiles {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b'):Profiles a' b' where
  profile:=p.profile
  support:=fun i _x hx=>⟨ha.trans (p.support i hx).1,(p.support i hx).2.trans hb⟩

lemma widenState_width {Z B b B' b':ℝ}(s:NaturalState Z B b)(hB:B≤B')(hb:b≤b'):
    (widenState s hB hb).width=s.width:=rfl

lemma widenProfiles_control {a b a' b':ℝ}(p:Profiles a b)(ha:a'≤a)(hb:b≤b')
    (S:Finset (ℕ×ℕ)):(widenProfiles p ha hb).control S=p.control S:=rfl

lemma profile_control_mono {a b:ℝ}(p:Profiles a b){S T:Finset (ℕ×ℕ)}(hst:S⊆T):
    p.control S≤p.control T:=by
  unfold Profiles.control
  exact mul_le_mul (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 0))
    (Seminorm.le_def.mp (Finset.sup_mono hst) (p.profile 1))
    (sourceControl_nonneg _ _) (sourceControl_nonneg _ _)

theorem zeroAt_transport (Q:Ideal O)(a b radial mask L Mcap eps Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:ZeroAt Q a b radial mask L Mcap eps Z J S C):
    ZeroAt Q a' b' radial' mask' L' Mcap' eps' Z J' T C':=by
  intro s hQ hwidth p t X₁ X₂ hX₁ hX₂ hcap₁ hcap₂
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    t X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap)
  change s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+‖t‖)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+‖t‖)^J≤(1+‖t‖)^J':=pow_le_pow_right₀ (by linarith [norm_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

omit [Fintype α] [DecidableEq α] in
theorem positiveAt_transport (W:ℝ→ℂ)(bslot a b radial mask L Lslot lo hi Mcap eps κ Z:ℝ)
    (a' b' radial' mask' L' Mcap' eps':ℝ)
    (η₀:Character)(Q:Ideal O)(J J':ℕ)(S T:Finset (ℕ×ℕ))(C C':ℝ)
    (hZ:1≤Z)(ha:a≤a')(hb:b'≤b)(hr:radial'≤radial)(hm:mask'≤mask)
    (hL:L'≤L)(hM:Mcap'≤Mcap)(he:eps≤eps')(hJ:J≤J')(hS:S⊆T)
    (hC:0≤C)(hCC:C≤C')
    (h:PositiveAt (α:=α) M H hH W bslot a b radial mask L Lslot lo hi Mcap eps κ Z η₀ Q J S C):
    PositiveAt (α:=α) M H hH W bslot a' b' radial' mask' L' Lslot lo hi Mcap' eps' κ Z η₀ Q J' T C':=by
  intro A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq s hQ hwidth
    p X₁ X₂ hX₁ hX₂ hcap₁ hcap₂ hcapacity
  have hcap:Z^L'≤Z^L:=Real.rpow_le_rpow_of_exponent_le hZ hL
  have hh:=h A θ w σ freq t height hw hwL hσlo hσhi hheight hfreq
    (widenState s hm hr) hQ (hwidth.trans hM) (widenProfiles p ha hb)
    X₁ X₂ hX₁ hX₂ (hcap₁.trans hcap) (hcap₂.trans hcap) hcapacity
  change _≤C*diagonalControl s.radial.profile*(p.control S)^2*
    (1+|t|+height)^J*Z^(s.width+eps) at hh
  have hp:=profile_control_mono p hS
  have hp0:=p.control_nonneg S
  have hd:=diagonalControl_nonneg s.radial.profile
  have ht:(1+|t|+height)^J≤(1+|t|+height)^J':=
    pow_le_pow_right₀ (by linarith [abs_nonneg t]) hJ
  have hz:Z^(s.width+eps)≤Z^(s.width+eps'):=Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hCnew:0≤C':=hC.trans hCC
  apply hh.trans
  gcongr

end SevenEighths.CenteredMomentEnergyBandMonotonicity

end

end OAI
end OAIOriginalModule2717

/-! Original module: OAI.NumberTheory.DirichletL.Energy.InputParentCapacity
Source SHA256: 8bd3b0868304b7b35f1eb9779dd0ce9c899585b0e5ca62acaea6aca632c33b85
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2718



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyInputParentCapacity
open CenteredMomentEnergyBands CenteredMomentCommonRadialData
open CenteredMomentAmplificationChildInput
variable {ι:Type*} [Fintype ι]

lemma raw_log_le_length (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    Real.logb Z X≤length Z X :=
  Real.logb_le_logb_of_le hZ hX (le_max_right _ _)

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X) := by
  by_cases hx:1≤X
  · rw [length,max_eq_right hx,max_eq_right (Real.logb_nonneg hZ hx)]
  · have hh:X≤1:=le_of_not_ge hx
    have hl:Real.logb Z X≤0 := by
      simpa using Real.logb_le_logb_of_le hZ hX hh
    rw [length,max_eq_left hh,Real.logb_one,max_eq_left hl]

theorem postmask_length (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)=length Z X-min (Real.logb Z D) (length Z X) := by
  have hp:0<max 1 X:=lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hd:0<D:=zero_lt_one.trans_le hD
  rw [length_eq_max_log Z _ hZ (div_pos hp hd),Real.logb_div hp.ne' hd.ne']
  change max 0 (length Z X-Real.logb Z D)=_
  by_cases h:Real.logb Z D≤length Z X
  · rw [min_eq_left h,max_eq_right (sub_nonneg.mpr h)]
  · rw [min_eq_right (le_of_not_ge h),max_eq_left (sub_nonpos.mpr (le_of_not_ge h)),sub_self]

lemma postmask_length_le (Z X D:ℝ)(hZ:1<Z)(hD:1≤D):
    length Z (max 1 X/D)≤length Z X := by
  rw [postmask_length Z X D hZ hD]
  have hm:0≤min (Real.logb Z D) (length Z X):=
    le_min (Real.logb_nonneg hZ hD) (length_nonneg Z X hZ)
  linarith

theorem input_volume_log (s:Input ι)(Z:ℝ):
    Real.logb Z (volume s)=Real.logb Z s.X₁+Real.logb Z s.X₂+
      ∑i,Real.logb Z (s.P i) := by
  rw [volume,Real.logb_mul (mul_pos s.X₁_pos s.X₂_pos).ne'
    (Finset.prod_pos (fun i _=>s.P_pos i)).ne',
    Real.logb_mul s.X₁_pos.ne' s.X₂_pos.ne',
    Real.logb_prod _ _ (fun i _=>(s.P_pos i).ne')]

theorem input_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [input_volume_log]
  have h1:=raw_log_le_length Z s.X₁ hZ s.X₁_pos
  have h2:=raw_log_le_length Z s.X₂ hZ s.X₂_pos
  nlinarith

theorem input_reference_affine_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    Real.logb Z (s.Y₁*s.Y₂*∏i,s.P i)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  rw [s.same_product]
  exact input_affine_capacity s Z κ M hZ hcap

theorem original_slot_logs (s:Input ι)(Z:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hw:∀i,0≤w i)(hP:∀i,s.P i=Z^(w i)):
    (∀i,1≤s.P i) ∧ (∀i,Real.logb Z (s.P i)=w i) := by
  constructor
  · intro i;rw [hP i];exact Real.one_le_rpow hZ.le (hw i)
  · intro i;rw [hP i,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']

theorem original_exponent_capacity (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(w:ι→ℝ)
    (hP:∀i,s.P i=Z^(w i))
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,w i)≤M):
    Real.logb Z (volume s)+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M := by
  apply input_affine_capacity s Z κ M hZ
  simpa only [hP,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using hcap

theorem original_volume_cap (s:Input ι)(Z κ M:ℝ)(hZ:1<Z)(hk:1/6≤κ)
    (hP:∀i,1≤s.P i)
    (hcap:length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M):
    volume s≤Z^M := by
  have hh:=input_affine_capacity s Z κ M hZ hcap
  have hn:0≤∑i,Real.logb Z (s.P i):=
    Finset.sum_nonneg (fun i _=>Real.logb_nonneg hZ (hP i))
  have hp:0≤(6*κ-1)*(∑i,Real.logb Z (s.P i)):=mul_nonneg (by linarith) hn
  exact (Real.logb_le_iff_le_rpow hZ (volume_pos s)).mp (by linarith)

end SevenEighths.CenteredMomentEnergyInputParentCapacity

end

end OAI
end OAIOriginalModule2718

/-! Original module: OAI.NumberTheory.DirichletL.Energy.DeletedChildCapacity
Source SHA256: e0ccf1127943f9103cb1274069c7496d2eb401d0f612928e39adffa70adea7b3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2719




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyDeletedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentAllocatedChildCapacity
open CenteredMomentRetainedProfile CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentDivisorRaw CenteredMomentEnergyBands CenteredMomentEnergyInputParentCapacity
open CenteredMomentFirstSecondCapacityLedger CenteredMomentLiveCapacity
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Finset.prod_ne_zero_iff.mpr hF))

lemma prime_deletion_norm (F : Finset (Ideal O)) (hF : ∀I∈F,Prime I) :
    (1:ℝ) ≤ (∏I∈F,I).absNorm :=
  deletion_norm F (fun I hI=>(hF I hI).ne_zero)

def postmaskLength (Z U : ℝ) (F : Finset (Ideal O)) : ℝ :=
  length Z (clippedScale U/((∏I∈F,I).absNorm:ℝ))

lemma postmaskLength_eq (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F=Real.logb Z (clippedScale U)-
      min (Real.logb Z ((∏I∈F,I).absNorm:ℝ)) (Real.logb Z (clippedScale U)) :=
  postmask_length Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_le (Z U : ℝ) (F : Finset (Ideal O))
    (hZ : 1<Z) (hF : ∀I∈F,I≠0) :
    postmaskLength Z U F≤Real.logb Z (clippedScale U) :=
  postmask_length_le Z U _ hZ (deletion_norm F hF)

lemma postmaskLength_nonneg (Z U : ℝ) (F : Finset (Ideal O)) (hZ : 1<Z) :
    0≤postmaskLength Z U F := length_nonneg Z _ hZ

theorem child_survives (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0) :
    1≤rawScale D a X₁ 0*V₁.b ∧ 1≤rawScale D a X₂ 1*V₂.b := by
  unfold child at hne
  have hp:=left_ne_zero_of_mul hne
  exact ⟨profile_polynomial_survives χ V₁ _ (rawScale_pos D a X₁ h₁ 0) t _ 0 0
    (left_ne_zero_of_mul hp),
    profile_polynomial_survives χ V₂ _ (rawScale_pos D a X₂ h₂ 1) t _ 0 0
      (right_ne_zero_of_mul hp)⟩

def deletedExcess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι) : ℝ :=
  excess (liveIndices D a\J) (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) M κ

lemma deletedExcess_le (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0) :
    deletedExcess D a Z X₁ X₂ κ M P F₁ F₂ J≤
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := by
  have h₁:=postmaskLength_le Z (rawScale D a X₁ 0) F₁ hZ hF₁
  have h₂:=postmaskLength_le Z (rawScale D a X₂ 1) F₂ hZ hF₂
  have hsum:(∑i∈liveIndices D a\J,Real.logb Z (P i))≤remainingLogs D a Z P :=
    Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun i _ _=>Real.logb_nonneg hZ (hP i))
  have hh:=mul_le_mul_of_nonneg_left hsum (by positivity : 0≤6*κ)
  unfold deletedExcess excess plainLogs
  exact max_le_max (by linarith) le_rfl

theorem child_excess_from_parent (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 := by
  obtain ⟨hs₁,hs₂⟩:=child_survives χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J hne
  apply (deletedExcess_le D a Z X₁ X₂ κ Mactual P F₁ F₂ J hZ hκ hP hF₁ hF₂).trans
  apply (excess_le_remaining D a Z X₁ X₂ V₁.b V₂.b κ Mactual hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
  linarith

theorem child_paid_width (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (t Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    Mactual+deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6≤
      Mnom+δ₂+w+ell+δ₁/6+θ/3 := by
  have he:=child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne hparent hshift hclip
  have hh:=width_defect_cost (Mactual-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mactual-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mactual by ring] at hh
  linarith

lemma eventually_endpoint_cost (b₁ b₂ θ : ℝ) (hθ : 0<θ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1<Z ∧ Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ :=
  CenteredMomentCommonMaskChildCapacity.eventually_fixed_clipping_cost b₁ b₂ (2*θ) (by positivity)

theorem paired_child_excess (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ Y₁ Y₂ κ A M Mnom Mactual w ell δ θ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hY₁ : 0<Y₁) (hY₂ : 0<Y₂)
    (hsame : Y₁*Y₂=X₁*X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    (∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ F₁ F₂ J≠0 →
      deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) ∧
    (∀χ t,child χ D a V₁ V₂ pool β P t Y₁ Y₂ hY₁ hY₂ F₁ F₂ J≠0 →
      deletedExcess D a Z Y₁ Y₂ κ Mactual P F₁ F₂ J≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0) := by
  constructor
  · intro χ t hn
    exact child_excess_from_parent χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
      w ell δ θ hX₁ hX₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift hclip
  · intro χ t hn
    apply child_excess_from_parent χ D a V₁ V₂ pool β P t Z Y₁ Y₂ κ A M Mnom Mactual
      w ell δ θ hY₁ hY₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent _ hclip
    simpa only [hsame] using hshift

theorem source_removal_width_cost (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (Z X₁ X₂ κ A M Mnom Mactual w ell δ₁ δ₂ θ mesh : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hparent : A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth : Mactual-Mnom≤δ₂) (hw : 0≤w) (hell : 0≤ell)
    (hδ₁ : 0≤δ₁) (hδ₂ : 0≤δ₂) (hθ : 0≤θ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ)
    (hm : 0≤mesh) (hmesh : ∀i∈liveIndices D a\J,Real.logb Z (P i)≤mesh) :
    ∃removed : Finset ι,removed⊆liveIndices D a\J ∧
      (removed=liveIndices D a\J ∨
        postmaskLength Z (rawScale D a X₁ 0) F₁+
        postmaskLength Z (rawScale D a X₂ 1) F₂+
        6*κ*(∑i∈(liveIndices D a\J)\removed,Real.logb Z (P i))≤Mactual) ∧
      ∀χ t,child χ D a V₁ V₂ pool β P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0 →
        Mactual-Mnom+κ*(∑i∈removed,Real.logb Z (P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  by_cases hk : κ=0
  · refine ⟨liveIndices D a\J,Finset.Subset.refl _,Or.inl rfl,?_⟩
    intro χ t _
    simp only [hk,zero_mul,add_zero]
    linarith
  have hkpos : 0<κ := lt_of_le_of_ne hκ (Ne.symm hk)
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a\J)
    (fun i=>Real.logb Z (P i))
    (postmaskLength Z (rawScale D a X₁ 0) F₁)
    (postmaskLength Z (rawScale D a X₂ 1) F₂) Mactual κ mesh hkpos hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  intro χ t hn
  have hp:=child_paid_width χ D a V₁ V₂ pool β P t Z X₁ X₂ κ A M Mnom Mactual
    w ell δ₁ δ₂ θ h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hn hparent hshift
    hwidth hw hell hδ₁ hδ₂ hθ hclip
  change κ*(∑i∈removed,Real.logb Z (P i))≤
    deletedExcess D a Z X₁ X₂ κ Mactual P F₁ F₂ J/6+κ*mesh at hcost
  linarith

lemma postmask_scale_pos (U : ℝ) (F : Finset (Ideal O)) (hF : ∀I∈F,I≠0) :
    0<clippedScale U/((∏I∈F,I).absNorm:ℝ) :=
  div_pos (zero_lt_one.trans_le (clippedScale_ge_one U))
    (zero_lt_one.trans_le (deletion_norm F hF))

theorem input_parent_child_excess (s : CenteredMomentCommonRadialData.Input ι)
    (χ : Character) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (V₁ V₂ : Plain)
    (t Z X₁ X₂ κ M Mnom Mactual w ell δ θ : ℝ)
    (h₁ : 0<X₁) (h₂ : 0<X₂) (F₁ F₂ : Finset (Ideal O)) (J : Finset ι)
    (hZ : 1<Z) (hκ : 0≤κ) (hP : ∀i,1≤s.P i)
    (hF₁ : ∀I∈F₁,I≠0) (hF₂ : ∀I∈F₂,I≠0)
    (hne : child χ D a V₁ V₂ s.slots s.coefficient s.P t X₁ X₂ h₁ h₂ F₁ F₂ J≠0)
    (hparent : length Z s.X₁+length Z s.X₂+6*κ*(∑i,Real.logb Z (s.P i))≤M)
    (hshift : Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤
      Real.logb Z (CenteredMomentAmplificationChildInput.volume s)-M+6*(w+ell)+δ)
    (hclip : Real.logb Z (max 1 V₁.b*max 1 V₂.b)≤2*θ) :
    deletedExcess D a Z X₁ X₂ κ Mactual s.P F₁ F₂ J≤
      max (6*(w+ell)+δ+2*θ+Mnom-Mactual) 0 :=
  child_excess_from_parent χ D a V₁ V₂ s.slots s.coefficient s.P t Z X₁ X₂ κ
    (Real.logb Z (CenteredMomentAmplificationChildInput.volume s)) M Mnom Mactual w ell δ θ
    h₁ h₂ F₁ F₂ J hZ hκ hP hF₁ hF₂ hne
    (input_affine_capacity s Z κ M hZ hparent) hshift hclip

end SevenEighths.CenteredMomentEnergyDeletedChildCapacity

end

end OAI
end OAIOriginalModule2719

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionCapacity
Source SHA256: b0ac576cd361867835a09a6603e62ef3067811d8ca81553a2de1e7611c890ec2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2720




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionCapacity
open HeckeFamily CenteredMomentEnergyReferenceDeletionBudget
open CenteredMomentEnergyReferenceState CenteredMomentEnergyBands CenteredMomentLiveCapacity

local notation "O"=>HeckeFamily.O

lemma deleted_short_length (Z M:ℝ)(hZ:1<Z)(hM:0≤M)
    (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    length Z (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤M/4:=by
  have hn:=product_norm_ge_one D hD
  have hY:1≤comparisonFirst Z M:=Real.one_le_rpow hZ.le (by linarith)
  have hdiv:comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ)≤comparisonFirst Z M:=
    div_le_self (zero_le_one.trans hY) hn
  have hm:max 1 (comparisonFirst Z M/((∏I∈D,I).absNorm:ℝ))≤comparisonFirst Z M:=max_le hY hdiv
  have he:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) hm
  simpa only [length,comparisonFirst,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'] using he

theorem deleted_reflection_excess {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤w i)
    (Z M X₁ X₂ κ xi reflected:ℝ)(hZ:1<Z)(hM:0≤M)
    (hX₁:0<X₁)(hX₂:0<X₂)(hκ:3/4≤κ)(hxi:0≤xi)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    excess J w (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ≤
      xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=by
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hn₂p:0<((∏I∈D₂,I).absNorm:ℝ):=zero_lt_one.trans_le hn₂
  have hlog:0≤Real.logb Z ((∏I∈D₂,I).absNorm:ℝ):=Real.logb_nonneg hZ hn₂
  have hell:0≤∑i∈F,w i:=Finset.sum_nonneg hw
  have hY₂:0<comparisonSecond Z M X₁ X₂:=by
    unfold comparisonSecond
    exact div_pos (mul_pos hX₁ hX₂) (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  rw [Real.logb_div hY₂.ne' hn₂p.ne'] at href
  have hb:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂)+
      (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)):=by linarith
  have hh:=(balanced_reflection_margins Z M X₁ X₂ (∑i∈F,w i) κ
    (xi+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)) reflected hZ hM hX₁ hX₂ hell hκ hlarge hcap hb).2
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hsum:(∑i∈J,w i)≤∑i∈F,w i:=
    Finset.sum_le_sum_of_subset_of_nonneg hJF (fun i hi _=>hw i hi)
  have hks:=mul_le_mul_of_nonneg_left hsum (by linarith:0≤6*κ)
  unfold excess
  apply max_le _ (add_nonneg hxi hlog)
  nlinarith

theorem deleted_reflection_removal {α:Type*}[DecidableEq α]
    (F J:Finset α)(hJF:J⊆F)(w:α→ℝ)(hw:∀i∈F,0≤w i)
    (Z M X₁ X₂ κ xi reflected mesh:ℝ)(hZ:1<Z)(hM:0≤M)
    (hX₁:0<X₁)(hX₂:0<X₂)(hκ:3/4≤κ)(hxi:0≤xi)(hm:0≤mesh)(hwm:∀i∈J,w i≤mesh)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+∑i∈F,w i)
    (hcap:Real.logb Z (X₁*X₂)+∑i∈F,w i+(6*κ-1)*(∑i∈F,w i)≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤M-Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi):
    ∃removed:Finset α,removed⊆J ∧
      (removed=J ∨ length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+reflected+
        6*κ*(∑i∈J\removed,w i)≤M) ∧
      κ*(∑i∈removed,w i)≤xi/6+Real.logb Z ((∏I∈D₂,I).absNorm:ℝ)/6+κ*mesh:=by
  obtain ⟨removed,hr,hcapacity,hcost⟩:=removal_excess_cost J w
    (length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))) reflected M κ mesh
    (by linarith) hm (fun i hi=>hw i (hJF hi)) hwm
  refine ⟨removed,hr,hcapacity,?_⟩
  have he:=deleted_reflection_excess F J hJF w hw Z M X₁ X₂ κ xi reflected
    hZ hM hX₁ hX₂ hκ hxi hlarge hcap D₁ D₂ hD₁ hD₂ href
  linarith

lemma plain_kappa_eq (beta : ℝ) :
    (3/4:ℝ)+2*(beta-7/8)=2*beta-1 := by ring

lemma plain_kappa_lower (beta : ℝ) (hbeta : 7/8 < beta) :
    (3/4:ℝ) < (3/4:ℝ)+2*(beta-7/8) := by linarith

lemma paid_divisor_power (Z cost xi kappa mesh : ℝ) (hZ : 1 < Z)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (hcost : cost ≤ xi/6 + Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6 + kappa*mesh) :
    Z^cost ≤ Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
  have hZp : 0 < Z := zero_lt_one.trans hZ
  have hn : 0 < ((∏ I ∈ D, I).absNorm:ℝ) :=
    zero_lt_one.trans_le (product_norm_ge_one D hD)
  calc
    Z^cost ≤ Z^((xi/6+kappa*mesh)+Real.logb Z ((∏ I ∈ D, I).absNorm:ℝ)/6) :=
      Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    _ = Z^(xi/6+kappa*mesh) * ((∏ I ∈ D, I).absNorm:ℝ)^(1/6:ℝ) := by
      rw [Real.rpow_add hZp]
      congr 1
      rw [div_eq_mul_inv, Real.rpow_mul hZp.le,
        Real.rpow_logb hZp hZ.ne' hn]
      norm_num

end SevenEighths.CenteredMomentEnergyReferenceDeletionCapacity

end

end OAI
end OAIOriginalModule2720

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionClipped
Source SHA256: 944057f947e92e20aaf28efddc62751e66386b88f76f3871293a462c6c9a2cd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2721


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionClipped
open HeckeFamily CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget

local notation "O" => HeckeFamily.O

lemma deleted_long_le_width (Z M X₁ X₂ ell kappa : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 3/4 ≤ kappa)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I) :
    Real.logb Z (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) ≤ M := by
  have hg := balanced_reference_geometry Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap
  have hn := product_norm_ge_one D hD
  have hp : 0 < ((∏ I ∈ D, I).absNorm:ℝ) := zero_lt_one.trans_le hn
  have hy := (comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂).2
  rw [Real.logb_div hy.ne' hp.ne']
  have hlog := Real.logb_nonneg hZ hn
  linarith [hg.2.2.2.2]

lemma clipped_reflected_bound (Z M X₁ X₂ ell kappa xi reflected : ℝ)
    (hZ : 1 < Z) (hM : 0 ≤ M) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hell : 0 ≤ ell) (hkappa : 3/4 ≤ kappa) (hxi : 0 ≤ xi)
    (hlarge : 5*M/6 ≤ Real.logb Z (X₁*X₂)+ell)
    (hcap : Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell ≤ M)
    (D : Finset (Ideal O)) (hD : ∀ I ∈ D, Prime I)
    (href : reflected ≤ max 0 (M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi)) :
    reflected ≤ M - Real.logb Z
      (comparisonSecond Z M X₁ X₂ / ((∏ I ∈ D, I).absNorm:ℝ)) + xi := by
  have hlong := deleted_long_le_width Z M X₁ X₂ ell kappa
    hZ hM hX₁ hX₂ hell hkappa hlarge hcap D hD
  rwa [max_eq_right (by linarith)] at href

end SevenEighths.CenteredMomentEnergyReferenceDeletionClipped

end

end OAI
end OAIOriginalModule2721

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowBranchGeometry
Source SHA256: 7e7e98943b00fb8afa21de7ca753750182152f6cbf680db71fdd9278c401a3f7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2722


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceDeletionBudget CenteredMomentEnergyReferenceDeletionCapacity
local notation "O"=>HeckeFamily.O

lemma length_eq_max_log (Z X:ℝ)(hZ:1<Z)(hX:0<X):
    length Z X=max 0 (Real.logb Z X):=by
  by_cases h:1≤X
  · rw [length,max_eq_right h,max_eq_right (Real.logb_nonneg hZ h)]
  · have hx:X≤1:=le_of_not_ge h
    have hl:Real.logb Z X≤0:=by
      simpa using Real.logb_le_logb_of_le hZ hX hx
    rw [length,max_eq_left hx,Real.logb_one,max_eq_left hl]

lemma slot_budgets (M total ell kappa:ℝ)(_hM:0≤M)(hell:0≤ell)(hk:3/4≤kappa)
    (hlarge:5*M/6≤total+ell)(hcap:total+ell+(6*kappa-1)*ell≤M):
    ell≤M/21 ∧ (6*kappa-1)*ell≤M/6:=by
  have hkell:7/2*ell≤(6*kappa-1)*ell:=mul_le_mul_of_nonneg_right (by linarith) hell
  constructor <;> nlinarith

theorem reflected_low (M short along ell z kappa xi reflected:ℝ)
    (hM:0≤M)(_hs:0≤short)(hsM:short≤M/4)(_hell:0≤ell)(_hz:0≤z)(hze:z≤ell)
    (hk:3/4≤kappa)(he:ell≤M/21)(hbudget:(6*kappa-1)*ell≤M/6)(hxi:0≤xi)
    (hhigh:5*M/6<short+max 0 along+z)
    (href:reflected≤max 0 (M-along+xi)):
    0<along ∧ reflected+short+z≤16*M/21+xi ∧
      reflected+short+6*kappa*z≤13*M/14+xi:=by
  have haz:0<along:=by
    by_contra hn
    have ha:along≤0:=le_of_not_gt hn
    rw [max_eq_left ha] at hhigh
    linarith
  rw [max_eq_right haz.le] at hhigh
  have hzbudget:(6*kappa-1)*z≤M/6:=
    (mul_le_mul_of_nonneg_left hze (by linarith)).trans hbudget
  have hzcap:z≤M/21:=hze.trans he
  refine ⟨haz,?_⟩
  by_cases hr:0≤M-along+xi
  · rw [max_eq_right hr] at href
    constructor <;> nlinarith
  · rw [max_eq_left (le_of_not_ge hr)] at href
    constructor <;> nlinarith

theorem deleted_reference_cases (Z M X₁ X₂ ell z kappa xi reflected:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hk:3/4≤kappa)(hxi:0≤xi)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I)
    (href:reflected≤max 0 (M-Real.logb Z
      (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+xi)):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let long:=length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+long+z≤5*M/6 ∧ short+long+6*kappa*z≤M) ∨
    (0<Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ)) ∧
      reflected+short+z≤16*M/21+xi ∧ reflected+short+6*kappa*z≤13*M/14+xi):=by
  dsimp only
  have hg:=balanced_reference_geometry Z M X₁ X₂ ell kappa hZ hM hX₁ hX₂ hell hk hlarge hcap
  have hpos:=comparison_positive Z M X₁ X₂ (zero_lt_one.trans hZ) hX₁ hX₂
  have hn₂:=product_norm_ge_one D₂ hD₂
  have hlongpos:=div_pos hpos.2 (zero_lt_one.trans_le hn₂)
  have hshort:=deleted_short_length Z M hZ hM D₁ hD₁
  have hshort0:=length_nonneg Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ)) hZ
  have hlong:length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))≤
      Real.logb Z (comparisonSecond Z M X₁ X₂):=by
    have hY:1≤comparisonSecond Z M X₁ X₂:=hg.2.1.trans hg.2.2.1
    have hdiv:=div_le_self hpos.2.le hn₂
    exact Real.logb_le_logb_of_le hZ (lt_of_lt_of_le zero_lt_one (le_max_left 1 _)) (max_le hY hdiv)
  by_cases hlo:length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ))+
      length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6
  · refine Or.inl ⟨hlo,?_⟩
    have hzcap:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*kappa)
    rw [hg.2.2.2.1] at hlong
    nlinarith
  · apply Or.inr
    obtain ⟨he,hbudget⟩:=slot_budgets M (Real.logb Z (X₁*X₂)) ell kappa hM hell hk hlarge hcap
    apply reflected_low M _ _ ell z kappa xi reflected hM hshort0 hshort hell hz hze hk he hbudget hxi _ href
    rw [←length_eq_max_log Z _ hZ hlongpos]
    exact lt_of_not_ge hlo

lemma reflected_low_admissible (M xi short reflected z kappa:ℝ)
    (hxi:xi≤M/14)(ht:reflected+short+z≤16*M/21+xi)
    (hc:reflected+short+6*kappa*z≤13*M/14+xi):
    reflected+short+z≤5*M/6 ∧ reflected+short+6*kappa*z≤M:=by
  constructor <;> linarith

end SevenEighths.CenteredMomentEnergyReferenceLowBranchGeometry

end

end OAI
end OAIOriginalModule2722

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowWindow
Source SHA256: a56c2be64bdae04dd6483e846bb8cf1ed0dea028b8a6424b8c4ec4a7ccdb7dba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2723


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowWindow
open HeckeFamily CenteredMomentEnergyBands CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=>HeckeFamily.O

lemma reflection_window_length (Z R x:ℝ)(hZ:1<Z)(hR:0≤R)
    (hx:x∈Set.Icc 0 (R*Real.log Z)):
    length Z (Real.exp x)≤R ∧ Real.exp x≤Z^R:=by
  have hlog:0<Real.log Z:=Real.log_pos hZ
  have hexp:Real.exp x≤Z^R:=by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
    apply Real.exp_le_exp.mpr
    simpa [mul_comm] using hx.2
  refine ⟨?_,hexp⟩
  have hmax:max 1 (Real.exp x)≤Z^R:=
    max_le (Real.one_le_rpow hZ.le hR) hexp
  have hl:=Real.logb_le_logb_of_le hZ
    (lt_of_lt_of_le zero_lt_one (le_max_left 1 (Real.exp x))) hmax
  simpa only [length,Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] using hl

theorem deleted_reference_window (Z M X₁ X₂ ell z kappa xi:ℝ)
    (hZ:1<Z)(hM:0≤M)(hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hk:3/4≤kappa)(hxi:0≤xi)(hxiM:xi≤M/14)
    (hlarge:5*M/6≤Real.logb Z (X₁*X₂)+ell)
    (hcap:Real.logb Z (X₁*X₂)+ell+(6*kappa-1)*ell≤M)
    (D₁ D₂:Finset (Ideal O))(hD₁:∀I∈D₁,Prime I)(hD₂:∀I∈D₂,Prime I):
    let short:=length Z (comparisonFirst Z M/((∏I∈D₁,I).absNorm:ℝ));
    let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ));
    (short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+z≤5*M/6 ∧
      short+length Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))+6*kappa*z≤M) ∨
    (0<along ∧ ∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
      length Z (Real.exp x)+short+z≤5*M/6 ∧
      length Z (Real.exp x)+short+6*kappa*z≤M):=by
  dsimp only
  let along:=Real.logb Z (comparisonSecond Z M X₁ X₂/((∏I∈D₂,I).absNorm:ℝ))
  rcases deleted_reference_cases Z M X₁ X₂ ell z kappa xi (max 0 (M-along+xi))
    hZ hM hX₁ hX₂ hell hz hze hk hxi hlarge hcap D₁ D₂ hD₁ hD₂ le_rfl with h|h
  · exact Or.inl h
  · refine Or.inr ⟨h.1,?_⟩
    intro x hx
    have hh:=reflection_window_length Z (max 0 (M-along+xi)) x hZ (le_max_left _ _) hx
    have hb:=reflected_low_admissible M xi _ (max 0 (M-along+xi)) z kappa hxiM h.2.1 h.2.2
    constructor <;> linarith [hh.1]

end SevenEighths.CenteredMomentEnergyReferenceLowWindow

end

end OAI
end OAIOriginalModule2723

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowDeletedGeometry
Source SHA256: 69eff4f2586186cf2f1580a4fccae2baf6de971c2a6f6d9c1bf1d618b2d3f142
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2724



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowWindow
local notation "O"=>HeckeFamily.O

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(hxiM:xi≤s.width/14)
    (hlarge:5*s.width/6≤Real.logb Z (X₁*X₂)+ell)
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
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)):=by
  dsimp only
  have hg:=balanced_reference_geometry Z s.width X₁ X₂ ell κ hZ s.width_nonneg
    hX₁ hX₂ hell hκ hlarge hcap
  have hd:=balanced_divisor_range s hZ Mcap X₁ X₂ ell κ hwidth
    hX₁ hX₂ hell hκ hlarge hcap D₁ D₂ hD₁ hD₂
  dsimp only at hd
  have hn₁:=divisor_norm s D₁ hD₁
  have hn₂:=divisor_norm s D₂ hD₂
  have hl₁:=Real.logb_nonneg hZ hn₁.1
  have hl₂:=Real.logb_nonneg hZ hn₂.1
  have hMcap:0≤Mcap:=s.width_nonneg.trans hwidth
  have hLc:0≤L:=by linarith
  refine ⟨hd.2.2.2.1,hd.2.2.2.2,by linarith,by linarith [s.width_nonneg],?_,
    hd.2.2.1,?_,?_⟩
  · linarith [hg.2.2.2.2]
  · exact max_le hLc (by linarith [hd.2.1])
  · have hp₁:∀I∈D₁,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₁ hi)
    have hp₂:∀I∈D₂,Prime I:=fun I hi=>
      CenteredMomentNaturalRowSource.support_prime s.puncture I
        (Finset.mem_powerset.mp hD₂ hi)
    let along:=Real.logb Z (X₁*X₂)-s.width/4-Real.logb Z ((∏P∈D₂,P).absNorm:ℝ)
    have halong:Real.logb Z (comparisonSecond Z s.width X₁ X₂/((∏P∈D₂,P).absNorm:ℝ))=along:=by
      rw [←hd.2.2.2.2]
      exact Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne'
    rcases CenteredMomentEnergyReferenceLowBranchGeometry.deleted_reference_cases
      Z s.width X₁ X₂ ell z κ xi (max 0 (s.width-along+xi)) hZ s.width_nonneg
      hX₁ hX₂ hell hz hze hκ hxi hlarge hcap D₁ D₂ hp₁ hp₂
      (by rw [halong]) with hc|hc
    · apply Or.inl
      simpa only [hd.2.2.2.1,hd.2.2.2.2] using hc
    · apply Or.inr
      have hh:=CenteredMomentEnergyReferenceLowBranchGeometry.reflected_low_admissible
        s.width xi _ (max 0 (s.width-along+xi)) z κ hxiM hc.2.1 hc.2.2
      simpa only [hd.2.2.2.1] using hh

end SevenEighths.CenteredMomentEnergyReferenceLowDeletedGeometry

end

end OAI
end OAIOriginalModule2724

/-! Original module: OAI.NumberTheory.DirichletL.Energy.OriginalHighReflectionGeometry
Source SHA256: 79dc83d60f7356ffe6ec7a8f948279cb865d504f3bc81062fb4fcb0e0e0ea9b8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2725


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentEnergyOriginalHighReflectionGeometry
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentEnergyReferenceState CenteredMomentEnergyReferenceDivisors
open CenteredMomentEnergyReferenceLowBranchGeometry
local notation "O"=>HeckeFamily.O

lemma original_long_positive (Z M X₁ X₂ ell κ:ℝ)(hZ:1<Z)(hM:0<M)
    (_hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hκ:3/4≤κ)
    (hshort:length Z X₁≤M/4)
    (hlarge:5*M/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤M):
    0<Real.logb Z X₂ ∧ length Z X₂=Real.logb Z X₂ ∧ 1≤X₂:=by
  have hbudget:=slot_budgets M (length Z X₁+length Z X₂) ell κ hM.le hell hκ hlarge (by linarith)
  have hpos:0<length Z X₂:=by linarith [hbudget.1]
  have he:=length_eq_max_log Z X₂ hZ hX₂
  have hl:0<Real.logb Z X₂:=by
    by_contra hn
    rw [he,max_eq_left (le_of_not_gt hn)] at hpos
    exact (lt_irrefl 0) hpos
  refine ⟨hl,he.trans (max_eq_right hl.le),?_⟩
  by_contra hn
  have hh:=Real.logb_le_logb_of_le hZ hX₂ (le_of_not_ge hn)
  rw [Real.logb_one] at hh
  linarith

lemma deleted_length_le (Z X N:ℝ)(hZ:1<Z)(hX:0<X)(hN:1≤N):
    length Z (X/N)≤length Z X:=by
  exact Real.logb_le_logb_of_le hZ (zero_lt_one.trans_le (le_max_left 1 _))
    (max_le_max_left 1 (div_le_self hX.le hN))

theorem actual_deleted_gates {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)
    (hZ:1<Z)(hM:0<s.width)(hB:0≤Bmask)(Mcap L X₁ X₂ ell z κ xi:ℝ)
    (hwidth:s.width≤Mcap)(hL:Mcap+Bmask+xi≤L)
    (hX₁:0<X₁)(hX₂:0<X₂)(hell:0≤ell)(hz:0≤z)(hze:z≤ell)
    (hκ:3/4≤κ)(hxi:0≤xi)(hxiM:xi≤s.width/14)
    (hshort:length Z X₁≤s.width/4)
    (hlarge:5*s.width/6≤length Z X₁+length Z X₂+ell)
    (hcap:length Z X₁+length Z X₂+6*κ*ell≤s.width)
    (D₁ D₂:Finset (Ideal O))
    (hD₁:D₁∈(CompletedGauss.primeSupport s.puncture).powerset)
    (hD₂:D₂∈(CompletedGauss.primeSupport s.puncture).powerset):
    let short:=Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ));
    let along:=Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ));
    Z^short=X₁/((∏P∈D₁,P).absNorm:ℝ) ∧
    Z^along=X₂/((∏P∈D₂,P).absNorm:ℝ) ∧
    short≤s.width/4 ∧ short≤L ∧ along≤L ∧
    s.width≤(Mcap+Bmask)+along ∧ max 0 (s.width-along+xi)≤L ∧
    ((length Z (Z^short)+length Z (Z^along)+z≤5*s.width/6 ∧
        length Z (Z^short)+length Z (Z^along)+6*κ*z≤s.width) ∨
      (max 0 (s.width-along+xi)+length Z (Z^short)+z≤5*s.width/6 ∧
        max 0 (s.width-along+xi)+length Z (Z^short)+6*κ*z≤s.width)):=by
  dsimp only
  have hZ0:=zero_lt_one.trans hZ
  obtain ⟨hn₁,hc₁⟩:=divisor_norm s D₁ hD₁
  obtain ⟨hn₂,hc₂⟩:=divisor_norm s D₂ hD₂
  have hp₁:=div_pos hX₁ (zero_lt_one.trans_le hn₁)
  have hp₂:=div_pos hX₂ (zero_lt_one.trans_le hn₂)
  have he₁:=Real.rpow_logb hZ0 hZ.ne' hp₁
  have he₂:=Real.rpow_logb hZ0 hZ.ne' hp₂
  have hd₁:=deleted_length_le Z X₁ _ hZ hX₁ hn₁
  have hd₂:=deleted_length_le Z X₂ _ hZ hX₂ hn₂
  have hraw₁:Real.logb Z (X₁/((∏P∈D₁,P).absNorm:ℝ))≤
      length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₁];exact le_max_right _ _
  have hraw₂:Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))≤
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ)):=by
    rw [length_eq_max_log Z _ hZ hp₂];exact le_max_right _ _
  have hlen₁:=length_nonneg Z X₁ hZ
  have hlen₂:=length_nonneg Z X₂ hZ
  have hslot:0≤6*κ*ell:=mul_nonneg (by linarith) hell
  have hl:=original_long_positive Z s.width X₁ X₂ ell κ hZ hM hX₁ hX₂ hell hκ hshort hlarge hcap
  have hrange:=divisor_reflection_range s hZ Mcap X₂ hwidth hl.2.2 D₂ hD₂
  dsimp only at hrange
  have hlogdiv:=Real.logb_div (b:=Z) hX₂.ne' (zero_lt_one.trans_le hn₂).ne'
  rw [←hlogdiv] at hrange
  have hL0:0≤L:=by linarith
  refine ⟨he₁,he₂,by linarith,by linarith,by linarith,hrange.2.1,
    max_le hL0 (by linarith [hrange.1]),?_⟩
  rw [he₁,he₂]
  by_cases hd:length Z (X₁/((∏P∈D₁,P).absNorm:ℝ))+
      length Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+z≤5*s.width/6
  · refine Or.inl ⟨hd,?_⟩
    have hkz:=mul_le_mul_of_nonneg_left hze (by linarith:0≤6*κ)
    linarith
  · obtain ⟨he,hbudget⟩:=slot_budgets s.width (length Z X₁+length Z X₂) ell κ
      hM.le hell hκ hlarge (by linarith)
    have hlow:=reflected_low s.width (length Z (X₁/((∏P∈D₁,P).absNorm:ℝ)))
      (Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))) ell z κ xi
      (max 0 (s.width-Real.logb Z (X₂/((∏P∈D₂,P).absNorm:ℝ))+xi))
      hM.le (length_nonneg Z _ hZ)
      (hd₁.trans hshort) hell hz hze hκ he hbudget hxi
      (by rw [←length_eq_max_log Z _ hZ hp₂];exact lt_of_not_ge hd) le_rfl
    exact Or.inr (reflected_low_admissible s.width xi _ _ z κ hxiM hlow.2.1 hlow.2.2)

end SevenEighths.CenteredMomentEnergyOriginalHighReflectionGeometry

end

end OAI
end OAIOriginalModule2725

/-! Original module: OAI.NumberTheory.DirichletL.Energy.SlotHeight
Source SHA256: af0d8c1a08386df802a579abcae97d055358cc24a4306446a80cdb278c9b97f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2726



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentEnergySlotHeight
open HeckeFamily CenteredMomentInductionEnergy CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentCommonMaskEnergy
open HeckePrimeAnnular CenteredMomentPrimeSlotShift
local notation "O"=>HeckeFamily.O

variable {α:Type*}[Fintype α]

lemma height_coefficient (ν:Ideal O→ℂ)(W:ℝ→ℂ)(P σ freq t:ℝ)(hP:0<P)
    (I:Ideal O)(hI:I≠0):
    heightCoefficient (fun J=>ν J*annularWeight W P σ freq J) t I=
      (P:ℂ)^(Complex.I*t)*(ν I*annularWeight W P σ (t+freq) I):=by
  have hN:0<(I.absNorm:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hh:=norm_height_split (I.absNorm:ℝ) P σ t freq hN hP
  unfold heightCoefficient annularWeight
  calc
    _=(ν I*W ((I.absNorm:ℝ)/P))*
      (((((I.absNorm:ℝ)/P:ℝ):ℂ)^(-HeckeDyadic.shift σ freq))*(I.absNorm:ℂ)^(Complex.I*t)):=by ring
    _=_:=by rw [show (I.absNorm:ℂ)=((I.absNorm:ℝ):ℂ) by simp,hh];ring

lemma row_slot_phase (η:Character)(m A z:O)(pool:Finset (Ideal O))
    (β γ:Ideal O→ℂ)(phase:ℂ)(t:ℝ)(he:∀I∈pool,β I=phase*γ I):
    rowSlot η m A z pool β t=phase*rowSlot η m A z pool γ t:=by
  unfold rowSlot
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [he I hI]
  ring

lemma positive_row_phase (η:Character)(m A z:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(he:∀i I,I∈pool i→β i I=phase i*γ i I):
    positiveSlotRow η m A z W₁ W₂ pool β P t X₁ X₂=
      (∏i,phase i)*positiveSlotRow η m A z W₁ W₂ pool γ P t X₁ X₂:=by
  have hs (i:α):rowSlot η m A z (pool i) (β i) t=
      phase i*rowSlot η m A z (pool i) (γ i) t:=
    row_slot_phase η m A z (pool i) (β i) (γ i) (phase i) t (he i)
  unfold positiveSlotRow
  simp_rw [hs]
  rw [Finset.prod_mul_distrib]
  ring

theorem energy_phase (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(β γ:α→Ideal O→ℂ)(phase:α→ℂ)(P:α→ℝ)
    (t X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (he:∀i I,I∈pool i→β i I=phase i*γ i I)(hp:∀i,‖phase i‖=1):
    energy η m A t W₁ W₂ pool β P X₁ X₂ keep Φ K=
      energy η m A t W₁ W₂ pool γ P X₁ X₂ keep Φ K:=by
  have hprod:‖∏i,phase i‖=1:=by rw [norm_prod];simp only [hp,Finset.prod_const_one]
  unfold energy
  apply tsum_congr
  intro z
  rw [positive_row_phase η m A z W₁ W₂ pool β γ phase P t X₁ X₂ he]
  simp only [norm_mul,hprod,one_mul]

theorem inherited_height_energy (η:Character)(m A:O)(W₁ W₂:ℝ→ℂ)
    (pool:α→Finset (Ideal O))(ν:α→Ideal O→ℂ)(W:α→ℝ→ℂ)
    (P σ freq:α→ℝ)(hP:∀i,0<P i)(hpool:∀i I,I∈pool i→I≠0)
    (t rowt X₁ X₂:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K:ℝ):
    energy η m A rowt W₁ W₂ pool
      (fun i=>heightCoefficient (fun I=>ν i I*annularWeight (W i) (P i) (σ i) (freq i) I) t)
      P X₁ X₂ keep Φ K=
    energy η m A rowt W₁ W₂ pool
      (fun i I=>ν i I*annularWeight (W i) (P i) (σ i) (t+freq i) I)
      P X₁ X₂ keep Φ K:=by
  apply energy_phase η m A W₁ W₂ pool _ _ (fun i=>(P i:ℂ)^(Complex.I*t)) P rowt X₁ X₂ keep Φ K
  · intro i I hi
    exact height_coefficient (ν i) (W i) (P i) (σ i) (freq i) t (hP i) I (hpool i I hi)
  · intro i
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos (hP i) (Complex.I*t)

end SevenEighths.CenteredMomentEnergySlotHeight

end

end OAI
end OAIOriginalModule2726

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceChild
Source SHA256: 9bbd31ddbe4be37e5d321b8e67a9626bdbd699f3d6101136724aea71ad4aeb39
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2727





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChild
open HeckeFamily HeckeDyadic ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentAllocatedNaturalRadial CenteredMomentNaturalRowSource
open CenteredMomentEnergyAllocatedChildren CenteredMomentEnergySlotHeight
open CenteredMomentOriginalRadialComparison CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentEnergyProfiles CenteredMomentFiniteProfileExceptional
open CenteredMomentSecondHeightFamily CenteredMomentLattice CenteredMomentRetainedProfile CenteredMomentTwist
local notation "O"=>HeckeFamily.O

def unpuncturedState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):NaturalState Z 0 bΦ where
  character:=s.character
  fixedModulus:=s.fixedModulus
  puncture:=1
  radial:=(effectiveState s).radial
  rowWidth:=s.rowWidth
  characterWidth:=s.characterWidth
  base_ge_one:=s.base_ge_one
  row_nonneg:=s.row_nonneg
  character_nonneg:=s.character_nonneg
  scale_eq:=s.scale_eq
  modulus_bound:=s.modulus_bound
  puncture_ne_zero:=one_ne_zero
  puncture_bound:=by simp
  radial_support:=s.radial_support
  row_ne_zero:=fun z hz=>s.row_ne_zero z hz.1
  nonexceptional:=by
    intro z hz hh
    have hn:=s.row_ne_zero z hz.1
    have hunit:CenteredExceptionalProfile.FixedInducingRow s.character s.fixedModulus fixedBadMask 1 z:=
      (CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator 1) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero 1 one_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mp hh
    exact s.nonexceptional z hz.1
      ((CenteredMomentFixedRowMask.fixedInducingRow_mul_mask_iff s.character s.fixedModulus
        fixedBadMask (idealGenerator s.puncture) 1 z fixedBadMask_ne_zero
        (idealGenerator_ne_zero _ s.puncture_ne_zero) one_ne_zero hn
        (dvd_mul_right _ _) (dvd_mul_left _ _)).mpr hunit)

lemma unpunctured_width {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ):
    (unpuncturedState s).width=s.width:=rfl

def independentProfiles {a b:ℝ}(ha:0<a)(W₁ W₂:𝓢(ℝ,ℂ))
    (hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)(t₁ t₂:ℝ):Profiles a b where
  profile:=fun i=>if i=0 then normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁
    else normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂
  support:=by
    intro i
    split_ifs
    · exact (normPowerProfile_support W₁ a b ha hs₁ (W₁.smooth ⊤) t₁).trans hs₁
    · exact (normPowerProfile_support W₂ a b ha hs₂ (W₂.smooth ⊤) t₂).trans hs₂

theorem independent_child_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ)
    (t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hP:∀i∈F,0<P i):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i) (β i) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=>pool i) (fun i:F=>β i) (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=natural_subset_radial_eq_energy s.character (effectiveState s).radial
    (fun z hz=>s.row_ne_zero z hz.1) F
    (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)
    (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)
    pool β P X₁ X₂ hX₁ hX₂ hP
  simp only [CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₁ a b ha hs₁ t₁,
    CenteredMomentNaturalMaskedFloor.twist_polynomial _ W₂ a b ha hs₂ t₂] at hh
  simpa only [independentProfiles,unpuncturedState,NaturalState.mask,
    show (1:Fin 2)≠0 by decide,ite_false,ite_true,effectiveState,effectiveRadial] using hh

theorem independent_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)
    (W₁ W₂:𝓢(ℝ,ℂ))(hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b)
    (hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(W:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0<P i)
    (t t₁ t₂ X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false W₁ X₁ 0 t₁ *
      polynomial (naturalCharacter s.character z) false W₂ X₂ 0 t₂ *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 0)
      ((independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).profile 1)
      (fun i:F=>pool i)
      (fun (i:F) I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (W i) (P i) (σ i) (t+freq i) I)
      (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  rw [independent_child_energy s ha W₁ W₂ hs₁ hs₂ F pool _ P t₁ t₂ X₁ X₂ hX₁ hX₂ hP]
  exact inherited_height_energy _ _ _ _ _ (fun i:F=>pool i)
    (fun (i:F) I=>idealCoeff (ν i) I) (fun i:F=>W i)
    (fun i:F=>P i) (fun i:F=>σ i) (fun i:F=>freq i)
    (fun i=>hP i i.property) (fun i I hI=>(hp i i.property I hI).ne_zero)
    t 0 X₁ X₂ _ _ _

end SevenEighths.CenteredMomentEnergyReferenceChild

end

end OAI
end OAIOriginalModule2727

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceChildProfiles
Source SHA256: e0cdd2758960d5f81f2573a465112742789bdbdd49efeea2eb4c1955de30c979
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2728


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceChildProfiles
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentEnergyState CenteredMomentEnergyReferenceState
open CenteredMomentEnergyReferenceChild CenteredMomentEnergyProfiles
open CenteredMomentAllocatedNaturalRadial CenteredMomentCommonMaskExpansion
open CenteredMomentCommonMaskEnergy CenteredMomentInductionEnergy
open CenteredMomentOriginalRadialComparison CenteredMomentFiniteProfileExceptional
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentLattice CenteredMomentRetainedProfile
local notation "O"=>HeckeFamily.O

def reflectionProfiles {a b:ℝ}(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v t:ℝ):Profiles a b:=
  independentProfiles ha (derivativeChoice (annulusSeed a b hlo hhi).profile j)
    (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t

theorem reflected_child_ray_energy {α:Type*}[Fintype α][DecidableEq α]
    {Z Bmask bΦ a b:ℝ}(s:NaturalState Z Bmask bΦ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (W:𝓢(ℝ,ℂ))(hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)
    (F:Finset α)(pool:α→Finset (Ideal O))(ν:α→Character)(Wslot:α→ℝ→ℂ)(P σ freq:α→ℝ)
    (hp:∀i∈F,∀I∈pool i,Prime I)(hP:∀i∈F,0<P i)
    (j k:Fin 2)(v t X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v) *
      polynomial (naturalCharacter s.character z) false (scaleTest W k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z) (pool i)
        (heightCoefficient (fun I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (freq i) I) t) (P i))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale=
    energy (unpuncturedState s).character (unpuncturedState s).mask 1 0
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 0)
      ((reflectionProfiles ha hlo hhi W hs j k v t).profile 1)
      (fun i:F=>pool i)
      (fun (i:F) I=>idealCoeff (ν i) I*HeckePrimeAnnular.annularWeight (Wslot i) (P i) (σ i) (t+freq i) I)
      (fun i:F=>P i) X₁ X₂
      (unpuncturedState s).radial.keep (unpuncturedState s).radial.profile (unpuncturedState s).radial.scale:=by
  have hh:=independent_child_ray_energy s ha
    (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) F pool ν Wslot P σ freq hp hP
    t (-2*Real.pi*v) t X₁ X₂ hX₁ hX₂
  have he:((annulusSeed a b hlo hhi).profile:ℝ→ℂ)=(fun y:ℝ=>(annulus y:ℂ)):=
    funext annulusTemplate_apply
  simpa only [derivativeChoice_apply,he,reflectionProfiles] using hh

theorem independent_profile_control (a b:ℝ)(ha:0<a)(S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀(W₁ W₂:𝓢(ℝ,ℂ)),∀hs₁:Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b,
      ∀hs₂:Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b,∀t₁ t₂:ℝ,
      (independentProfiles ha W₁ W₂ hs₁ hs₂ t₁ t₂).control S≤
        C*(sourceControl T W₁*sourceControl T W₂)*(1+‖t₁‖+‖t₂‖)^(2*n):=by
  obtain ⟨n,T,C,hC,hc⟩:=normPowerProfile_source_control a b ha S
  refine ⟨n,T,C^2,sq_pos_of_pos hC,?_⟩
  intro W₁ W₂ hs₁ hs₂ t₁ t₂
  have h₁:=hc W₁ hs₁ t₁
  have h₂:=hc W₂ hs₂ t₂
  have hp₁:(1+‖t₁‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₂]) n
  have hp₂:(1+‖t₂‖)^n≤(1+‖t₁‖+‖t₂‖)^n:=pow_le_pow_left₀ (by positivity) (by linarith [norm_nonneg t₁]) n
  have h₁':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₁ a b ha hs₁ (W₁.smooth ⊤) t₁)≤C*sourceControl T W₁*(1+‖t₁‖+‖t₂‖)^n:=
    h₁.trans (mul_le_mul_of_nonneg_left hp₁ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  have h₂':S.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (normPowerProfile W₂ a b ha hs₂ (W₂.smooth ⊤) t₂)≤C*sourceControl T W₂*(1+‖t₁‖+‖t₂‖)^n:=
    h₂.trans (mul_le_mul_of_nonneg_left hp₂ (mul_nonneg hC.le (sourceControl_nonneg _ _)))
  simp only [Profiles.control,independentProfiles,show (1:Fin 2)≠0 by decide,ite_true,ite_false]
  apply (mul_le_mul h₁' h₂' (apply_nonneg _ _)
    (mul_nonneg (mul_nonneg hC.le (sourceControl_nonneg _ _)) (by positivity))).trans_eq
  rw [show (1+‖t₁‖+‖t₂‖)^(2*n)=((1+‖t₁‖+‖t₂‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

lemma derivative_choice_control (S:Finset (ℕ×ℕ)):
    ∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧ ∀W:𝓢(ℝ,ℂ),∀j:Fin 2,
      sourceControl S (derivativeChoice W j)≤C*sourceControl T W:=by
  obtain ⟨T,C,hC,hc⟩:=scale_source_control S
  refine ⟨S∪T,1+C,by positivity,?_⟩
  intro W j
  have h₁:sourceControl S W≤sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_left:S⊆S∪T)) W
  have h₂:sourceControl T W≤sourceControl (S∪T) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_union_right:T⊆S∪T)) W
  by_cases hj:j=0
  · simp only [derivativeChoice,ite_eq_left hj]
    exact h₁.trans (le_mul_of_one_le_left (sourceControl_nonneg _ _) (by linarith))
  · simp only [derivativeChoice,ite_eq_right hj]
    exact (hc W).trans (mul_le_mul (by linarith) h₂ (sourceControl_nonneg _ _) (by positivity))

theorem reflected_profile_control (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ)):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃C:ℝ,0<C ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t:ℝ,
      (reflectionProfiles ha hlo hhi W hs j k v t).control S≤
        C*sourceControl T W*(1+‖v‖+‖t‖)^n:=by
  obtain ⟨n,T,C,hC,hc⟩:=independent_profile_control a b ha S
  obtain ⟨U,D,hD,hd⟩:=derivative_choice_control T
  let A:ℝ:=1+∑j:Fin 2,sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)
  have hA:0<A:=by
    have hh:=Finset.sum_nonneg (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j))
    dsimp [A];linarith
  refine ⟨2*n,U,C*A*D*(1+2*Real.pi)^(2*n),by positivity,?_⟩
  intro W hs j k v t
  have haSeed:sourceControl T (derivativeChoice (annulusSeed a b hlo hhi).profile j)≤A:=by
    have hh:=Finset.single_le_sum (fun (j:Fin 2) (_:j∈Finset.univ)=>
      sourceControl_nonneg T (derivativeChoice (annulusSeed a b hlo hhi).profile j)) (Finset.mem_univ j)
    dsimp [A];linarith
  have hheight:1+‖-2*Real.pi*v‖+‖t‖≤(1+2*Real.pi)*(1+‖v‖+‖t‖):=by
    rw [norm_mul,norm_mul,Real.norm_of_nonneg Real.pi_pos.le]
    norm_num only [norm_neg,Real.norm_of_nonneg (by norm_num:0≤(2:ℝ))]
    nlinarith [Real.pi_pos,norm_nonneg v,norm_nonneg t]
  have hh:=hc (derivativeChoice (annulusSeed a b hlo hhi).profile j) (derivativeChoice W k)
    (derivativeChoice_support _ _ _ (annulusSeed a b hlo hhi).support j)
    (derivativeChoice_support _ _ _ hs k) (-2*Real.pi*v) t
  apply hh.trans
  calc
    _≤C*(A*(D*sourceControl U W))*((1+2*Real.pi)*(1+‖v‖+‖t‖))^(2*n):=by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left
          (mul_le_mul haSeed (hd W k) (sourceControl_nonneg _ _) hA.le) hC.le
      · exact pow_le_pow_left₀ (by positivity) hheight _
      · positivity
      · exact mul_nonneg hC.le (mul_nonneg hA.le (mul_nonneg hD.le (sourceControl_nonneg _ _)))
    _=_:=by rw [mul_pow];ring

end SevenEighths.CenteredMomentEnergyReferenceChildProfiles

end

end OAI
end OAIOriginalModule2728

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowBands
Source SHA256: 19b4c160798924a6b31683a3c9b3877227d8cdfab0e9d9c7dbc6e11fbd0fcb88
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2729



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowBands
open HeckeFamily CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentNaturalFixedRaySource CenteredMomentInductionEnergy
open CenteredMomentPrimeSlot QuadraticInitialBound
open CenteredMomentFiniteProfileExceptional
local notation "O"=>HeckeFamily.O

def ZeroLowAt (Q:Ideal O)(a b bΦ Bmask L M ε Z:ℝ)
    (degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=Q→s.width≤M→
  ∀p:Profiles a b,∀t X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂≤5*s.width/6→
    s.plainEnergy p t X₁ X₂≤C*diagonalControl s.radial.profile*(p.control S)^2*
      (1+‖t‖)^degree*Z^(s.width+ε)

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

def PositiveLowAt (W:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ):Prop:=
  ∀T:Finset α,∀(θ:T→RayQuotient.Characters M H)(w σ v:T→ℝ)(t height:ℝ),
    (∀i,0≤w i)→(∀i,w i≤Lslot)→(∀i,lo≤σ i)→(∀i,σ i≤hi)→
    0≤height→(∀i,|v i|≤height)→
  ∀s:NaturalState Z Bmask bΦ,s.fixedModulus=internalQ Q η₀→s.width≤Mcap→
  ∀p:Profiles a b,∀X₁ X₂:ℝ,0<X₁→0<X₂→X₁≤Z^L→X₂≤Z^L→
    length Z X₁+length Z X₂+6*κ*(∑i,w i)≤s.width→
    length Z X₁+length Z X₂+(∑i,w i)≤5*s.width/6→
    energy s.character s.mask 1 t (p.profile 0) (p.profile 1)
      (fun i=>primePool M H bslot (Z^(w i)))
      (fun i I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
        HeckePrimeAnnular.annularWeight W (Z^(w i)) (σ i) (v i) I)
      (fun i=>Z^(w i)) X₁ X₂ s.radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*(p.control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε)

end SevenEighths.CenteredMomentEnergyReferenceLowBands

end

end OAI
end OAIOriginalModule2729

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowChild
Source SHA256: 5a72b9b43f10bff44dc88ed894ab305063debb33650f5610e4bd3271b63be270
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2730


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowChild
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

def unitBudgetState {Z Bmask bΦ:ℝ}(s:NaturalState Z Bmask bΦ)(hB:0≤Bmask):
    NaturalState Z Bmask bΦ:=
  {unpuncturedState s with
    puncture_bound:=by simpa only [unpuncturedState,map_one,Nat.cast_one] using Real.one_le_rpow s.base_ge_one hB}

variable {α:Type*}[Fintype α][DecidableEq α]
variable (M:Ideal O)[NeZero M]
local instance : Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤H)

theorem reflected_child_from_low
    (Wslot:ℝ→ℂ)(bslot a b bΦ Bmask L Lslot lo hi Mcap ε κ Z:ℝ)
    (η₀:Character)(Q:Ideal O)(degree:ℕ)(S:Finset (ℕ×ℕ))(C:ℝ)
    (hlow:PositiveLowAt (α:=α) M H hH Wslot bslot a b bΦ Bmask L Lslot lo hi
      Mcap ε κ Z η₀ Q degree S C)
    (hB:0≤Bmask)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (F:Finset α)(θ:α→RayQuotient.Characters M H)(w σ freq:α→ℝ)(t height:ℝ)
    (hw:∀i,0≤w i)(hwL:∀i,w i≤Lslot)(hσlo:∀i,lo≤σ i)(hσhi:∀i,σ i≤hi)
    (hheight:0≤height)(hfreq:∀i,|freq i|≤height)
    (s:NaturalState Z Bmask bΦ)(hQ:s.fixedModulus=internalQ Q η₀)(hs:s.width≤Mcap)
    (Wshort:𝓢(ℝ,ℂ))(hsW:Function.support (Wshort:ℝ→ℂ)⊆Set.Icc a b)
    (j k:Fin 2)(v X₁ X₂:ℝ)(hX₁:0<X₁)(hX₂:0<X₂)(hc₁:X₁≤Z^L)(hc₂:X₂≤Z^L)
    (hcapacity:length Z X₁+length Z X₂+6*κ*(∑i∈F,w i)≤s.width)
    (hsmall:length Z X₁+length Z X₂+(∑i∈F,w i)≤5*s.width/6):
    radialEnergy (fun z=>polynomial (naturalCharacter s.character z) false
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) X₁ 0 (-2*Real.pi*v)*
      polynomial (naturalCharacter s.character z) false (scaleTest Wshort k) X₂ 0 t *
      ∏i∈F,naturalSlot (naturalCharacter s.character z)
        (primePool M H bslot (Z^(w i)))
        (heightCoefficient (fun I=>idealCoeff (relativeCharacter M H hH η₀ (θ i)) I*
          HeckePrimeAnnular.annularWeight Wslot (Z^(w i)) (σ i) (freq i) I) t) (Z^(w i)))
      (effectiveState s).radial.keep s.radial.profile s.radial.scale≤
      C*diagonalControl s.radial.profile*
        ((reflectionProfiles ha hlo hhi Wshort hsW j k v t).control S)^2*
        (1+|t|+height)^degree*Z^(s.width+ε):=by
  have hZ:0<Z:=zero_lt_one.trans_le s.base_ge_one
  have hh:=hlow F (fun i=>θ i) (fun i=>w i) (fun i=>σ i) (fun i=>t+freq i)
    0 (|t|+height) (fun i=>hw i) (fun i=>hwL i) (fun i=>hσlo i) (fun i=>hσhi i)
    (add_nonneg (abs_nonneg t) hheight)
    (fun i=>(abs_add_le t (freq i)).trans (add_le_add le_rfl (hfreq i)))
    (unitBudgetState s hB) hQ hs (reflectionProfiles ha hlo hhi Wshort hsW j k v t)
    X₁ X₂ hX₁ hX₂ hc₁ hc₂
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hcapacity)
    (by simpa only [Finset.sum_coe_sort,unitBudgetState,unpuncturedState,NaturalState.width] using hsmall)
  rw [reflected_child_ray_energy s ha hlo hhi Wshort hsW F
    (fun i=>primePool M H bslot (Z^(w i)))
    (fun i=>relativeCharacter M H hH η₀ (θ i)) (fun _=>Wslot)
    (fun i=>Z^(w i)) σ freq
    (fun i _ I hI=>(Finset.mem_filter.mp hI).2.1)
    (fun i _=>Real.rpow_pos_of_pos hZ _) j k v t X₁ X₂ hX₁ hX₂]
  simpa only [unitBudgetState,unpuncturedState,NaturalState.width,
    NaturalState.mask,effectiveState,effectiveRadial,abs_zero,add_zero,add_assoc] using hh

end SevenEighths.CenteredMomentEnergyReferenceLowChild

end

end OAI
end OAIOriginalModule2730

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceLowControl
Source SHA256: 1a3d106e8fe51ee7898ede354e276b256a07bb2535fb42aece18c41a5ea7db85
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2731


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentEnergyReferenceLowControl
open CenteredMomentEnergyReferenceChildProfiles
open CenteredMomentFiniteProfileExceptional

lemma height_product (v t H:ℝ)(hH:0≤H):
    1+‖v‖+‖t‖≤(1+‖v‖)*(1+|t|+H):=by
  simp only [Real.norm_eq_abs]
  nlinarith [abs_nonneg v,abs_nonneg t]

theorem reflected_child_control (a b:ℝ)(ha:0<a)(hlo:a≤1/4)(hhi:1≤b)
    (S:Finset (ℕ×ℕ))(degree:ℕ):
    ∃n:ℕ,∃T:Finset (ℕ×ℕ),∃D:ℝ,0<D ∧
      ∀W:𝓢(ℝ,ℂ),∀hs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b,
      ∀j k:Fin 2,∀v t height:ℝ,0≤height →
      ((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2*
        (1+|t|+height)^degree≤
        D*(sourceControl T W)^2*(1+|t|+height)^(degree+2*n)*(1+‖v‖)^(2*n):=by
  obtain ⟨n,T,D,hD,hd⟩:=reflected_profile_control a b ha hlo hhi S
  refine ⟨n,T,D^2,sq_pos_of_pos hD,?_⟩
  intro W hs j k v t height hheight
  have hbase:=hd W hs j k v t
  have hgrowth:(1+‖v‖+‖t‖)^n≤((1+‖v‖)*(1+|t|+height))^n:=
    pow_le_pow_left₀ (by positivity) (height_product v t height hheight) n
  have hprof:((reflectionProfiles ha hlo hhi W hs j k v t).control S)^2≤
      (D*sourceControl T W*((1+‖v‖)*(1+|t|+height))^n)^2:=
    pow_le_pow_left₀ (Profiles.control_nonneg _ _) (hbase.trans
      (mul_le_mul_of_nonneg_left hgrowth (mul_nonneg hD.le (sourceControl_nonneg _ _)))) 2
  apply (mul_le_mul_of_nonneg_right hprof (by positivity)).trans_eq
  simp only [mul_pow] at *
  rw [pow_add,show (1+|t|+height)^(2*n)=((1+|t|+height)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul],
    show (1+‖v‖)^(2*n)=((1+‖v‖)^n)^2 by rw [Nat.mul_comm 2 n,pow_mul]]
  ring

end SevenEighths.CenteredMomentEnergyReferenceLowControl

end

end OAI
end OAIOriginalModule2731
