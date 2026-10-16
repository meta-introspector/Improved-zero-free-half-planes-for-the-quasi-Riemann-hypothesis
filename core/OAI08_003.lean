  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i (Finset.mem_univ i),
    Finset.mem_pi.mp hq i (Finset.mem_univ i)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i _=>(q i).val,Finset.mem_pi.mpr (fun i hi=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_pi (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ:Finset {i:ι // i∉J}).pi (fun i=>L i.val),
        (∏i∈(Finset.univ:Finset {i:ι // i∉J}).attach,
          star (coeff i.val.val (q i.val i.property)))*
        residualNormalizedPolynomial S
          (assignedIdeal L J x*survivingProduct Finset.univ q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=>star (W v)) Z r z G u := by
  rw [←sum_tuple_pi]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  simp only [survivingProduct,remainingIdeal]
  rw [Finset.prod_attach _ (fun i=>star (coeff i.val (q i).val)),
    Finset.prod_attach _ (fun i=>(q i).val)]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2526

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceEnergy
Source SHA256: 4df72f0535b2c5ebcfcde58809d8428ca265f29c488efb43d00e677bcf71fc38
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2527


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialConjugateEnergy InverseInitialPoissonBridge
open UniqueFactorizationMonoid CanonicalRowCompletion CanonicalQuadraticSieve
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def assignedMass (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ) : ℝ :=
  ‖∏i:↥J,coeff i.val (x i).val‖*Z^(-G)

def assignedTerm (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) : ℂ :=
  (∏i:↥J,coeff i.val (x i).val)*(moebius (assignedIdeal L J x):ℂ)*
    (Z^(-G):ℝ)*η (assignedIdeal L J x)^2*(idealRowHom u (assignedIdeal L J x))^2*
    star (remainingResidual S L J x coeff η (fun _=>1) W Z r z G u)

omit [Fintype ι] [DecidableEq ι] in
theorem assignedMass_nonneg (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (coeff:ι→Ideal O→ℂ)(Z G:ℝ)(hZ:0<Z) : 0≤assignedMass L J x coeff Z G :=
  mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hZ.le _)

theorem assignedTerm_norm_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(u:O) :
    ‖assignedTerm S L J x coeff η W Z r z G u‖≤
      assignedMass L J x coeff Z G*‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
  have hμ:‖(moebius (assignedIdeal L J x):ℂ)‖=1 := by simp [hj.2.1.moebius_eq]
  have hrow:‖idealRowHom u (assignedIdeal L J x)‖^2≤1 := by
    have hh:=admissible_row_four_le_one _ hj u
    nlinarith [sq_nonneg (‖idealRowHom u (assignedIdeal L J x)‖^2-1)]
  have hmass:=assignedMass_nonneg L J x coeff Z G hZ
  have he:‖η (assignedIdeal L J x)‖^2≤1:=pow_le_one₀ (norm_nonneg _) hη
  rw [assignedTerm,remainingResidual_eq_polynomial S L hprime hdis]
  simp only [norm_mul,norm_pow,norm_star,norm_neg,norm_one,one_pow,one_mul,
    hμ,mul_one,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hZ.le (-G))]
  change assignedMass L J x coeff Z G*‖η (assignedIdeal L J x)‖^2*
    ‖idealRowHom u (assignedIdeal L J x)‖^2*
    ‖remainingPolynomial S L J x coeff η W Z r z G u‖≤_
  calc
    _≤assignedMass L J x coeff Z G*1*1*
      ‖remainingPolynomial S L J x coeff η W Z r z G u‖ := by
      gcongr
    _=_:=by ring

theorem assignedTerm_energy_le (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:Admissible (assignedIdeal L J x))(hη:‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (assignedMass L J x coeff Z G)^2*
      ∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro u hu
  have hh:=mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (assignedTerm_norm_le S L hprime hdis J x coeff η hj hη W Z r z G hZ u) 2)
    (hw u)
  convert hh using 1 ; ring

theorem assigned_family_energy (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z G:ℝ)(hZ:0<Z)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u) :
    (∑u∈rows,w u*‖∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z G u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z G*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z G u‖^2))^2 := by
  refine (finite_weighted_triangle Finset.univ rows w hw
    (fun x u=>assignedTerm S L J x coeff η W Z r z G u)).trans ?_
  apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
  apply Finset.sum_le_sum
  intro x hx
  have hh:=Real.sqrt_le_sqrt (assignedTerm_energy_le S L hprime hdis J x coeff η
    (hj x) (hη x) W Z r z G hZ rows w hw)
  rwa [Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (assignedMass_nonneg L J x coeff Z G hZ)] at hh

theorem original_energy_of_remaining (S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hprime:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(Z r z:ℝ)(G:Finset ι→ℝ)(hZ:0<Z)
    (rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u‖^2)≤
      (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff Z (G J))^2*E := by
  have heq (u:O) :
      (∑q:Tuple L,(∏i,coeff i (q i).val)*
        originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W Z r z u)=
      ∑J∈Finset.univ.powerset,∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u :=
    original_selected_overlap S L hprime hdis coeff η (fun _=>1) W Z r z G hZ u
  simp_rw [heq]
  have hroot (J:Finset ι) :
      Real.sqrt (∑u∈rows,w u*‖∑x:Assigned L J,
        assignedTerm S L J x coeff η W Z r z (G J) u‖^2)≤
      (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
    have hm:0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J) :=
      Finset.sum_nonneg (fun x _=>assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hb:=assigned_family_energy S L hprime hdis J coeff η (hj J) (hη J)
      W Z r z (G J) hZ rows w hw
    have hc : (∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2))≤
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hres J x))
        (assignedMass_nonneg L J x coeff Z (G J) hZ)
    have hn : 0≤∑x:Assigned L J,assignedMass L J x coeff Z (G J)*
        Real.sqrt (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W Z r z (G J) u‖^2) :=
      Finset.sum_nonneg (fun x _=>mul_nonneg (assignedMass_nonneg L J x coeff Z (G J) hZ) (Real.sqrt_nonneg _))
    have hh:=Real.sqrt_le_sqrt (hb.trans (pow_le_pow_left₀ hn hc 2))
    rwa [Real.sqrt_sq (mul_nonneg hm (Real.sqrt_nonneg E))] at hh
  refine (finite_weighted_triangle Finset.univ.powerset rows w hw
    (fun J u=>∑x:Assigned L J,assignedTerm S L J x coeff η W Z r z (G J) u)).trans ?_
  calc
    _≤(∑J∈Finset.univ.powerset,
        (∑x:Assigned L J,assignedMass L J x coeff Z (G J))*Real.sqrt E)^2 := by
      apply pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _))
      exact Finset.sum_le_sum (fun J _=>hroot J)
    _=_:=by rw [←Finset.sum_mul,mul_pow,Real.sq_sqrt hE]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2527

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceFiber
Source SHA256: a2f745369681aec2717770a6bdf19a95740bc03e8fd35930c147b1d7eb8f1aca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2528


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open InverseInitialRawDictionary InverseInitialDetectorSource InverseInitialPhysicalSlots
open DetectorDictionaryInverseMarkedPadding HeckeDetectorCoefficientTransfer
open InverseInitialConjugateEnergy
local notation "O"=>HeckeFamily.O
variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

def fiberLists (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (s:selected) : Finset (Ideal O) :=
  livePrimes M H (F.profile s) (F.upper s) (U^(F.widths s))

def fiberCoefficient (F:Fiber M H Label Slot U a ε tstar T allowance i)(s:Slot)
    (P:Ideal O) : ℂ := slotCoefficient F.rowData (F.profile s) (U^(F.widths s)) (F.external s) P

omit [NeZero M] in
theorem fiberLists_prime (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(s:selected)(P:Ideal O)(hP:P∈fiberLists F selected s) : Prime P := by
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp hP).1).2.1

omit [NeZero M] in
theorem fiberLists_disjoint (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0<U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)<lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)<lower s*U^(F.widths s)) :
    ((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
  intro s hs t ht hst
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  have hp:=livePrime_data M H (F.profile s) (lower s) (F.upper s) (U^(F.widths s))
    (Real.rpow_pos_of_pos hU _) (hV s s.property) P hP
  have hq:=livePrime_data M H (F.profile t) (lower t) (F.upper t) (U^(F.widths t))
    (Real.rpow_pos_of_pos hU _) (hV t t.property) P hQ
  rcases hsep s s.property t t.property (fun he=>hst (Subtype.ext he)) with h|h <;>
    linarith [hp.2.2.1,hp.2.2.2,hq.2.2.1,hq.2.2.2]

omit [NeZero M] in
theorem selectedSource_tuple (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(u:O) :
    selectedSource F selected W σ t bW u=
      ∑q:Tuple (fiberLists F selected),(∏s:selected,fiberCoefficient F s (q s).val)*
        originalTotalPolynomial
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (∏s:selected,(q s).val) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) u := by
  rw [sum_tuple_original (fiberLists F selected) (fun q=>
    (∏s:selected,fiberCoefficient F s (q s))*originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
      (∏s:selected,q s) (fixedBase F.rowData.η F.rowData.m F.rowData.f) (fun _=>1)
      (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
      U F.r (∑s:selected,F.widths s) u)]
  unfold selectedSource
  apply Finset.sum_congr rfl
  intro q hq
  rw [tuple_coefficient]
  rfl

omit [NeZero M] in
theorem selectedSource_overlap (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(W:ℝ→ℂ)(σ t bW:ℝ)(hU:0<U)
    (hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected))
    (u:O) :
    selectedSource F selected W σ t bW u=
      ∑J∈(Finset.univ:Finset selected).powerset,∑x:Assigned (fiberLists F selected) J,
        assignedTerm
          ((ConcretePrimeRowBridge.idealsUpTo ⌈U^F.r*bW⌉₊).filter CanonicalQuadraticSieve.Supported)
          (fiberLists F selected) J x (fun s=>fiberCoefficient F s)
          (fixedBase F.rowData.η F.rowData.m F.rowData.f)
          (twistedProfile (orientedProfile F.reverse W) σ (orientedFrequency F.reverse t))
          U F.r (∑s:selected,F.widths s) (∑s∈J,F.widths s) u := by
  rw [selectedSource_tuple]
  exact original_selected_overlap _ (fiberLists F selected) (fiberLists_prime F selected)
    hdis (fun s=>fiberCoefficient F s) _ (fun _=>1) _ U F.r _
    (fun J=>∑s∈J,F.widths s) hU u

omit [NeZero M] in
theorem fiberAssigned_admissible (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(lower:Slot→ℝ)(hU:0<U)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((baseCharacter F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s))
    (hsep:∀s∈selected,∀t∈selected,s≠t→
      F.upper s*U^(F.widths s)<lower t*U^(F.widths t) ∨
      F.upper t*U^(F.widths t)<lower s*U^(F.widths s))
    (J:Finset selected)(x:Assigned (fiberLists F selected) J) :
    CanonicalQuadraticSieve.Admissible (assignedIdeal (fiberLists F selected) J x) := by
  have hdis:=fiberLists_disjoint F selected lower hU hV hsep
  have hp (s:↥J):Prime (x s).val:=fiberLists_prime F selected s.val _ (x s).property
  have hinj:Function.Injective (fun s:↥J=>(x s).val) := by
    intro s t he
    apply Subtype.ext
    by_contra hst
    exact Finset.disjoint_left.mp (hdis (Finset.mem_univ s.val) (Finset.mem_univ t.val) hst)
      (x s).property (by simpa only [he] using (x t).property)
  have hs (s:↥J):CanonicalQuadraticSieve.Supported (x s).val := by
    by_contra hn
    have hd:=livePrime_data M H (F.profile s.val) (lower s.val) (F.upper s.val)
      (U^(F.widths s.val)) (Real.rpow_pos_of_pos hU _) (hV s.val s.val.property)
      (x s).val (x s).property
    exact base_nonzero_prime F.rowData (x s).val (hp s)
      ((hlarge s.val s.val.property).trans_le hd.2.2.1)
      (fixedBase_zero_unsupported F.rowData.η F.rowData.m F.rowData.f
        F.rowData.lambda_dvd F.rowData.two_dvd (x s).val hn)
  have hprod (T:Finset ↥J):CanonicalQuadraticSieve.Supported (∏s∈T,(x s).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert s T hsT ih =>
      rw [Finset.prod_insert hsT]
      exact (CanonicalQuadraticSieve.supported_mul_iff _ _).mpr ⟨hs s,ih⟩
  exact ⟨(hprod Finset.univ).1,tuple_product_squarefree _ hp hinj,(hprod Finset.univ).2⟩

omit [NeZero M] in
theorem fiberBase_norm (F:Fiber M H Label Slot U a ε tstar T allowance i)(P:Ideal O) :
    ‖fixedBase F.rowData.η F.rowData.m F.rowData.f P‖≤1 := by
  rw [←baseCharacter_coeff]
  exact idealCoeff_norm_le_one _ _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2528

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceDeleted
Source SHA256: 24e3ccf48202d7da725a84207d394857a6d5978d3e115aae242b6f73fd88acc1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2529




namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialConjugateEnergy InverseInitialPhysicalSlots
open InverseInitialMarkedDictionary
open DetectorDictionaryInverseRawInitialGates InverseInitialExcludedPeriod
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι]

theorem deletedBase_zero_unsupported (data:RowData)(I:Ideal O)(hI:¬Supported I) :
    idealCoeff (deletedBase data) I=0 := by
  unfold deletedBase excluded
  rw [idealCoeff_excludePrimes,baseCharacter_coeff,
    fixedBase_zero_unsupported data.η data.m data.f data.lambda_dvd data.two_dvd I hI]
  split_ifs <;> rfl

theorem deletedBase_eq_of_ne_zero (data:RowData)(I:Ideal O)
    (hI:idealCoeff (deletedBase data) I≠0) :
    idealCoeff (deletedBase data) I=fixedBase data.η data.m data.f I := by
  unfold deletedBase excluded at hI ⊢
  rw [idealCoeff_excludePrimes,baseCharacter_coeff] at hI ⊢
  split_ifs with h
  · rfl
  · exact False.elim (hI (by simp [h]))

def deletedSelectedSource (data:RowData)(M:Ideal O)[NeZero M]
    (H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(b ell:ι→ℝ)(ζ:ι→ℂ)(u:O) : ℂ :=
  ∑p∈Fintype.piFinset (fun i=>livePrimes M H (V i) (b i) (Z^(ell i))),
    (star (∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i))/
      idealCoeff (deletedBase data) (∏i,p i))*
    originalTotalPolynomial
      ((ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊).filter Supported)
      (∏i,p i) (idealCoeff (deletedBase data)).toMonoidHom (fun _=>1)
      (twistedProfile W σ freq) Z r (∑i,ell i) u

theorem deleted_physical_slots_norm_initial (data:RowData)(u:NonzeroElement)
    (M:Ideal O)[NeZero M](H:Subgroup (O⧸M)ˣ)(W:ℝ→ℂ)(V:ι→ℝ→ℂ)
    (Z r σ freq bW:ℝ)(a b ell:ι→ℝ)(ζ:ι→ℂ)(hZ:0<Z)
    (hW:∀x,W x≠0→x≤bW)(hV:∀i x,V i x≠0→x∈Set.Icc (a i) (b i))
    (hlarge:∀i,((deletedBase data).modulus.absNorm:ℝ)<a i*Z^(ell i)) :
    ‖polynomial ((data.character u).excludePrimes (excluded data)
        (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*
      (∏i,HeckePrimeRow.canonicalPrimeAmplitude M H u.val (V i) (b i) (Z^(ell i)) (ζ i))‖=
    ‖deletedSelectedSource data M H W V Z r σ freq bW b ell ζ u.val‖ := by
  let L:=fun i=>livePrimes M H (V i) (b i) (Z^(ell i))
  let A:=fun p:ι→Ideal O=>∏i,primeProfile (V i) (Z^(ell i)) (ζ i) (p i)
  have hn (p:ι→Ideal O)(hp:p∈Fintype.piFinset L)(_ha:A p≠0):
      idealCoeff (deletedBase data) (∏i,p i)≠0 := by
    rw [map_prod]
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    have hd:=livePrime_data M H (V i) (a i) (b i) (Z^(ell i))
      (Real.rpow_pos_of_pos hZ _) (hV i) (p i) (Fintype.mem_piFinset.mp hp i)
    exact HeckeDetectorRelativePrime.idealCoeff_ne_zero_of_coprime _ _ hd.1.ne_zero
      (ProbeRaySlots.prime_coprime_of_norm_gt (deletedBase data) ⟨p i,hd.1⟩
        ((hlarge i).trans_le hd.2.2.1))
  have he:=indexed_conjugate_mark_norm (Fintype.piFinset L) (fun p=>∏i,p i) A
    (idealCoeff (deletedBase data)).toMonoidHom
    ((data.character u).excludePrimes (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)))
    u.val (actual_deleted_row data u) W Z r (∑i,ell i) σ freq hZ
    (ConcretePrimeRowBridge.idealsUpTo ⌈Z^r*bW⌉₊)
    (finite_source_cover W (Z^r) bW (Real.rpow_pos_of_pos hZ _) hW) hn
  rw [amplitude_product_eq_tuples M H _ _ _ _ _ _ hZ,←mul_assoc]
  change ‖polynomial ((data.character u).excludePrimes (excluded data)
    (reflectionExcludedPrimes_prime (basePeriod data))) true W (Z^r) σ freq*↑(Z^(-(∑i,ell i)/2))*
    (∑p∈Fintype.piFinset L,A p*star (idealRowHom u.val (∏i,p i)))‖=_
  rw [he]
  unfold deletedSelectedSource
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  rw [originalTotal_supported_source _ _ _ (deletedBase_zero_unsupported data)]
  rfl

theorem marked_fixed_deletion (data:RowData)(rows:Finset NonzeroElement)
    (W:ℝ→ℂ)(X σ t bW:ℝ)(hX:0<X)(hW:∀x,W x≠0→x≤bW)
    (mark:NonzeroElement→ℂ) :
    (∑u∈rows,‖polynomial (data.character u) true W X σ t*mark u‖^2)≤
      ((IdealMobiusDivisorSum.idealDivisors (∏P∈excluded data,P)).card:ℝ)*
      ∑j∈IdealMobiusDivisorSum.idealDivisors (∏P∈excluded data,P),∑u∈rows,
        ‖polynomial ((data.character u).excludePrimes (excluded data)
          (reflectionExcludedPrimes_prime (basePeriod data))) true W
          (X/(j.absNorm:ℝ)) σ t*mark u‖^2 := by
  simpa only [one_mul] using InverseInitialExcludedEnergy.marked_family rows data.character
    (excluded data) (reflectionExcludedPrimes_prime (basePeriod data)) W X σ t bW hX hW mark
    (fun _=>1) (fun _ _=>zero_le_one)

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2529

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceMass
Source SHA256: e279abef4a100fc2722c69ef7c7705c078e43cd92a2250cfed50480857595708
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2530



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily DetectorDictionaryInverseAssignedCount
local notation "O"=>HeckeFamily.O

private theorem sum_tuple_real {ι:Type*}[Fintype ι](L:ι→Finset (Ideal O))
    (f:(ι→Ideal O)→ℝ) :
    (∑q:Tuple L,f (fun i=>(q i).val))=∑q∈assignedTuples L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i,(mem_assignedTuples L q).mp hq i⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i
    exact congrArg Subtype.val (congrFun he i)
  · intro q hq
    refine ⟨fun i=>(q i).val,(mem_assignedTuples L _).mpr (fun i=>(q i).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

variable {ι:Type*}[Fintype ι][DecidableEq ι]

omit [Fintype ι] in
theorem assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (L:ι→Finset (Ideal O))(J:Finset ι)(hJ:J.card≤K)(ell:ι→ℝ)
    (hL:∀i∈J,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i∈J,∀P∈L i,‖coeff i P‖≤1) :
    (∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤assignedConstant K b := by
  have he:=assigned_sum_normalized_le K hb hU (by simpa using hJ)
    (fun i:↥J=>ell i) (fun i:↥J=>L i)
    (fun i P hP=>hL i i.property P hP)
    (fun i:↥J=>coeff i) (fun i P hP=>hc i i.property P hP)
  rw [←sum_tuple_real] at he
  simp only [assignedMass,assignedCoefficient,Finset.sum_coe_sort] at he ⊢
  convert he using 1
  congr 1
  ext x
  simp

theorem all_assignedMass_sum_le (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(L:ι→Finset (Ideal O))(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1) :
    (∑J∈Finset.univ.powerset,∑x:Assigned L J,assignedMass L J x coeff U (∑i∈J,ell i))≤
      (2:ℝ)^K*assignedConstant K b := by
  calc
    _≤∑J∈(Finset.univ:Finset ι).powerset,assignedConstant K b := by
      apply Finset.sum_le_sum
      intro J hJ
      exact assignedMass_sum_le K hb hU L J ((Finset.card_le_univ J).trans hK) ell
        (fun i _=>hL i) coeff (fun i _=>hc i)
    _=(2:ℝ)^Fintype.card ι*assignedConstant K b := by
      simp
    _≤_:=mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hK)
      (assignedConstant_pos K hb).le

theorem original_energy_with_assigned_count (K:ℕ){b U:ℝ}(hb:1≤b)(hU:1≤U)
    (hK:Fintype.card ι≤K)(S:Finset (Ideal O))(L:ι→Finset (Ideal O))
    (hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(ell:ι→ℝ)
    (hL:∀i,∀P∈L i,P≠0 ∧ (P.absNorm:ℝ)≤b*U^(ell i))
    (coeff:ι→Ideal O→ℂ)(hc:∀i,∀P∈L i,‖coeff i P‖≤1)(η:Ideal O→*ℂ)
    (hj:∀J:Finset ι,∀x:Assigned L J,CanonicalQuadraticSieve.Admissible (assignedIdeal L J x))
    (hη:∀J:Finset ι,∀x:Assigned L J,‖η (assignedIdeal L J x)‖≤1)
    (W:ℝ→ℂ)(r z:ℝ)(rows:Finset O)(w:O→ℝ)(hw:∀u,0≤w u)(E:ℝ)(hE:0≤E)
    (hres:∀J:Finset ι,∀x:Assigned L J,
      (∑u∈rows,w u*‖remainingPolynomial S L J x coeff η W U r z (∑i∈J,ell i) u‖^2)≤E) :
    (∑u∈rows,w u*‖∑q:Tuple L,(∏i,coeff i (q i).val)*
      InverseInitialConjugateEnergy.originalTotalPolynomial S (∏i,(q i).val) η (fun _=>1) W U r z u‖^2)≤
      ((2:ℝ)^K*assignedConstant K b)^2*E := by
  have hU0:0<U:=zero_lt_one.trans_le hU
  refine (original_energy_of_remaining S L hp hdis coeff η hj hη W U r z
    (fun J=>∑i∈J,ell i) hU0 rows w hw E hE hres).trans ?_
  apply mul_le_mul_of_nonneg_right _ hE
  apply pow_le_pow_left₀
    (Finset.sum_nonneg (fun J _=>Finset.sum_nonneg
      (fun x _=>assignedMass_nonneg L J x coeff U (∑i∈J,ell i) hU0)))
  exact all_assignedMass_sum_le K hb hU hK L ell hL coeff hc

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2530

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceReindex
Source SHA256: ca4452a61ad755586df40bed019e4cc773a1d594066e186b3c8cb765f589ecf9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2531


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily InverseInitialPoissonBridge InverseInitialConjugateEnergy InverseInitialCommonRatios
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

def remainingIndexEquiv (J:Finset ι) : {i:ι // i∉J} ≃ ↥(Finset.univ\J) where
  toFun i:=⟨i.val,Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩⟩
  invFun i:=⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩
  left_inv _:=rfl
  right_inv _:=rfl

theorem remaining_product_attach {A:Type*}[CommMonoid A]
    (J:Finset ι)(f:{i:ι // i∉J}→A) :
    (∏i,f i)=∏i∈(Finset.univ\J).attach,f ⟨i.val,(Finset.mem_sdiff.mp i.property).2⟩ := by
  exact ((remainingIndexEquiv J).symm.prod_comp f).symm

def remainingPi (L:ι→Finset (Ideal O))(J:Finset ι)(q:Remaining L J) :
    ∀i∈Finset.univ\J,Ideal O := fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).val

theorem sum_remaining_original (L:ι→Finset (Ideal O))(J:Finset ι)
    (f:(∀i∈Finset.univ\J,Ideal O)→ℂ) :
    (∑q:Remaining L J,f (remainingPi L J q))=∑q∈(Finset.univ\J).pi L,f q := by
  symm
  apply Finset.sum_bij (fun q hq i=>⟨q i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp hq i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩)
  · intro q hq
    exact Finset.mem_univ _
  · intro q hq r hr he
    funext i hi
    exact congrArg Subtype.val (congrFun he ⟨i,(Finset.mem_sdiff.mp hi).2⟩)
  · intro q hq
    refine ⟨remainingPi L J q,Finset.mem_pi.mpr (fun i hi=>(q ⟨i,(Finset.mem_sdiff.mp hi).2⟩).property),?_⟩
    funext i
    rfl
  · intro q hq
    rfl

theorem remainingPolynomial_original_pi (S:Finset (Ideal O))(L:ι→Finset (Ideal O))(J:Finset ι)
    (x:Assigned L J)(coeff:ι→Ideal O→ℂ)(η:Ideal O→*ℂ)
    (W:ℝ→ℂ)(Z r z G:ℝ)(u:O) :
    remainingPolynomial S L J x coeff η W Z r z G u=
      ∑q∈(Finset.univ\J).pi L,(∏i∈(Finset.univ\J).attach,star (coeff i.val (q i.val i.property)))*
        residualNormalizedPolynomial S (assignedIdeal L J x*survivingProduct (Finset.univ\J) q)
          (assignedIdeal L J x) (conjugateIdealCharacter η) (fun _=>1)
          (fun v=>star (W v)) Z r z G u := by
  rw [←sum_remaining_original]
  unfold remainingPolynomial
  apply Finset.sum_congr rfl
  intro q hq
  unfold remainingIdeal survivingProduct remainingPi
  rw [remaining_product_attach J (fun i=>star (coeff i.val (q i).val)),
    remaining_product_attach J (fun i=>(q i).val)]

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2531

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceArithmetic
Source SHA256: f3e64234b166647219fcae5df614885e057ef129c99b85b755576191d129a467
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2532



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve InverseInitialCommonRatios InverseInitialExcludedPool
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem tuple_supported (L:ι→Finset (Ideal O))(hs:∀i,∀P∈L i,Supported P)(q:Tuple L) :
    Supported (∏i,(q i).val) := by
  have hh (T:Finset ι):Supported (∏i∈T,(q i).val) := by
    induction T using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty]
      exact ⟨one_ne_zero,by intro P hP;simp only [UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP⟩
    | @insert i T hi ih =>
      rw [Finset.prod_insert hi]
      exact (supported_mul_iff _ _).mpr ⟨hs i _ (q i).property,ih⟩
  exact hh Finset.univ

theorem tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)(q:Tuple L) :
    Admissible (∏i,(q i).val) :=
  ⟨(tuple_supported L hs q).1,tuple_product_squarefree _ (fun i=>hp i _ (q i).property)
    (tuple_injective L hdis q),(tuple_supported L hs q).2⟩

def remainingFromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) : Remaining L J :=
  fun i=>⟨t i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩),
    Finset.mem_pi.mp ht i.val (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,i.property⟩)⟩

theorem remainingIdeal_fromPi (L:ι→Finset (Ideal O))(J:Finset ι)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    remainingIdeal L J (remainingFromPi L J t ht)=survivingProduct (Finset.univ\J) t := by
  unfold remainingIdeal
  rw [remaining_product_attach]
  rfl

theorem remaining_tuple_admissible (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J)(t:∀i∈Finset.univ\J,Ideal O)
    (ht:t∈(Finset.univ\J).pi L) :
    Admissible (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_admissible L hp hs hdis _

theorem remaining_tuple_coprime (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    Pairwise (Function.onFun IsCoprime (fun i:↥(Finset.univ\J)=>t i.val i.property)) := by
  intro i j hij
  have hiP:=hp i.val _ (Finset.mem_pi.mp ht i.val i.property)
  have hjP:=hp j.val _ (Finset.mem_pi.mp ht j.val j.property)
  let:(t i.val i.property).IsMaximal:=(Ideal.isPrime_of_prime hiP).isMaximal hiP.ne_zero
  let:(t j.val j.property).IsMaximal:=(Ideal.isPrime_of_prime hjP).isMaximal hjP.ne_zero
  apply Ideal.isCoprime_of_isMaximal
  intro he
  dsimp only at he
  exact Finset.disjoint_left.mp (hdis (Finset.mem_univ i.val) (Finset.mem_univ j.val)
    (fun hh=>hij (Subtype.ext hh))) (Finset.mem_pi.mp ht i.val i.property)
      (by rw [he];exact Finset.mem_pi.mp ht j.val j.property)

omit [DecidableEq ι] in
theorem tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(q:Tuple L) : outside E (∏i,(q i).val) := by
  intro P hP hd
  obtain ⟨i,hi,hdi⟩:=((hE P hP).dvd_finsetProd_iff (fun i=>(q i).val)).mp hd
  exact hout i _ (q i).property P hP hdi

theorem remaining_tuple_outside (L:ι→Finset (Ideal O))(E:Finset (Ideal O))(hE:∀P∈E,Prime P)
    (hout:∀i,∀P∈L i,outside E P)(J:Finset ι)(x:Assigned L J)
    (t:∀i∈Finset.univ\J,Ideal O)(ht:t∈(Finset.univ\J).pi L) :
    outside E (assignedIdeal L J x*survivingProduct (Finset.univ\J) t) := by
  rw [←remainingIdeal_fromPi L J t ht,←joinTuple_product]
  exact tuple_outside L E hE hout _

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2532

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedUniform
Source SHA256: 23c29fa13356192fa68b824104c30b0f37c3b759aaefc2dccf2f434d622aba7a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2533




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory

namespace SevenEighths.DetectorDictionaryInverseMarkedUniform
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open DetectorDictionaryInverseUniform DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseRawFourier InverseInitialClippedColumns
open InverseInitialOverlapFourier FourierBridge HeckeDetectorRawFiber

private theorem clipped_one_zero (W : ℝ→ℂ) : clippedTest W 1 0=W := by
  funext x
  simp [clippedTest,childLogTest,logPhase]

theorem family_mode_integrable (χ : Character) (A : ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t D : ℝ) (hD : 0<D) :
    Integrable (fun v : ℝ=>familyDensity scaled reverse n U tstar r σ t 1 v*
      (polynomial χ true (childLogTest referenceWindow v) D 0 0*A)) := by
  simpa only [familyDensity,zero_add,mul_assoc] using
    (polynomial_mode_integrable χ true (logSource scaled reverse n U tstar r σ t)
      referenceWindow (13/4) 1 0 D hD
      (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)).mul_const A

theorem family_polynomial_fourier (χ : Character) (A : ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t D : ℝ) (hD : 0<D) :
    polynomial χ true (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A=
      ∫v : ℝ,familyDensity scaled reverse n U tstar r σ t 1 v*
        (polynomial χ true (childLogTest referenceWindow v) D 0 0*A) := by
  have h:=polynomial_clipped_fourier χ true
    (inverseSourceSchwartz scaled reverse n U tstar r σ t) (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow (13/4) 1 0 D (by norm_num) hD
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy)
  rw [clipped_one_zero] at h
  rw [h,←integral_mul_const]
  apply integral_congr_ae
  filter_upwards with v
  simp only [familyDensity,logSource_eq_logSchwartz,zero_add,mul_assoc]

theorem moving_finite_energy (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{ι : Type*}(rows : Finset ι)
      (χ : ι→Character)(A : ι→ℂ)(D E : ℝ),0<D→0≤E→
    (∀v : ℝ,(∑u∈rows,‖polynomial (χ u) true (childLogTest referenceWindow v) D 0 0*A u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀scaled reverse : Bool,∀n : ℕ,n≤2→∀U : ℝ,0<U→
    ∀tstar r : ℝ,∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈rows,‖polynomial (χ u) true
      (inverseSourceSchwartz scaled reverse n U tstar r σ t) D 0 0*A u‖^2)
      ≤C*E*(1+‖t‖)^K := by
  obtain ⟨K,B,hB,hmass⟩:=familyDensity_moment J
  refine ⟨2*K,B^2,sq_pos_of_pos hB,?_⟩
  intro ι rows χ A D E hD hE href scaled reverse n hn U hU tstar r σ hσ t
  let W:=inverseSourceSchwartz scaled reverse n U tstar r σ t
  have hb:=polynomial_clipped_energy rows χ true A W (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t) (W.smooth ⊤)
    referenceWindow (13/4) 1 0 D E J (by norm_num) hD hE
    (fun x hx=>(referenceWindow_support (subset_tsupport _ hx)).2)
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t 1 y
      (by norm_num) (by norm_num) hy) href
  rw [clipped_one_zero] at hb
  simp only [norm_zero,add_zero,one_pow,mul_one] at hb
  have hm:=hmass scaled reverse n hn U hU tstar r σ hσ t 1
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  apply hb.trans
  calc
    _≤E*(B*(1+‖t‖)^K)^2:=mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (integral_nonneg (fun _=>by positivity)) hm 2) hE
    _= _:=by rw [mul_pow,←pow_mul];ring_nf

theorem logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) :
    logTest W n=(HeckeDetectorRowwisePolynomial.logProfile^[n]) W := by
  induction n with
  | zero=>rfl
  | succ n ih=>rw [logTest,Function.iterate_succ_apply',←ih]

section Fiber
variable {M : Ideal O} {H : Subgroup (O⧸M)ˣ} {Label Slot : Type*}
  {U a ε tstar T allowance : ℝ} {i : ℕ}

theorem fiber_inverse_source
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (n : ℕ) (σ t : ℝ) :
    (inverseSourceSchwartz false false n U tstar F.r σ t : ℝ→ℂ)=
      twistProfile ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile) σ t := by
  funext x
  simpa only [Bool.false_eq_true,ite_false,HeckeDetectorCoefficientTransfer.orientedProfile,
    logTest_eq_iterate,Fiber.inverseProfile] using
    inverseSourceSchwartz_apply false false n U tstar F.r σ t x

theorem fiber_inverse_polynomial
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (selected : Finset Slot)
    (n : ℕ) (σ t : ℝ) (u : FreeRow) :
    polynomial (F.family u F.label) true
      (inverseSourceSchwartz false false n U tstar F.r σ t) (U^F.r) 0 0*
        F.physicalProduct selected u=
    polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u := by
  rw [fiber_inverse_source,polynomial_twistProfile]

theorem fiber_inverse_fourier
    (F : Fiber M H Label Slot U a ε tstar T allowance i) (selected : Finset Slot)
    (n : ℕ) (σ t : ℝ) (hU : 0<U) (u : FreeRow) :
    polynomial (F.family u F.label) true ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u=
      ∫v : ℝ,familyDensity false false n U tstar F.r σ t 1 v*
        (polynomial (F.family u F.label) true (childLogTest referenceWindow v) (U^F.r) 0 0*
          F.physicalProduct selected u) := by
  rw [←fiber_inverse_polynomial]
  exact family_polynomial_fourier _ _ false false n U tstar F.r σ t _
    (Real.rpow_pos_of_pos hU _)
end Fiber

theorem fiber_inverse_energy_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t : ℝ,
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+‖t‖)^K := by
  obtain ⟨K,C,hC,hb⟩:=moving_finite_energy J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ t
  have hh:=hb F.rows (fun u=>F.family u F.label) (F.physicalProduct selected)
    (U^F.r) E (Real.rpow_pos_of_pos hU _) hE href false false n hn U hU tstar F.r σ hσ t
  simpa only [fiber_inverse_polynomial] using hh

theorem fiber_inverse_height_uniform (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀E : ℝ,0≤E→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤E*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height→t∈Set.Icc (-height) height→
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)≤C*E*(1+height)^K := by
  obtain ⟨K,C,hC,hb⟩:=fiber_inverse_energy_uniform J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU E hE href n hn σ hσ height t _ ht
  apply (hb F selected hU E hE href n hn σ hσ t).trans
  have hnorm : ‖t‖≤height := by simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using ht
  gcongr

theorem fiber_inverse_height_budget (J : ℕ) :
    ∃K : ℕ,∃C : ℝ,0<C ∧ ∀{M : Ideal O}{H : Subgroup (O⧸M)ˣ}{Label Slot : Type*}
      {U a ε tstar T allowance : ℝ}{i : ℕ}
      (F : Fiber M H Label Slot U a ε tstar T allowance i)(selected : Finset Slot),0<U→
    ∀A epsInternal : ℝ,0≤A→
    (∀v : ℝ,(∑u∈F.rows,‖polynomial (F.family u F.label) true
      (childLogTest referenceWindow v) (U^F.r) 0 0*F.physicalProduct selected u‖^2)
      ≤(A*U^(1+epsInternal))*(1+‖v‖)^(2*J))→
    ∀n : ℕ,n≤2→∀σ∈Set.Icc (0:ℝ) 1,∀height t : ℝ,0≤height→t∈Set.Icc (-height) height→
    (∑u∈F.rows,‖polynomial (F.family u F.label) true
      ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
      (U^F.r) σ t*F.physicalProduct selected u‖^2)
      ≤C*A*U^(1+epsInternal)*(1+height)^K := by
  obtain ⟨K,C,hC,hb⟩:=fiber_inverse_height_uniform J
  refine ⟨K,C,hC,?_⟩
  intro M H Label Slot U a ε tstar T allowance i F selected hU A epsInternal hA
    href n hn σ hσ height t hheight ht
  simpa only [mul_assoc] using hb F selected hU (A*U^(1+epsInternal))
    (mul_nonneg hA (Real.rpow_nonneg hU.le _)) href n hn σ hσ height t hheight ht

end SevenEighths.DetectorDictionaryInverseMarkedUniform

end

end OAI
end OAIOriginalModule2533

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedPhysicalRows
Source SHA256: 6f99894c98554f1016e9b14143ea1e7efca109f1d96edad87cb5d1a55c83e6f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2534




namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber
open HeckeDetectorCoefficientTransfer HeckeDetectorPhysicalSelection
open InverseInitialPhysicalSlots InverseInitialRawDictionary InverseInitialDetectorSource
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseRawInitialGates
open InverseInitialExcludedPeriod CanonicalRowCompletion IdealMobiusDivisorSum InverseMoment
local notation "O"=>HeckeFamily.O

 def actualRow (u:FreeRow):NonzeroElement:=⟨u.val,u.property.1⟩

 theorem actualRow_injective:Function.Injective actualRow:=by
  intro u v he
  exact Subtype.ext (congrArg (fun w:NonzeroElement=>w.val) he)

 theorem actual_rows_sum (rows:Finset FreeRow)(f:NonzeroElement→ℝ):
    (∑u∈rows.image actualRow,f u)=∑u∈rows,f (actualRow u):=
  Finset.sum_image (fun _u _ _v _ h=>actualRow_injective h)

 theorem oriented_child (reverse:Bool)(W:ℝ→ℂ)(v:ℝ):
    orientedProfile reverse (childLogTest W v)=
      childLogTest (orientedProfile reverse W) (orientedFrequency reverse v):=by
  cases reverse
  · rfl
  · exact DetectorDictionaryInverseRawConjugateGates.childLogTest_conjugate W v

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
  {U a ε tstar T allowance:ℝ}{i:ℕ}

omit [NeZero M] in
theorem physicalProduct_eq (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(u:FreeRow):
    F.physicalProduct selected u=
      ∏s:selected,HeckePrimeRow.canonicalPrimeAmplitude M H u.val
        (F.profile s) (F.upper s) (U^(F.widths s)) (F.external s):=by
  simp only [Fiber.physicalProduct,physical]
  exact (Finset.prod_coe_sort selected _).symm

 theorem fiber_rows_le_deleted_sources
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (W:ℝ→ℂ)(σ freq bW:ℝ)(lower:Slot→ℝ)(hU:1<U)
    (hW:∀x,W x≠0→x≤bW)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)):
    (∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ freq*
      F.physicalProduct selected u‖^2)≤
      ((idealDivisors (∏P∈excluded F.rowData,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded F.rowData,P),∑u∈F.rows,
          ‖deletedSelectedSource F.rowData M H (orientedProfile F.reverse W)
            (fun s:selected=>F.profile s) U (shiftedExponent F.rowData U F.r j)
            σ (orientedFrequency F.reverse freq) bW
            (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
            (fun s:selected=>F.external s) u.val‖^2:=by
  have hU0:0<U:=zero_lt_one.trans hU
  let mark:NonzeroElement→ℂ:=fun u=>∏s:selected,
    HeckePrimeRow.canonicalPrimeAmplitude M H u.val (F.profile s) (F.upper s)
      (U^(F.widths s)) (F.external s)
  have hw:∀x,orientedProfile F.reverse W x≠0→x≤bW:=by
    intro x hx
    apply hW x
    intro hz
    exact hx (by cases F.reverse <;> simp [orientedProfile,hz])
  have he:(∑u∈F.rows,‖polynomial (F.family u F.label) true W (U^F.r) σ freq*
        F.physicalProduct selected u‖^2)=
      ∑u∈F.rows.image actualRow,‖polynomial (F.rowData.character u) true
        (orientedProfile F.reverse W) (U^F.r) σ (orientedFrequency F.reverse freq)*mark u‖^2:=by
    rw [actual_rows_sum]
    apply Finset.sum_congr rfl
    intro u hu
    have hn:=norm_of_oriented_coefficients (F.family u F.label)
      (F.rowData.character (actualRow u)) F.reverse (F.row_coeff u hu)
      true W (U^F.r) σ freq (Real.rpow_pos_of_pos hU0 _)
    rw [norm_mul,hn,physicalProduct_eq,norm_mul]
    rfl
  rw [he]
  apply (marked_fixed_deletion F.rowData (F.rows.image actualRow)
    (orientedProfile F.reverse W) (U^F.r) σ (orientedFrequency F.reverse freq) bW
    (Real.rpow_pos_of_pos hU0 _) hw mark).trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [actual_rows_sum]
  apply Finset.sum_congr rfl
  intro u hu
  have hjpos:0<(j.absNorm:ℝ):=zero_lt_one.trans_le (excluded_divisor_norm F.rowData j hj).1
  have hr:U^(shiftedExponent F.rowData U F.r j)=U^F.r/(j.absNorm:ℝ):=
    by rw [shiftedExponent,Real.rpow_sub hU0,Real.rpow_logb hU0 (ne_of_gt hU) hjpos]
  have hn:=deleted_physical_slots_norm_initial F.rowData (actualRow u) M H
    (orientedProfile F.reverse W) (fun s:selected=>F.profile s)
    U (shiftedExponent F.rowData U F.r j) σ (orientedFrequency F.reverse freq) bW
    (fun s:selected=>lower s) (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
    (fun s:selected=>F.external s) hU0 hw (fun s=>hV s s.property)
    (fun s=>hlarge s s.property)
  rw [hr] at hn
  exact congrArg (fun x:ℝ=>x^2) hn

 theorem fiber_child_rows_le_deleted_sources
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(selected:Finset Slot)
    (W:ℝ→ℂ)(v bW:ℝ)(lower:Slot→ℝ)(hU:1<U)
    (hW:∀x,W x≠0→x≤bW)
    (hV:∀s∈selected,∀x,F.profile s x≠0→x∈Set.Icc (lower s) (F.upper s))
    (hlarge:∀s∈selected,((deletedBase F.rowData).modulus.absNorm:ℝ)<lower s*U^(F.widths s)):
    (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest W v) (U^F.r) 0 0*
      F.physicalProduct selected u‖^2)≤
      ((idealDivisors (∏P∈excluded F.rowData,P)).card:ℝ)*
        ∑j∈idealDivisors (∏P∈excluded F.rowData,P),∑u∈F.rows,
          ‖deletedSelectedSource F.rowData M H
            (childLogTest (orientedProfile F.reverse W) (orientedFrequency F.reverse v))
            (fun s:selected=>F.profile s) U (shiftedExponent F.rowData U F.r j)
            0 0 bW (fun s:selected=>F.upper s) (fun s:selected=>F.widths s)
            (fun s:selected=>F.external s) u.val‖^2:=by
  have hw:∀x,childLogTest W v x≠0→x≤bW:=by
    intro x hx
    apply hW x
    intro hz
    exact hx (by simp only [childLogTest,hz,zero_mul])
  have hh:=fiber_rows_le_deleted_sources F selected (childLogTest W v) 0 0 bW lower hU hw hV hlarge
  simpa only [oriented_child,orientedFrequency,neg_zero,ite_self] using hh

omit [NeZero M] in
theorem actual_rows_norm (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (u:NonzeroElement)(hu:u∈F.rows.image actualRow):
    ((Ideal.span {u.val}).absNorm:ℝ)≤U:=by
  obtain ⟨v,hv,rfl⟩:=Finset.mem_image.mp hu
  exact F.row_norm v hv

end SevenEighths.DetectorDictionaryInverseMarkedPhysicalRows

end

end OAI
end OAIOriginalModule2534

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialMarkedAssignedGeometry
Source SHA256: 39ef7061ab2fb5b2d40952f1f84537806b5134169fbf0f9f3b1c5b8f2cb38f1a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2535



namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialMarkedAssignedGeometry
open HeckeFamily ConcretePrimeRowBridge
open DetectorDictionaryInverseMarkedReference InverseInitialQuotientGeometry
local notation "O"=>HeckeFamily.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

 def assignedGenerator (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)(i:ι):O:=
  if h:i∈J then idealGenerator (x ⟨i,h⟩).val else 1

omit [Fintype ι] in
 theorem assignedGenerator_mem (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):assignedGenerator L J x i=idealGenerator (x ⟨i,hi⟩).val:=by
  simp only [assignedGenerator,dite_eq_left hi]

omit [Fintype ι] in
 theorem assignedGenerator_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (i:ι)(hi:i∈J):Ideal.span {assignedGenerator L J x i}=(x ⟨i,hi⟩).val:=by
  rw [assignedGenerator_mem L J x i hi,span_idealGenerator]

omit [Fintype ι] in
 theorem assignedGenerator_ne_zero (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (hne:∀i∈J,∀P∈L i,P≠0)(i:ι)(hi:i∈J):assignedGenerator L J x i≠0:=by
  rw [assignedGenerator_mem L J x i hi]
  exact idealGenerator_ne_zero _ (hne i hi _ (x ⟨i,hi⟩).property)

omit [Fintype ι] in
 theorem assignedElement_span (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J):
    Ideal.span {assignedElement J (assignedGenerator L J x)}=assignedIdeal L J x:=by
  rw [assignedElement,FiniteGaussPhase.span_finset_prod,←Finset.prod_coe_sort]
  unfold assignedIdeal
  apply Finset.prod_congr rfl
  intro i hi
  exact assignedGenerator_span L J x i.val i.property

omit [Fintype ι] in
 theorem assignedGenerator_window_live (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(ell:ι→ℝ)(W:ι→ℝ→ℂ)
    (hW:∀i∈J,∀P∈L i,W i ((P.absNorm:ℝ)/U^(ell i))≠0):
    ∀i∈J,W i ((Ideal.absNorm (Ideal.span {assignedGenerator L J x i}):ℝ)/U^(ell i))≠0:=by
  intro i hi
  rw [assignedGenerator_span L J x i hi]
  exact hW i hi _ (x ⟨i,hi⟩).property

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_product (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ):
    (Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell)=
      ∏i:↥J,((x i).val.absNorm:ℝ)/U^(ell i.val):=by
  simp only [assignedIdeal,map_prod,Nat.cast_prod,Finset.prod_div_distrib,
    ←Real.rpow_sum_of_pos hU,Finset.sum_coe_sort,assignedCenter]

omit [Fintype ι] [DecidableEq ι] in
 theorem assigned_ratio_interval (L:ι→Finset (Ideal O))(J:Finset ι)(x:Assigned L J)
    (U:ℝ)(hU:0<U)(ell:ι→ℝ)(K:ℕ)(hK:J.card≤K)
    (hL:∀i∈J,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2):
    ((Ideal.absNorm (assignedIdeal L J x):ℝ)/U^(assignedCenter J ell))∈Set.Icc (1:ℝ) ((2:ℝ)^K):=by
  rw [assigned_ratio_product L J x U hU ell]
  constructor
  · have hh:=Finset.prod_le_prod₀ (s:=Finset.univ)
      (f:=fun _i:↥J=>(1:ℝ)) (g:=fun i=>((x i).val.absNorm:ℝ)/U^(ell i.val))
      (fun _ _=>zero_le_one) (fun i _=>(hL i.val i.property _ (x i).property).1)
    simpa only [Finset.prod_const_one] using hh
  · calc
      _≤∏_i:↥J,(2:ℝ):=Finset.prod_le_prod₀
        (fun i _=>(zero_le_one.trans (hL i.val i.property _ (x i).property).1))
        (fun i _=>(hL i.val i.property _ (x i).property).2)
      _=(2:ℝ)^J.card:=by simp
      _≤(2:ℝ)^K:=pow_le_pow_right₀ (by norm_num) hK

end SevenEighths.InverseInitialMarkedAssignedGeometry

end

end OAI
end OAIOriginalModule2535

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferenceSourceEnergy
Source SHA256: 72a58db1108aaaf0473ef1bf9e36c257f1ae1059057eb10f8e4806c26481d76d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2536








namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure
open InverseInitialMarkedAssignedGeometry DetectorDictionaryInverseRawConjugateGates
local notation "O"=>HeckeFamily.O

private theorem assigned_admissible {ι:Type}[Fintype ι][DecidableEq ι]
    (L:ι→Finset (Ideal O))(hp:∀i,∀P∈L i,Prime P)
    (hs:∀i,∀P∈L i,Supported P)
    (hdis:((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)
    (J:Finset ι)(x:Assigned L J):Admissible (assignedIdeal L J x) := by
  apply tuple_admissible (fun i:↥J=>L i.val)
    (fun i=>hp i.val) (fun i=>hs i.val) _ x
  intro i hi j hj hij
  exact hdis (Finset.mem_univ _) (Finset.mem_univ _)
    (fun he=>hij (Subtype.ext he))

theorem original_source_energy
    (W:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (gap eps π eta τ loss:ℝ)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (heta:0<eta)(hetaone:eta≤1)(hetagap:eta≤gap/50)
    (hτ:0<τ)(hτgap:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∀q:ℕ,q≠0→∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U→(2:ℝ)^K≤U^eta→
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K→
    ∀(L:ι→Finset (Ideal O))(ell:ι→ℝ)(coeff:ι→Ideal O→ℂ),
      (∀i,0≤ell i)→(∀i,∀P∈L i,Prime P)→
      (∀i,∀P∈L i,Supported P)→
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L)→
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,‖coeff i P‖≤1)→
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P)→
    ∀(primeW:ι→ℝ→ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2)→
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀I,‖χ I‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ))→
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I→
        conjugateIdealCharacter χ I=0)→
    ∀m r:ℝ,0≤m→m≤2→
      (∀J:Finset ι,-2≤r+(∑i,ell i)-2*(∑i∈J,ell i))→
      r+2*(∑i,ell i)≤m-2*gap→2*r+8*(∑i,ell i)≤3*m-2*gap→
      r+(∑i,ell i)+7*eta≤2→
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U^m)→∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U r bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U r (∑i,ell i) u‖^2)≤
      C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc ao bo := by
    intro x hx
    exact hsW (by simpa using hx)
  obtain ⟨degree,henergy⟩:=InverseInitialResidualUniformEnergy.original_residual_uniform_energy
    (fun x=>star (W x)) ao bo hao hab hsstar (Complex.conjCLE.contDiff.comp hW)
    DetectorDictionaryInverseMarkedPadding.radialMajorant
    DetectorDictionaryInverseMarkedPadding.radialMajorant_nonneg
    DetectorDictionaryInverseMarkedPadding.radialMajorant_one
    2 gap eps π eta τ loss (by norm_num) hgap heps hπ heta hetaone hetagap hτ hτgap hloss K
  refine ⟨degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  let A:ℝ:=((2:ℝ)^K*DetectorDictionaryInverseAssignedCount.assignedConstant K 2)^2
  have hA:0<A:=sq_pos_of_pos (mul_pos (by positivity)
    (DetectorDictionaryInverseAssignedCount.assignedConstant_pos K (by norm_num)))
  refine ⟨A*C,U₀,mul_pos hA hC,hU₀,?_⟩
  intro U hU hpow ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero m r hm hmcap hD hfirst hsecond hparent rows hrows θ
  have hUone:1<U:=hU₀.trans_le hU
  have hUpos:0<U:=zero_lt_one.trans hUone
  have hscale (i:ι):0<U^(ell i):=Real.rpow_pos_of_pos hUpos _
  have hnorm (i:ι)(P:Ideal O)(hP:P∈L i):(P.absNorm:ℝ)≤2*U^(ell i):=
    (div_le_iff₀ (hscale i)).mp (hratio i P hP).2
  let E:ℝ:=C*U^(m+15*eta+π+eps+loss)*((1+‖θ‖)^degree)^2
  have hE:0≤E:=by dsimp [E];positivity
  have hres (J:Finset ι)(x:Assigned L J):
      (∑u∈rows,(1:ℝ)*‖remainingPolynomial (originalSource U r bo) L J x coeff χ
        (childLogTest W θ) U r (∑i,ell i) (∑i∈J,ell i) u‖^2)≤E := by
    have hJ:J.card≤K:=(Finset.card_le_univ J).trans hK
    have hH (i:ι):1≤2*U^(ell i) := by
      have hh:=Real.one_le_rpow hUone.le (hell i)
      linarith
    have hprod (T:Finset ι):
        (∏i∈T,2*U^(ell i))≤U^((∑i∈T,ell i)+eta) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,←Real.rpow_sum_of_pos hUpos,
        Real.rpow_add hUpos]
      rw [mul_comm (U^(∑i∈T,ell i))]
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hUpos.le _)
      exact (pow_le_pow_right₀ (by norm_num) ((Finset.card_le_univ T).trans hK)).trans hpow
    have hje:Admissible (assignedIdeal L J x):=assigned_admissible L hp hs hdis J x
    have hh:=henergy U hU Finset.univ J (Finset.subset_univ _) (by simpa using hK)
      L (fun i=>2*U^(ell i)) (fun i P=>star (coeff i P)) hdis
      (fun i _=>hH i) (fun i _=>hnorm i)
      (fun i _ P hP=>by simpa using hc i P hP)
      (assignedGenerator L J x) ell (fun _=>1) (fun _=>2) primeW
      (fun i _=>hell i)
      (assignedGenerator_ne_zero L J x (fun i _ P hP=>(hp i P hP).ne_zero))
      (fun i _=>hprimeW i) (assignedGenerator_window_live L J x U ell primeW (fun i _=>hlive i))
      (conjugateIdealCharacter χ)
      (fun u=>by simpa [elementCharacter,conjugateIdealCharacter] using hχ (Ideal.span {u}))
      hperiod hzero (r+(∑i,ell i)-2*(∑i∈J,ell i)) m r hm hmcap (hD J)
      (by simpa using (pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hJ).trans hpow)
      (by simpa [assignedCenter] using hprod (Finset.univ\J))
      rfl (by simpa [assignedCenter] using hfirst) (by simpa [assignedCenter] using hsecond)
      (by simpa [assignedCenter] using hparent) rows hrows (assignedIdeal L J x) hje
      (assignedElement_span L J x)
      (assigned_ratio_interval L J x U hUpos ell K hJ (fun i _=>hratio i))
      (fun i _=>hp i) (fun i _ P hP _=>hratio i P hP)
      (remaining_tuple_admissible L hp hs hdis J x)
      (remaining_tuple_coprime L hp hdis J)
      (remaining_tuple_outside L (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
        hout J x) (-θ)
    simpa only [one_mul,remainingPolynomial_original_pi,childLogTest_conjugate,
      assignedCenter,norm_neg,E] using hh
  have hb:=original_energy_with_assigned_count K (by norm_num : (1:ℝ)≤2) hUone.le hK
    (originalSource U r bo) L hp hdis ell (fun i P hP=>⟨(hp i P hP).ne_zero,hnorm i P hP⟩)
    coeff hc χ (assigned_admissible L hp hs hdis) (fun J x=>hχ _)
    (childLogTest W θ) r (∑i,ell i) rows (fun _=>1) (fun _=>zero_le_one) E hE hres
  simpa only [one_mul,E,A,mul_assoc] using hb

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2536

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseMarkedReferencePaddedEnergy
Source SHA256: e42a888cc31fdd5ca02bbd99fca6ee3d64d8844efaffd9c1067bda0e94e38981
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2537


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff Topology
namespace SevenEighths.DetectorDictionaryInverseMarkedReference
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCoefficientClass ConcreteTraceCRT InverseInitialRayAttachment InverseMoment InverseInitialProfile
open InverseInitialOverlapFourier InverseInitialConjugateEnergy InverseInitialQuotientGeometry
open InverseInitialEnergyCallerWindow InverseInitialPoissonBridge InverseInitialPhysicalMeasure Filter
local notation "O"=>HeckeFamily.O

theorem padded_source_energy
    (W:ℝ → ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hsW:Function.support W⊆Set.Icc ao bo)(hW:ContDiff ℝ ∞ W)
    (εm:ℝ)(hεm:0<εm)(K:ℕ):
    ∃eta:ℝ,0<eta ∧ ∃degree:ℕ,∀q:ℕ,q≠0 → ∃C U₀:ℝ,0<C ∧ 1<U₀ ∧
    ∀U:ℝ,U₀≤U →
    ∀{ι:Type}[Fintype ι][DecidableEq ι],Fintype.card ι≤K →
    ∀(L:ι → Finset (Ideal O))(ell:ι → ℝ)(coeff:ι → Ideal O → ℂ),
      (∀i,0≤ell i) → (∀i,∀P∈L i,Prime P) →
      (∀i,∀P∈L i,Supported P) →
      (((Finset.univ:Finset ι):Set ι).PairwiseDisjoint L) →
      (∀i,∀P∈L i,((P.absNorm:ℝ)/U^(ell i))∈Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,‖coeff i P‖≤1) →
      (∀i,∀P∈L i,InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) P) →
    ∀(primeW:ι → ℝ → ℂ),
      (∀i,Function.support (primeW i)⊆Set.Icc (1:ℝ) 2) →
      (∀i,∀P∈L i,primeW i ((P.absNorm:ℝ)/U^(ell i))≠0) →
    ∀χ:Ideal O →*ℂ,(∀I,‖χ I‖≤1) →
      FactorsModulo (fixedBaseConductor q) (elementCharacter (conjugateIdealCharacter χ)) →
      (∀I,¬InverseInitialExcludedPool.outside (reflectionExcludedPrimes q) I →
        conjugateIdealCharacter χ I=0) →
    ∀r rr:ℝ,0≤r → r-eta≤rr → rr≤r →
      r+2*(∑i,ell i)<1 → 2*r+8*(∑i,ell i)<3 →
    ∀rows:Finset O,(∀u∈rows,‖eisEmbedding u‖^2≤U) → ∀θ:ℝ,
      (∑u∈rows,‖∑x:Tuple L,(∏i,coeff i (x i).val)*
        originalTotalPolynomial (originalSource U rr bo) (∏i,(x i).val) χ (fun _=>1)
          (childLogTest W θ) U rr (∑i,ell i) u‖^2)≤
      C*U^(1+εm)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨ρ,gap,eta,τ,π,eps,loss,hρ,hρmax,hρε,hgap,hgapρ,heta,hetamax,hetagap,
    hτ,hτgap,hπ,heps,hloss,hcost⟩:=InverseInitialMarkedReserve.exists_reserve εm hεm
  obtain ⟨degree,henergy⟩:=original_source_energy W ao bo hao hab hsW hW
    gap eps π eta τ loss hgap heps hπ heta (by linarith) hetagap hτ hτgap hloss K
  have hev:∀ᶠU:ℝ in atTop,(2:ℝ)^K≤U^eta:=
    (tendsto_rpow_atTop heta).eventually (eventually_ge_atTop _)
  obtain ⟨Uscale,hscale⟩:=eventually_atTop.mp hev
  refine ⟨eta,heta,degree,?_⟩
  intro q hq
  obtain ⟨C,U₀,hC,hU₀,henergy⟩:=henergy q hq
  refine ⟨C,max U₀ Uscale,hC,lt_max_of_lt_left hU₀,?_⟩
  intro U hU ι inst dec hK L ell coeff hell hp hs hdis hratio hc hout primeW hprimeW hlive
    χ hχ hperiod hzero r rr hr hrlo hrhi hfirst hsecond rows hrows θ
  have hU0:U₀≤U:=(le_max_left _ _).trans hU
  have hUone:1<U:=hU₀.trans_le hU0
  have hs0:0≤∑i,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hG (J:Finset ι):0≤∑i∈J,ell i:=Finset.sum_nonneg (fun i _=>hell i)
  have hGmax (J:Finset ι):(∑i∈J,ell i)≤∑i,ell i:=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)
  have hcap (J:Finset ι):
      0≤1+ρ ∧ 1+ρ≤2 ∧ -2≤rr+(∑i,ell i)-2*(∑i∈J,ell i) ∧
      rr+2*(∑i,ell i)≤1+ρ-2*gap ∧
      2*rr+8*(∑i,ell i)≤3*(1+ρ)-2*gap ∧ rr+(∑i,ell i)+7*eta≤2 :=
    InverseInitialMarkedReserve.shifted_capacity ρ gap eta r rr _ _ hρ hρmax hgapρ
      heta hetamax hr hs0 (hG J) (hGmax J) hrlo hrhi hfirst hsecond
  have hbase:=hcap ∅
  have hrows':∀u∈rows,‖eisEmbedding u‖^2≤U^(1+ρ) := by
    intro u hu
    refine (hrows u hu).trans ?_
    calc U=U^(1:ℝ):=(Real.rpow_one U).symm
         _≤U^(1+ρ):=Real.rpow_le_rpow_of_exponent_le hUone.le (by linarith)
  have hh:=henergy U hU0 (hscale U ((le_max_right _ _).trans hU)) hK L ell coeff hell hp hs
    hdis hratio hc hout primeW hprimeW hlive χ hχ hperiod hzero (1+ρ) rr
    hbase.1 hbase.2.1 (fun J=>(hcap J).2.2.1) hbase.2.2.2.1 hbase.2.2.2.2.1
    hbase.2.2.2.2.2 rows hrows' θ
  refine hh.trans ?_
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  apply mul_le_mul_of_nonneg_left _ hC.le
  apply Real.rpow_le_rpow_of_exponent_le hUone.le
  linarith

end SevenEighths.DetectorDictionaryInverseMarkedReference

end

end OAI
end OAIOriginalModule2537

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySupport
Source SHA256: 4f4ed7590dc3d5ceb78ef2ad3aaa673ee6efc41c5b884b18b545aafcea4be38a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2538



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma annular_prime_coprime (η : Character) (a D : ℝ) (ha : 0<a) (hD : 0<D)
    (hlarge : (η.modulus.absNorm:ℝ)/a<D)
    (W : ℝ→ℂ) (hs : Function.support W⊆Set.Ici a)
    (P : Ideal O) (hp : Prime P) (hW : W ((P.absNorm:ℝ)/D)≠0) :
    IsCoprime P η.modulus := by
  apply ProbeRaySlots.prime_coprime_of_norm_gt η ⟨P,hp⟩
  have hlo : a*D≤(P.absNorm:ℝ) := (le_div_iff₀ hD).mp (hs hW)
  have hh : (η.modulus.absNorm:ℝ)<a*D := by
    have hh := (div_lt_iff₀ ha).mp hlarge
    nlinarith
  exact hh.trans_le hlo

theorem eventually_primePool_coprime (η : Character) (a : ℝ) (ha : 0<a) :
    ∀ᶠD : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus := by
  filter_upwards [eventually_gt_atTop (0:ℝ),eventually_gt_atTop ((η.modulus.absNorm:ℝ)/a)] with D hD hlarge
  intro M H W b hs P hP hW
  exact annular_prime_coprime η a D ha hD hlarge W hs P (Finset.mem_filter.mp hP).2.1 hW

theorem eventually_primePool_power_coprime (η : Character) (a ell : ℝ) (ha : 0<a) (hell : 0<ell) :
    ∀ᶠZ : ℝ in atTop,∀(M : Ideal O)(H : Subgroup (O⧸M)ˣ)(W : ℝ→ℂ)(b : ℝ),
      Function.support W⊆Set.Ici a →
      ∀P∈primePool M H b (Z^ell),W ((P.absNorm:ℝ)/(Z^ell))≠0→IsCoprime P η.modulus :=
  (tendsto_rpow_atTop hell).eventually (eventually_primePool_coprime η a ha)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2538

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralSlots
Source SHA256: 18d547251edc7de4f56eaa64fac728d85f15be12ae1e8fc14b0b2b193f60aa61
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2539




namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

lemma row_phase_norm_one_of_not_dvd (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) :
    ‖idealRowHom u.val P.val‖=1 := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hg := supported_prime_data p hp (hspan.symm ▸ hs)
  have hnot : ¬p∣u.val := by
    intro hd
    apply hn
    rw [Ideal.dvd_iff_le,←hspan,Ideal.span_singleton_le_span_singleton]
    exact hd
  have hu : IsCoprime u.val p := (hp.irreducible.coprime_iff_not_dvd.mpr hnot).symm
  have he : idealRowHom u.val P.val=actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ u.val) := by
    rw [←hspan,idealRowHom_prime u.val (Ideal.span {p}) hg.1]
  rw [he]
  exact Complex.norm_eq_one_of_pow_eq_one (actualSextic_unit_six p u.val hg.1 hg.2 hu) (by decide)

theorem actual_central_unramified_error (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (4:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w))+
      idealUnramifiedCorrection η u P x w z*star (idealRowHom u.val P.val)‖≤
        720*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hV : ‖coordV P.val.absNorm z‖<1 := by
    rw [coordV_norm _ hQ0]
    exact (rpow_le_half _ _ hQ (by rw [hz];norm_num)).trans_lt (by norm_num)
  have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
    (coordR_norm_le _ hQ0 _ x z (actualAPhase_norm_le_one η _)).trans_lt
      ((rpow_le_half _ _ hQ (by rw [hx,hz];linarith)).trans_lt (by norm_num))
  rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
  exact unramifiedSelected_central_error _ a e _ _ _ x w z hQ ha ha1 he he1
    (actualAPhase_norm_le_one η _)
    (PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη)
    (row_phase_norm_one_of_not_dvd u P hs hn) hx hw hz

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2539

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralNormalized
Source SHA256: 0a8731c99e036e8d654681925166f7178f1ae1ffe5a772dcee41080388ec41ac
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2540



namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeLocal
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge

theorem actual_central_unramified_normalized (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hn : ¬P.val∣Ideal.span {u.val}) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖idealUnramifiedCorrection η u P x w z‖ ∧
    ‖continuedCompensatedLocal η u P hs x w z
        (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
      idealUnramifiedCorrection η u P x w z+star (idealRowHom u.val P.val)‖≤
        1440*(P.val.absNorm:ℝ)^(-(51/100:ℝ)) := by
  have heta := PrincipalSignalComparison.idealCoeff_norm_one_of_coprime η P.val P.property.ne_zero hη
  have hv := row_phase_norm_one_of_not_dvd u P hs hn
  have hA := actualAPhase_norm_le_one η (primaryGenerator P.val)
  constructor
  · exact unramifiedClosed_central_lower _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta.le hv.le hx hw hz
  · have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
    have hV : ‖coordV P.val.absNorm z‖<1 := by
      rw [coordV_norm _ hQ0]
      exact (rpow_le_half _ _ (by linarith) (by rw [hz];norm_num)).trans_lt (by norm_num)
    have hR : ‖coordR P.val.absNorm (actualAPhase η (primaryGenerator P.val)) x z‖<1 :=
      (coordR_norm_le _ hQ0 _ x z hA).trans_lt
        ((rpow_le_half _ _ (by linarith) (by rw [hx,hz];linarith)).trans_lt (by norm_num))
    rw [continuedCompensatedLocal_unramified η u P hs hn x w z hV hR]
    exact unramifiedSelected_central_quotient _ a e _ _ _ x w z hQ ha ha1 he he1 hA heta hv hx hw hz
end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2540

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralSplit
Source SHA256: ad58dffec12b6f266030ae79073365ff6c5f6f12b75e7dd6f77170c6b8fb6862
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2541




namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss

def centralNormalizedSlot (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  continuedCompensatedLocal η u P hs x w z
    (star (idealCoeff η P.val)*(P.val.absNorm:ℂ)^x) ((P.val.absNorm:ℂ)^(-w)) /
    supportedCorrection η u P x w z

def repeatedRowPrime (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : Prop :=
  P.val∣Ideal.span {u.val} ∧ 2≤multiplicity (primaryGenerator P.val) u.val

def centralRegularError (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then 0 else
    centralNormalizedSlot η u P hs x w z+star (idealRowHom u.val P.val)

def centralRepeatedTerm (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : ℂ :=
  if repeatedRowPrime u P then centralNormalizedSlot η u P hs x w z else 0

theorem centralNormalizedSlot_split (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=
      -star (idealRowHom u.val P.val)+centralRegularError η u P hs x w z+
        centralRepeatedTerm η u P hs x w z := by
  by_cases hp : repeatedRowPrime u P
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_left hp,row_phase_ramified u P hp.1,
      star_zero,neg_zero,zero_add]
  · simp only [centralRegularError,centralRepeatedTerm,ite_eq_right hp]
    ring

theorem central_actual_local_bounds (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e : ℝ) (x w z : ℂ) (hQ : (480:ℝ)≤P.val.absNorm)
    (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50) :
    1/2≤‖supportedCorrection η u P x w z‖ ∧
    ‖centralRegularError η u P hs x w z‖≤
      1440*(if P.val∣Ideal.span {u.val} then (P.val.absNorm:ℝ)^(1/2:ℝ)
        else (P.val.absNorm:ℝ)^(-(51/100:ℝ))) ∧
    ‖centralRepeatedTerm η u P hs x w z‖≤
      if repeatedRowPrime u P then 812*(P.val.absNorm:ℝ)^(1-w.re) else 0 := by
  have hQ0 : (0:ℝ)<P.val.absNorm := by linarith
  have hQ1 : (1:ℝ)≤P.val.absNorm := by linarith
  by_cases hd : P.val∣Ideal.span {u.val}
  · have hb := actual_central_ramified_normalized η u P hs hd (by linarith)
      a e x w z hsmall ha ha1 he he1 hx hw hz
    have hcorr : supportedCorrection η u P x w z=ramifiedCorrection η u P hs x w z := by
      simp [supportedCorrection,hs,hd]
    refine ⟨hcorr.symm ▸ hb.1,?_,?_⟩
    · by_cases hj : 2≤multiplicity (primaryGenerator P.val) u.val
      · simp [centralRegularError,repeatedRowPrime,hd,hj]
        positivity
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        rw [centralRegularError,ite_eq_right hp,row_phase_ramified u P hd,star_zero,add_zero,ite_eq_left hd]
        have h := hb.2
        simp only [ite_eq_right hj,add_zero] at h
        have hn : ‖centralNormalizedSlot η u P hs x w z‖≤800*(P.val.absNorm:ℝ)^(1/2:ℝ) := by
          dsimp only [centralNormalizedSlot]
          rw [hcorr]
          have hm := mul_le_mul_of_nonneg_left h hQ0.le
          have hpow : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
            rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
          have hp2 : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-(1/2:ℝ))=
              (P.val.absNorm:ℝ)^(1/2:ℝ) := by
            conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
            rw [←Real.rpow_add hQ0];norm_num
          rw [←mul_assoc,hpow,one_mul] at hm
          rw [mul_left_comm (P.val.absNorm:ℝ) 800,hp2] at hm
          exact hm
        exact hn.trans (mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hQ0.le _))
    · by_cases hj : 2≤multiplicity (primaryGenerator P.val) u.val
      · have hp : repeatedRowPrime u P := ⟨hd,hj⟩
        rw [centralRepeatedTerm,ite_eq_left hp,ite_eq_left hp]
        have h := hb.2
        rw [ite_eq_left hj] at h
        have hpow : (P.val.absNorm:ℝ)^(-(1/2:ℝ))≤(P.val.absNorm:ℝ)^(-w.re) := by
          apply Real.rpow_le_rpow_of_exponent_le hQ1
          rw [hw];linarith
        have hn : (P.val.absNorm:ℝ)^(-1:ℝ)*‖centralNormalizedSlot η u P hs x w z‖≤
            812*(P.val.absNorm:ℝ)^(-w.re) := by
          dsimp only [centralNormalizedSlot];rw [hcorr]
          nlinarith
        have hm := mul_le_mul_of_nonneg_left hn hQ0.le
        have hi : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-1:ℝ)=1 := by
          rw [Real.rpow_neg_one];exact mul_inv_cancel₀ hQ0.ne'
        have heq : (P.val.absNorm:ℝ)*(P.val.absNorm:ℝ)^(-w.re)=
            (P.val.absNorm:ℝ)^(1-w.re) := by
          conv_lhs => lhs;rw [←Real.rpow_one (P.val.absNorm:ℝ)]
          rw [←Real.rpow_add hQ0]; congr 1
        rw [←mul_assoc,hi,one_mul] at hm
        rw [mul_left_comm (P.val.absNorm:ℝ) 812,heq] at hm
        exact hm
      · have hp : ¬repeatedRowPrime u P := fun h=>hj h.2
        simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
  · have hb := actual_central_unramified_normalized η u P hs hd hη a e x w z hQ
      ha ha1 he he1 hx hw hz
    have hc : supportedCorrection η u P x w z=idealUnramifiedCorrection η u P x w z := by
      simp [supportedCorrection,hs,hd]
    have hp : ¬repeatedRowPrime u P := fun h=>hd h.1
    refine ⟨hc.symm ▸ hb.1,?_,?_⟩
    · simpa only [centralRegularError,ite_eq_right hp,centralNormalizedSlot,hc,ite_eq_right hd] using hb.2
    · simp only [centralRepeatedTerm,ite_eq_right hp,norm_zero,le_refl]
end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2541

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralRepeatedChoices
Source SHA256: e57ad907c7377ac6e942f7faf1dceae374abd2dea2df39a1b05edd603c7452a9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2542



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedChoices
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
local notation "O" => HeckeFamily.O

def activeChoices {k : ℕ} (u : FreeRow) (T : Fin k→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) : Finset (∀j,T j) :=
  Finset.univ.filter (fun P=>∀j,repeatedRowPrime u (P j).val ∧
    W j (((P j).val.val.absNorm:ℝ)/Y j)≠0)

lemma active_card_le_divisors {k : ℕ} (u : FreeRow) (T : Fin k→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) :
    (activeChoices u T W Y).card≤(IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card^k := by
  let U : Ideal O := Ideal.span {u.val}
  have hU : U≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  let f : activeChoices u T W Y→(Fin k→IdealMobiusDivisorSum.idealDivisors U) :=
    fun P j=>⟨(P.val j).val.val,(IdealMobiusDivisorSum.mem_idealDivisors hU).mpr
      (((Finset.mem_filter.mp P.property).2 j).1.1)⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    funext j
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun g=>(g j).val) h
  have hc := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe,Fintype.card_fun,Fintype.card_fin] using hc

theorem active_card_subpower (N : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀k : ℕ,k≤N → ∀(u : FreeRow) (T : Fin k→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
      (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      ((activeChoices u T W Y).card:ℝ)≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps := by
  let δ := eps/(N+1)
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨(max 1 D)^N,by positivity,?_⟩
  intro k hk u T W Y
  have hU : (Ideal.span {u.val}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  have hU1 : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hU)
  have hd := hdiv (Ideal.span {u.val}) hU
  have hcard : ((activeChoices u T W Y).card:ℝ)≤
      ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := by
    exact_mod_cast active_card_le_divisors u T W Y
  have hpow : D^k≤(max 1 D)^N :=
    (pow_le_pow_left₀ hD.le (le_max_right 1 D) k).trans (pow_le_pow_right₀ (le_max_left 1 D) hk)
  have hke : δ*k≤eps := by
    have hn : (k:ℝ)≤N := by exact_mod_cast hk
    have he : δ*(N+1)=eps := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ ((IdealMobiusDivisorSum.idealDivisors (Ideal.span {u.val})).card:ℝ)^k := hcard
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^δ)^k := pow_le_pow_left₀ (by positivity) hd k
    _ = D^k*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(δ*k) := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul (by positivity)]
    _ ≤ _ := mul_le_mul hpow (Real.rpow_le_rpow_of_exponent_le hU1 hke)
      (by positivity) (by positivity)

lemma sum_products_restrict {k : ℕ} (η : Character) (u : FreeRow)
    (T : Fin k→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀j P,P∈T j→CanonicalQuadraticSieve.Supported P.val)
    (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ) (x w z : ℂ) :
    (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hT j P.val P.property) x w z‖)=
    ∑P∈activeChoices u T W Y,∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u (P j).val (hT j (P j).val (P j).property) x w z‖ := by
  rw [Fintype.prod_sum]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro P _ hp
  have hn : ¬∀j,repeatedRowPrime u (P j).val ∧ W j (((P j).val.val.absNorm:ℝ)/Y j)≠0 := by
    simpa only [activeChoices,Finset.mem_filter,Finset.mem_univ,true_and] using hp
  push Not at hn
  obtain ⟨j,hj⟩ := hn
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  by_cases hr : repeatedRowPrime u (P j).val
  · simp [hj hr]
  · simp [centralRepeatedTerm,hr]
end SevenEighths.ProbeCentralRepeatedChoices

end

end OAI
end OAIOriginalModule2542

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralProduct
Source SHA256: c0213a7d86d447ddef6abf4c0f7eefc1cbc8aa7bb6b9f948cc6c4d63d675788b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2543



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

def centralRowScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  (star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x))*
    continuedCorrection S hS η u x w z

theorem calibratedTupleValue_central {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i,(480:ℝ)≤(P i).val.absNorm)
    (hη : ∀i,IsCoprime (P i).val η.modulus)
    (hsmall : ∀i,198*((P i).val.absNorm:ℝ)^(-10*e)≤1/2) :
    calibratedTupleValue S hS hmax η u P hPS W Y x w z=
      centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.absNorm:ℝ)/Y i)*((P i).val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i) (outside_prime_supported S hS.bad (P i) (hPS i)) x w z := by
  have hrestore := continuedCorrection_restore (4*e) S hS htail (Finset.univ.image P)
    (tupleOutside S P hPS) η u x w z (by rw [hx];linarith) (by rw [hz])
    (by rw [hw];linarith) (by rw [hx,hw];linarith)
  rw [Finset.prod_image hP.injOn] at hrestore
  have hn : (∏i,supportedCorrection η u (P i) x w z)≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _ hz0
    have h := (central_actual_local_bounds η u (P i)
      (outside_prime_supported S hS.bad (P i) (hPS i)) (hη i) a e x w z
      (hQ i) (hsmall i) ha ha1 he he1 hx hw hz).1
    rw [hz0,norm_zero] at h
    norm_num at h
  rw [calibratedTupleValue_factor S hS hmax η u P hP hPS W Y x w z]
  unfold centralRowScalar centralNormalizedSlot
  rw [hrestore]
  simp only [Finset.prod_mul_distrib,Finset.prod_div_distrib]
  field_simp

theorem calibrated_prime_slots_separate {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
        ∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val
            (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z := by
  calc
    _ = ∑P:(∀i,T i),centralRowScalar S hS hmax η u x w z*
        ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u (P i).val
            (outside_prime_supported S hS.bad (P i).val (hPS i (P i).val (P i).property)) x w z := by
      apply Finset.sum_congr rfl
      intro P _
      exact calibratedTupleValue_central S hS hmax η u (fun i=>(P i).val) (hdis P)
        (fun i=>hPS i (P i).val (P i).property) W Y a e x w z htail ha ha1 he he1 hx hw hz
        (fun i=>hQ i (P i).val (P i).property) (fun i=>hη i (P i).val (P i).property)
        (fun i=>hsmall i (P i).val (P i).property)
    _ = _ := by
      rw [←Finset.mul_sum]
      congr 1
      exact (Fintype.prod_sum (fun i (P:T i)=>W i ((P.val.val.absNorm:ℝ)/Y i)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z)).symm

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2543

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralExpansion
Source SHA256: 5e5996b77a2787123e4fe5361f08b1a04843e9c615614f5e191ad6d700bc308e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2544


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss CanonicalRowCompletion
local notation "O" => HeckeFamily.O

def centralBranch (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) : Fin 3→ℂ :=
  ![-star (idealRowHom u.val P.val),centralRegularError η u P hs x w z,
    centralRepeatedTerm η u P hs x w z]

theorem central_branch_sum (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    centralNormalizedSlot η u P hs x w z=∑b:Fin 3,centralBranch η u P hs x w z b := by
  simpa [centralBranch,Fin.sum_univ_three] using centralNormalizedSlot_split η u P hs x w z

theorem central_slots_branch_expansion {K : ℕ}
    (η : Character) (u : FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    (∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hT i P.val P.property) x w z)=
    ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralBranch η u P.val (hT i P.val P.property) x w z (b i) := by
  simp_rw [central_branch_sum,Finset.mul_sum]
  have hs (i : Fin K) :
      (∑P:T i,∑b:Fin 3,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b)=
      ∑b:Fin 3,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val (hT i P.val P.property) x w z b := Finset.sum_comm
  simp_rw [hs]
  exact Fintype.prod_sum _

theorem calibrated_central_branch_expansion {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (u : FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hPS : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (a e : ℝ) (x w z : ℂ)
    (htail : FirstTail (4*e) S) (ha : (51/100:ℝ)≤a) (ha1 : a≤1)
    (he : 0<e) (he1 : e≤1/1000) (hx : x.re=a+16*e)
    (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hQ : ∀i P,P∈T i→(480:ℝ)≤P.val.absNorm)
    (hη : ∀i P,P∈T i→IsCoprime P.val η.modulus)
    (hsmall : ∀i P,P∈T i→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) :
    (∑P:(∀i,T i),calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hPS i (P i).val (P i).property) W Y x w z)=
      centralRowScalar S hS hmax η u x w z*
      ∑b:Fin K→Fin 3,∏i,∑P:T i,W i ((P.val.val.absNorm:ℝ)/Y i)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralBranch η u P.val
          (outside_prime_supported S hS.bad P.val (hPS i P.val P.property)) x w z (b i) := by
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hdis W Y a e x w z
    htail ha ha1 he he1 hx hw hz hQ hη hsmall]
  congr 1
  exact central_slots_branch_expansion η u T
    (fun i P hP=>outside_prime_supported S hS.bad P (hPS i P hP)) W Y x w z
end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2544

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralBranchProduct
Source SHA256: 3020e59478bc1026778c48bccd6215b70b2a2099fa48a8c3a6b44253eb4a5dc3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2545


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralBranchProduct

theorem coupled_product_bound {ι : Type*} [Fintype ι]
    (L R : ℝ) (f g y : ι→ℝ) (hf : ∀i,0≤f i)
    (hsub : ∀J : Finset ι,L*(∏j ∈ J,g j)≤R*(∏j ∈ J,y j)) :
    L*(∏j : ι, (f j+g j))≤R*(∏j : ι, (f j+y j)) := by
  rw [Finset.prod_add,Finset.prod_add,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J hJ
  calc
    _ = (∏j ∈ J,f j)*(L*∏j ∈ Finset.univ\J,g j) := by ring
    _ ≤ (∏j ∈ J,f j)*(R*∏j ∈ Finset.univ\J,y j) :=
      mul_le_mul_of_nonneg_left (hsub _) (Finset.prod_nonneg (fun j _=>hf j))
    _ = _ := by ring

theorem three_branch_bound {N : ℕ} (L R E : ℝ)
    (A B T : Fin N→ℂ) (y p : Fin N→ℝ)
    (hL : 0≤L) (hR : 0≤R) (hE : 0≤E) (hy : ∀j,0≤y j) (hp : ∀j,1≤p j)
    (hA : ∀j,‖A j‖≤y j*p j) (hB : ∀j,‖B j‖≤y j*E)
    (hT : ∀J : Finset (Fin N),L*(∏j ∈ J,‖T j‖)≤R*(∏j ∈ J,y j)) :
    L*‖∏j : Fin N, (A j+B j+T j)‖≤R*(E+2)^N*(∏j : Fin N, y j)*(∏j : Fin N,p j) := by
  have hnorm : ‖∏j : Fin N, (A j+B j+T j)‖≤∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro j _
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hc := coupled_product_bound L R (fun j=>‖A j‖+‖B j‖) (fun j=>‖T j‖) y
    (fun j=>add_nonneg (norm_nonneg _) (norm_nonneg _)) hT
  have hpoint (j : Fin N) : (‖A j‖+‖B j‖)+y j≤y j*((E+2)*p j) := by
    have h := hp j
    have hp0 : 0≤p j := zero_le_one.trans h
    have he := mul_nonneg (show 0≤E+1 by linarith) (show 0≤p j-1 by linarith)
    have hm := mul_nonneg (hy j) he
    nlinarith [hA j,hB j]
  calc
    _ ≤ L*(∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖)) := mul_le_mul_of_nonneg_left hnorm hL
    _ ≤ R*(∏j : Fin N,((‖A j‖+‖B j‖)+y j)) := hc
    _ ≤ R*(∏j : Fin N, y j*((E+2)*p j)) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.prod_le_prod₀ (fun j _=>add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hy j)) (fun j _=>hpoint j)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin];ring
end SevenEighths.ProbeCentralBranchProduct

end

end OAI
end OAIOriginalModule2545

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralSlotSum
Source SHA256: c93e17cce027413068a5443715b78f516d3e27e0db4142ca30cb49508441289b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2546



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CompletedGauss
local notation "O" => HeckeFamily.O

theorem central_regular_slot_sum (eps c d B : ℝ) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
      (hT : ∀P∈T,Supported P.val ∧ (480:ℝ)≤P.val.absNorm ∧ IsCoprime P.val η.modulus)
      (Y : ℝ),1≤Y → ∀(W : ℝ→ℂ),Function.support W⊆Set.Icc c d →
      (∀y,‖W y‖≤B) → ∀(a e : ℝ) (x w z : ℂ),
      (51/100:ℝ)≤a → a≤1 → 0<e → e≤1/1000 →
      x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      (∀P∈T,198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∑P:T,‖W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*
        centralRegularError η u P.val (hT P.val P.property).1 x w z‖)≤
      C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*Y^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hbound⟩ := ProbeSelectedPrimeSums.weighted_slot_bound_indexed
    eps c d (-(4/25:ℝ)) 1 B 1440 heps hc hd (by norm_num) hB (by norm_num)
  refine ⟨C,hC,?_⟩
  intro η u T hT Y hY W hWS hWB a e x w z ha ha1 he he1 hx hw hz hsmall
  let f : T→Ideal O := fun P=>P.val.val
  have hf : Function.Injective f := fun P Q h=>Subtype.ext (Subtype.ext h)
  let E : T→ℂ := fun P=>centralRegularError η u P.val (hT P.val P.property).1 x w z
  let G : T→ℂ := fun P=>((f P).absNorm:ℂ)^(1/2:ℂ)*E P
  have hnorm (P : T) : ‖G P‖≤1440*(if f P∣Ideal.span {u.val} then ((f P).absNorm:ℝ)^(1:ℝ) else 1) := by
    have hQ : (480:ℝ)≤(f P).absNorm := (hT P.val P.property).2.1
    have hQ0 : (0:ℝ)<(f P).absNorm := by linarith
    have hQ1 : (1:ℝ)≤(f P).absNorm := by linarith
    have hb := (central_actual_local_bounds η u P.val (hT P.val P.property).1
      (hT P.val P.property).2.2 a e x w z hQ (hsmall P.val P.property) ha ha1 he he1 hx hw hz).2.1
    have hn : ‖((f P).absNorm:ℂ)^(1/2:ℂ)‖=((f P).absNorm:ℝ)^(1/2:ℝ) := by
      rw [show ((f P).absNorm:ℂ)=(((f P).absNorm:ℝ):ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hQ0];norm_num
    dsimp only [G]
    rw [norm_mul,hn]
    calc
      _ ≤ ((f P).absNorm:ℝ)^(1/2:ℝ)*(1440*(if f P∣Ideal.span {u.val} then
          ((f P).absNorm:ℝ)^(1/2:ℝ) else ((f P).absNorm:ℝ)^(-(51/100:ℝ)))) :=
        mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hQ0.le _)
      _ ≤ _ := by
        by_cases hp : f P∣Ideal.span {u.val}
        · simp only [ite_eq_left hp]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          norm_num
        · simp only [ite_eq_right hp,mul_one]
          rw [mul_left_comm,←Real.rpow_add hQ0]
          have hh : ((f P).absNorm:ℝ)^((1/2:ℝ)-(51/100:ℝ))≤1 := by
            exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : (1/2:ℝ)-51/100≤0)).trans_eq (Real.rpow_zero _)
          norm_num only [show (1/2:ℝ)+-(51/100:ℝ)=(1/2:ℝ)-(51/100:ℝ) by ring]
          nlinarith
  have hb := hbound f hf (Ideal.span {u.val}) (Ideal.span_singleton_eq_bot.not.mpr u.property.1)
    Y hY Finset.univ (fun P _=>P.val.property.ne_zero) W hWS hWB G (fun P _=>hnorm P)
    (z-1/2) (by simp only [Complex.sub_re];rw [hz];norm_num)
  have heq (P : T) :
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^((z-1/2)-1)*G P=
      W (((f P).absNorm:ℝ)/Y)*((f P).absNorm:ℂ)^(z-1)*E P := by
    have hn : ((f P).absNorm:ℂ)≠0 := by exact_mod_cast Ideal.absNorm_eq_zero_iff.not.mpr P.val.property.ne_zero
    dsimp only [G]
    rw [←mul_assoc,mul_assoc (W _) ,←Complex.cpow_add _ _ hn]
    rw [show (z - 1 / 2) - 1 + 1 / 2 = z - 1 by ring]
  simpa only [heq] using hb
end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2546

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubePrimeThresholds
Source SHA256: 19753c4d672e2a1b47029e850ec5f468f9a566c50bcf535022b723cf28640872
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2547



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbeRaySlots
local notation "O" => HeckeFamily.O

theorem central_pool_good_eventually (η : Character) (e c b dmin rmin : ℝ)
    (he : 0<e) (hc : 0<c) (hcb : c≤b) (hd : 0<dmin) (hr : 0<rmin) :
    ∀ᶠ Z : ℝ in atTop,∀(C : Set (Ideal O)) (S : Finset (Ideal O)) (d r : ℝ),dmin≤d → rmin≤r →
      ∀P∈pool C S c b ((Z^d)^r),P.val∉S ∧ IsCoprime P.val η.modulus ∧
        (480:ℝ)≤P.val.absNorm ∧ 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2 := by
  obtain ⟨Q0,hQ0,hsmall⟩ := ProbeEuler.central_correction_threshold e he
  have ht := (tendsto_rpow_atTop (mul_pos hd hr)).const_mul_atTop hc
  filter_upwards [eventually_ge_atTop (1:ℝ),ht.eventually (eventually_ge_atTop Q0),
    ht.eventually (eventually_gt_atTop (η.modulus.absNorm:ℝ))] with Z hZ hQ hη
  intro C S d r hdd hrr P hP
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hle : c*Z^(dmin*rmin)≤c*(Z^d)^r := by
    rw [←Real.rpow_mul hZp.le]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ
      (mul_le_mul hdd hrr hr.le (hd.trans_le hdd).le)) hc.le
  have hl := (pool_norm_bounds C S hc.le hcb hD P hP).1
  have hq : Q0≤(P.val.absNorm:ℝ) := hQ.trans (hle.trans (by linarith))
  exact ⟨(mem_pool C S c b _ P).mp hP |>.2.2.2,
    prime_coprime_of_norm_gt η P (hη.trans_le (hle.trans (by linarith))),hQ0.trans hq,hsmall _ hq⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2547

/-! Original module: OAI.NumberTheory.DirichletL.UnitSexticWitness
Source SHA256: 7b71e378603ed0913714291aae223814d0306b51e100bbb24356e0b493a3dc4f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2548




namespace OAI

namespace SevenEighths.UnitSexticWitness

open ActualEisensteinCubic CanonicalRowCompletion CanonicalUnitEuler
open ConcreteTraceCRT
open scoped Classical
noncomputable section
local notation "lambda" => ConcretePrimeRowBridge.goodLambda

lemma idealRowHom_unit_eq_of_norm_mod_seven (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P) (hodd : ringChar (O ⧸ P) ≠ 2)
    (hmod : Ideal.absNorm P % 36 = 7) (u : Oˣ) :
    idealRowHom u.val P = eisEmbedding u.val := by
  rw [idealRowHom_prime _ P hg, actualSextic_unit_euler P hg hodd]
  have hcard : Nat.card (O ⧸ P) = Ideal.absNorm P := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [hcard]
  have hm : (Ideal.absNorm P - 1) / 6 ≡ 1 [MOD 6] := by
    dsimp [Nat.ModEq]
    omega
  have he := pow_eq_pow_of_modEq hm (unit_pow_six u)
  simpa only [pow_one] using congrArg eisEmbedding he

lemma prime_norm_good {p : ℕ} (_hp : p.Prime) (hp3 : 3 < p)
    (P : Ideal O) (hP : Ideal.absNorm P = p) : lambda ∉ P := by
  intro hl
  have hd := Ideal.absNorm_dvd_absNorm_of_le
    ((Ideal.span_singleton_le_iff_mem P).mpr hl)
  have hlambda : Ideal.absNorm (Ideal.span {lambda}) = 3 := CubicEisenstein.absNorm_span_lambda
  rw [hP, hlambda] at hd
  have := Nat.le_of_dvd (by decide : 0 < 3) hd
  omega

lemma prime_norm_ringChar {p : ℕ} (hp : p.Prime)
    (P : Ideal O) [P.IsMaximal] (hP : Ideal.absNorm P = p) :
    ringChar (O ⧸ P) = p := by
  let : Fintype (O ⧸ P) := Fintype.ofFinite _
  let : Fact p.Prime := ⟨hp⟩
  have hcard : Fintype.card (O ⧸ P) = p := by
    rw [← Nat.card_eq_fintype_card]
    exact hP
  let : CharP (O ⧸ P) p := charP_of_card_eq_prime hcard
  exact ringChar.eq (O ⧸ P) p

lemma exists_primeIdeal_norm {p : ℕ} (hp : p.Prime) (hmod : p % 3 = 1) :
    ∃ P : Ideal O, P.IsMaximal ∧ Ideal.absNorm P = p := by
  have hc := ShortDraftHeckeBridge.split_count_of_mod_one hp hmod
  have hne : ((Ideal.span {(p : ℤ)}).primesOver O).Nonempty := by
    exact Set.nonempty_of_ncard_ne_zero (by rw [hc]; decide)
  obtain ⟨P, hP⟩ := hne
  let : P.IsPrime := hP.1
  let : P.LiesOver (Ideal.span {(p : ℤ)}) := hP.2
  have hn := ShortDraftHeckeBridge.absNorm_split hp hmod P
  have hP0 : P ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hn
    exact hp.ne_zero hn.symm
  exact ⟨P, hP.1.isMaximal hP0, hn⟩

theorem exists_prime_unit_embedding (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      Ideal.absNorm P % 36 = 7 ∧ lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      ∀ u : Oˣ, idealRowHom u.val P = eisEmbedding u.val := by
  obtain ⟨p, hpB, hp, hmod⟩ := Nat.forall_exists_prime_gt_and_modEq
    (max (max B 3) (S.sup Ideal.absNorm)) (q := 36) (a := 7) (by decide) (by decide)
  have hp36 : p % 36 = 7 := by simpa only [Nat.ModEq, Nat.reduceMod] using hmod
  have hp3 : 3 < p := lt_of_le_of_lt ((le_max_right B 3).trans (le_max_left _ _)) hpB
  have hpmod : p % 3 = 1 := by omega
  obtain ⟨P, hmax, hn⟩ := exists_primeIdeal_norm hp hpmod
  let : P.IsMaximal := hmax
  have hg : lambda ∉ P := prime_norm_good hp hp3 P hn
  have hodd : ringChar (O ⧸ P) ≠ 2 := by
    rw [prime_norm_ringChar hp P hn]
    omega
  refine ⟨P, hmax, ?_, ?_, hn ▸ hp36, hg, hodd, ?_⟩
  · intro hPS
    have hle := Finset.le_sup (f := Ideal.absNorm) hPS
    rw [hn] at hle
    have := le_max_right (max B 3) (S.sup Ideal.absNorm)
    omega
  · rw [hn]
    exact lt_of_le_of_lt ((le_max_left B 3).trans (le_max_left _ _)) hpB
  · exact idealRowHom_unit_eq_of_norm_mod_seven P hg hodd (hn ▸ hp36)

theorem exists_unit_witness (u : Oˣ) (hu : u ≠ 1)
    (S : Finset (Ideal O)) (B : ℕ) :
    ∃ P : Ideal O, P.IsMaximal ∧ P ∉ S ∧ B < Ideal.absNorm P ∧
      lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2 ∧
      idealRowHom u.val P ≠ 0 ∧ idealRowHom u.val P ≠ 1 := by
  obtain ⟨P, hp, hs, hb, hm, hg, ho, he⟩ := exists_prime_unit_embedding S B
  refine ⟨P, hp, hs, hb, hg, ho, ?_, ?_⟩
  · rw [he u]
    intro hz
    exact Units.ne_zero u (eisEmbedding_injective (by simpa using hz))
  · rw [he u]
    intro hh
    apply hu
    apply Units.ext
    exact eisEmbedding_injective (by simpa using hh)

theorem exists_prime_embedding_after_deletion
    (S : Finset SmoothMobiusCorrection.PrimeIdeal) (B : ℕ) :
    ∃ P : SmoothMobiusCorrection.PrimeIdeal, P ∉ S ∧ B < Ideal.absNorm P.val ∧
      lambda ∉ P.val ∧ ringChar (O ⧸ P.val) ≠ 2 ∧
      ∀ u : Oˣ, IdealEuler.deletePrimes S (idealRowHom u.val) P.val = eisEmbedding u.val := by
  obtain ⟨P, hp, hs, hb, hm, hg, ho, he⟩ :=
    exists_prime_unit_embedding (S.image Subtype.val) B
  let : P.IsMaximal := hp
  let Q : SmoothMobiusCorrection.PrimeIdeal :=
    ⟨P, Ideal.prime_of_isPrime (NeZero.ne P) inferInstance⟩
  have hQ : Q ∉ S := fun h => hs (Finset.mem_image.mpr ⟨Q, h, rfl⟩)
  refine ⟨Q, hQ, hb, hg, ho, ?_⟩
  intro u
  rw [IdealEuler.deletePrimes_prime, ite_eq_right hQ]
  exact he u

theorem deleted_unit_row_ne_principal (u : Oˣ) (hu : u ≠ 1)
    (S : Finset SmoothMobiusCorrection.PrimeIdeal) :
    IdealEuler.deletePrimes S (idealRowHom u.val) ≠
      IdealEuler.deletePrimes S (idealRowHom (1 : O)) := by
  obtain ⟨P, hs, hb, hg, ho, he⟩ := exists_prime_embedding_after_deletion S 0
  intro h
  have hp := DFunLike.congr_fun h P.val
  rw [he u, show (1 : O) = (1 : Oˣ).val from rfl, he 1, Units.val_one, map_one] at hp
  apply hu
  apply Units.ext
  exact eisEmbedding_injective (by simpa using hp)

end
end SevenEighths.UnitSexticWitness

end OAI
end OAIOriginalModule2548

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.Principal
Source SHA256: 6c954a15471a4249775f4057cac8c0651d0804459bfb4e3e69e6cabd96688e6c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2549





namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalRowCompletion
open CanonicalQuadraticSieve UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma rawRow_elementCoeff (u : FreeRow) (n : O) :
    elementCoeff (rawRow u) n = rowTwist (HeckeRowClosure.elementHom
      (fixedSourcePrincipal ∅ (by simp))) rowMaskElement 1 u.val n :=
  (Classical.choose_spec (HeckeRowClosure.exists_row_character_with_conductor
    (fixedSourcePrincipal ∅ (by simp)) rowMaskElement 1 u.val
    rowMaskElement_ne_zero one_ne_zero u.property.1 (dvd_mul_left _ _) (dvd_mul_right _ _))).2 n

lemma rowCharacter_principal_iff (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow) :
    (rowCharacter S hS u).residue=1 ↔ (rawRow u).residue=1 :=
  HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (rawRow u) S hS)

lemma supported_coprime_row_fixed (r : O) (hr : Supported (Ideal.span {r})) :
    IsCoprime (Ideal.span {r})
      ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*
        Ideal.span {(72:O)}) := by
  have hl : IsCoprime λ₀ r :=
    PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
      ((supported_span_iff r).mp hr).1
  have hn : IsCoprime (-2:O) r := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff r).mp hr).2)
  have h2 : IsCoprime (2:O) r := hn.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  have h9 : IsCoprime (9:O) r := ShortDraftCRT.nine_coprime_of_not_lambda_dvd r
    ((supported_span_iff r).mp hr).1
  have h72 : IsCoprime (72:O) r := by
    convert (h2.pow_left (m:=3)).mul_left h9 using 1; norm_num
  have hm := (h2.mul_left hl).symm
  have hmod : (fixedSourcePrincipal ∅ (by simp)).modulus=(1:Ideal O) := by
    simp [fixedSourcePrincipal,HeckeRayFamily.character,Character.ofResidue]
  rw [hmod,one_mul]
  exact ((Ideal.isCoprime_span_singleton_iff _ _).mpr hm).mul_right
    ((Ideal.isCoprime_span_singleton_iff _ _).mpr h72.symm)

theorem rawRow_principal_supported_isUnit (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rawRow u).residue=1) : IsUnit u.val := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hu
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hu
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by
    simp [r]
  have hempty : normalizedFactors (Ideal.span {r})=0 := by
    apply Multiset.eq_zero_iff_forall_notMem.mpr
    intro P hP
    have hcop : IsCoprime
        ((fixedSourcePrincipal ∅ (by simp)).modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)}) P :=
      (supported_coprime_row_fixed r hr).symm.of_isCoprime_of_dvd_right (dvd_of_mem_normalizedFactors hP)
    have hd := HeckeRowNonprincipal.principal_row_multiplicity
      (fixedSourcePrincipal ∅ (by simp)) (rawRow u) rowMaskElement 1 u.val
      (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx (rawRow_elementCoeff u) hp P hP hcop
    have hlt : (normalizedFactors (Ideal.span {r})).count P<6 := by
      rw [hspan]
      exact u.property.2 P
    exact Nat.not_dvd_of_pos_of_lt (Multiset.count_pos.mpr hP) hlt hd
  have hone : (Ideal.span {u.val}:Ideal O)=1 := by
    rw [←hspan,←Ideal.prod_normalizedFactors_eq_self hr.1,hempty,Multiset.prod_zero]
  exact Ideal.span_singleton_eq_top.mp (by simpa only [Ideal.one_eq_top] using hone)

lemma idealCoeff_principal_eq_one (χ : Character) (hχ : χ.residue=1)
    (I : Ideal O) (hI : idealCoeff χ I≠0) : idealCoeff χ I=1 := by
  change IdealCharacter.value χ.modulus χ.residue I=1
  change IdealCharacter.value χ.modulus χ.residue I≠0 at hI
  unfold IdealCharacter.value at *
  split_ifs at * with hzero
  · exact False.elim (hI rfl)
  · have hu := MulChar.apply_ne_zero_iff.mp hI
    rw [hχ,MulChar.one_apply hu]

theorem rowCharacter_unit_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (v : Oˣ) (hu : u.val=(v:O)) (hv : v≠1) :
    (rowCharacter S hS u).residue≠1 := by
  obtain ⟨P,hmax,hPS,hN,hg,hodd,hval0,hval1⟩ := UnitSexticWitness.exists_unit_witness v hv S 0
  let : P.IsMaximal := hmax
  have hP0 : P≠0 := by
    intro he
    simp [he] at hN
  let Q : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := ⟨P,Ideal.prime_of_isPrime hP0 hmax.isPrime⟩
  have he : idealCoeff (rowCharacter S hS u) P=idealRowHom (v:O) P := by
    rw [rowCharacter_coeff S hS hbad,highExclusion_prime S hS Q,ite_eq_right hPS,one_mul,hu]
  intro hp
  have hv0 : idealCoeff (rowCharacter S hS u) P≠0 := he ▸ hval0
  exact hval1 (he.symm.trans (idealCoeff_principal_eq_one _ hp P hv0))

theorem rowCharacter_principal_supported_eq_one (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (u : FreeRow)
    (hu : Supported (Ideal.span {u.val})) (hp : (rowCharacter S hS u).residue=1) : u.val=1 := by
  obtain ⟨v,hv⟩ := rawRow_principal_supported_isUnit u hu ((rowCharacter_principal_iff S hS u).mp hp)
  by_contra hn
  have hv1 : v≠1 := by
    intro he
    subst v
    exact hn hv.symm
  exact rowCharacter_unit_nonprincipal S hS hbad u v hv.symm hv1 hp

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2549

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.PrincipalMask
Source SHA256: 459874de2ab1bc2d4adf224c1fb537c1630857ef1d0e70365955f0ed1d907258
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2550




namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_nonzero_supported (S : Finset (Ideal O)) (hS : ∀P∈S,P.IsMaximal)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S) (a : O)
    (ha : (calibrationForSet S hS).residueMonoid a≠0) : Supported (Ideal.span {a}) := by
  have hu := (calibrationForSet S hS).residue.apply_ne_zero_iff.mp ha
  have hc := (CubicEisenstein.isUnit_quotient_span_iff _ _).mp hu
  have havoid := (calibrationForSet_coprime_iff S hS a).mp hc
  rw [supported_span_iff]
  constructor
  · intro hd
    exact havoid (Ideal.span {λ₀}) (hbad (Finset.mem_insert_self _ _))
      (Ideal.mem_span_singleton.mpr hd)
  · intro hd
    exact havoid (Ideal.span {(2:O)}) (hbad (by simp [CanonicalQuadraticSieve.fixedBadPrimes]))
      (Ideal.mem_span_singleton.mpr hd)

theorem calibrated_row_nonprincipal (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1)
    (hcal : (calibrationForSet S hmax).residueMonoid u.val≠0) :
    (rowCharacter S hS u).residue≠1 := fun hp=>hu
      (rowCharacter_principal_supported_eq_one S hS hbad u
        (calibration_nonzero_supported S hmax hbad u.val hcal) hp)

theorem principal_calibration_vanish (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1) (hp : (rowCharacter S hS u).residue=1) :
    (calibrationForSet S hmax).residueMonoid u.val=0 := by
  by_contra hn
  exact calibrated_row_nonprincipal S hS hmax hbad u hu hn hp

theorem calibrated_numerator_differentiable (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hmax : ∀P∈S,P.IsMaximal) (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (u : FreeRow) (hu : u.val≠1) :
    Differentiable ℂ (fun w=>star ((calibrationForSet S hmax).residueMonoid u.val)*
      HeckeOrigin.continued (rowCharacter S hS u) w) := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiable_const _
  · intro w
    exact (HeckeOrigin.continued_differentiableAt _
      (Or.inr (calibrated_row_nonprincipal S hS hmax hbad u hu hc))).const_mul _

theorem calibrated_physicalRow_first_differentiableAt_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x w z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z) w := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiableAt_const _
  · exact (physicalCompensatedRow_first_differentiableAt_w eps heps S hS hfirst T hT η u
      x w z hx hw hz hxw (Or.inr
        (calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc))).const_mul _

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2550

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstWGrowth
Source SHA256: 3ca83247992310674e5f8cf4e4732f352c013917722a33c460f71a7ad07eccf3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2551





namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem nonprincipal_first_growth (χ : Character) (hχ : χ.residue≠1) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(3+|s.im|)^2 := by
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let R : ℝ := (HeckeDeletionBounds.radical χ.modulus).absNorm
  have hR : 1≤R := by
    dsimp only [R]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (HeckeDeletionBounds.radical_ne_zero χ.modulus))
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  let C : ℝ := HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*Cd*R^(101/100:ℝ)
  have hC : 0≤C := by dsimp [C];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro s hs
  have hl := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hl
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*R^(101/100:ℝ) := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    exact Real.rpow_le_rpow_of_exponent_le hR (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num); linarith)
  rw [HeckeOrigin.continued,ite_eq_right hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*R^(101/100:ℝ)) := mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ = C*(3+|s.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|s.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

theorem calibrated_numerator_first_growth (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0<C ∧ ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤C*(3+|s.im|)^2 := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · refine ⟨1,by norm_num,?_⟩
    intro s hs
    simp only [hc,star_zero,zero_mul,norm_zero,one_mul]
    positivity
  · obtain ⟨C,hC,hbound⟩ := nonprincipal_first_growth (rowCharacter S hS.prime u)
      (calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc)
    refine ⟨C,hC,?_⟩
    intro s hs
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _) ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
      (hbound s hs)

theorem calibrated_physicalRow_first_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    ∃C : ℝ,0<C ∧ ∀w : ℂ,l≤w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*Cn*(Ch*N)*∏P:T,A P
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  have hC : 0≤C := by dsimp [C,L,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn w (hl.trans hw)
  have hh' := hh eps S hS hfirst T η u x w z hx (hl.trans hw) hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      (hl.trans hw) hz (by linarith [hfirst.positive])
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
        ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [he,norm_mul,norm_mul,norm_mul]
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh'
  calc
    _ ≤ L*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      rw [norm_mul]
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [L,N];positivity)
      apply mul_le_mul _ hh'' (norm_nonneg _) (by dsimp [L,N];positivity)
      exact mul_le_mul_of_nonneg_left hn' (by positivity)
    _ = C*(3+|w.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2551

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CoarseUniform
Source SHA256: eeb3a14cb314945ecdda35cda70780adfd250a39e7a7c11dea739a20c0629d25
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2552




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma selectedFirstBound_polynomial {Q : ℝ} (hQ : 1≤Q) : selectedFirstBound Q 2≤8192*Q^3 := by
  have hQ0 : 0≤Q := by linarith
  have hsmall : Q^(1/100:ℝ)≤Q := by
    simpa using Real.rpow_le_rpow_of_exponent_le hQ (by norm_num : (1/100:ℝ)≤1)
  have hsmall0 : 0≤Q^(1/100:ℝ) := Real.rpow_nonneg hQ0 _
  have hQQ : Q≤Q^2 := by nlinarith
  have hQ2 : 0≤Q^2 := sq_nonneg Q
  have hQ3 : Q^2≤Q^3 := by nlinarith [mul_nonneg (sub_nonneg.mpr hQ) (sq_nonneg Q)]
  unfold selectedFirstBound
  rw [Real.rpow_two]
  calc
    _ ≤ 2*((2*Q^2)*2*(2*Q)*388+Q*(2*Q)) := by gcongr <;> nlinarith
    _ ≤ _ := by nlinarith

theorem nonprincipal_first_uniform_growth :
    ∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(χ.modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hd⟩ := HeckeDeletionBounds.factors_any_re_subpower_bound 1 (by norm_num)
  let U := HeckeLogarithmicInput.uniformConstant
  have hU : 0≤U := HeckeLogarithmicInput.uniformConstant_nonneg
  refine ⟨1+U*Cd,by positivity,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hN : (1:ℝ)≤χ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one χ
  have hψN : (1:ℝ)≤ψ.modulus.absNorm := HeckeLogarithmicInput.modulus_norm_ge_one ψ
  have hQ' : (ψ.modulus.absNorm:ℝ)≤χ.modulus.absNorm := by exact_mod_cast hQ
  have hpow : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤χ.modulus.absNorm := by
    apply le_trans _ hQ'
    simpa using Real.rpow_le_rpow_of_exponent_le hψN (by norm_num : (3/5:ℝ)≤1)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hl : ‖LFunction ψ s‖≤U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2 := by
    exact hg.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hU) (sq_nonneg _))
  have hdel : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*(χ.modulus.absNorm:ℝ)^2 := by
    apply (hd χ.modulus ψ s).trans
    apply mul_le_mul_of_nonneg_left _ hCd.le
    calc
      _ ≤ (χ.modulus.absNorm:ℝ)^(max (-s.re) 0+1) := Real.rpow_le_rpow (by positivity)
        (HeckeDyadic.radical_norm_le_modulus χ) (by positivity)
      _ ≤ (χ.modulus.absNorm:ℝ)^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hN
        (by have hm : max (-s.re) 0≤(1/100:ℝ) := max_le (by linarith) (by norm_num);linarith)
      _ = _ := Real.rpow_two _
  rw [HeckeOrigin.continued,ite_eq_right hχ,HeckeDyadicReflection.LFunction_eq_of_mask_entire χ ψ hχ hmask,norm_mul]
  calc
    _ ≤ (U*(χ.modulus.absNorm:ℝ)*(3+|s.im|)^2)*(Cd*(χ.modulus.absNorm:ℝ)^2) :=
      mul_le_mul hl hdel (norm_nonneg _) (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤χ.modulus.absNorm) 3) (sq_nonneg (3+|s.im|))]

theorem calibrated_numerator_first_uniform_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀u : FreeRow,u.val≠1 → ∀s : ℂ,-(1/100:ℝ)≤s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^3*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := nonprincipal_first_uniform_growth
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨C*(1+A^3),by positivity,?_⟩
  intro u hu s hs
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    have hg := hmain (rowCharacter S hS.prime u) hnp s hs
    have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖≤1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      have h := rowCharacter_conductor S hS.prime u
      dsimp [A]
      exact_mod_cast (by simpa only [mul_right_comm] using h)
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^3*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^3*(3+|s.im|)^2 := by gcongr
      _ ≤ _ := by
        rw [mul_pow]
        nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm) 3)
          (sq_nonneg (3+|s.im|))]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2552

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstJoint
Source SHA256: 86c755e71c186b9064f457bcf613ecf95c284cfdff976fc58d373c1708248b71
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2553



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physicalRow_first_joint_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*L*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hx hw hz
  have hn' := hn w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by rw [hx];norm_num) hx.le hw hz (by rw [hx];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*L)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hL)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2553

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalContour
Source SHA256: a29e130f2690bad6e50ec7ff8d28443a984563ab3ca48f98639af6e8dad1b9ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2554




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma calibrated_physicalRow_first_w (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z) w := by
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul]
    exact differentiableAt_const _
  · have hp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    apply DifferentiableAt.const_mul
    unfold physicalCompensatedRow continuedCompensatedRow
    apply DifferentiableAt.mul
    · exact ((HeckeOrigin.continued_differentiableAt _ (Or.inr hp)).const_mul _).mul_const _
    · apply DifferentiableAt.mul
      · exact (continuedCorrection_first_boundary_w eps heps (markExclusions S T)
          (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
          hx hw hz hxw).differentiableAt
      · apply DifferentiableAt.fun_finsetProd
        intro P hP
        exact (continuedCompensatedLocal_first_differentiable_w η u P.val _
          (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x z
          (by linarith) (by linarith)) w

theorem contourTupleOutside {K : ℕ} (S : Finset (Ideal O)) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) : ∀Q∈Finset.univ.image P,Q.val∉S := by
  intro Q hQ
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
  exact hPS i

def continuedPhysicalRowKernel {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z x w z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z)

theorem continuedPhysicalRowKernel_initial {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (t : ProbeMellinBoundary.HeightSpace) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)=
    compensatedRowOnLines η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z ⟨u.val,u.property.1⟩ t := by
  unfold continuedPhysicalRowKernel physicalCompensatedRow compensatedRowOnLines
  rw [continuedCompensatedRow_eq_indexed S hS P hP hPS η u _ _ _
    (by norm_num) (by norm_num) (by norm_num)]
  ring

lemma sourceMellinWeight_differentiable_w (W0 W1 : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) :
    Differentiable ℂ (fun w=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hm : Differentiable ℂ (mellin W1) := fun w=>
    CubicReflectionKernel.compact_source_mellin_differentiable W1 a b ha hW (W1.smooth (⊤:ℕ∞)) w
  have hy : (Y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hY.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hy)

theorem continuedPhysicalRowKernel_differentiableAt_w {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) w := by
  exact (((sourceMellinWeight_differentiable_w W0 W1 a b ha hW X Y Z hY x z) w).mul_const _ |>.mul_const _).mul
    (calibrated_physicalRow_first_w eps heps S hS hfirst hmax _ (contourTupleOutside S P hPS) η u hu x w z hx hw hz hxw)

theorem nonprincipal_w_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r T : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hr : -(1/100:ℝ)≤r)
    (hz : (17/50:ℝ)≤z.re) (hxl : 1+eps≤x.re+l) (hxr : 1+eps≤x.re+r) :
    let F := fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro w hw
    have hwlo : min l r≤w.re := hw.1.1
    have hw' : -(1/100:ℝ)≤w.re := (le_min hl hr).trans hwlo
    have hxw : 1+eps≤x.re+w.re := by
      have := (le_min (by linarith : 1+eps-x.re≤l) (by linarith : 1+eps-x.re≤r)).trans hwlo
      linarith
    exact (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
      W0 W1 a b ha hW X Y Z hY x w z hx hw' hz hxw).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2554

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedContour
Source SHA256: d3d4a0a5426ff7c36b88b462d36d02d13c64ac69cf1a9cd48203d4490a04b9fe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2555


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma reciprocal_differentiableAt_of_nonzero (χ : Character) (s : ℂ) (h0 : s≠0)
    (hnz : ¬(χ.residue=1 ∧ s=1) → LFunction χ s≠0) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal χ) s := by
  by_cases hχ : χ.residue=1
  · have hr : HeckeReciprocal.regularizedL χ s≠0 := by
      by_cases hs : s=1
      · subst s
        exact HeckeReciprocal.regularizedL_ne_zero_at_one χ hχ
      · rw [HeckeReciprocal.regularizedL_eq χ h0 hs]
        exact mul_ne_zero (sub_ne_zero.mpr hs) (hnz (by simp [hs]))
    have he : HeckeReciprocal.reciprocal χ=(fun z=>(z-1)/HeckeReciprocal.regularizedL χ z) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_left hχ]
    rw [he]
    exact (differentiableAt_id.sub_const 1).div
      (HeckeReciprocal.regularizedL_differentiableAt χ h0) hr
  · have he : HeckeReciprocal.reciprocal χ=(fun z=>(LFunction χ z)⁻¹) := by
      funext z
      simp only [HeckeReciprocal.reciprocal,ite_eq_right hχ]
    rw [he]
    exact (LFunction_differentiableAt χ h0 (Or.inr hχ)).inv (hnz (by simp [hχ]))

theorem physicalCompensatedRow_buffered_differentiableAt_x
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>physicalCompensatedRow S hS T hT η u x w z) x := by
  have hx0 : x≠0 := by intro h;norm_num [h] at hx
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (reciprocal_differentiableAt_of_nonzero _ x hx0 hnz).const_mul _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_x eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_x η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiable_x (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) :
    Differentiable ℂ (fun x=>sourceMellinWeight W0 W1 X Y Z x w z) := by
  have hz : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  unfold sourceMellinWeight
  fun_prop (disch := exact Or.inl hz)

theorem continuedPhysicalRowKernel_buffered_differentiableAt_x {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re)
    (hnz : ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
      LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    DifferentiableAt ℂ (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) x :=
  (((sourceMellinWeight_differentiable_x W0 W1 X Y Z hZ w z) x).mul_const _ |>.mul_const _).mul
    ((physicalCompensatedRow_buffered_differentiableAt_x eps heps S hS hfirst _
      (contourTupleOutside S P hPS) η u x w z hx hw hz hxw hnz).const_mul _)

theorem buffered_x_rectangle {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r T : ℝ)
    (hl : (51/100:ℝ)≤l) (hr : (51/100:ℝ)≤r) (hw : -(1/100:ℝ)≤w.re)
    (hz : (17/50:ℝ)≤z.re) (hlw : 1+eps≤l+w.re) (hrw : 1+eps≤r+w.re)
    (hnz : ∀x∈(uIcc l r ×ℂ uIcc (-T) T),
      ¬(((targetRow η u).excludePrimes S hS.prime).residue=1 ∧ x=1) →
        LFunction ((targetRow η u).excludePrimes S hS.prime) x≠0) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -T..T,F ((l:ℂ)+t*I))+
        I*((∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))) := by
  dsimp only
  let F := fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
  have hh : DifferentiableOn ℂ F (uIcc l r ×ℂ uIcc (-T) T) := by
    intro x hx
    have hxlo : min l r≤x.re := hx.1.1
    have hx' : (51/100:ℝ)≤x.re := (le_min hl hr).trans hxlo
    have hxw : 1+eps≤x.re+w.re := by
      have := (le_min (by linarith : 1+eps-w.re≤l) (by linarith : 1+eps-w.re≤r)).trans hxlo
      linarith
    exact (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hZ x w z hx' hw hz hxw (hnz x hx)).differentiableWithinAt
  have hb := Complex.integral_boundary_rect_eq_zero_of_differentiableOn F
    ((l:ℂ)+(-T)*I) ((r:ℂ)+T*I) (by simpa using hh)
  have hc : (∫v : ℝ in l..r,F ((v:ℂ)+(-T)*I))-(∫v : ℝ in l..r,F ((v:ℂ)+T*I))+
      I*(∫t : ℝ in -T..T,F ((r:ℂ)+t*I))-I*(∫t : ℝ in -T..T,F ((l:ℂ)+t*I))=0 := by
    simpa [smul_eq_mul] using hb
  have hd := congrArg (fun z : ℂ=>-I*z) hc
  change (∫t : ℝ in -T..T,F ((r:ℂ)+t*I))=_
  ring_nf at hd ⊢
  simp only [I_sq] at hd
  linear_combination hd

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2555

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.DetectorZeros
Source SHA256: 054c1c7aef3663542351baa604b3ee1c1f67730e141189ee8e4660184f0b6d12
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2556



namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily

def detectorEntire (χ : Character) (s : ℂ) : ℂ :=
  if χ.residue=1 then HeckeOrigin.poleRemoved χ s else HeckeOrigin.continued χ s

lemma detectorEntire_eq_nonprincipal (χ : Character) (hχ : χ.residue≠1) :
    detectorEntire χ=LFunction χ := by
  funext s
  simp only [detectorEntire,HeckeOrigin.continued,ite_eq_right hχ]

lemma detectorEntire_entire (χ : Character) : Differentiable ℂ (detectorEntire χ) := by
  by_cases hχ : χ.residue=1
  · have he : detectorEntire χ=HeckeOrigin.poleRemoved χ := by funext s;simp [detectorEntire,hχ]
    rw [he]
    exact HeckeOrigin.poleRemoved_entire χ
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    exact LFunction_entire_nonprincipal χ hχ

lemma detectorEntire_zero_iff (χ : Character) {s : ℂ} (hs : 0<s.re) :
    detectorEntire χ s=0 ↔ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · simp only [detectorEntire,ite_eq_left hχ]
    by_cases h1 : s=1
    · subst s
      simp [HeckeOrigin.poleRemoved_one_ne_zero χ hχ,hχ]
    · rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
      simp [mul_eq_zero,sub_ne_zero.mpr h1,h1]
  · rw [detectorEntire_eq_nonprincipal χ hχ]
    simp [hχ]

lemma detectorEntire_ne_zero_of_one_lt_re (χ : Character) {s : ℂ} (hs : 1<s.re) :
    detectorEntire χ s≠0 := by
  intro hz
  exact LFunction_ne_zero_of_one_lt_re χ hs ((detectorEntire_zero_iff χ (by linarith)).mp hz).1

def detectorZeros (χ : Character) (T : ℝ) : Set ℂ :=
  {s | s∈HeckeDetectorZeros.rectangle T ∧ LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1)}

lemma detectorZeros_finite (χ : Character) (T : ℝ) : (detectorZeros χ T).Finite := by
  have ha : AnalyticOnNhd ℂ (detectorEntire χ) Set.univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr (detectorEntire_entire χ)
  have hc := ha.preimage_zero_mem_codiscreteWithin
    (detectorEntire_ne_zero_of_one_lt_re χ (by norm_num : 1<(2:ℂ).re))
    (Set.mem_univ (2:ℂ)) isConnected_univ
  have hf := (HeckeDetectorZeros.rectangle_compact T).finite_sdiff_of_mem_codiscreteWithin
    (codiscreteWithin_mono (Set.subset_univ (HeckeDetectorZeros.rectangle T)) hc)
  convert hf using 1
  ext s
  by_cases hs : s∈HeckeDetectorZeros.rectangle T
  · have hr : 0<s.re := by have h:=hs.1;linarith
    simp [detectorZeros,hs,detectorEntire_zero_iff χ hr]
  · simp [detectorZeros,hs]

def detectorZeroFinset (χ : Character) (T : ℝ) : Finset ℂ := (detectorZeros_finite χ T).toFinset

@[simp] lemma mem_detectorZeroFinset (χ : Character) (T : ℝ) (s : ℂ) :
    s∈detectorZeroFinset χ T ↔ (51/100:ℝ)≤s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction χ s=0 ∧ ¬(χ.residue=1 ∧ s=1) := by
  simp only [detectorZeroFinset,Set.Finite.mem_toFinset,detectorZeros,HeckeDetectorZeros.rectangle,Set.mem_ofPred_eq]
  tauto

variable {ι : Type*} [Fintype ι]

def detectorFamilyZeros (χ : ι→Character) (T : ℝ) : Finset (ι × ℂ) :=
  Finset.univ.biUnion (fun i=>(detectorZeroFinset (χ i) T).image (fun s=>(i,s)))

@[simp] lemma mem_detectorFamilyZeros (χ : ι→Character) (T : ℝ) (i : ι) (s : ℂ) :
    (i,s)∈detectorFamilyZeros χ T ↔ (51/100:ℝ)≤s.re ∧ s.re≤1 ∧ |s.im|≤T ∧
      LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) := by
  simp [detectorFamilyZeros]

def detectorRealParts (χ : ι→Character) (T : ℝ) : Finset ℝ :=
  insert (51/100) ((detectorFamilyZeros χ T).image (fun p=>p.2.re))

lemma detectorRealParts_nonempty (χ : ι→Character) (T : ℝ) : (detectorRealParts χ T).Nonempty :=
  Finset.insert_nonempty _ _

def detectorMaximum (χ : ι→Character) (T : ℝ) : ℝ :=
  (detectorRealParts χ T).max' (detectorRealParts_nonempty χ T)

lemma detectorMaximum_mem (χ : ι→Character) (T : ℝ) : detectorMaximum χ T∈detectorRealParts χ T :=
  Finset.max'_mem _ _

lemma detectorMaximum_bounds (χ : ι→Character) (T : ℝ) :
    (51/100:ℝ)≤detectorMaximum χ T ∧ detectorMaximum χ T≤1 := by
  constructor
  · exact Finset.le_max' _ _ (Finset.mem_insert_self _ _)
  · apply Finset.max'_le
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl|hx
    · norm_num
    · obtain ⟨⟨i,s⟩,hs,rfl⟩ := Finset.mem_image.mp hx
      exact (mem_detectorFamilyZeros χ T i s |>.mp hs).2.1

lemma detector_zero_re_le_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : (51/100:ℝ)≤s.re) (ht : |s.im|≤T) (hz : LFunction (χ i) s=0)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : s.re≤detectorMaximum χ T := by
  have hle : s.re≤1 := by
    by_contra hn
    exact LFunction_ne_zero_of_one_lt_re (χ i) (lt_of_not_ge hn) hz
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr
    ⟨(i,s),(mem_detectorFamilyZeros χ T i s).mpr ⟨hs,hle,ht,hz,hpole⟩,rfl⟩)

lemma detectorMaximum_attained (χ : ι→Character) (T : ℝ)
    (hmax : (51/100:ℝ)<detectorMaximum χ T) :
    ∃i s,LFunction (χ i) s=0 ∧ ¬((χ i).residue=1 ∧ s=1) ∧
      |s.im|≤T ∧ s.re=detectorMaximum χ T := by
  have hm := detectorMaximum_mem χ T
  rcases Finset.mem_insert.mp hm with hm|hm
  · exact False.elim ((ne_of_gt hmax) hm)
  · obtain ⟨⟨i,s⟩,hs,heq⟩ := Finset.mem_image.mp hm
    have hz := (mem_detectorFamilyZeros χ T i s).mp hs
    exact ⟨i,s,hz.2.2.2.1,hz.2.2.2.2,hz.2.2.1,heq⟩

lemma detectorMaximum_mono (χ : ι→Character) {T T' : ℝ} (hT : T≤T') :
    detectorMaximum χ T≤detectorMaximum χ T' := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum χ T) with hm|hm
  · obtain ⟨i,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained χ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum χ T' i (by rw [heq];exact hm.le) (ht.trans hT) hz hpole
  · exact hm.trans (detectorMaximum_bounds χ T').1

lemma detector_nonzero_above_maximum (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T)
    (hpole : ¬((χ i).residue=1 ∧ s=1)) : LFunction (χ i) s≠0 := by
  intro hz
  exact (not_lt_of_ge (detector_zero_re_le_maximum χ T i
    ((detectorMaximum_bounds χ T).1.trans hs.le) ht hz hpole)) hs

lemma detector_reciprocal_differentiableAt (χ : ι→Character) (T : ℝ) (i : ι) {s : ℂ}
    (hs : detectorMaximum χ T<s.re) (ht : |s.im|≤T) :
    DifferentiableAt ℂ (HeckeReciprocal.reciprocal (χ i)) s := by
  apply reciprocal_differentiableAt_of_nonzero (χ i) s
    (by intro h;have hb:=(detectorMaximum_bounds χ T).1;norm_num [h] at hs;linarith)
  exact detector_nonzero_above_maximum χ T i hs ht

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2556

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.DetectorBins
Source SHA256: 8e24c6ac8cdbb4156ad9b7b65d33fe59a0e7a89d4c578f2650dabe2d6cd7673a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2557


namespace OAI

noncomputable section
open scoped Classical Topology
open Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily
variable {ι : Type*} [Fintype ι]

lemma detector_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e))
    (hpole : ¬((χ j).residue=1 ∧ s=1)) : LFunction (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  have hi := Complex.abs_im_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr hi
  have hre : a+2*e≤s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  have him : |s.im|≤3*(i+1:ℕ)*T := by
    have ht' := abs_add_le (s.im-t) t
    rw [sub_add_cancel] at ht'
    push_cast at ht ⊢
    nlinarith [hi.trans hn]
  exact detector_nonzero_above_maximum χ _ j (hmax.trans_le hre) him hpole

lemma detectorEntire_nonzero_on_buffered_disk (χ : ι→Character)
    (T a e : ℝ) (i : ℕ) (hT : 2<T) (ha : (51/100:ℝ)≤a) (he : 0<e)
    (hmax : detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e)
    (j : ι) (t : ℝ) (ht : |t|≤(3*i+2:ℕ)*T)
    {s : ℂ} (hs : s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e)) :
    detectorEntire (χ j) s≠0 := by
  have hn : ‖s-((2:ℂ)+t*Complex.I)‖≤2-a-2*e := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hs
  have hr := Complex.abs_re_le_norm (s-((2:ℂ)+t*Complex.I))
  norm_num at hr
  have hre : 0<s.re := by linarith [(abs_le.mp (hr.trans hn)).1]
  intro hz
  obtain ⟨hL,hpole⟩ := (detectorEntire_zero_iff (χ j) hre).mp hz
  exact detector_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht hs hpole hL

lemma exists_detector_buffered_bin (χ : ι→Character)
    (T e : ℝ) (hT : 2<T) (he : 0<e) (n : ℕ) (hn : 0<n)
    (hwidth : (49/100:ℝ)≤n*e) :
    ∃ i k : ℕ, 1 ≤ i ∧ i ≤ n ∧
      let a : ℝ := 51/100+e*k
      a≤1 ∧ a≤detectorMaximum χ (3*i*T) ∧
      detectorMaximum χ (3*i*T)<a+e ∧
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e ∧
      (51/100<a → ∃j s,LFunction (χ j) s=0 ∧ ¬((χ j).residue=1 ∧ s=1) ∧
        a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*i*T) ∧
      (∀j t,|t|≤(3*i+2:ℕ)*T → ∀s∈Metric.closedBall ((2:ℂ)+t*Complex.I) (2-a-2*e),
        detectorEntire (χ j) s≠0) := by
  let M : ℕ→ℝ := fun j=>detectorMaximum χ (3*(j+1:ℕ)*T)
  obtain ⟨i,hk,k,hone,hlo,hhi,hnext⟩ := Detector.exists_buffered_bin M hn he
    (fun j _=>detectorMaximum_bounds χ _) hwidth
  refine ⟨i+1,k,by omega,by omega,hone,hlo,hhi,?_,?_,?_⟩
  · exact hnext
  · intro ha
    obtain ⟨j,s,hz,hpole,ht,hs⟩ := detectorMaximum_attained χ (3*(i+1:ℕ)*T) (lt_of_lt_of_le ha hlo)
    exact ⟨j,s,hz,hpole,by rw [hs];exact hlo,by rw [hs];exact hhi,ht⟩
  · intro j t ht s hs
    apply detectorEntire_nonzero_on_buffered_disk χ T (51/100+e*k) e (i+1) hT
      (by nlinarith [Nat.cast_nonneg (α:=ℝ) k]) he hnext j t ht hs

lemma detectorMaximum_eq_nonprincipal (χ : ι→Character) (hχ : ∀i,(χ i).residue≠1) (T : ℝ) :
    detectorMaximum χ T=HeckeDetectorZeros.zeroMaximum χ hχ T := by
  have hz (i : ι) : detectorZeroFinset (χ i) T=HeckeDetectorZeros.zeroFinset (χ i) (hχ i) T := by
    ext s
    simp [hχ i]
  have hr : detectorRealParts χ T=HeckeDetectorZeros.realParts χ hχ T := by
    simp only [detectorRealParts,HeckeDetectorZeros.realParts,detectorFamilyZeros,HeckeDetectorZeros.familyZeros,hz]
  unfold detectorMaximum HeckeDetectorZeros.zeroMaximum
  simp only [hr]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2557

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedBin
Source SHA256: 12139ac3630fa9c4416b66d68a588838881d97158291f0550de3a7b80c9c7090
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2558


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def sourceDetectorFamily (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) : Sum Bool ι→Character :=
  Sum.elim (fun b=>if b then rowCharacter S hS u else (targetRow η u).excludePrimes S hS) ψ

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_denominator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl false)=(targetRow η u).excludePrimes S hS := rfl

omit [Fintype ι] in
@[simp] lemma sourceDetectorFamily_numerator (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) :
    sourceDetectorFamily S hS η u ψ (Sum.inl true)=rowCharacter S hS u := rfl

lemma source_bin_denominator_nonzero (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (ψ : ι→Character) (T a e : ℝ) (i : ℕ) (he : 0<e)
    (hmax : detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (x : ℂ) (hx : a+16*e≤x.re) (ht : |x.im|≤3*(i+1:ℕ)*T)
    (hpole : ¬(((targetRow η u).excludePrimes S hS).residue=1 ∧ x=1)) :
    LFunction ((targetRow η u).excludePrimes S hS) x≠0 :=
  detector_nonzero_above_maximum (sourceDetectorFamily S hS η u ψ) _ (Sum.inl false)
    (by linarith) ht hpole

theorem source_buffered_x_rectangle {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmaxS : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (ψ : ι→Character)
    (T a e : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hfirst : FirstTail (4*e) S)
    (hmax : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*T)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0<Z)
    (w z : ℂ) (hw : w.re=1-a-6*e) (hz : (17/50:ℝ)≤z.re)
    (r H : ℝ) (hr : a+16*e≤r) (hH : 0≤H) (hHT : H≤3*(i+1:ℕ)*T) :
    let F := fun x=>continuedPhysicalRowKernel S hS hmaxS P hPS η u W0 W1 X Y Z x w z
    (∫t : ℝ in -H..H,F ((r:ℂ)+t*I))=
      (∫t : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+t*I))+
        I*((∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+(-H)*I))-
          (∫v : ℝ in (a+16*e)..r,F ((v:ℂ)+H*I))) := by
  apply buffered_x_rectangle (8*e) (by positivity) S hS
    (by convert hfirst using 1 ; ring) hmaxS P hPS η u W0 W1 X Y Z hZ w z (a+16*e) r H
    (by linarith) (by linarith) (by rw [hw];linarith) hz (by rw [hw];linarith) (by rw [hw];linarith)
  intro x hx hpole
  have hxr : a+16*e≤x.re := by simpa only [min_eq_left hr] using hx.1.1
  have hxi : |x.im|≤H := by
    apply abs_le.mpr
    simpa only [uIcc_of_le (by linarith : -H≤H),Set.mem_preimage,Set.mem_Icc] using hx.2
  exact source_bin_denominator_nonzero S hS.prime η u ψ T a e i he hmax x hxr (hxi.trans hHT) hpole

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2558

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.DiskControl
Source SHA256: 925b34c4f797792b03e36d16a3cae1cc68f5ede1d7c1924ad7f8045c4bfcd52f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2559



namespace OAI

noncomputable section
open scoped Classical Topology
open Set Metric
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeLogarithmicInput HeckeLogarithmic HeckeFiniteDeletion
open HeckeDeletionBounds HeckeReciprocalGrowth

lemma poleRemoved_eq_regularizedL (χ : Character) {s : ℂ} (hs : 0<s.re) :
    HeckeOrigin.poleRemoved χ s=HeckeReciprocal.regularizedL χ s := by
  by_cases h1 : s=1
  · subst s;exact HeckeOrigin.poleRemoved_one χ
  · have h0 : s≠0 := by intro h;simp [h] at hs
    rw [HeckeOrigin.poleRemoved_eq χ h0 h1,HeckeReciprocal.regularizedL_eq χ h0 h1]

lemma regular_eq_of_mask (χ ψ : Character)
    (hmask : ∀ I : Ideal O, idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    {s : ℂ} (hs : 0<s.re) : regular χ s=regular ψ s*factors χ.modulus ψ s := by
  by_cases hχ : χ.residue=1
  · have hψ := (principal_iff_of_mask χ ψ hmask).mp hχ
    simp only [regular,ite_eq_left hχ,ite_eq_left hψ,HeckePrincipalStrip.sourceNormalized,
      poleRemoved_eq_regularizedL χ hs,poleRemoved_eq_regularizedL ψ hs]
    rw [regularizedL_eq_of_mask χ ψ hmask hs]
    ring
  · have hψ : ψ.residue≠1 := fun h=>hχ ((principal_iff_of_mask χ ψ hmask).mpr h)
    rw [regular_eq_nonprincipal χ hχ,regular_eq_nonprincipal ψ hψ]
    exact LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ hs

lemma regular_eq_detector (χ : Character) (s : ℂ) :
    regular χ s=if χ.residue=1 then detectorEntire χ s/(s+1) else detectorEntire χ s := by
  by_cases hχ : χ.residue=1
  · simp [regular,detectorEntire,HeckePrincipalStrip.sourceNormalized,hχ]
  · simp [regular,detectorEntire_eq_nonprincipal χ hχ,hχ]

lemma regular_nonzero_of_detector (χ : Character) {s : ℂ} (hs : 0<s.re)
    (hz : detectorEntire χ s≠0) : regular χ s≠0 := by
  rw [regular_eq_detector]
  split_ifs
  · apply div_ne_zero hz
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  · exact hz

lemma reciprocal_norm_le_regular_inverse_on_positive (χ : Character) {s : ℂ}
    (hs : 0<s.re) (hz : regular χ s≠0) :
    ‖HeckeReciprocal.reciprocal χ s‖≤‖(regular χ s)⁻¹‖ := by
  have h0 : s≠0 := by intro h;simp [h] at hs
  by_cases hχ : χ.residue=1
  · by_cases h1 : s=1
    · subst s
      rw [HeckeReciprocal.reciprocal_principal_one χ hχ,norm_zero]
      exact norm_nonneg _
    have hp : s+1≠0 := by
      intro h
      have hr := congrArg Complex.re h
      simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
      linarith
    have hL : LFunction χ s≠0 := by
      intro h
      apply hz
      simp [regular,hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1,h]
    have heq : HeckeReciprocal.reciprocal χ s=((s-1)/(s+1))*(regular χ s)⁻¹ := by
      rw [HeckeReciprocal.reciprocal_eq_inv χ h0 h1]
      simp only [regular,ite_eq_left hχ,HeckePrincipalStrip.sourceNormalized,HeckeOrigin.poleRemoved_eq χ h0 h1]
      field_simp
    rw [heq,norm_mul]
    apply mul_le_of_le_one_left (norm_nonneg _)
    rw [norm_div]
    exact (div_le_one (norm_pos_iff.mpr hp)).mpr (principal_regular_factor_bound hs.le)
  · simp only [HeckeReciprocal.reciprocal,regular,ite_eq_right hχ,le_refl]

theorem original_regular_disk_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (χ : Character), ∀ a t : ℝ,
      1/2≤a → a≤1 →
      (∀ z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular χ z ≠ 0) →
      ∀ z ∈ closedBall ((2 : ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular χ z‖ + ‖HeckeReciprocal.reciprocal χ z‖ ≤
          C*(presentationComplexity χ t)^ε := by
  obtain ⟨Dp,B,hDp,_,hprimitive⟩ := HeckeLogarithmicActual.disk_control e ε he he' hε
  obtain ⟨Cd,hCd,hdelete⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Dp*Cd,mul_pos hDp hCd,?_⟩
  intro χ a t ha ha' hzero z hz
  obtain ⟨ψ,_,hp,hn,hmask⟩ := exists_primitive_character χ
  have hzeroψ : ∀ w ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e), regular ψ w ≠ 0 := by
    intro w hw
    have hwp : 0 < w.re := by
      have hr := LogarithmicControl.disk_re_gt hw
      linarith
    intro hh
    apply hzero w hw
    rw [regular_eq_of_mask χ ψ hmask hwp, hh, zero_mul]
  have hbound := (hprimitive ψ hp a t ha ha' hzeroψ).1 z hz
  have hz2 : z ∈ ball ((2 : ℂ)+t*Complex.I) (2-a-2*e) :=
    closedBall_subset_ball (by linarith) hz
  have hzre : (1/2 : ℝ) ≤ z.re := by
    have hr := LogarithmicControl.disk_re_gt hz2
    linarith
  have hzpos : 0 < z.re := by linarith
  have hdel := hdelete χ.modulus ψ z hzre
  have hL : regular χ z = regular ψ z*factors χ.modulus ψ z :=
    regular_eq_of_mask χ ψ hmask hzpos
  have hR : HeckeReciprocal.reciprocal χ z =
      HeckeReciprocal.reciprocal ψ z*(factors χ.modulus ψ z)⁻¹ :=
    HeckeDeletionReciprocal.reciprocal_eq_of_mask χ ψ hmask hzpos
  have hrec := reciprocal_norm_le_regular_inverse_on_positive ψ hzpos (hzeroψ z hz2)
  have hdel1 : ‖factors χ.modulus ψ z‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg ((factors χ.modulus ψ z)⁻¹)]
  have hdel2 : ‖(factors χ.modulus ψ z)⁻¹‖ ≤ Cd*((radical χ.modulus).absNorm : ℝ)^ε := by
    linarith [norm_nonneg (factors χ.modulus ψ z)]
  have hQ : complexity ψ t ≤ complexity χ t := by
    unfold complexity
    have hn' : (ψ.modulus.absNorm : ℝ) ≤ χ.modulus.absNorm := by exact_mod_cast hn
    gcongr
  have hc0 : 0 ≤ complexity ψ t := (Real.exp_pos 1).le.trans (complexity_ge_exp ψ t)
  have hr0 : 0 ≤ ((radical χ.modulus).absNorm : ℝ) := by positivity
  rw [hL,hR,norm_mul,norm_mul]
  calc
    _ ≤ (‖regular ψ z‖+‖(regular ψ z)⁻¹‖)*
        (Cd*((radical χ.modulus).absNorm : ℝ)^ε) := by
      have h1 := mul_le_mul_of_nonneg_left hdel1 (norm_nonneg (regular ψ z))
      have h2 := mul_le_mul hrec hdel2 (norm_nonneg _) (norm_nonneg _)
      nlinarith
    _ ≤ (Dp*(complexity ψ t)^ε)*(Cd*((radical χ.modulus).absNorm : ℝ)^ε) :=
      mul_le_mul_of_nonneg_right hbound (by positivity)
    _ = (Dp*Cd)*(((radical χ.modulus).absNorm : ℝ)*complexity ψ t)^ε := by
      rw [Real.mul_rpow hr0 hc0]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (mul_nonneg hr0 hc0) (mul_le_mul_of_nonneg_left hQ hr0) hε.le)
      (mul_pos hDp hCd).le

theorem buffered_regular_control (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (T a : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j t,|t|≤(3*i+2:ℕ)*T →
      ∀z∈closedBall ((2:ℂ)+t*Complex.I) (2-a-6*e),
        ‖regular (χ j) z‖+‖HeckeReciprocal.reciprocal (χ j) z‖≤
          C*(presentationComplexity (χ j) t)^ε := by
  obtain ⟨C,hC,hbound⟩ := original_regular_disk_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a i hT ha ha1 hmax j t ht z hz
  apply hbound (χ j) a t (by linarith) ha1 _ z hz
  intro w hw
  have hre : 0<w.re := by have h:=LogarithmicControl.disk_re_gt hw;linarith
  exact regular_nonzero_of_detector (χ j) hre
    (detectorEntire_nonzero_on_buffered_disk χ T a e i hT ha he hmax j t ht (ball_subset_closedBall hw))

theorem buffered_rectangle_reciprocal_bound (e ε : ℝ)
    (he : 0<e) (he' : e<1/1000) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι→Character)
      (T a H : ℝ) (i : ℕ),2<T → (51/100:ℝ)≤a → a≤1 →
      H≤(3*i+2:ℕ)*T → detectorMaximum χ (3*(i+1:ℕ)*T)<a+2*e →
      ∀j z,a+16*e≤z.re → z.re≤2 → |z.im|≤H →
        ‖HeckeReciprocal.reciprocal (χ j) z‖≤C*(presentationComplexity (χ j) H)^ε := by
  obtain ⟨C,hC,hbound⟩ := buffered_regular_control e ε he he' hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ T a H i hT ha ha1 hHT hmax j z hzl hzr hzi
  have hz : z∈closedBall ((2:ℂ)+z.im*Complex.I) (2-a-6*e) := by
    rw [mem_closedBall,dist_eq_norm]
    have heq : z-((2:ℂ)+z.im*Complex.I)=((z.re-2:ℝ):ℂ) := by apply Complex.ext <;> simp
    rw [heq,Complex.norm_real,Real.norm_eq_abs,abs_of_nonpos (by linarith)]
    linarith
  have hb := hbound χ T a i hT ha ha1 hmax j z.im (hzi.trans hHT) z hz
  have hc : presentationComplexity (χ j) z.im≤presentationComplexity (χ j) H := by
    unfold presentationComplexity complexity
    have hH : 0≤H := (abs_nonneg _).trans hzi
    rw [abs_of_nonneg hH]
    gcongr
  have hnonneg : 0≤presentationComplexity (χ j) z.im := by
    unfold presentationComplexity complexity
    positivity
  apply (le_trans (le_add_of_nonneg_left (norm_nonneg _)) hb).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hnonneg hc hε.le) hC.le

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2559

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RowReflectedAllocation
Source SHA256: 1b84fb630dd4a48c1a8c77043279dacafddf61b45470f6e3cc2f770840099ed5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2560







namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ComplexConjugate
open Set Complex
namespace SevenEighths.ProbeRowReflectedAllocation
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open HeckeFiniteDeletion HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma prod_rpow_nonneg {ι : Type*} (T : Finset ι) (q : ι → ℝ)
    (hq : ∀ i ∈ T, 0 ≤ q i) (A : ℝ) :
    (∏ i ∈ T, q i) ^ A = ∏ i ∈ T, (q i) ^ A := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert i T hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi,
      Real.mul_rpow (hq i (Finset.mem_insert_self i T))
        (Finset.prod_nonneg (fun j hj => hq j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hq j (Finset.mem_insert_of_mem hj))]

lemma selected_exponent_allocation {a e : ℝ} (ha : 51/100 ≤ a)
    (he : 0 < e) {j : ℕ} (hj : 2 ≤ j) :
    -(1-a-6*e) ≤ (j-1 : ℕ)*(a-1/2+6*e)-1/2 := by
  have hA : 0 ≤ a-1/2+6*e := by linarith
  have hj' : (1 : ℝ) ≤ (j-1 : ℕ) := by exact_mod_cast (show 1 ≤ j-1 by omega)
  nlinarith [mul_le_mul_of_nonneg_right hj' hA]

theorem allocation_of_deficit {k : ℕ} (q : Fin k → ℝ)
    (hq : ∀ i, 1 ≤ q i) (j : Fin k → ℕ) (hj : ∀ i, 2 ≤ j i)
    (N D a e : ℝ) (hN : 0 ≤ N) (ha : 51/100 ≤ a) (he : 0 < e)
    (hdef : N * ∏ i, q i ^ (j i-1) ≤ D) :
    N ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1-a-6*e)) ≤
      D ^ (a-1/2+6*e) * ∏ i, q i ^ (-(1/2 : ℝ)) := by
  let A := a-1/2+6*e
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hq0 (i) : 0 ≤ q i := (by linarith [hq i])
  have hlocal (i) : q i ^ (-(1-a-6*e)) ≤
      (q i ^ (j i-1)) ^ A * q i ^ (-(1/2 : ℝ)) := by
    rw [← Real.rpow_natCast_mul (hq0 i), ← Real.rpow_add (by linarith [hq i])]
    apply Real.rpow_le_rpow_of_exponent_le (hq i)
    exact selected_exponent_allocation ha he (hj i)
  have hprod := Finset.prod_le_prod₀ (s := Finset.univ) (fun i _ => Real.rpow_nonneg (hq0 i) _)
    (fun i _ => hlocal i)
  rw [Finset.prod_mul_distrib, ← prod_rpow_nonneg Finset.univ
    (fun i => q i ^ (j i-1)) (fun i _ => pow_nonneg (hq0 i) _) A] at hprod
  have hD0 : 0 ≤ ∏ i, q i ^ (j i-1) := Finset.prod_nonneg (fun i _ => pow_nonneg (hq0 i) _)
  calc
    _ ≤ N ^ A * ((∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hprod (Real.rpow_nonneg hN _)
    _ = (N * ∏ i, q i ^ (j i-1)) ^ A * ∏ i, q i ^ (-(1/2 : ℝ)) := by
      rw [Real.mul_rpow hN hD0]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Real.rpow_le_rpow (mul_nonneg hN hD0) hdef hA)
      (Finset.prod_nonneg (fun i _ => Real.rpow_nonneg (hq0 i) _))

lemma prime_norm_ge_one (P : Ideal O) (hP : Prime P) : (1 : ℝ) ≤ P.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)

lemma original_row_conductor_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((rowCharacter S hS u).modulus.absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm := by
  exact_mod_cast (by simpa only [fixedConductorConstant, mul_assoc, mul_comm, mul_left_comm]
    using rowCharacter_conductor S hS u)

lemma original_row_deletion_radical_le (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ≤
      (fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm :=
  by
    let χ := rowCharacter S hS u
    have hd : radical χ.modulus ∣ χ.modulus := by
      unfold radical SmoothMobiusCorrection.primeProduct
      rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O => J)]
      exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
    have hn : ((radical χ.modulus).absNorm : ℝ) ≤ χ.modulus.absNorm := by
      exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
    exact hn.trans (original_row_conductor_le S hS u)

theorem row_same_primitive_allocation (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (u : FreeRow) :
    ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
        if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
      ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ i, Prime (P i)) → Function.Injective P →
        ∀ (j : Fin k → ℕ), (∀ i, 2 ≤ j i) →
          (∀ i, P i ^ j i ∣ Ideal.span {u.val}) →
          ∀ a e : ℝ, 51/100 ≤ a → 0 < e →
          (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
              ∏ i, ((P i).absNorm : ℝ) ^ (-(1-a-6*e)) ≤
            ((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
              (a-1/2+6*e) * ∏ i, ((P i).absNorm : ℝ) ^ (-(1/2 : ℝ)) := by
  obtain ⟨ψ, hle, hp, hm, hdef⟩ := rowCharacter_primitive_selected_deficit S hS u
  refine ⟨ψ, hle, hp, hm, ?_⟩
  intro k P hP hdis j hj hdiv a e ha he
  apply allocation_of_deficit _ (fun i => prime_norm_ge_one _ (hP i)) j hj
    _ _ a e (by positivity) ha he
  exact_mod_cast hdef k P hP hdis j hj hdiv

lemma actual_multiplicity_divisor (u : FreeRow) (p : O) (hp : Prime p) :
    (Ideal.span {p} : Ideal O) ^ multiplicity p u.val ∣ Ideal.span {u.val} ∧
      multiplicity p u.val < 6 := by
  refine ⟨⟨Ideal.span {unitPart u p hp}, ?_⟩, multiplicity_lt_six u p hp⟩
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_mul_span_singleton]
  exact congrArg (fun x : O => (Ideal.span {x} : Ideal O)) (unitPart_spec u p hp).1

lemma actual_ideal_multiplicity (u : FreeRow) (P : Ideal O) (hP : Prime P) :
    P ^ multiplicity P (Ideal.span {u.val} : Ideal O) ∣ Ideal.span {u.val} ∧
      multiplicity P (Ideal.span {u.val} : Ideal O) < 6 := by
  refine ⟨pow_multiplicity_dvd _ _, ?_⟩
  rw [UniqueFactorizationMonoid.multiplicity_eq_count_normalizedFactors hP.irreducible
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1), normalize_eq]
  exact u.property.2 P

theorem buffered_reflected_right_bound (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι), (χ j).residue ≠ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) (1-conj w)‖ ≤
        C * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_regular_control e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hwr : (1-conj w).re = a+6*e := by simp; linarith
  have hwm : (1-conj w).im = w.im := by simp
  have hz : 1-conj w ∈ Metric.closedBall ((2 : ℂ)+w.im*I) (2-a-6*e) := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    have heq : 1-conj w-((2 : ℂ)+w.im*I) = ((a+6*e-2 : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; linarith
      · simp
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have h := hb χ B a i hB ha ha1 hmax j w.im hwi (1-conj w) hz
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal _ hχ] at h
  have hH : 0 ≤ (3*i+2 : ℕ)*B := (abs_nonneg _).trans hwi
  have hc : presentationComplexity (χ j) w.im ≤
      presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    gcongr
  apply (le_trans (le_add_of_nonneg_right (norm_nonneg _)) h).trans
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by
    unfold presentationComplexity HeckeLogarithmic.complexity; positivity) hc hε.le) hC.le

theorem central_deletion_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (χ ψ : Character) (a e : ℝ),
      0 < e → 51/100 ≤ a → a ≤ 1 →
      ∀ w : ℂ, w.re = 1-a-6*e →
      ‖factors χ.modulus ψ w‖ * ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
        C * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+2*ε) := by
  obtain ⟨Cl, hCl, hl⟩ := factors_any_re_subpower_bound ε hε
  obtain ⟨Cr, hCr, hr⟩ := factors_radical_subpower_bound (1/2) ε (by norm_num) hε
  refine ⟨Cl*Cr, mul_pos hCl hCr, ?_⟩
  intro χ ψ a e he ha ha1 w hw
  have hR := HeckeDyadic.radical_norm_ge_one χ.modulus
  have hR0 : 0 < ((radical χ.modulus).absNorm : ℝ) := by linarith
  have hleft : ‖factors χ.modulus ψ w‖ ≤
      Cl * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+ε) := by
    apply (hl χ.modulus ψ w).trans
    apply mul_le_mul_of_nonneg_left _ hCl.le
    apply Real.rpow_le_rpow_of_exponent_le hR
    have hm : max (-w.re) 0 ≤ 6*e := max_le (by rw [hw]; linarith) (by positivity)
    linarith
  have hright : ‖(factors χ.modulus ψ (1-conj w))⁻¹‖ ≤
      Cr * ((radical χ.modulus).absNorm : ℝ) ^ ε := by
    exact (le_add_of_nonneg_left (norm_nonneg _)).trans
      (hr χ.modulus ψ (1-conj w) (by simp; linarith))
  calc
    _ ≤ (Cl * ((radical χ.modulus).absNorm : ℝ) ^ (6*e+ε)) *
        (Cr * ((radical χ.modulus).absNorm : ℝ) ^ ε) :=
      mul_le_mul hleft hright (norm_nonneg _) (by positivity)
    _ = _ := by
      rw [mul_mul_mul_comm, ← Real.rpow_add hR0]
      congr 2
      ring

theorem buffered_same_primitive_reflected (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type*} [Fintype ι] (χ : ι → Character)
      (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
      detectorMaximum χ (3*(i+1 : ℕ)*B) < a+2*e →
      ∀ (j : ι) (ψ : Character), FiniteFourier.IsPrimitiveOnIdeals ψ.residue →
      (χ j).residue ≠ 1 →
      (∀ I : Ideal O, idealCoeff (χ j) I =
        if IsCoprime I (χ j).modulus then idealCoeff ψ I else 0) →
      ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
      ‖LFunction (χ j) w‖ ≤ C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
        ((radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
        (3+(3*i+2 : ℕ)*B)^2 *
        (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨Cg, hCg, hg⟩ := HeckeDyadicReflection.original_reflected_bound
  obtain ⟨Cb, hCb, hb⟩ := buffered_reflected_right_bound e ε he he' hε
  obtain ⟨Cd, hCd, hd⟩ := central_deletion_bound ε hε
  refine ⟨Cg*Cb*Cd, by positivity, ?_⟩
  intro ι _ χ B a i hB ha ha1 hmax j ψ hp hχ hm w hw hwi
  have hr := hg (χ j) ψ hp hχ hm w (by rw [hw]; linarith) (by rw [hw]; linarith)
  have hexp : 1/2-w.re = a-1/2+6*e := by rw [hw]; ring
  rw [hexp] at hr
  have hright := hb χ B a i hB ha ha1 hmax j hχ w hw hwi
  have hdel := hd (χ j) ψ a e he ha ha1 w hw
  have hpc0 : 0 ≤ presentationComplexity (χ j) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  calc
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+|w.im|)^2 *
        ‖LFunction (χ j) (1-conj w)‖ *
        (‖factors (χ j).modulus ψ w‖ * ‖(factors (χ j).modulus ψ (1-conj w))⁻¹‖) := hr
    _ ≤ Cg * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) * (3+(3*i+2 : ℕ)*B)^2 *
        (Cb * (presentationComplexity (χ j) ((3*i+2 : ℕ)*B)) ^ ε) *
        (Cd * ((radical (χ j).modulus).absNorm : ℝ) ^ (6*e+2*ε)) := by
      gcongr
    _ = _ := by ring

theorem source_calibrated_reflected_allocation (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          ∀ (v : Fin k → ℕ), (∀ j, 2 ≤ v j) →
            (∀ j, P j ^ v j ∣ Ideal.span {u.val}) →
            ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := buffered_same_primitive_reflected e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hall⟩ := row_same_primitive_allocation S hS u
  have hactive (hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) :
      (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1 := by
    have hn := calibrated_row_nonprincipal S hS hmaxS hbad u hu hc
    exact ⟨hn, fun h => hn ((principal_iff_of_mask _ ψ hm).mpr h)⟩
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis v hv hdiv w hw hwi
  have hpc0 : 0 ≤ presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B) := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    positivity
  by_cases hc : (ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val = 0
  · simp only [hc, star_zero, zero_mul, norm_zero]
    positivity
  · have hn := (hactive hc).1
    have hL := hb (sourceDetectorFamily S hS η u twists) B a i hB ha ha1 hbin
      (Sum.inl true) ψ hp hn hm w hw hwi
    simp only [sourceDetectorFamily_numerator] at hL
    have hcal : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val)‖ ≤ 1 := by
      rw [norm_star]
      exact (ProbePhysical.calibrationForSet S hmaxS).residueMonoid_norm_le_one _
    have hweighted : ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
        HeckeOrigin.continued (rowCharacter S hS u) w‖ ≤ ‖LFunction (rowCharacter S hS u) w‖ := by
      rw [HeckeOrigin.continued, ite_eq_right hn, norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) hcal
    have hal := hall k P hP hdis v hv hdiv a e ha he
    rw [← hw] at hal
    have hprod0 : 0 ≤ ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
      Finset.prod_nonneg (fun j _ => Real.rpow_nonneg (by positivity) _)
    calc
      _ ≤ (C * (ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) :=
        mul_le_mul_of_nonneg_right (hweighted.trans hL) hprod0
      _ = (C * ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((ψ.modulus.absNorm : ℝ) ^ (a-1/2+6*e) *
          ∏ j, ((P j).absNorm : ℝ) ^ (-w.re)) := by ring
      _ ≤ (C * ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
          (3+(3*i+2 : ℕ)*B)^2 *
          (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε) *
          ((((fixedConductorConstant S : ℝ) * (Ideal.span {u.val} : Ideal O).absNorm) ^
            (a-1/2+6*e)) * ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hal (by positivity)
      _ = _ := by ring

theorem source_actual_valuation_reflection (e ε : ℝ)
    (he : 0 < e) (he' : e < 1/1000) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
      (hmaxS : ∀ P ∈ S, P.IsMaximal)
      (_hbad : CanonicalQuadraticSieve.fixedBadPrimes ⊆ S)
      (u : FreeRow), u.val ≠ 1 →
      ∃ ψ : Character, (rowCharacter S hS u).modulus ≤ ψ.modulus ∧
        FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
        (∀ I : Ideal O, idealCoeff (rowCharacter S hS u) I =
          if IsCoprime I (rowCharacter S hS u).modulus then idealCoeff ψ I else 0) ∧
        (((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val ≠ 0) →
          (rowCharacter S hS u).residue ≠ 1 ∧ ψ.residue ≠ 1) ∧
        ∀ {ι : Type*} [Fintype ι] (η : Character) (twists : ι → Character)
          (B a : ℝ) (i : ℕ), 2 < B → 51/100 ≤ a → a ≤ 1 →
          detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1 : ℕ)*B) < a+2*e →
          ∀ (k : ℕ) (P : Fin k → Ideal O), (∀ j, Prime (P j)) → Function.Injective P →
          (∀ j, 2 ≤ multiplicity (P j) (Ideal.span {u.val} : Ideal O)) →
          (∀ j, multiplicity (P j) (Ideal.span {u.val} : Ideal O) < 6) ∧
          ∀ w : ℂ, w.re = 1-a-6*e → |w.im| ≤ (3*i+2 : ℕ)*B →
            ‖star ((ProbePhysical.calibrationForSet S hmaxS).residueMonoid u.val) *
                HeckeOrigin.continued (rowCharacter S hS u) w‖ *
                ∏ j, ((P j).absNorm : ℝ) ^ (-w.re) ≤
              C * (((fixedConductorConstant S : ℝ) *
                (Ideal.span {u.val} : Ideal O).absNorm) ^ (a-1/2+6*e) *
                ∏ j, ((P j).absNorm : ℝ) ^ (-(1/2 : ℝ))) *
                ((radical (rowCharacter S hS u).modulus).absNorm : ℝ) ^ (6*e+2*ε) *
                (3+(3*i+2 : ℕ)*B)^2 *
                (presentationComplexity (rowCharacter S hS u) ((3*i+2 : ℕ)*B)) ^ ε := by
  obtain ⟨C, hC, hb⟩ := source_calibrated_reflected_allocation e ε he he' hε
  refine ⟨C, hC, ?_⟩
  intro S hS hmaxS hbad u hu
  obtain ⟨ψ, hle, hp, hm, hactive, hbound⟩ := hb S hS hmaxS hbad u hu
  refine ⟨ψ, hle, hp, hm, hactive, ?_⟩
  intro ι _ η twists B a i hB ha ha1 hbin k P hP hdis hv
  refine ⟨fun j => (actual_ideal_multiplicity u (P j) (hP j)).2, ?_⟩
  exact hbound η twists B a i hB ha ha1 hbin k P hP hdis
    (fun j => multiplicity (P j) (Ideal.span {u.val} : Ideal O)) hv
    (fun j => (actual_ideal_multiplicity u (P j) (hP j)).1)

end SevenEighths.ProbeRowReflectedAllocation

end

end OAI
end OAIOriginalModule2560

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralRepeatedProduct
Source SHA256: f39045d7916a6eafa0ede5783a30dd4a95de882a284dddfca261e01cd461997e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2561



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedProduct
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CompletedGauss ProbeRowReflectedAllocation
open HeckeDeletionBounds HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def rowCost (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : ℝ :=
  ((ProbeRowRadicalConductor.fixedConductorConstant S:ℝ)*(Ideal.span {u.val}:Ideal O).absNorm)^(a-1/2+6*e)*
    ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)^(6*e+2*eps)*
    (3+T)^2*(presentationComplexity (rowCharacter S hS u) T)^eps

lemma rowCost_nonneg (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (u : FreeRow)
    (a e eps T : ℝ) : 0≤rowCost S hS u a e eps T := by
  unfold rowCost presentationComplexity HeckeLogarithmic.complexity
  positivity

lemma repeated_weight_bound (η : Character) (u : FreeRow) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hs : Supported P.val) (hη : IsCoprime P.val η.modulus)
    (a e B Y : ℝ) (W : ℝ→ℂ) (x w z : ℂ)
    (hB : 0≤B) (hW : ∀t,‖W t‖≤B)
    (hQ : (480:ℝ)≤P.val.absNorm) (hsmall : 198*(P.val.absNorm:ℝ)^(-10*e)≤1/2)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he1 : e≤1/1000)
    (hx : x.re=a+16*e) (hw : w.re=1-a-6*e) (hz : z.re=17/50)
    (hr : repeatedRowPrime u P) :
    ‖W ((P.val.absNorm:ℝ)/Y)*(P.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P hs x w z‖≤
      (812*B*(P.val.absNorm:ℝ)^z.re)*(P.val.absNorm:ℝ)^(-w.re) := by
  have hp : (0:ℝ)<P.val.absNorm := by linarith
  have hb := (central_actual_local_bounds η u P hs hη a e x w z hQ hsmall ha ha1 he he1 hx hw hz).2.2
  rw [ite_eq_left hr] at hb
  have hn : ‖(P.val.absNorm:ℂ)^(z-1)‖=(P.val.absNorm:ℝ)^(z.re-1) := by
    rw [show (P.val.absNorm:ℂ)=(((P.val.absNorm:ℝ):ℂ)) by simp,
      Complex.norm_cpow_eq_rpow_re_of_pos hp]
    simp
  rw [norm_mul,norm_mul,hn]
  calc
    _ ≤ B*(P.val.absNorm:ℝ)^(z.re-1)*(812*(P.val.absNorm:ℝ)^(1-w.re)) := by
      gcongr
      exact hW _
    _ = _ := by
      calc
        _ = 812*B*((P.val.absNorm:ℝ)^(z.re-1)*(P.val.absNorm:ℝ)^(1-w.re)) := by ring
        _ = 812*B*(P.val.absNorm:ℝ)^(z.re-w.re) := by rw [←Real.rpow_add hp];congr 2;ring
        _ = _ := by rw [show z.re-w.re=z.re+(-w.re) by ring,Real.rpow_add hp];ring

theorem selected_repeated_product (e eps : ℝ) (he : 0<e) (he1 : e<1/1000)
    (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T a : ℝ) (i : ℕ),2<T → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T)<a+2*e →
    ∀(k : ℕ) (P : Fin k→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : ∀j,Supported (P j).val),
      Function.Injective P → (∀j,IsCoprime (P j).val η.modulus) →
      (∀j,(480:ℝ)≤(P j).val.absNorm) →
      (∀j,198*((P j).val.absNorm:ℝ)^(-10*e)≤1/2) →
      (∀j,repeatedRowPrime u (P j)) →
    ∀(B : ℝ) (W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),0≤B → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,‖W j (((P j).val.absNorm:ℝ)/Y j)*((P j).val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u (P j) (hs j) x w z‖ ≤
        C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*
          ∏j,((P j).val.absNorm:ℝ)^(z.re-1/2) := by
  obtain ⟨C,hC,hbound⟩ := source_calibrated_reflected_allocation e eps he he1 heps
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T a i hT ha ha1 hbin k P hs hdis hη hQ hsmall hr B W Y hB hW x w z hx hw hz hwi
  obtain ⟨ψ,hle,hprim,hmask,hactive,hb⟩ := hbound S hS hmax hbad u hu
  have hi : Function.Injective (fun j=>(P j).val) := fun j l h=>hdis (Subtype.ext h)
  have hdiv (j : Fin k) := actual_multiplicity_divisor u (primaryGenerator (P j).val) (supported_primeGenerator_prime (P j) (hs j))
  have hspan (j : Fin k) : (Ideal.span {primaryGenerator (P j).val}:Ideal O)=(P j).val := span_primaryGenerator_of_supported (P j).val (hs j)
  have hb' := hb η twists T a i hT ha ha1 hbin k (fun j=>(P j).val) (fun j=>(P j).property) hi
    (fun j=>multiplicity (primaryGenerator (P j).val) u.val) (fun j=>(hr j).2)
    (fun j=>by have hd := (hdiv j).1;rw [hspan j] at hd;exact hd) w hw hwi
  let q : Fin k→ℝ := fun j=>(P j).val.absNorm
  have hq (j : Fin k) : 0<q j := by dsimp [q];have := hQ j;linarith
  have hp : (∏j,‖W j (q j/Y j)*((P j).val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u (P j) (hs j) x w z‖)≤
      (812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re)) := by
    have ht := Finset.prod_le_prod₀ (s:=Finset.univ) (fun j (_:j∈Finset.univ)=>norm_nonneg _)
      (fun j (_:j∈Finset.univ)=>repeated_weight_bound η u (P j) (hs j) (hη j)
        a e B (Y j) (W j) x w z hB (hW j) (hQ j) (hsmall j) ha ha1 he he1.le hx hw hz (hr j))
    simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,mul_pow] using ht
  have hbc :
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ∏j,q j^(-w.re) ≤ C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)) := by
    convert hb' using 1 ; dsimp only [rowCost,q] ; ring
  have heq : (∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))=∏j,q j^(z.re-1/2) := by
    rw [←Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j _
    rw [←Real.rpow_add (hq j)]
    congr 1
  calc
    _ ≤ ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ((812*B)^k*(∏j,q j^z.re)*(∏j,q j^(-w.re))) := mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = ((812*B)^k*(∏j,q j^z.re))*(‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS u) w‖*∏j,q j^(-w.re)) := by ring
    _ ≤ ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ))) :=
      mul_le_mul_of_nonneg_left hbc (by positivity)
    _ = _ := by rw [show ((812*B)^k*(∏j,q j^z.re))*(C*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*∏j,q j^(-(1/2:ℝ)))=
      C*(812*B)^k*rowCost S hS u a e eps ((3*i+2:ℕ)*T)*((∏j,q j^z.re)*(∏j,q j^(-(1/2:ℝ)))) by ring,heq]
end SevenEighths.ProbeCentralRepeatedProduct

end

end OAI
end OAIOriginalModule2561

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralRepeatedSum
Source SHA256: 4ecd5c6ac202151f659fea564b5c0c4c681f7aa60c5f32f5537ce0b02b30c86a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2562


