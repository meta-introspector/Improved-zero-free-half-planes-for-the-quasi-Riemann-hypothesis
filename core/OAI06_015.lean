open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowPrimeIdealList (T : Finset PrimeIdeal) : Finset Id := T.image Subtype.val

def lowPrimeListEquiv (T : Finset PrimeIdeal) : T≃lowPrimeIdealList T :=
  Equiv.ofBijective (fun p=>⟨p.val.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩) (by
    constructor
    · intro p q h
      exact Subtype.ext (Subtype.ext (congrArg (fun x : lowPrimeIdealList T=>x.val) h))
    · intro I
      obtain ⟨P,hP,h⟩ := Finset.mem_image.mp I.property
      exact ⟨⟨P,hP⟩,Subtype.ext h⟩)

@[simp] lemma lowPrimeListEquiv_val (T : Finset PrimeIdeal) (p : T) :
    (lowPrimeListEquiv T p).val=p.val.val := rfl

lemma lowPrimeIdealList_prime (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : Prime I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact P.property

lemma lowPrimeIdealList_supported (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) : Supported I := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

lemma lowPrimeIdealList_maximal (T : Finset PrimeIdeal) (I : Id) (hI : I∈lowPrimeIdealList T) : I.IsMaximal :=
  (Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI)).isMaximal (lowPrimeIdealList_prime T I hI).ne_zero

lemma lowPrimeIdealList_good_odd (T : Finset PrimeIdeal) (hT : ∀P∈T,Supported P.val)
    (I : Id) (hI : I∈lowPrimeIdealList T) :
    ConcretePrimeRowBridge.goodLambda∉I ∧ ringChar (O⧸I)≠2 := by
  have hs := lowPrimeIdealList_supported T hT I hI
  exact hs.2 I ((Ideal.mem_normalizedFactors_iff hs.1).mpr
    ⟨Ideal.isPrime_of_prime (lowPrimeIdealList_prime T I hI),le_rfl⟩)

lemma lowPrimeIdealList_disjoint {ι : Type*} (T : ι→Finset PrimeIdeal)
    (hT : Pairwise (fun i j=>Disjoint (T i) (T j))) :
    Pairwise (fun i j=>Disjoint (lowPrimeIdealList (T i)) (lowPrimeIdealList (T j))) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro I hI hJ
  obtain ⟨P,hP,hPI⟩ := Finset.mem_image.mp hI
  obtain ⟨Q,hQ,hQI⟩ := Finset.mem_image.mp hJ
  have he : P=Q := Subtype.ext (hPI.trans hQI.symm)
  exact Finset.disjoint_left.mp (hT hij) hP (he.symm ▸ hQ)

lemma lowPrimeIdealList_norm (T : Finset PrimeIdeal) (H : ℝ)
    (hT : ∀P∈T,(Ideal.absNorm P.val:ℝ)≤H) (I : Id) (hI : I∈lowPrimeIdealList T) :
    (Ideal.absNorm I:ℝ)≤H := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact hT P hP

lemma lowPrimeIdealList_coprime (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (T : Finset PrimeIdeal)
    (I : Id) (hI : I∈lowPrimeIdealList (lowPeriodPrimeList η S hS T)) :
    IsCoprime I (lowPeriodIdeal η S hS) := by
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hI
  exact lowPeriodPrimeList_coprime η S hS T P hP

theorem low_actual_ideal_polynomial {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→Id)→ℂ) :
    (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (p i).val)*F (fun i=>Ideal.span {(p i).val}))=
    ∑p : ∀i,lowPrimeIdealList (lowPeriodPrimeList η S hS (T i)),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val) := by
  let E := Equiv.piCongrRight (fun i=>canonicalSlotEquiv (T i) (hT i))
  rw [←Equiv.sum_comp E]
  simp only [E,Equiv.piCongrRight_apply,Pi.map_apply,canonicalSlotEquiv_val]
  have hspan (p : ∀i,T i) (i : ι) : Ideal.span {primaryGenerator (p i).val.val}=(p i).val.val :=
    span_primaryGenerator_of_supported _ (hT i _ (p i).property)
  simp_rw [hspan]
  rw [low_canonical_polynomial_period_filter η S hS hbad T hT hout W Y t (fun p=>F (fun i=>(p i).val))]
  exact Equiv.sum_comp (Equiv.piCongrRight (fun i=>lowPrimeListEquiv (lowPeriodPrimeList η S hS (T i))))
    (fun p=>(∏i,lowSingleSlotWeight η (W i) (Y i) t (primaryGenerator (p i).val))*F (fun i=>(p i).val))

lemma low_actual_ideal_weight_bound (η : HeckeFamily.Character) (W : ℝ→ℂ)
    (hW : ∀x,‖W x‖≤1) (Y t : ℝ) (I : Id) :
    ‖lowSingleSlotWeight η W Y t (primaryGenerator I)‖≤1 :=
  (lowSingleSlotWeight_norm η W Y t _).trans (hW _)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1918

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowActualReflectedEnergy
Source SHA256: 734d2beea6df9a2b319f30493a872c9e5c6a355a0c546c5161b557bb9eef6285
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1919



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

def lowActualIdealPolynomial {ι : Type*} [Fintype ι]
    (L : ι→Finset Id) (w : ι→Id→ℂ) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) : ℂ :=
  ∑p : ∀i,L i,(∏i,w i (p i).val)*InverseMoment.markedCompletedT Ψ W X
    (fun A=>∏i,if (p i).val∣A then (1:ℂ) else 0)

theorem lowSelectedInverseRow_actual_ideal {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (z : O) :
    lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        lowActualIdealPolynomial
          (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
          (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X := by
  rw [lowSelectedInverseRow_correction]
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  simp_rw [lowSelectedWeight_eq_product]
  have hm (b : LowSelectedTuple (fun i=>canonicalSlotSupport (T i)) J) :
      (fun A : Id=>if lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0) := by
    funext A
    exact lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b) A
  simp_rw [hm,←physical_markedCompletedT_absorb_true_period η S hS hbad σ χ]
  convert low_actual_ideal_polynomial η S hS hbad (fun i : SelectedSlot J=>T i.val)
    (fun i=>hT i.val) (fun i=>hout i.val) (fun i=>W i.val) (fun i=>Y i.val) t
    (fun p=>InverseMoment.markedCompletedT
      (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
      (fun A=>∏i : SelectedSlot J,if p i∣A then (1:ℂ) else 0)) using 1
  · congr 1
    ext p
    simp
  · rfl

theorem lowSelectedInverseRow_actual_reflected_energy {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=>Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖lowSelectedInverseRow Finset.univ
      (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
    lowCorrectionEnergy*∑χ : RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
      ‖lowActualIdealPolynomial
        (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) X‖^2 := by
  simp_rw [lowSelectedInverseRow_actual_ideal η S hS hbad T hT hout hdis J W Y X t σ]
  apply (fixed_correction_energy R ProbeCompleted.correctionCoeff _).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (lowReflectionMask η S hS) (fun Ψ=>lowActualIdealPolynomial
      (fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
      (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I)) Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1919

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSelectedBound
Source SHA256: 766514b55a0c29c78f12dbf72bea2f35289a772f2fd36ac7f24c0410dcda4161
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1920



namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units

lemma gaussianFixedWindow_support : Function.support gaussianFixedWindow⊆Set.Icc (1/2:ℝ) 2 := by
  intro y hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))

lemma lowReflectionMask_bad_ideals (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    ∀P∈fixedBadPrimes,P∣Ideal.span {lowReflectionMask η S hS}*(1:Id) := by
  intro P hP
  rw [mul_one,lowReflectionMask,←Ideal.span_singleton_mul_span_singleton,calibrationForSet_span]
  exact dvd_mul_of_dvd_left (Finset.dvd_prod_of_mem (fun P : Id=>P) (hbad hP)) _

theorem low_selected_physical_energy (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (K : ℕ) (Ck ε : ℝ) (hCk : 0<Ck) (hε : 0<ε) (hε1 : ε≤1) :
    ∃degree : ℕ,∃C Z₀ : ℝ,0<C ∧ 1<Z₀ ∧
    ∀(Z d ell0 shift : ℝ),Z₀≤Z→0≤d→d≤1/6→0≤ell0→ell0≤1/6-d+ε→|shift|≤ε→
    ∀(R : Finset O),(∀z∈R,z≠0 ∧ elementNorm z≤Ck*Z^(5/6-2*d))→
    ∀(T : Fin K→Finset PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=>Disjoint (T i) (T j))→
    ∀(J : Finset (Fin K))(H : SelectedSlot J→ℝ),
      (∀i,1≤H i)→(∀i P,P∈T i.val→(Ideal.absNorm P.val:ℝ)≤H i)→(∏i,H i)≤Z^ell0→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀(Y : Fin K→ℝ)(t : ℝ)(σ : RayRing),
      (∑z∈R,‖lowSelectedInverseRow Finset.univ
        (lowSelectedWeight η (fun i=>canonicalSlotSupport (T i)) J W Y t)
        η S hS (lowSelectedIdeal (fun i=>canonicalSlotSupport (T i)) J) (Z^(1+ell0+shift)) t σ z‖^2)≤
        C*(1+‖t‖)^degree*Z^((5/6-2*d)+507*ε) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := InverseReflectedPhase.low_original_completed_energy
    (lowReflectionPeriod η S hS) (lowReflectionPeriod_ne_zero η S hS)
    (1:Id) squarefree_one (lowReflectionMask η S hS) (lowReflectionMask_ne_zero η S hS)
    (lowReflectionMask_bad η S hS hbad).1 (lowReflectionMask_bad η S hS hbad).2
    (lowReflectionMask_period η S hS) (lowReflectionMask_bad_ideals η S hS hbad)
    (1/2) 2 (by norm_num) gaussianFixedWindow gaussianFixedWindow_support gaussianFixedWindow_contDiff
    Ck ε hCk hε hε1 K
  let C0 := (lowCorrectionEnergy+1)*((Fintype.card RayCharacter:ℝ)+1)*6*C
  have hC0 : 0<C0 := by have hh := lowCorrectionEnergy_nonneg;dsimp [C0];positivity
  refine ⟨degree,C0,Z₀,hC0,hZ₀,?_⟩
  intro Z d ell0 shift hZ hd hd1 hell hellcap hshift R hR T hT hout hdis J H hH1 hH hprod W hW Y t σ
  let L := fun i : SelectedSlot J=>lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val))
  have hLP (i : SelectedSlot J) : lowPeriodPrimeList η S hS (T i.val)⊆T i.val := Finset.filter_subset _ _
  have hLS (i : SelectedSlot J) : ∀P∈lowPeriodPrimeList η S hS (T i.val),Supported P.val :=
    fun P hP=>hT i.val P (hLP i hP)
  have hlists : Pairwise (fun i j=>Disjoint (L i) (L j)) :=
    lowPrimeIdealList_disjoint _ (lowPeriodPrimeList_disjoint η S hS _
      (fun i j hij=>hdis (fun h=>hij (Subtype.ext h))))
  have hparents : ∀I∈lowIdealRows R,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) :=
    fun I hI=>⟨lowIdealRows_nonzero R (fun z hz=>(hR z hz).1) I hI,
      lowIdealRows_norm_bound R _ (fun z hz=>(hR z hz).2) I hI⟩
  have hcard : Fintype.card (SelectedSlot J)≤K := by
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using
      Finset.card_le_card (Finset.subset_univ (Finset.univ\J))
  have hrow (χ : RayCharacter) (u : Oˣ) :
      (∑I∈lowIdealRows R,‖lowActualIdealPolynomial L
        (fun i I=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator I))
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (ConcretePrimeRowBridge.idealGenerator (1:Id)) (u.val*ConcretePrimeRowBridge.idealGenerator I))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) (Z^(1+ell0+shift))‖^2)≤
          C*(1+‖t‖)^degree*Z^((5/6-2*d)+507*ε) := by
    convert he Z d ell0 shift hZ hd hd1 hell hellcap hshift (lowIdealRows R) hparents hcard L H
      hlists (fun i=>lowPrimeIdealList_maximal _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).1)
      (fun i=>lowPrimeIdealList_prime _)
      (fun i P hP=>(lowPrimeIdealList_good_odd _ (hLS i) P hP).2)
      hH1 (fun i=>lowPrimeIdealList_norm _ _ (fun P hP=>hH i P (hLP i hP))) hprod
      (physicalRayPeriodicBase η S hS σ χ) (lowReflectionPeriod_actual η S hS σ χ).2
      (lowReflectionPeriod_actual η S hS σ χ).1 u t
      (fun i P=>lowSingleSlotWeight η (W i.val) (Y i.val) t (primaryGenerator P.val))
      (fun i P=>low_actual_ideal_weight_bound η (W i.val) (hW i.val) (Y i.val) t P.val) using 1
    apply Finset.sum_congr rfl
    intro I hI
    congr 2
    unfold lowActualIdealPolynomial
    congr 1
    ext p
    simp
  apply (lowSelectedInverseRow_actual_reflected_energy η S hS hbad T hT hout hdis J W Y
    (Z^(1+ell0+shift)) t σ R (fun z hz=>(hR z hz).1)).trans
  have hh := Finset.sum_le_sum (fun χ (_ : χ∈(Finset.univ:Finset RayCharacter))=>
    Finset.sum_le_sum (fun u (_ : u∈(Finset.univ:Finset Oˣ))=>hrow χ u))
  have hm := mul_le_mul_of_nonneg_left hh lowCorrectionEnergy_nonneg
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,low_unit_card] at hm
  simp only [Nat.cast_ofNat,Real.norm_eq_abs] at hm ⊢
  apply hm.trans
  dsimp [C0]
  have hc0 := lowCorrectionEnergy_nonneg
  have hcount : 0≤(Fintype.card RayCharacter:ℝ) := Nat.cast_nonneg _
  have hzpos : 0≤Z^((5/6-2*d)+507*ε) := Real.rpow_nonneg (le_trans zero_le_one (hZ₀.le.trans hZ)) _
  have htpos : 0≤(1+|t|)^degree := by positivity
  calc
    _=(lowCorrectionEnergy*(Fintype.card RayCharacter:ℝ)*6*C)*(1+|t|)^degree*
        Z^((5/6-2*d)+507*ε) := by ring
    _≤_ := by gcongr <;> linarith

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1920

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowTupleGram
Source SHA256: d3235add8c39a0637cb6fbcb55dc270c2456c2c6c031df4449b5eb5ab5c890a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1921



namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowGramFactor (C : CalibrationData) (X Y δ : ℝ) : ℝ :=
  Real.sqrt ((lowPhysicalScale C X Y/Y)*(1+(Y^2/lowPhysicalScale C X Y)^(1/6:ℝ)+
    (Y^2/lowPhysicalScale C X Y)^2/Y)*Y^δ)

def lowInverseMass (C : CalibrationData) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) : ℝ :=
  ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a b ha hb (lowPhysicalScale C X Y)
    (lowPhysicalScale_pos C X Y hX hY),‖B σ m‖^2)

lemma lowInverseMass_nonneg (C : CalibrationData) (a b : ℝ) (ha : 0<a) (hb : 0<b)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (B : RayRing→O→ℂ) :
    0≤lowInverseMass C a b ha hb X Y hX hY B :=
  Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _)

lemma low_mellin_normalizer_norm (Q : ℝ) (_hQ : 0<Q) :
    ‖(Real.sqrt Q:ℂ)⁻¹*(1/(2*Real.pi):ℂ)‖=(Real.sqrt Q)⁻¹/(2*Real.pi) := by
  rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [norm_div,norm_one,norm_mul]
  norm_num [Complex.norm_real,Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  ring

theorem compensation_tuple_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hab1 : a1<b1) (hM : 0≤M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M) :
    ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
    ∃C : ℝ,0<C ∧ ∀(K : ℕ)(η : HeckeFamily.Character)(slots : Fin K→Finset O)
      (hslots : ∀i x,x∈slots i→x≠0)(J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ)
      (X Y T t : ℝ)(hX : 0<X)(hY : 0<Y)(_hT : 0<T),
      (∀a : LowUnselectedTuple slots J,1≤Y/elementNorm (∏i : J,(a i).val))→
      (∀a : LowUnselectedTuple slots J,
        1≤(Y/elementNorm (∏i : J,(a i).val))^2/
          lowPhysicalScale (calibrationForSet S hS) (X/elementNorm (∏i : J,(a i).val))
            (Y/elementNorm (∏i : J,(a i).val)))→
      ‖∑p : (∀i,↥(slots i)),compensationSubsetWeight η W P (fun i=>(p i).val) J*
        compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
          selectedSlotFactor W P (fun i=>(p i).val) J t‖≤
      C*∑a : LowUnselectedTuple slots J,
        ‖lowUnselectedWeight slots J W P a‖*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))))⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val)) δ*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
          (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (div_pos hX (lowUnselectedProduct_norm_pos slots hslots J a))
          (div_pos hY (lowUnselectedProduct_norm_pos slots hslots J a))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
            η S hS (lowSelectedIdeal slots J) T t) := by
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  intro S hS hbad
  obtain ⟨C,hC,hgram⟩ := lowSeparatedIntegral_actual_gram δ hδ hδ1 a1 b1 M ha1 hab1 hM
    W1 hW1c hW1 hW1s hWM (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) W0 a0 b0 ha0 hW0 hW0s S hS hbad
  refine ⟨C,hC,?_⟩
  intro K η slots hslots J W P X Y T t hX hY hT hYs hPs
  rw [compensation_tuple_low_polynomial η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hW0s
    slots hslots J W P X Y T t hX hY hT]
  apply (norm_sum_le _ _).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  have hh := hgram (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
    (div_pos hX hL) (hYs a)
    (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W P t)
      η S hS (lowSelectedIdeal slots J) T t) (hPs a)
  rw [norm_mul,norm_mul,low_mellin_normalizer_norm _ (lowPhysicalScale_pos _ _ _ (div_pos hX hL) (div_pos hY hL))]
  calc
    _≤‖lowUnselectedWeight slots J W P a‖*
      ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))))⁻¹/(2*Real.pi))*
      (C*lowGramFactor (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val)) δ*
      lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1))
        (mul_pos ha0 ha1) (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
        (div_pos hX hL) (div_pos hY hL) _) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _=_ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1921

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSourceScales
Source SHA256: 6151ef7adff228aba72f9c7b85eab4d31a7ac3d76d85cd156227a4e935e94de2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1922




namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma source_scale_ratio (Z : ℝ) (hZ : 0<Z) :
    Z^(23/48:ℝ)/Z^(17/48:ℝ)=Z^(1/8:ℝ) := by
  rw [←Real.rpow_sub hZ]
  norm_num

lemma source_scale_square (Z : ℝ) (hZ : 0<Z) :
    Z^(11/48:ℝ)*Z^(23/48:ℝ)=(Z^(17/48:ℝ))^2 := by
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  norm_num

lemma source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(1/8:ℝ)) (hLl : L≤Z^(11/48:ℝ)) :
    1≤Z^(23/48:ℝ)/L ∧
    q*Z^(17/48:ℝ)≤Z^(23/48:ℝ) ∧
    L*Z^(23/48:ℝ)≤q^2*(Z^(17/48:ℝ))^2 := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show (11/48:ℝ)≤23/48 by norm_num))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (17/48))).mp
    rwa [source_scale_ratio Z hz]
  · calc
      _≤Z^(11/48:ℝ)*Z^(23/48:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(17/48:ℝ))^2 := source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(1/8:ℝ)) (hLl : L≤Z^(11/48:ℝ)) (hδ : 0≤δ) :
    (q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)/(Z^(23/48:ℝ)/L))*
      (1+((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^2/(Z^(23/48:ℝ)/L))*
      (Z^(23/48:ℝ)/L)^δ ≤
        (3*q/L)*Z^(3/8+(23/48)*δ:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0<L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(23/48:ℝ)/(q*Z^(17/48:ℝ))≤Z^(1/8:ℝ) := by
    rw [←source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(23/48:ℝ)/(q*Z^(17/48:ℝ))) hratio (show 0≤(1/6:ℝ) by norm_num)
  calc
    _≤3*(q*Z^(17/48:ℝ)/L)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(23/48:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(17/48:ℝ)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(23/48:ℝ))^δ) := by ring
    _=_ := by rw [source_gram_power Z δ hz]

lemma source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤q) (hZ : 1≤Z)
    (hL : 1≤L) (hql : q≤Z^(1/8:ℝ)) (hLl : L≤Z^(11/48:ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)/(Z^(23/48:ℝ)/L))*
      (1+((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(23/48:ℝ)/L)^2/(q*(Z^(17/48:ℝ)/L)*(Z^(23/48:ℝ)/L)))^2/(Z^(23/48:ℝ)/L))*
      (Z^(23/48:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  apply (Real.sqrt_le_sqrt (source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤Z)
    (hL : 1≤L) (hql : elementNorm C.generator≤Z^(1/8:ℝ))
    (hLl : L≤Z^(11/48:ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(3/16+(23/96)*δ:ℝ) :=
  source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧ elementNorm C.generator≤Z^(1/8:ℝ) ∧
      ∀L : ℝ,1≤L→L≤B*Z^(1/6:ℝ)→
        1≤Z^(23/48:ℝ)/L ∧
        1≤(Z^(23/48:ℝ)/L)^2/lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  have hq := (tendsto_rpow_atTop (show 0<(1/8:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<(1/16:ℝ) by norm_num)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤Z^(11/48:ℝ) := calc
    L≤B*Z^(1/6:ℝ) := hLB
    _≤Z^(1/16:ℝ)*Z^(1/6:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^(11/48:ℝ) := by rw [←Real.rpow_add hz];norm_num
  obtain ⟨hy,hp,_⟩ := source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=>lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1922

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowSlotScales
Source SHA256: 31f477ed5ee42505a53ea82aea9f7f982933f4ac4386adb232e82ad402e7fc3a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1923


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma elementNorm_finset_prod {ι : Type*} (F : Finset ι) (p : ι→O) :
    elementNorm (∏i∈F,p i)=∏i∈F,elementNorm (p i) := by
  induction F using Finset.induction_on with
  | empty => simp [elementNorm_one]
  | @insert i F hi ih => simp only [Finset.prod_insert hi,elementNorm_mul,ih]

lemma lowUnselectedProduct_norm_ge_one {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    1≤elementNorm (∏i : J,(a i).val) := by
  have hn : (∏i : J,(a i).val)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hslots i.val _ (a i).property)
  unfold elementNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hn))

lemma lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6)
    (b Z : ℝ) (hb : 1≤b) (hZ : 1≤Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤b^K*Z^(1/6:ℝ) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤1/6 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=>hell i)).trans hsum
  have hc : J.card≤K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=>by unfold elementNorm;positivity)
      (fun i _=>hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤b^K*Z^(1/6:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ell i) (hsum : ∑i,ell i≤1/6) (b : ℝ) (hb : 1≤b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤Z^(23/48:ℝ)/L ∧
      1≤(Z^(23/48:ℝ)/L)^2/lowPhysicalScale C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(17/48:ℝ)/L) (Z^(23/48:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(3/16+(23/96)*δ:ℝ) := by
  filter_upwards [eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1923

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowUnselectedMass
Source SHA256: f990fd7ad91c20736be9c1a43719301b46b7cf3ed3efff33950b4c833327a879
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1924



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "SupportedIdeal" => {I : Ideal O // Supported I}

lemma canonical_slot_inverse_square : ∃C : ℝ,0<C ∧
    ∀(T : Finset PrimeIdeal)(_hT : ∀P∈T,Supported P.val),
      (∑a : canonicalSlotSupport T,elementNorm a.val^(-2:ℝ))≤C := by
  obtain ⟨C,hC,hb⟩ := ProbeGramCommon.supportedIdeal_rpow_finite_bound (-2) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro T hT
  let f : T→SupportedIdeal := fun P=>⟨P.val.val,hT P.val P.property⟩
  have hf : Function.Injective f := by
    intro P Q h
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun I : SupportedIdeal=>I.val) h
  have he : (∑a : canonicalSlotSupport T,elementNorm a.val^(-2:ℝ))=
      ∑I∈Finset.univ.image f,ProbeGramCommon.gramIdealNorm I^(-2:ℝ) := by
    rw [Finset.sum_image (fun P _ Q _ h=>hf h)]
    have hh := (canonicalSlotEquiv T hT).sum_comp (fun a=>elementNorm a.val^(-2:ℝ))
    rw [←hh]
    apply Finset.sum_congr rfl
    intro P hP
    rw [canonicalSlotEquiv_norm]
    rfl
  rw [he]
  exact hb _

lemma lowUnselectedWeight_norm_identity {K : ℕ} (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→x≠0) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (a : LowUnselectedTuple slots J) :
    ‖lowUnselectedWeight slots J W P a‖*elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ))=
      ∏i : J,elementNorm (a i).val^(-2:ℝ)*‖W i.val (elementNorm (a i).val/P i.val)‖ := by
  have hL := lowUnselectedProduct_norm_pos slots hslots J a
  rw [lowUnselectedWeight,norm_mul,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hL.le _),norm_prod]
  calc
    _=(elementNorm (∏i : J,(a i).val)^(-(3/2:ℝ))*elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ)))*
        ∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by ring
    _=elementNorm (∏i : J,(a i).val)^(-2:ℝ)*∏i : J,‖W i.val (elementNorm (a i).val/P i.val)‖ := by
      rw [←Real.rpow_add hL]
      norm_num
    _=_ := by
      rw [elementNorm_finset_prod,Finset.prod_mul_distrib,Real.finsetProd_rpow Finset.univ
        (fun i : J=>elementNorm (a i).val) (fun i _=>by unfold elementNorm;positivity)]

theorem lowUnselectedMass_bound (K : ℕ) (M : ℝ) (hM : 0≤M) :
    ∃C : ℝ,0<C ∧ ∀(T : Fin K→Finset PrimeIdeal)(_hT : ∀i P,P∈T i→Supported P.val)
      (J : Finset (Fin K))(W : Fin K→ℝ→ℂ)(P : Fin K→ℝ),
      (∀i x,‖W i x‖≤M)→
      (∑a : LowUnselectedTuple (fun i=>canonicalSlotSupport (T i)) J,
        ‖lowUnselectedWeight (fun i=>canonicalSlotSupport (T i)) J W P a‖*
          elementNorm (∏i : J,(a i).val)^(-(1/2:ℝ)))≤C := by
  obtain ⟨C,hC,hb⟩ := canonical_slot_inverse_square
  refine ⟨(max 1 (C*M))^K,by positivity,?_⟩
  intro T hT J W P hW
  simp_rw [lowUnselectedWeight_norm_identity _ (fun i=>canonicalSlotSupport_nonzero _ (hT i))]
  rw [←Fintype.prod_sum (fun (i : J) (a : canonicalSlotSupport (T i.val))=>
    elementNorm a.val^(-2:ℝ)*‖W i.val (elementNorm a.val/P i.val)‖)]
  calc
    _≤∏i : J,C*M := by
      apply Finset.prod_le_prod₀ (fun i _=>Finset.sum_nonneg (fun a _=>mul_nonneg (Real.rpow_nonneg (by unfold elementNorm;positivity) _) (norm_nonneg _)))
      intro i hi
      calc
        _≤∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-2:ℝ)*M := by
          apply Finset.sum_le_sum
          intro a ha
          exact mul_le_mul_of_nonneg_left (hW i.val _) (Real.rpow_nonneg (by unfold elementNorm;positivity) _)
        _=(∑a : canonicalSlotSupport (T i.val),elementNorm a.val^(-2:ℝ))*M := (Finset.sum_mul ..).symm
        _≤C*M := mul_le_mul_of_nonneg_right (hb _ (hT i.val)) hM
    _≤∏_i : J,max 1 (C*M) := Finset.prod_le_prod₀ (fun _ _=>by positivity) (fun _ _=>le_max_right _ _)
    _≤_ := by
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_coe]
      exact pow_le_pow_right₀ (le_max_left _ _) (by simpa using Finset.card_le_card (Finset.subset_univ J))

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1924

/-! Original module: OAI.NumberTheory.DirichletL.Detector.TuplePrincipal
Source SHA256: 725c0abcc507c786f8cbfe4dae744833d047b0175abd60d8f5e8831dad0689d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1925


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve ProbeEuler ProbeLocal
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem indexedCompensatedHigh_principal_continued {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (P : Fin K→PrimeIdeal)
    (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    indexedCompensatedHigh η S (fun i=>primaryGenerator (P i).val) 1 x w z=
      (HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeFamily.LFunction (fixedSourcePrincipal S hS.prime) w /
        HeckeFamily.LFunction (η.excludePrimes S hS.prime) x*globalClosedCorrection η S x w z)*
      ∏i,compensatedReplacement (coordV (Ideal.absNorm (P i).val) z)
        (coordW (Ideal.absNorm (P i).val) 1 w)
        (coordD (Ideal.absNorm (P i).val) (HeckeFamily.idealCoeff η (P i).val) 1 x)
        (idealMarkedClosed η (P i) x w z)
        (star (HeckeFamily.idealCoeff η (P i).val)*(Ideal.absNorm (P i).val:ℂ)^x)
        ((Ideal.absNorm (P i).val:ℂ)^(-w))/idealClosedCorrection η (P i) x w z := by
  have hs (i : Fin K) : Supported (P i).val := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_principal η S P hP hs]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedHigh_continued S hS (Finset.univ.image P) ht η x w z _ _ hx hw hz,
    Finset.prod_image hP.injOn]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1925

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CompensatedTriple
Source SHA256: 122de2c8cdfd7171fbf9214f2beb5f9eb6ef61d8e9d99bbe83a51e613f01f386
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1926


namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def compensatedRowSeries {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (x w z : ℂ) : ℂ :=
  (∏i,(elementNorm (p i):ℂ)^(z-1))*
    ∑'u : FreeRow,star (C.residueMonoid u.val)*frequencyWeight z ⟨u.val,u.property.1⟩*
      indexedCompensatedHigh η S p u.val x w z

def compensatedRowTripleIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    compensatedRowSeries η S C p ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

lemma tupleSourceTripleIntegral_eq_rows {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (W0 W1 : SchwartzMap ℝ ℂ) (p : Fin K→O)
    (hp : ∀i,p i≠0) (X Y Z : ℝ) :
    tupleSourceTripleIntegral η S C W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S C W0 W1 p X Y Z := by
  unfold tupleSourceTripleIntegral compensatedRowTripleIntegral
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  exact tupleSourceSeries_eq_rows η S C p hp
    ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])
    (by norm_num [Complex.add_re,Complex.mul_re])

theorem compensatedTuple_eq_row_triple {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (p : Fin K→O) (hp : ∀i,p i≠0)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedTuple η (calibrationForSet S hS) W0 W1 p X Y Z=
      compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 p X Y Z := by
  rw [compensatedTuple_eq_source_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    p hp X Y Z hX hY hZ,tupleSourceTripleIntegral_eq_rows η S _ W0 W1 p hp]

theorem compensatedPhysicalProbe_eq_row_triples {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (slotPrimes : Fin K→Finset O) (hp : ∀i a,a∈slotPrimes i→a≠0)
    (slotWindow : Fin K→ℝ→ℂ) (slotScale : Fin K→ℝ)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1 slotPrimes slotWindow slotScale X Y Z=
      ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
        (∏i,slotWindow i (elementNorm (p i).val/slotScale i))*
        compensatedRowTripleIntegral η S (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) X Y Z := by
  unfold compensatedPhysicalProbe
  apply Finset.sum_congr rfl
  intro p _
  rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (fun i=>(p i).val) (fun i=>hp i (p i).val (p i).property) X Y Z hX hY hZ]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1926

/-! Original module: OAI.NumberTheory.DirichletL.Detector.InitialRows
Source SHA256: 529e6c4c8d20a081dfc176eb71a07df8a099bbd06e7450f00d023771e9b88b5e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1927


namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def highRowOnLines (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  star (C.residueMonoid u.val)*frequencyWeight ((ξ:ℂ)+t.1.2*Complex.I) u*
    markedIdealHighSeries S D η u.val ((σ:ℂ)+t.1.1*Complex.I)
      ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)

lemma highRowOnLines_eq_tsum (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (u : NonzeroFrequency) (t : HeightSpace) :
    highRowOnLines η S C D σ υ ξ u t=
      ∑'q : (Id×Id)×(Id×Id),initialHighOnLines S D η (fun H=>star (C.residueMonoid H.val))
        σ υ ξ (u,q) t := by
  unfold highRowOnLines markedIdealHighSeries initialHighOnLines fullHighCoefficient
  exact (tsum_mul_left (a:=star (C.residueMonoid u.val)*frequencyWeight ((ξ:ℂ)+t.1.2*Complex.I) u)
    (f:=fun q : (Id×Id)×(Id×Id)=>markedIdealHighSummand S D η u.val
      ((σ:ℂ)+t.1.1*Complex.I) ((υ:ℂ)+t.2*Complex.I) ((ξ:ℂ)+t.1.2*Complex.I)
      q.1.1 q.1.2 q.2.1 q.2.2)).symm

lemma initialHighMajorant_row_summable (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ)
    (u : NonzeroFrequency) : Summable (fun q : (Id×Id)×(Id×Id)=>initialHighMajorant σ υ ξ (u,q)) := by
  unfold initialHighMajorant
  exact (highAbsoluteMajorant_summable (σ:ℂ) (υ:ℂ) (ξ:ℂ) hσ hυ hξ).mul_left ‖frequencyWeight (ξ:ℂ) u‖

lemma highRowOnLines_continuous (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ) (u : NonzeroFrequency) :
    Continuous (highRowOnLines η S C D σ υ ξ u) := by
  change Continuous (fun t=>highRowOnLines η S C D σ υ ξ u t)
  simp_rw [highRowOnLines_eq_tsum]
  apply continuous_tsum _ (initialHighMajorant_row_summable σ υ ξ hσ hυ hξ u)
    (fun q t=>initialHighOnLines_norm_le S D η (fun H=>star (C.residueMonoid H.val))
      (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val) σ υ ξ (u,q) t)
  intro q
  exact initialHighOnLines_continuous S D η _ σ υ ξ (u,q)

lemma highRowOnLines_bound (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1/6<ξ) (u : NonzeroFrequency) (t : HeightSpace) :
    ‖highRowOnLines η S C D σ υ ξ u t‖≤
      ‖frequencyWeight (ξ:ℂ) u‖*(∑'q : (Id×Id)×(Id×Id),highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) q) := by
  rw [highRowOnLines_eq_tsum]
  have hm := initialHighMajorant_row_summable σ υ ξ hσ hυ hξ u
  have hb (q : (Id×Id)×(Id×Id)) := initialHighOnLines_norm_le S D η
    (fun H=>star (C.residueMonoid H.val))
    (fun H=>by simpa only [norm_star] using C.residueMonoid_norm_le_one H.val) σ υ ξ (u,q) t
  have hs := Summable.of_nonneg_of_le (fun q=>norm_nonneg _) hb hm
  apply (norm_tsum_le_tsum_norm hs).trans
  have he := hs.tsum_le_tsum hb hm
  simpa only [initialHighMajorant,tsum_mul_left] using he

lemma highRows_counting_product_integrable {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (e : ρ→NonzeroFrequency) (he : Function.Injective e)
    (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData) (D : Id)
    (σ υ ξ : ℝ) (hσ : 3/2<σ) (hυ : 2<υ) (hξ : 1<ξ)
    (T : HeightSpace→ℂ) (hT : Integrable T heightMeasure) (hcT : Continuous T) :
    Integrable (fun p : ρ×HeightSpace=>highRowOnLines η S C D σ υ ξ (e p.1) p.2*T p.2)
      ((Measure.count:Measure ρ).prod heightMeasure) := by
  let A : ℝ := ∑'q : (Id×Id)×(Id×Id),highAbsoluteMajorant (σ:ℂ) (υ:ℂ) (ξ:ℂ) q
  have hA : 0≤A := tsum_nonneg (highAbsoluteMajorant_nonneg _ _ _)
  have hb : Integrable (fun r : ρ=>‖frequencyWeight (ξ:ℂ) (e r)‖*A) Measure.count := by
    rw [integrable_count_iff]
    simpa only [Function.comp_def,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (norm_nonneg _) hA)] using
      ((frequencyWeight_summable_norm (ξ:ℂ) hξ).comp_injective he).mul_right A
  apply (hb.mul_prod hT.norm).mono'
  · apply Measurable.aestronglyMeasurable
    apply measurable_from_prod_countable_right
    intro r
    exact ((highRowOnLines_continuous η S C D σ υ ξ hσ hυ (by linarith) (e r)).mul hcT).measurable
  · apply Filter.Eventually.of_forall
    intro p
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right
      (highRowOnLines_bound η S C D σ υ ξ hσ hυ (by linarith) (e p.1) p.2) (norm_nonneg _)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1927

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CompensatedRows
Source SHA256: 3107d4c3b40c7a1b78437fe8f8c8319a22f6caa270d76dfb39935c2669f77c3d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1928



namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def compensatedRowOnLines {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (C : CalibrationData) (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ)
    (u : NonzeroFrequency) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
    ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
  (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
    (star (C.residueMonoid u.val)*frequencyWeight ((2:ℂ)+t.1.2*Complex.I) u*
      indexedCompensatedHigh η S p u.val ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I))

lemma compensatedRows_counting_product_integrable {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (e : ρ→NonzeroFrequency) (he : Function.Injective e)
    {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (hp : ∀i,p i≠0) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun q : ρ×HeightSpace=>compensatedRowOnLines η S C p W0 W1 X Y Z (e q.1) q.2)
      ((Measure.count:Measure ρ).prod heightMeasure) := by
  let F : Finset (Fin K)→ρ×HeightSpace→ℂ := fun J q=>tuplePhysicalScalar η p J*
    (highRowOnLines η S C (Ideal.span {∏i∈Finset.univ\J,p i}) 3 3 2 (e q.1) q.2*
      sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i)) (Y/elementNorm (∏i∈J,p i))
        (Z*elementNorm (∏i∈Finset.univ\J,p i))
        ((3:ℂ)+q.2.1.1*Complex.I) ((3:ℂ)+q.2.2*Complex.I) ((2:ℂ)+q.2.1.2*Complex.I))
  have hF (J : Finset (Fin K)) : Integrable (F J) ((Measure.count:Measure ρ).prod heightMeasure) := by
    apply Integrable.const_mul
    apply highRows_counting_product_integrable e he η S C _ 3 3 2 (by norm_num) (by norm_num) (by norm_num)
      (fun t : HeightSpace=>sourceMellinWeight W0 W1 (X/elementNorm (∏i∈J,p i))
        (Y/elementNorm (∏i∈J,p i)) (Z*elementNorm (∏i∈Finset.univ\J,p i))
        ((3:ℂ)+t.1.1*Complex.I) ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I))
    · exact sourceMellinWeight_initial_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
        _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
        (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J))) 3 2 3 (by norm_num)
    · exact sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1
        _ _ _ (div_pos hX (tuple_norm_pos p hp J)) (div_pos hY (tuple_norm_pos p hp J))
        (mul_pos hZ (tuple_norm_pos p hp (Finset.univ\J))) 3 2 3 (by norm_num)
  have hi := integrable_finsetSum (Finset.univ:Finset (Fin K)).powerset (fun J _=>hF J)
  apply hi.congr
  apply Filter.Eventually.of_forall
  intro q
  symm
  exact compensatedRow_kernel_subsets η S p hp (e q.1).val
    (star (C.residueMonoid (e q.1).val)*frequencyWeight ((2:ℂ)+q.2.1.2*Complex.I) (e q.1))
    W0 W1 X Y Z hX hY hZ _ _ _

lemma counting_product_integral_tsum {ρ : Type*} [Countable ρ]
    [MeasurableSpace ρ] [MeasurableSingletonClass ρ]
    (F : ρ×HeightSpace→ℂ)
    (hF : Integrable F ((Measure.count:Measure ρ).prod heightMeasure)) :
    (∫t,∑'r,F (r,t) ∂heightMeasure)=∑'r,∫t,F (r,t) ∂heightMeasure := by
  calc
    _ = ∫t,∫r,F (r,t) ∂(Measure.count:Measure ρ) ∂heightMeasure := by
      apply integral_congr_ae
      filter_upwards [hF.prod_left_ae] with t ht
      exact (integral_count_eq_tsum _ ht).symm
    _ = ∫q,F q ∂((Measure.count:Measure ρ).prod heightMeasure) := (integral_prod_symm F hF).symm
    _ = _ := by rw [integral_prod F hF,integral_count_eq_tsum _ hF.integral_prod_left]

theorem compensatedRowTripleIntegral_eq_tsum {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedRowTripleIntegral η S C W0 W1 p X Y Z=
      ∑'u : FreeRow,((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫t,compensatedRowOnLines η S C p W0 W1 X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure := by
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>Subtype.ext (congrArg (fun u : NonzeroFrequency=>u.val) h)
  have hi := compensatedRows_counting_product_integrable e he η S C p hp W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  unfold compensatedRowTripleIntegral compensatedRowSeries
  rw [tsum_mul_left]
  congr 1
  rw [←counting_product_integral_tsum _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  simp only [compensatedRowOnLines,e,tsum_mul_left,mul_assoc]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1928

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalSplit
Source SHA256: 79246324533c426fdfc6743518a99b45a8821ce3689a6c48bccafd34c88c6d14
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1929


namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeMellinBoundary HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def principalFreeRow : FreeRow := ⟨1,one_ne_zero,by
  intro P
  simp [Ideal.span_singleton_one,←Ideal.one_eq_top]⟩

def rowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫t,compensatedRowOnLines η S C p W0 W1 X Y Z ⟨u.val,u.property.1⟩ t ∂heightMeasure

def principalRowIntegral {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
    sourceMellinWeight W0 W1 X Y Z ((3:ℂ)+t.1.1*Complex.I)
      ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I)*
    (∏i,(elementNorm (p i):ℂ)^(((2:ℂ)+t.1.2*Complex.I)-1))*
      indexedCompensatedHigh η S p 1 ((3:ℂ)+t.1.1*Complex.I)
        ((3:ℂ)+t.2*Complex.I) ((2:ℂ)+t.1.2*Complex.I) ∂heightMeasure

lemma rowIntegral_principal {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    rowIntegral η S C p W0 W1 X Y Z principalFreeRow=principalRowIntegral η S p W0 W1 X Y Z := by
  simp only [rowIntegral,principalRowIntegral,compensatedRowOnLines,principalFreeRow,
    frequencyWeight,elementNorm_one,map_one,star_one,Complex.ofReal_one,Complex.one_cpow,one_mul]

lemma rowIntegral_summable {K : ℕ} (η : HeckeFamily.Character) (S : Finset Id) (C : CalibrationData)
    (p : Fin K→O) (hp : ∀i,p i≠0) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Summable (rowIntegral η S C p W0 W1 X Y Z) := by
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>Subtype.ext (congrArg (fun v : NonzeroFrequency=>v.val) h)
  have hi := (compensatedRows_counting_product_integrable e he η S C p hp W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).integral_prod_left
  rw [integrable_count_iff] at hi
  exact hi.of_norm.mul_left _

theorem compensatedRowTripleIntegral_principal_split {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (C : CalibrationData) (p : Fin K→O) (hp : ∀i,p i≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedRowTripleIntegral η S C W0 W1 p X Y Z=
      principalRowIntegral η S p W0 W1 X Y Z+
        ∑'u : FreeRow,if u=principalFreeRow then 0 else rowIntegral η S C p W0 W1 X Y Z u := by
  rw [compensatedRowTripleIntegral_eq_tsum η S C p hp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  change (∑'u : FreeRow,rowIntegral η S C p W0 W1 X Y Z u)=_
  rw [(rowIntegral_summable η S C p hp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).tsum_eq_add_tsum_ite principalFreeRow,
    rowIntegral_principal]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1929

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedSubset
Source SHA256: dfe5f667a25ad9f65aa633a463918423225eb80fa6fbfc8fac913858a370b66b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1930



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEulerFinsupp
local notation "O" => HeckeFamily.O

theorem markedRowSeries_subset_replacement (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T J : Finset PrimeIdeal) (hJ : J⊆T) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : O) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z)*
        (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
  let A := fun P : PrimeIdeal=>if P∈T\J then idealRowMarkedLocalFactor η u P x w z else 1
  let B := fun P : PrimeIdeal=>if P∈J then idealRowHighLocalFactor η u P.val x w z else 1
  have hA : HasProd A (∏P∈T\J,idealRowMarkedLocalFactor η u P x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=T\J) (f:=A)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [A,Finset.prod_ite_mem,Finset.inter_self] using hh
  have hB : HasProd B (∏P∈J,idealRowHighLocalFactor η u P.val x w z) := by
    have hh := hasProd_prod_of_ne_finset_one (s:=J) (f:=B)
      (L:=SummationFilter.unconditional PrimeIdeal) (fun P hP=>ite_eq_right hP)
    simpa only [B,Finset.prod_ite_mem,Finset.inter_self] using hh
  have he := ((excludedIdealHighSeries_row_hasProd (markExclusions S T)
    (markExclusions_prime S hS T) η u x w z hx hw hz).mul hA).mul hB
  have heq (P : PrimeIdeal) :
      ((∑'b : HighValuation,markedIdealHighSummand (markExclusions S T) 1 η u x w z
        (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2))*A P)*B P=
      ∑'b : HighValuation,markedLocal (T\J) completedValuationMark
        (excludedRowPrimeTerm S η u x w z) P b := by
    rw [excludedRowHighLocalFactor _ (markExclusions_prime S hS T) η u x w z hx hw hz]
    by_cases hPJ : P∈J
    · have hPT := hJ hPJ
      have hPA : P∉T\J := by simp only [Finset.mem_sdiff]; tauto
      rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hPT)),
        selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,ite_eq_right hPA]
      simp only [A,B,ite_eq_right hPA,ite_eq_left hPJ,one_mul]
    · by_cases hPT : P∈T
      · have hPA : P∈T\J := Finset.mem_sdiff.mpr ⟨hPT,hPJ⟩
        rw [ite_eq_left ((mem_markExclusions S T P).mpr (Or.inr hPT)),
          selectedRowLocal_outside S hS (T\J) η u P (hT P hPT) x w z hx hw hz,ite_eq_left hPA]
        simp only [A,B,ite_eq_left hPA,ite_eq_right hPJ,one_mul,mul_one]
      · have hPA : P∉T\J := fun h=>hPT (Finset.mem_sdiff.mp h).1
        simp only [A,B,ite_eq_right hPA,ite_eq_right hPJ,mul_one,markedLocal,one_mul]
        change _=∑'b : HighValuation,markedIdealHighSummand S 1 η u x w z
          (P.val^b.1.1) (P.val^b.1.2) (P.val^b.2.1) (P.val^b.2.2)
        rw [excludedRowHighLocalFactor S hS η u x w z hx hw hz]
        simp only [mem_markExclusions,hPT,or_false]
  apply (markedRowSeries_hasProd S hS (T\J) η u x w z hx hw hz).unique
  convert he using 1
  funext P
  exact (heq P).symm

def spectralCompensatedRow (S : Finset (Ideal O)) (T : Finset PrimeIdeal)
    (η : Character) (u : O) (x w z : ℂ) (B q : PrimeIdeal→ℂ) : ℂ :=
  ∑J∈T.powerset,(-1:ℂ)^J.card*(∏P∈J,q P)*(∏P∈T\J,B P)*
    markedIdealHighSeries S (∏P∈T\J,P.val) η u x w z

theorem spectralCompensatedRow_eq_product (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : O)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η u x w z B q=
      markedIdealHighSeries (markExclusions S T) 1 η u x w z*
        ∏P∈T,(B P*idealRowMarkedLocalFactor η u P x w z-
          q P*idealRowHighLocalFactor η u P.val x w z) := by
  rw [spectralCompensatedRow,Finset.prod_sub,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [markedRowSeries_subset_replacement S hS T J (Finset.mem_powerset.mp hJ) hT η u x w z hx hw hz]
  simp only [Finset.prod_mul_distrib]
  ring

theorem indexedCompensatedHigh_eq_spectral {K : ℕ} (η : Character) (S : Finset (Ideal O))
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P)
    (hs : ∀i,CanonicalQuadraticSieve.Supported (P i).val) (u : O) (x w z : ℂ) :
    indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u x w z=
      spectralCompensatedRow S (Finset.univ.image P) η u x w z
        (fun Q=>star (idealCoeff η Q.val)*(Q.val.absNorm:ℂ)^x)
        (fun Q=>(Q.val.absNorm:ℂ)^(-w)) := by
  unfold indexedCompensatedHigh spectralCompensatedRow
  rw [Finset.powerset_image,Finset.sum_image (Finset.image_injective hP).injOn]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [Finset.card_image_of_injective J hP,←Finset.image_sdiff _ _ hP]
  simp only [Finset.prod_image hP.injOn]
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (hs i)]
    norm_cast
  have hc (i : Fin K) : elementCoeff η (CompletedGauss.primaryGenerator (P i).val)=
      idealCoeff η (P i).val := targetMonoid_primaryGenerator η (P i).val (hs i)
  simp only [tupleIndexedCoefficient,hnorm,hc,span_tupleProduct,
    span_primaryGenerator_of_supported _ (hs _)]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1930

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedCompensation
Source SHA256: 6263a2c392520556bfc5453dab8d272a51578cf58b69dc5ef5a07e7cc2b9cb61
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1931



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def compensatedLocalCorrection (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (x w z B q : ℂ) : ℂ :=
  B*markedLocalCorrection η u P x w z-q*localCorrection η u P x w z

theorem compensatedLocalCorrection_eq_raw (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (x w z B q : ℂ) :
    compensatedLocalCorrection η u P x w z B q=
      (B*idealRowMarkedLocalFactor η u.val P x w z-q*idealRowHighLocalFactor η u.val P.val x w z)*
        localNormalization η u P x w z := by
  rw [compensatedLocalCorrection,markedLocalCorrection,localCorrection_eq_normalization]
  ring

theorem spectralCompensatedRow_original_L_factorization
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (T : Finset PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (B q : PrimeIdeal→ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    spectralCompensatedRow S T η u.val x w z B q=
      (LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (rowCharacter S hS u) w/
        LFunction ((targetRow η u).excludePrimes S hS) x)*
      (globalCorrection (markExclusions S T) η u x w z*
        ∏P∈T,compensatedLocalCorrection η u P x w z (B P) (q P)) := by
  have hx1 : 1<x.re := by linarith
  have hw1 : 1<w.re := by linarith
  have hz1 : 1<(6*z).re := by norm_num [Complex.mul_re];linarith
  have hZ := LFunction_ne_zero_of_one_lt_re (fixedSourcePrincipal S hS) hz1
  have hW := LFunction_ne_zero_of_one_lt_re (rowCharacter S hS u) hw1
  have hD := LFunction_ne_zero_of_one_lt_re ((targetRow η u).excludePrimes S hS) hx1
  have hn := finite_replacement_normalized S hS hbad T hT η u x w z
    (fun P=>B P*idealRowMarkedLocalFactor η u.val P x w z-q P*idealRowHighLocalFactor η u.val P.val x w z)
    hx hw hz
  simp_rw [←compensatedLocalCorrection_eq_raw] at hn
  rw [←spectralCompensatedRow_eq_product S hS T hT η u.val x w z B q hx hw hz] at hn
  rw [←hn,globalNormalization]
  field_simp

theorem indexedCompensatedHigh_original_L_factorization {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→PrimeIdeal) (hP : Function.Injective P) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    indexedCompensatedHigh η S (fun i=>CompletedGauss.primaryGenerator (P i).val) u.val x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (rowCharacter S hS.prime u) w/
        LFunction ((targetRow η u).excludePrimes S hS.prime) x)*
      (globalCorrection (markExclusions S (Finset.univ.image P)) η u x w z*
        ∏i,compensatedLocalCorrection η u (P i) x w z
          (star (idealCoeff η (P i).val)*((P i).val.absNorm:ℂ)^x)
          (((P i).val.absNorm:ℂ)^(-w))) := by
  have hs (i : Fin K) := outside_prime_supported S hS.bad (P i) (hPS i)
  rw [indexedCompensatedHigh_eq_spectral η S P hP hs u.val x w z]
  have ht : ∀Q∈Finset.univ.image P,Q.val∉S := by
    intro Q hQ
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hQ
    exact hPS i
  rw [spectralCompensatedRow_original_L_factorization S hS.prime hS.bad
    (Finset.univ.image P) ht η u x w z _ _ hx hw hz,Finset.prod_image hP.injOn]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1931

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.MarkedCoordinates
Source SHA256: 68b1c66ea47137b664a64c450a4e2075255f310f339e9953c0c4e544c3b150b3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1932



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeEuler ProbeRow
open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

def continuedMarkedLocal (η : Character) (u : FreeRow) (P : PrimeIdeal) (hs : Supported P.val)
    (x w z : ℂ) : ℂ :=
  let p := primaryGenerator P.val
  let hp := supported_primeGenerator_prime P hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
  let hg := (supported_prime_data p hp hsp).1
  rowClosedMarked p hp hg (targetMonoid η p) (actualACube η p)
    ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
    (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
    (multiplicity p u.val)

theorem idealRowMarkedLocalFactor_eq_source (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ) :
    let p := primaryGenerator P.val
    let hp := supported_primeGenerator_prime P hs
    let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
    let hsp : Supported (Ideal.span {p}) := (span_primaryGenerator_of_supported P.val hs).symm ▸ hs
    let hg := (supported_prime_data p hp hsp).1
    idealRowMarkedLocalFactor η u.val P x w z=
      rowMarkedSeries p hp hg (targetMonoid η p) (actualACube η p)
        ((P.val.absNorm:ℂ)^(-x)) ((P.val.absNorm:ℂ)^(-w)) (coordV P.val.absNorm z)
        (actualSextic (Ideal.span {p}) hg (Ideal.Quotient.mk _ (unitPart u p hp)))
        (multiplicity p u.val) := by
  dsimp only
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hprimary := (primaryGenerator_spec P.val (supported_primaryGenerator_ne_zero P.val hs)).2
  unfold idealRowMarkedLocalFactor rowMarkedSeries rowInner
  apply Finset.sum_congr rfl
  intro e he
  apply tsum_congr
  intro l
  apply tsum_congr
  intro k
  apply tsum_congr
  intro m
  change completedValuationMark P ((e.val,l),(k,m))*bareIdealHighSummand η u.val x w z
    (P.val^e.val) (P.val^l) (P.val^k) (P.val^m)=_
  have ht := bareIdealHighSummand_row_at_prime η p hp hg.1 hg.2 hprimary hsp
    (unitPart u p hp) (unitPart_coprime u p hp) (multiplicity p u.val) e.val l k m (by omega) x w z
  rw [←(canonical_decomposition u p hp).1] at ht
  conv_lhs at ht => rw [hspan]
  rw [ht]
  by_cases hzero : e.val+3*l=0
  · simp only [completedValuationMark,hzero,ne_eq,not_true_eq_false,ite_false,zero_mul,
      rowMarkedTerm,ite_true]
  · simp only [completedValuationMark,hzero,ne_eq,not_false_eq_true,ite_true,one_mul]
    simpa only [hspan] using sourceRowTerm_pos p hp hg.1 (targetMonoid η p) (actualACube η p)
      (actualSextic (Ideal.span {p}) hg.1 (Ideal.Quotient.mk _ (unitPart u p hp))) x w z
      (multiplicity p u.val) e.val l k m hzero

theorem continuedMarkedLocal_eq_initial (η : Character) (u : FreeRow) (P : PrimeIdeal)
    (hs : Supported P.val) (x w z : ℂ)
    (hx : 3/2<x.re) (hw : 2<w.re) (hz : 1/6<z.re) :
    continuedMarkedLocal η u P hs x w z=idealRowMarkedLocalFactor η u.val P x w z := by
  let p := primaryGenerator P.val
  have hp : Prime p := supported_primeGenerator_prime P hs
  have hspan : Ideal.span {p}=P.val := span_primaryGenerator_of_supported P.val hs
  let : (Ideal.span {p}:Ideal O).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hp.irreducible
  have hsp : Supported (Ideal.span {p}) := hspan.symm ▸ hs
  have hg := supported_prime_data p hp hsp
  have hρ := actualSextic_unit_six p (unitPart u p hp) hg.1 hg.2 (unitPart_coprime u p hp)
  have hgeom := row_initial_geometric η p hp hg.1 hg.2 (unitPart u p hp)
    (unitPart_coprime u p hp) x w z hx hw hz
  have hQ0 : (0:ℝ)<Ideal.absNorm (Ideal.span {p}) :=
    HeckeDyadic.norm_pos ⟨Ideal.span {p},Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero⟩
  have he := evenRatio_eq_coordR (Ideal.absNorm (Ideal.span {p}):ℝ) hQ0 (actualACube η p) x z
  simp only [Complex.ofReal_natCast] at he
  have hR : ‖evenRatio (Ideal.absNorm (Ideal.span {p})) (actualACube η p)
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) (coordV (Ideal.absNorm (Ideal.span {p})) z)‖<1 := by
    rw [he]
    exact hgeom.2.1
  rw [idealRowMarkedLocalFactor_eq_source η u P hs x w z]
  unfold continuedMarkedLocal
  symm
  simpa only [hspan] using rowMarkedSeries_eq_closed p hp hg.1 hg.2 (targetMonoid η p)
    (actualACube η p) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x))
    ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w)) (coordV (Ideal.absNorm (Ideal.span {p})) z)
    _ hρ hgeom.1 hR (multiplicity p u.val) (multiplicity_lt_six u p hp)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule1932

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ProfileIntegral
Source SHA256: 509f6531c3bf400ff55520144b8d3d40f0f6ad7d5a52ef42d6b1c2ec04eb5536
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1933


namespace OAI

noncomputable section
open scoped BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

lemma two_height_bound (t v w : ℝ) :
    (3+|t|)^2*(3+|w|)^2≤81*jointHeight t v w^4 := by
  have ht : 3+|t|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  have hw : 3+|w|≤3*jointHeight t v w := by
    unfold jointHeight
    linarith [abs_nonneg t,abs_nonneg v,abs_nonneg w]
  calc
    _ ≤ (3*jointHeight t v w)^2*(3*jointHeight t v w)^2 := by gcongr
    _ = _ := by ring

theorem source_profile_integral_bound (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) :
    ∃C : ℝ,0<C ∧ ∀σ∈Icc slo shi,∀r∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀A : ℝ,0≤A → ∀F : HeightSpace→ℝ,
      AEStronglyMeasurable F heightMeasure → (∀p,0≤F p) →
      (∀p,F p≤A*(3+|p.1.1|)^2*(3+|p.2|)^2) →
      Integrable (fun p=>‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p) heightMeasure ∧
      (∫p,‖sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p ∂heightMeasure)
        ≤C*A*(X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)) := by
  obtain ⟨D,hD,hM⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo 4
  refine ⟨81*D,by positivity,?_⟩
  intro σ hσ r hr υ hυ X Y Z hX hY hZ A hA F hF hF0 hFb
  let E : ℝ := X^(1/2-r)*Z^(σ+r-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let M : HeightSpace→ℝ := fun p=>jointHeight p.1.1 p.1.2 p.2^4*‖onLines W0 W1 σ r υ p‖
  have hMi : Integrable M heightMeasure := (hM σ hσ r hr υ hυ).1
  have hMb : (∫p,M p ∂heightMeasure)≤D := (hM σ hσ r hr υ hυ).2
  let f : HeightSpace→ℝ := fun p=>‖sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*F p
  have hfm : AEStronglyMeasurable f heightMeasure :=
    (sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ
      σ r υ (hzlo.trans_le hr.1)).norm.aestronglyMeasurable.mul hF
  have hf0 (p : HeightSpace) : 0≤f p := mul_nonneg (norm_nonneg _) (hF0 p)
  have hfb (p : HeightSpace) : f p≤(E*A*81)*M p := by
    have h1 := (hFb p).trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (two_height_bound p.1.1 p.1.2 p.2) hA)
    have hs : ‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖=E*‖onLines W0 W1 σ r υ p‖ := by
      rw [sourceMellinWeight_eq_scale,norm_mul,sourceScale_norm X Y Z hX hY hZ]
      simp [E,onLines]
    dsimp only [f]
    rw [hs]
    calc
      _ ≤ (E*‖onLines W0 W1 σ r υ p‖)*(A*(81*jointHeight p.1.1 p.1.2 p.2^4)) :=
        mul_le_mul_of_nonneg_left h1 (mul_nonneg hE (norm_nonneg _))
      _ = _ := by dsimp [M];ring
  have hfi : Integrable f heightMeasure := (hMi.const_mul (E*A*81)).mono' hfm
    (Filter.Eventually.of_forall fun p=>by rw [Real.norm_eq_abs,abs_of_nonneg (hf0 p)];exact hfb p)
  refine ⟨hfi,?_⟩
  calc
    (∫p,f p ∂heightMeasure) ≤ ∫p,(E*A*81)*M p ∂heightMeasure :=
      integral_mono hfi (hMi.const_mul _) hfb
    _ = (E*A*81)*(∫p,M p ∂heightMeasure) := integral_const_mul _ _
    _ ≤ (E*A*81)*D := mul_le_mul_of_nonneg_left hMb (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule1933

/-! Original module: OAI.NumberTheory.DirichletL.PrincipalSlotEstimate
Source SHA256: cf5f5e473a2d9ae46c0b4628824eb3c2fbed706a4698179397cb075b86e8fb6e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1934


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex

namespace SevenEighths.PrincipalSlotEstimate
open ProbeEuler ProbeLocal

def principalMarked (Q : ℝ) (A η s : ℂ) : ℂ :=
  markedFactor (coordR Q A s (1 / 6)) (coordV Q (1 / 6)) (Q : ℂ)⁻¹
    (coordK Q η s 1) (-coordD Q η 1 s + coordW Q 1 1 * coordR Q A s (1 / 6)) 1

def principalReplacement (Q : ℝ) (A η s : ℂ) : ℂ :=
  compensatedReplacement (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
    (principalMarked Q A η s) (star η * (Q : ℂ) ^ s) ((Q : ℂ) ^ (-1 : ℂ))

def principalSlot (Q : ℝ) (A η s : ℂ) : ℂ :=
  principalReplacement Q A η s / unramifiedClosed Q A η 1 s 1 (1 / 6)

theorem principal_correction_defect {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    ‖unramifiedClosed Q A η 1 s 1 (1 / 6) - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have h := unramifiedClosed_second_region_bound Q A η 1 s 1 (1 / 6)
    (by linarith) hA hη (by simp) hs (by norm_num) (by norm_num)
  calc
    _ ≤ 240 * Q ^ (-(363 / 200 : ℝ)) := h
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem principal_correction_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ := by
  have h := principal_correction_defect hQ hA hη hs
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s 1 (1 / 6))
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem principal_correction_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (principal_correction_lower_bound hQ hA hη hs)

theorem principal_correction_inverse_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    ‖(unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹‖ ≤ 2 := by
  have hl := principal_correction_lower_bound hQ hA hη hs
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖)).mpr
  linarith

theorem unit_phase_inverse (η : ℂ) (hη : ‖η‖ = 1) : star η * η = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hη]
  norm_num

theorem principal_coord_cancellation {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    (star η * (Q : ℂ) ^ s) * coordD Q η 1 s = 1 := by
  have hQ0 : (Q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hQ.ne'
  unfold coordD
  simp only [star_one, mul_one]
  calc
    _ = (star η * η) * ((Q : ℂ) ^ s * (Q : ℂ) ^ (-s)) := by ring
    _ = 1 := by rw [unit_phase_inverse η hη, ← Complex.cpow_add _ _ hQ0]; simp

theorem principal_V {Q : ℝ} : coordV Q (1 / 6) = (Q : ℂ)⁻¹ := by
  norm_num [coordV, Complex.cpow_neg_one]

theorem principal_W {Q : ℝ} : coordW Q 1 1 = (Q : ℂ)⁻¹ := by
  simp [coordW, Complex.cpow_neg_one]

theorem principal_B_norm {Q : ℝ} (hQ : 0 < Q) (η s : ℂ) (hη : ‖η‖ = 1) :
    ‖star η * (Q : ℂ) ^ s‖ = Q ^ s.re := by
  rw [norm_mul, norm_star, hη, one_mul, Complex.norm_cpow_eq_rpow_re_of_pos hQ]

theorem compensated_unit_error_bound (V W D P B q : ℂ) (T : ℝ)
    (_hT : 0 ≤ T) (hV : ‖V‖ ≤ 1 / 2) (hW : ‖W‖ ≤ 1)
    (hD : ‖D‖ ≤ 1 / 2) (hq : ‖q‖ ≤ 1)
    (hVT : ‖V‖ ≤ T) (hDT : ‖D‖ ≤ T)
    (hE : ‖P + D‖ ≤ 28 * T) (hBE : ‖B‖ * ‖P + D‖ ≤ 28 * T)
    (hBD : B * D = 1) (hWq : W = q) :
    ‖compensatedReplacement V W D P B q + continuedCorrection V W D P‖ ≤ 720 * T := by
  have h1V : ‖1 - V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have h1W : ‖1 - W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have h1q : ‖1 - q‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) q
    simp only [norm_one] at this
    linarith
  have hiV := inv_one_sub_norm_le_two V hV
  have hiD := inv_one_sub_norm_le_two D hD
  have hfac : ‖(1 - V) * (1 - W) / (1 - D)‖ ≤ 8 := by
    rw [div_eq_mul_inv, norm_mul, norm_mul]
    calc
      ‖1 - V‖ * ‖1 - W‖ * ‖(1 - D)⁻¹‖ ≤ (2 : ℝ) * 2 * 2 := by gcongr
      _ = 8 := by norm_num
  have hleft : ‖(1 - q) * (V / (1 - V) - D)‖ ≤ 6 * T := by
    calc
      _ = ‖1 - q‖ * ‖V / (1 - V) - D‖ := norm_mul _ _
      _ ≤ 2 * (‖V‖ * 2 + ‖D‖) := by
        gcongr
        calc
          _ ≤ ‖V / (1 - V)‖ + ‖D‖ := norm_sub_le _ _
          _ ≤ _ := by rw [div_eq_mul_inv, norm_mul]; gcongr
      _ ≤ 6 * T := by linarith
  have hright : ‖(B + 1 - q) * (P + D)‖ ≤ 84 * T := by
    have hc : ‖B + 1 - q‖ ≤ ‖B‖ + 2 := by
      calc
        _ = ‖B + (1 - q)‖ := by congr 1; ring
        _ ≤ ‖B‖ + ‖1 - q‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    calc
      _ = ‖B + 1 - q‖ * ‖P + D‖ := norm_mul _ _
      _ ≤ (‖B‖ + 2) * ‖P + D‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg _)
      _ ≤ 84 * T := by nlinarith
  have hid := continued_normalized_cancellation V W D P B q 1
    (one_sub_ne_zero_of_norm_le_half V hV) (one_sub_ne_zero_of_norm_le_half D hD)
    hBD (by simpa using hWq)
  simp only [mul_one] at hid
  rw [hid, norm_mul]
  calc
    _ ≤ 8 * (‖(1 - q) * (V / (1 - V) - D)‖ + ‖(B + 1 - q) * (P + D)‖) := by
      gcongr
      exact norm_add_le _ _
    _ ≤ 720 * T := by linarith

theorem principal_marked_error_bounds {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(7 / 8 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by
    have h := coordW_norm_le Q hQ0 (1 : ℂ) 1 (by simp)
    norm_num at h
    exact h.trans (by simpa using hpow (-1) 0 (by norm_num))
  have hR : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (3 - 6 * s.re) := by
    convert coordR_norm_le Q hQ0 A s (1 / 6) hA using 1
    norm_num
    congr 1
    ring
  have hD : ‖coordD Q η 1 s‖ ≤ Q ^ (-s.re) :=
    coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hK : ‖coordK Q η s 1‖ ≤ Q ^ (-s.re) := by
    convert coordK_norm_le Q hQ1 η s 1 hη.le using 1
    norm_num
  have hB := principal_B_norm hQ0 η s hη
  have hRhalf : ‖coordR Q A s (1 / 6)‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q (3 - 6 * s.re) hQ4 (by linarith))
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hDhalf : ‖coordD Q η 1 s‖ ≤ 1 / 2 :=
    hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [← principal_V]; linarith
  have hE := unramified_marked_error_bound (coordR Q A s (1 / 6))
    (coordV Q (1 / 6)) (Q : ℂ)⁻¹ (coordK Q η s 1) (coordW Q 1 1)
    (coordD Q η 1 s) hRhalf hVhalf hq hDhalf
  change ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s (1 / 6)‖ ≤ Q ^ (-(7 / 8 : ℝ)) :=
    hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ (-s.re) * Q ^ (-1 : ℝ) := by rw [hV]; gcongr
      _ = Q ^ (-s.re - 1) := by rw [← Real.rpow_add hQ0]; congr 1
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s (1 / 6)‖ ≤
      Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (3 - 6 * s.re) := by rw [hB]; gcongr
      _ = Q ^ (3 - 5 * s.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ *
      (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (-s.re) * Q ^ (-1 : ℝ)) := by rw [hB, hV]; gcongr
      _ = Q ^ (-1 : ℝ) := by rw [← mul_assoc, ← Real.rpow_add hQ0]; simp
      _ ≤ _ := hpow _ _ (by norm_num)
  have hE' : ‖principalMarked Q A η s + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s (1 / 6)‖ + 4 * (‖coordK Q η s 1‖ * ‖coordV Q (1 / 6)‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s (1 / 6)))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem principal_replacement_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      720 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ = Q ^ (-1 : ℝ) := by
    rw [coordV_norm Q hQ0]; norm_num
  have hVhalf : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [hV]; exact rpow_le_half Q (-1) hQ4 (by norm_num)
  have hD := coordD_norm_le Q hQ0 η 1 s hη.le (by simp)
  have hDhalf := hD.trans (rpow_le_half Q (-s.re) hQ4 (by linarith))
  have hWq : coordW Q 1 1 = (Q : ℂ) ^ (-1 : ℂ) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-1 : ℂ)‖ ≤ 1 := by
    rw [Complex.cpow_neg_one, ← principal_V]; linarith
  have hW : ‖coordW Q 1 1‖ ≤ 1 := by rw [hWq]; exact hq
  have hVT : ‖coordV Q (1 / 6)‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    rw [hV]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(7 / 8 : ℝ)) :=
    hD.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := principal_marked_error_bounds hQ hA hη hs
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hVhalf hW hDhalf hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem principal_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖principalSlot Q A η s + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  have hn := principal_correction_ne_zero hQ hA hη.le hs
  have he := principal_replacement_error hQ hA hη hs
  have hi := principal_correction_inverse_bound hQ hA hη.le hs
  have hid : principalSlot Q A η s + 1 =
      (principalReplacement Q A η s + unramifiedClosed Q A η 1 s 1 (1 / 6)) *
        (unramifiedClosed Q A η 1 s 1 (1 / 6))⁻¹ := by
    unfold principalSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(7 / 8 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem actual_target_norm (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) :
    ‖HeckeFamily.elementCoeff η p‖ = 1 := by
  let : Finite (HeckeFamily.O ⧸ η.modulus) :=
    Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (HeckeFamily.O ⧸ η.modulus) := Fintype.ofFinite _
  obtain ⟨u, hu⟩ := hp
  unfold HeckeFamily.elementCoeff
  rw [← hu]
  exact FiniteRayExpansion.norm_char_unit η.residue u

theorem actual_principal_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : 7 / 8 ≤ s.re) :
    ‖principalSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(7 / 8 : ℝ)) :=
  principal_slot_error hQ (actualAPhase_norm_le_one η p) (actual_target_norm η p hp) hs

theorem weighted_slot_error {ι : Type*} (S : Finset ι) (w : ι → ℝ) (B : ι → ℂ)
    (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i) (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)‖ ≤
      δ * ∑ i ∈ S, w i := by
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ) =
      ∑ i ∈ S, (w i : ℂ) * (B i + 1) := by
    simp only [mul_add, mul_one, Finset.sum_add_distrib, Complex.ofReal_sum]
  rw [hid]
  calc
    _ ≤ ∑ i ∈ S, ‖(w i : ℂ) * (B i + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ S, δ * w i := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hw i hi)]
      simpa [mul_comm] using mul_le_mul_of_nonneg_left (hB i hi) (hw i hi)
    _ = _ := by rw [Finset.mul_sum]

theorem weighted_slot_relative_error {ι : Type*} (S : Finset ι) (w : ι → ℝ)
    (B : ι → ℂ) (δ : ℝ) (hw : ∀ i ∈ S, 0 ≤ w i)
    (hB : ∀ i ∈ S, ‖B i + 1‖ ≤ δ) (hS : 0 < ∑ i ∈ S, w i) :
    ‖(∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1‖ ≤ δ := by
  have hSc : ((∑ i ∈ S, w i : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hS.ne'
  have hid : (∑ i ∈ S, (w i : ℂ) * B i) / (-(∑ i ∈ S, w i : ℝ) : ℂ) - 1 =
      -((∑ i ∈ S, (w i : ℂ) * B i) + (∑ i ∈ S, w i : ℝ)) /
        (∑ i ∈ S, w i : ℝ) := by field_simp; ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hS]
  exact (div_le_iff₀ hS).mpr (weighted_slot_error S w B δ hw hB)

theorem weighted_principal_slot_error {ι : Type*} (S : Finset ι) (w Q : ι → ℝ)
    (A η : ι → ℂ) (s : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hw : ∀ i ∈ S, 0 ≤ w i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 7 / 8 ≤ s.re) :
    ‖(∑ i ∈ S, (w i : ℂ) * principalSlot (Q i) (A i) (η i) s) +
        (∑ i ∈ S, w i : ℝ)‖ ≤
      (1440 * P ^ (-(7 / 8 : ℝ))) * ∑ i ∈ S, w i := by
  apply weighted_slot_error S w _ _ hw
  intro i hi
  apply (principal_slot_error (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs).trans
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)

theorem product_error {κ : Type*} (S : Finset κ) (F : κ → ℂ)
    (δ : ℝ) (hδ : 0 ≤ δ) (hF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ) :
    ‖(∏ i ∈ S, F i) - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert a S ha ih =>
    have haF := hF a (Finset.mem_insert_self a S)
    have hSF : ∀ i ∈ S, ‖F i - 1‖ ≤ δ := fun i hi => hF i (Finset.mem_insert_of_mem hi)
    have hprod := ih hSF
    have haN : ‖F a‖ ≤ 1 + δ := by
      have h := norm_sub_norm_le (F a) (1 : ℂ)
      simp only [norm_one] at h
      linarith
    rw [Finset.prod_insert ha, Finset.card_insert_of_notMem ha]
    calc
      _ = ‖F a * ((∏ i ∈ S, F i) - 1) + (F a - 1)‖ := by congr 1; ring
      _ ≤ ‖F a * ((∏ i ∈ S, F i) - 1)‖ + ‖F a - 1‖ := norm_add_le _ _
      _ ≤ (1 + δ) * ((1 + δ) ^ S.card - 1) + δ := by
        rw [norm_mul]
        exact add_le_add (mul_le_mul haN hprod (norm_nonneg _) (by linarith)) haF
      _ = _ := by rw [pow_succ]; ring

theorem product_error_linear (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    (1 + δ) ^ n - 1 ≤ n * 2 ^ n * δ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hp : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hbase : 0 ≤ (1 + δ) ^ n - 1 := by
      exact sub_nonneg.mpr (one_le_pow₀ (by linarith))
    calc
      _ = (1 + δ) * ((1 + δ) ^ n - 1) + δ := by rw [pow_succ]; ring
      _ ≤ 2 * ((n : ℝ) * 2 ^ n * δ) + δ := by
        gcongr
        linarith
      _ ≤ _ := by rw [Nat.cast_succ, pow_succ]; nlinarith

def principalScalar {κ : Type*} (S : Finset κ) (M : κ → ℝ) : ℂ :=
  (-1 : ℂ) ^ S.card * (∏ i ∈ S, M i : ℝ)

theorem principalScalar_eq {κ : Type*} (S : Finset κ) (M : κ → ℝ) :
    principalScalar S M = ∏ i ∈ S, (-(M i : ℂ)) := by
  unfold principalScalar
  rw [Complex.ofReal_prod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  ring

theorem principalScalar_ne_zero {κ : Type*} (S : Finset κ) (M : κ → ℝ)
    (hM : ∀ i ∈ S, 0 < M i) : principalScalar S M ≠ 0 := by
  rw [principalScalar_eq]
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hM i hi).ne')

theorem fixed_product_relative_error {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ (1 + δ) ^ S.card - 1 := by
  rw [principalScalar_eq, ← Finset.prod_div_distrib]
  apply product_error S _ δ hδ
  intro i hi
  have hMi : (M i : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hM i hi).ne'
  have hid : W i / (-(M i : ℂ)) - 1 = -(W i + (M i : ℂ)) / (M i : ℂ) := by
    field_simp
    ring
  rw [hid, norm_div, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (hM i hi)]
  exact (div_le_iff₀ (hM i hi)).mpr (hW i hi)

theorem fixed_product_relative_error_linear {κ : Type*} (S : Finset κ)
    (M : κ → ℝ) (W : κ → ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hM : ∀ i ∈ S, 0 < M i)
    (hW : ∀ i ∈ S, ‖W i + (M i : ℂ)‖ ≤ δ * M i) :
    ‖(∏ i ∈ S, W i) / principalScalar S M - 1‖ ≤ S.card * 2 ^ S.card * δ :=
  (fixed_product_relative_error S M W δ hδ hM hW).trans
    (product_error_linear S.card hδ hδ1)

theorem weighted_principal_product_error {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 7 / 8 ≤ s.re)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      (1 + 1440 * P ^ (-(7 / 8 : ℝ))) ^ S.card - 1 := by
  apply fixed_product_relative_error S _ _ _ (by positivity) hM
  intro j hj
  exact weighted_principal_slot_error (T j) (w j) (Q j) (A j) (η j) s P hP
    (hw j hj) (hQ j hj) (hA j hj) (hη j hj) hs

def principalRawFactor (Q : ℝ) (A η s : ℂ) : ℂ :=
  localFactor (coordV Q (1 / 6)) (coordW Q 1 1) (principalMarked Q A η s)

theorem principal_geometric_bounds {Q : ℝ} {η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    ‖coordV Q (1 / 6)‖ ≤ 1 / 2 ∧ ‖coordW Q 1 1‖ ≤ 1 / 2 ∧
      ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hV : ‖coordV Q (1 / 6)‖ ≤ 1 / 2 := by
    rw [coordV_norm Q hQ0]
    norm_num
    exact rpow_le_half Q (-1) hQ4 (by norm_num)
  refine ⟨hV, ?_, ?_⟩
  · rw [principal_W, ← principal_V]; exact hV
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans
      (rpow_le_half Q (-s.re) hQ4 (by linarith))

theorem principal_correction_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    unramifiedClosed Q A η 1 s 1 (1 / 6) =
      localCorrection (coordV Q (1 / 6)) (coordW Q 1 1) (coordD Q η 1 s)
        (principalMarked Q A η s) := by
  have h := principal_geometric_bounds hQ hη hs
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem principal_raw_lower_bound {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    1 / 16 ≤ ‖principalRawFactor Q A η s‖ := by
  have hl := principal_correction_lower_bound hQ hA hη hs
  have hg := principal_geometric_bounds hQ hη hs
  have hV : ‖1 - coordV Q (1 / 6)‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q (1 / 6))
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 1‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 1)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s 1 (1 / 6)‖ ≤
      8 * ‖principalRawFactor Q A η s‖ := by
    rw [principal_correction_eq_raw hQ hη hs]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖principalRawFactor Q A η s‖ *
      (‖1 - coordV Q (1 / 6)‖ * ‖1 - coordW Q 1 1‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖principalRawFactor Q A η s‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem principal_raw_ne_zero {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    principalRawFactor Q A η s ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (principal_raw_lower_bound hQ hA hη hs)

theorem principal_slot_eq_raw {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re) :
    principalSlot Q A η s =
      (star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) := by
  have hg := principal_geometric_bounds hQ hη hs
  have hn := principal_correction_ne_zero hQ hA hη hs
  have hp := principal_raw_ne_zero hQ hA hη hs
  have hr := compensatedReplacement_eq_raw (coordV Q (1 / 6)) (coordW Q 1 1)
    (coordD Q η 1 s) (principalMarked Q A η s) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-1 : ℂ))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← principal_correction_eq_raw hQ hη hs] at hr
  unfold principalSlot principalReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem principal_raw_slot_error {Q : ℝ} {A η s : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re) :
    ‖(star η * (Q : ℂ) ^ s) * principalMarked Q A η s / principalRawFactor Q A η s -
        (Q : ℂ) ^ (-1 : ℂ) + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  rw [← principal_slot_eq_raw hQ hA hη.le hs]
  exact principal_slot_error hQ hA hη hs

theorem weighted_principal_product_error_linear {κ ι : Type*} (S : Finset κ)
    (T : κ → Finset ι) (w Q : κ → ι → ℝ) (A η : κ → ι → ℂ)
    (s : ℂ) (P : ℝ) (hP : 480 ≤ P) (hs : 7 / 8 ≤ s.re)
    (hsmall : 1440 * P ^ (-(7 / 8 : ℝ)) ≤ 1)
    (hw : ∀ j ∈ S, ∀ i ∈ T j, 0 ≤ w j i)
    (hQ : ∀ j ∈ S, ∀ i ∈ T j, P ≤ Q j i)
    (hA : ∀ j ∈ S, ∀ i ∈ T j, ‖A j i‖ ≤ 1)
    (hη : ∀ j ∈ S, ∀ i ∈ T j, ‖η j i‖ = 1)
    (hM : ∀ j ∈ S, 0 < ∑ i ∈ T j, w j i) :
    ‖(∏ j ∈ S, ∑ i ∈ T j, (w j i : ℂ) * principalSlot (Q j i) (A j i) (η j i) s) /
        principalScalar S (fun j => ∑ i ∈ T j, w j i) - 1‖ ≤
      S.card * 2 ^ S.card * (1440 * P ^ (-(7 / 8 : ℝ))) :=
  (weighted_principal_product_error S T w Q A η s P hP hs hw hQ hA hη hM).trans
    (product_error_linear S.card (by positivity) hsmall)

def regionMarked (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  markedFactor (coordR Q A s z) (coordV Q z) (Q : ℂ)⁻¹ (coordK Q η s w)
    (-coordD Q η 1 s + coordW Q 1 w * coordR Q A s z) 1

def regionReplacement (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  compensatedReplacement (coordV Q z) (coordW Q 1 w) (coordD Q η 1 s)
    (regionMarked Q A η s w z) (star η * (Q : ℂ) ^ s) ((Q : ℂ) ^ (-w))

def regionSlot (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  regionReplacement Q A η s w z / unramifiedClosed Q A η 1 s w z

def regionRawFactor (Q : ℝ) (A η s w z : ℂ) : ℂ :=
  localFactor (coordV Q z) (coordW Q 1 w) (regionMarked Q A η s w z)

theorem region_correction_defect {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖unramifiedClosed Q A η 1 s w z - 1‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  calc
    _ ≤ 240 * Q ^ (-(363 / 200 : ℝ)) :=
      unramifiedClosed_second_region_bound Q A η 1 s w z (by linarith) hA hη (by simp) hs hw hz
    _ ≤ 240 * Q ^ (-1 : ℝ) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num)) (by norm_num)
    _ ≤ 1 / 2 := by
      rw [Real.rpow_neg_one, ← div_eq_mul_inv]
      exact (div_le_iff₀ hQ0).mpr (by linarith)

theorem region_correction_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 2 ≤ ‖unramifiedClosed Q A η 1 s w z‖ := by
  have h := region_correction_defect hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (1 : ℂ) (unramifiedClosed Q A η 1 s w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem region_correction_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 2).trans_le
    (region_correction_lower_bound hQ hA hη hs hw hz)

theorem region_correction_inverse_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(unramifiedClosed Q A η 1 s w z)⁻¹‖ ≤ 2 := by
  have hl := region_correction_lower_bound hQ hA hη hs hw hz
  rw [norm_inv, inv_eq_one_div]
  apply (div_le_iff₀ (by linarith : 0 < ‖unramifiedClosed Q A η 1 s w z‖)).mpr
  linarith

theorem region_geometric_bounds {Q : ℝ} {η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖coordV Q z‖ ≤ 1 / 2 ∧ ‖coordW Q 1 w‖ ≤ 1 / 2 ∧ ‖coordD Q η 1 s‖ ≤ 1 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ4 (by linarith)
  · exact (coordW_norm_le Q hQ0 1 w (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))
  · exact (coordD_norm_le Q hQ0 η 1 s hη (by simp)).trans (rpow_le_half Q _ hQ4 (by linarith))

theorem region_marked_error_bounds {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ 28 * Q ^ (-(7 / 8 : ℝ)) ∧
    ‖star η * (Q : ℂ) ^ s‖ * ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      28 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hQ4 : 4 ≤ Q := by linarith
  have hpow (x y : ℝ) (h : x ≤ y) : Q ^ x ≤ Q ^ y :=
    Real.rpow_le_rpow_of_exponent_le hQ1 h
  have hV := coordV_norm Q hQ0 z
  have hR := coordR_norm_le Q hQ0 A s z hA
  have hK := coordK_norm_le Q hQ1 η s w hη.le
  have hB := principal_B_norm hQ0 η s hη
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hRhalf : ‖coordR Q A s z‖ ≤ 1 / 2 :=
    hR.trans (rpow_le_half Q _ hQ4 (by linarith))
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hq : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have hE := unramified_marked_error_bound (coordR Q A s z) (coordV Q z)
    (Q : ℂ)⁻¹ (coordK Q η s w) (coordW Q 1 w) (coordD Q η 1 s)
    hRhalf hg.1 hq hg.2.2
  change ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤ _ at hE
  have hRT : ‖coordR Q A s z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := hR.trans (hpow _ _ (by linarith))
  have hKV : ‖coordK Q η s w‖ * ‖coordV Q z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re) := by rw [hV]; gcongr
      _ = Q ^ (1 - s.re - w.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBR : ‖star η * (Q : ℂ) ^ s‖ * ‖coordR Q A s z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * Q ^ (4 - 6 * s.re - 6 * z.re) := by rw [hB]; gcongr
      _ = Q ^ (4 - 5 * s.re - 6 * z.re) := by rw [← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hBKV : ‖star η * (Q : ℂ) ^ s‖ * (‖coordK Q η s w‖ * ‖coordV Q z‖) ≤
      Q ^ (-(7 / 8 : ℝ)) := by
    calc
      _ ≤ Q ^ s.re * (Q ^ (1 - s.re - w.re) * Q ^ (-6 * z.re)) := by rw [hB, hV]; gcongr
      _ = Q ^ (1 - w.re - 6 * z.re) := by
        rw [← Real.rpow_add hQ0, ← Real.rpow_add hQ0]; congr 1; ring
      _ ≤ _ := hpow _ _ (by linarith)
  have hE' : ‖regionMarked Q A η s w z + coordD Q η 1 s‖ ≤
      24 * ‖coordR Q A s z‖ + 4 * (‖coordK Q η s w‖ * ‖coordV Q z‖) := by
    apply hE.trans
    nlinarith [mul_le_mul_of_nonneg_left hW (norm_nonneg (coordR Q A s z))]
  constructor
  · linarith
  · have h := mul_le_mul_of_nonneg_left hE' (norm_nonneg (star η * (Q : ℂ) ^ s))
    nlinarith

theorem region_replacement_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z‖ ≤
      720 * Q ^ (-(7 / 8 : ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hg := region_geometric_bounds hQ hη.le hs hw hz
  have hWq : coordW Q 1 w = (Q : ℂ) ^ (-w) := by simp [coordW]
  have hq : ‖(Q : ℂ) ^ (-w)‖ ≤ 1 := by rw [← hWq]; linarith [hg.2.1]
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by linarith [hg.2.1]
  have hVT : ‖coordV Q z‖ ≤ Q ^ (-(7 / 8 : ℝ)) := by
    rw [coordV_norm Q hQ0]; exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hDT : ‖coordD Q η 1 s‖ ≤ Q ^ (-(7 / 8 : ℝ)) :=
    (coordD_norm_le Q hQ0 η 1 s hη.le (by simp)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hE := region_marked_error_bounds hQ hA hη hs hw hz
  exact compensated_unit_error_bound _ _ _ _ _ _ _ (Real.rpow_nonneg hQ0.le _)
    hg.1 hW hg.2.2 hq hVT hDT hE.1 hE.2
    (principal_coord_cancellation hQ0 η s hη) hWq

theorem region_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  have hn := region_correction_ne_zero hQ hA hη.le hs hw hz
  have he := region_replacement_error hQ hA hη hs hw hz
  have hi := region_correction_inverse_bound hQ hA hη.le hs hw hz
  have hid : regionSlot Q A η s w z + 1 =
      (regionReplacement Q A η s w z + unramifiedClosed Q A η 1 s w z) *
        (unramifiedClosed Q A η 1 s w z)⁻¹ := by
    unfold regionSlot
    field_simp
  rw [hid, norm_mul]
  calc
    _ ≤ (720 * Q ^ (-(7 / 8 : ℝ))) * 2 := mul_le_mul he hi (norm_nonneg _) (by positivity)
    _ = _ := by ring

@[simp] theorem region_slot_at_residue (Q : ℝ) (A η s : ℂ) :
    regionSlot Q A η s 1 (1 / 6) = principalSlot Q A η s := rfl

theorem region_correction_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    unramifiedClosed Q A η 1 s w z =
      localCorrection (coordV Q z) (coordW Q 1 w) (coordD Q η 1 s)
        (regionMarked Q A η s w z) := by
  have h := region_geometric_bounds hQ hη hs hw hz
  exact continuedCorrection_eq_raw _ _ _ _
    (one_sub_ne_zero_of_norm_le_half _ h.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.1)
    (one_sub_ne_zero_of_norm_le_half _ h.2.2)

theorem region_raw_lower_bound {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    1 / 16 ≤ ‖regionRawFactor Q A η s w z‖ := by
  have hl := region_correction_lower_bound hQ hA hη hs hw hz
  have hg := region_geometric_bounds hQ hη hs hw hz
  have hV : ‖1 - coordV Q z‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordV Q z)
    simp only [norm_one] at this
    linarith [hg.1]
  have hW : ‖1 - coordW Q 1 w‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) (coordW Q 1 w)
    simp only [norm_one] at this
    linarith [hg.2.1]
  have hD := inv_one_sub_norm_le_two (coordD Q η 1 s) hg.2.2
  have hupper : ‖unramifiedClosed Q A η 1 s w z‖ ≤
      8 * ‖regionRawFactor Q A η s w z‖ := by
    rw [region_correction_eq_raw hQ hη hs hw hz]
    unfold localCorrection
    rw [div_eq_mul_inv, norm_mul, norm_mul, norm_mul]
    change ‖regionRawFactor Q A η s w z‖ *
      (‖1 - coordV Q z‖ * ‖1 - coordW Q 1 w‖) * ‖(1 - coordD Q η 1 s)⁻¹‖ ≤ _
    calc
      _ ≤ ‖regionRawFactor Q A η s w z‖ * (2 * 2) * 2 := by gcongr
      _ = _ := by ring
  linarith

theorem region_raw_ne_zero {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionRawFactor Q A η s w z ≠ 0 := by
  apply norm_pos_iff.mp
  exact (by norm_num : (0 : ℝ) < 1 / 16).trans_le
    (region_raw_lower_bound hQ hA hη hs hw hz)

theorem region_slot_eq_raw {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    regionSlot Q A η s w z =
      (star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) := by
  have hg := region_geometric_bounds hQ hη hs hw hz
  have hn := region_correction_ne_zero hQ hA hη hs hw hz
  have hp := region_raw_ne_zero hQ hA hη hs hw hz
  have hr := compensatedReplacement_eq_raw (coordV Q z) (coordW Q 1 w)
    (coordD Q η 1 s) (regionMarked Q A η s w z) (star η * (Q : ℂ) ^ s)
    ((Q : ℂ) ^ (-w))
    (one_sub_ne_zero_of_norm_le_half _ hg.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.1)
    (one_sub_ne_zero_of_norm_le_half _ hg.2.2) hp
  rw [← region_correction_eq_raw hQ hη hs hw hz] at hr
  unfold regionSlot regionReplacement
  rw [hr]
  exact mul_div_cancel_left₀ _ hn

theorem region_raw_slot_error {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖(star η * (Q : ℂ) ^ s) * regionMarked Q A η s w z / regionRawFactor Q A η s w z -
        (Q : ℂ) ^ (-w) + 1‖ ≤ 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  rw [← region_slot_eq_raw hQ hA hη.le hs hw hz]
  exact region_slot_error hQ hA hη hs hw hz

theorem region_slot_norm_le {Q : ℝ} {A η s w z : ℂ}
    (hQ : 480 ≤ Q) (hA : ‖A‖ ≤ 1) (hη : ‖η‖ = 1) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot Q A η s w z‖ ≤ 1 + 1440 * Q ^ (-(7 / 8 : ℝ)) := by
  have he := region_slot_error hQ hA hη hs hw hz
  have hn := norm_sub_norm_le (regionSlot Q A η s w z) (-1 : ℂ)
  simp only [norm_neg, norm_one, sub_neg_eq_add] at hn
  linarith

theorem weighted_region_slot_norm {ι : Type*} (S : Finset ι) (b Q : ι → ℝ)
    (A η : ι → ℂ) (s w z : ℂ) (P : ℝ) (hP : 480 ≤ P)
    (hb : ∀ i ∈ S, 0 ≤ b i) (hQ : ∀ i ∈ S, P ≤ Q i)
    (hA : ∀ i ∈ S, ‖A i‖ ≤ 1) (hη : ∀ i ∈ S, ‖η i‖ = 1)
    (hs : 7 / 8 ≤ s.re) (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖∑ i ∈ S, (b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ ≤
      (1 + 1440 * P ^ (-(7 / 8 : ℝ))) * ∑ i ∈ S, b i * (Q i) ^ (z.re - 1) := by
  calc
    _ ≤ ∑ i ∈ S, ‖(b i : ℂ) * (Q i : ℂ) ^ (z - 1) * regionSlot (Q i) (A i) (η i) s w z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ S, (1 + 1440 * P ^ (-(7 / 8 : ℝ))) * (b i * (Q i) ^ (z.re - 1)) := by
      apply Finset.sum_le_sum
      intro i hi
      have hQi : 0 < Q i := by linarith [hQ i hi]
      have he := region_slot_norm_le (hP.trans (hQ i hi)) (hA i hi) (hη i hi) hs hw hz
      have he' : ‖regionSlot (Q i) (A i) (η i) s w z‖ ≤ 1 + 1440 * P ^ (-(7 / 8 : ℝ)) := by
        apply he.trans
        apply add_le_add le_rfl
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        exact Real.rpow_le_rpow_of_nonpos (by linarith) (hQ i hi) (by norm_num)
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hb i hi),
        Complex.norm_cpow_eq_rpow_re_of_pos hQi]
      simp only [Complex.sub_re, Complex.one_re]
      exact (mul_le_mul_of_nonneg_left he'
        (mul_nonneg (hb i hi) (Real.rpow_nonneg hQi.le _))).trans_eq (mul_comm _ _)
    _ = _ := by rw [Finset.mul_sum]

theorem actual_region_slot_error (η : HeckeFamily.Character) (p : HeckeFamily.O)
    (hp : IsUnit (Ideal.Quotient.mk η.modulus p)) (s w z : ℂ)
    (hQ : 480 ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ)) (hs : 7 / 8 ≤ s.re)
    (hw : 19 / 20 ≤ w.re) (hz : 33 / 200 ≤ z.re) :
    ‖regionSlot (Ideal.absNorm (Ideal.span {p})) (actualAPhase η p)
      (HeckeFamily.elementCoeff η p) s w z + 1‖ ≤
      1440 * (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (-(7 / 8 : ℝ)) :=
  region_slot_error hQ (actualAPhase_norm_le_one η p) (actual_target_norm η p hp) hs hw hz

end SevenEighths.PrincipalSlotEstimate

end

end OAI
end OAIOriginalModule1934
