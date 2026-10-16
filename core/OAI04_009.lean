    slotAssignmentWeight J₂ a₂
    (fun i hi => x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem assignedSecondCoefficient_attach {Jo : ℕ}
    (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i ∈ J₁,ι) × (∀ i ∈ J₂,ι)) :
    assignedSecondCoefficient J₁ J₂ a₁ a₂ (attachPairedSlots J₁ J₂ (x,q)) =
      pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [assignedSecondCoefficient,attachPairedSlots,attachSecondSlots,
    pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem paired_assignment_filter (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (A : Finset ι) :
    ((J₁.pi L₁) ×ˢ (J₂.pi L₂)).filter (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ A) =
      (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hmem
    apply Finset.mem_product.mpr
    constructor
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · apply Finset.mem_pi.mpr
      intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa only [pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · intro hq
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_,?_⟩,?_⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q.1 hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q.2 hq₂ k)).2

theorem assignedSecondSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card) → ℂ) :
    ∑ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂, F x =
      ∑ y ∈ source, ∑ q ∈
        (J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap))) ×ˢ
        (J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap))),
          F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [assignedSecondSource,Finset.sum_image (fun q _ r _ h => attachPairedSlots_injective J₁ J₂ h),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem assignedSecondSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (w P : MarkedSecondSource ι Jo 0 → ℂ) :
    (∑ y ∈ source, w y * (star (primeMark J₁ L₁ a₁ (y.second.sourceCommon∪y.second.overlap)) *
      primeMark J₂ L₂ a₂ (y.second.sourceCommon∪y.second.overlap)) * P y) =
    ∑ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x) * P (eraseSecondSlots x) := by
  rw [assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

theorem assignedSecondCoefficient_norm_le_one {Jo : ℕ}
    (source : Finset (MarkedSecondSource ι Jo 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card))
    (hx : x ∈ assignedSecondSource source J₁ J₂ L₁ L₂) :
    ‖assignedSecondCoefficient J₁ J₂ a₁ a₂ x‖ ≤ 1 := by
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  rw [assignedSecondCoefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ (q₁,q₂)
    (Finset.mem_product.mpr ⟨hq₁,hq₂⟩) ha₁ ha₂

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0578

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondMarkedEnergy
Source SHA256: 4d5bd46bb4f928d6530622330b01e34b94a41cde706b73997d22577ba16b220b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0579


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondChild_erase {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v (eraseSecondSlots x) = actualSecondChild p u v x := rfl

theorem actualSecondChild_neg_frequency {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}} =
      ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,-(actualSecondChild p u v x).2.2) := by
  simp only [actualSecondChild,secondChild,originalSecondTuple,markedSecondOriginal,cubeSecondSource,
    secondUnitFrequency_neg,mul_neg]

include hp hcop in
theorem actual_second_marked_weighted_count
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  let S := assignedSecondSource source J₁ J₂ L₁ L₂
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card) =>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hs' : ActualSecondSourceConditions p S := assignedSecondSource_conditions p source hs J₁ J₂ L₁ L₂
  have herase : ∀ x ∈ S, eraseSecondSlots x ∈ source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  have hw' : ∀ x ∈ S, ‖w' x‖ ≤ 1 := by
    intro x hx
    rw [show w' x = w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ x hx)
  have hc' : ∀ x ∈ S, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := assignedSecondSource_sum_marks source J₁ J₂ L₁ L₂ a₁ a₂ w
    (fun x => F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0579

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSquarefree
Source SHA256: c0946137613f5e51ba86b421abd21f7ebd2ffad113ad811f4ddeed916f5d569b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0580



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourcePrime sourceIdeal_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem sourceIdeal_squarefree (S : Finset ι) : Squarefree (sourceIdeal p S) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (sourcePrime p i).property.squarefree

include hcop in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_coprime_of_disjoint (S T : Finset ι) (hST : Disjoint S T) :
    IsCoprime (sourceIdeal p S) (sourceIdeal p T) := by
  simp only [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact hcop (fun he => Finset.disjoint_left.mp hST hi (he.symm ▸ hj))

omit [DecidableEq ι] in
lemma prime_span_coprime_of_not_mem (i : ι) (c : Eis) (hc : c ∉ Ideal.span {p i}) :
    IsCoprime (Ideal.span {p i}) (Ideal.span {c} : Ideal Eis) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have he := (inferInstance : (Ideal.span {p i}).IsMaximal).eq_of_le hne le_sup_left
  apply hc
  rw [he]
  exact (show Ideal.span {c} ≤ (Ideal.span {p i} : Ideal Eis) ⊔ Ideal.span {c} from le_sup_right)
    (Ideal.subset_span (by simp))

omit [DecidableEq ι] in
theorem sourceIdeal_coprime_of_not_mem (S : Finset ι) (c : Eis)
    (hc : ∀ i ∈ S, c ∉ Ideal.span {p i}) :
    IsCoprime (sourceIdeal p S) (Ideal.span {c} : Ideal Eis) := by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact IsCoprime.prod_left (fun i hi => prime_span_coprime_of_not_mem p i c (hc i hi))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem jLabel_span_dvd_source (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {jLabel p B v ε₁ ε₂} : Ideal Eis) ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i^bit (retained (parity (v i)) (ε₁ i) (ε₂ i))) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases retained (parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit]

omit [DecidableEq ι] in
theorem secondInputCoefficient_zero_of_label_mem (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S) (hc : c ∈ Ideal.span {p i}) :
    secondInputCoefficient p hg Ψ m c d H S = 0 := by
  have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
    simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
  have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
  simp only [secondInputCoefficient,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondPreColumn_zero_of_mask_label_mem (Ψ : Eis →* ℂ) (m c d e k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hc : m*c ∈ Ideal.span {p i}) : secondPreColumn p hp hcop hg Ψ m c d e k H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hc with hm|hc
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S m = 0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,m ∈ Ideal.span {p i} from ⟨i,hi,hm⟩)]
    simp only [secondPreColumn,hz,mul_zero,zero_mul]
  · have hz : rowCoprimeMask (fun i => Ideal.span {p i}) S c = 0 := by
      simp only [rowCoprimeMask,ite_eq_left (show ∃ i ∈ S,c ∈ Ideal.span {p i} from ⟨i,hi,hc⟩)]
    have hr := row_zero_of_mask_zero (fun i => Ideal.span {p i}) hg S c hz
    simp only [secondPreColumn,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondSignedSourceWeight_nonzero_masks
    (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon)
    (hw : secondSignedSourceWeight p hp hcop hg Ψ m c d z x ≠ 0) :
    IsCoprime (sourceIdeal p x.sourceCommon) (Ideal.span {c}) ∧
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.sourceCommon * Ideal.span {c}) := by
  constructor
  · apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    have hz := secondInputCoefficient_zero_of_label_mem p hg Ψ m c d (fun _ => 1) x.sourceCommon i hi hc
    apply hw
    simp only [secondSignedSourceWeight,hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      Complex.ofReal_zero,zero_mul]
  · change IsCoprime (sourceIdeal p x.overlap) (Ideal.span {∏ i ∈ x.sourceCommon,p i} * Ideal.span {c})
    rw [Ideal.span_singleton_mul_span_singleton]
    apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
    let r := secondExpansionQuotient p x
    have her : e*r = ∏ j ∈ x.sourceCommon,p j := by
      dsimp only [r]
      rw [secondExpansionQuotient_of_subset p x hE]
      exact (secondMaskQuotient_spec p _ _ hE).symm
    have hmc : (m*(e*r))*c ∈ Ideal.span {p i} := by
      rw [her,mul_assoc]
      exact Ideal.mul_mem_left _ m hc
    have hz := secondPreColumn_zero_of_mask_label_mem p hp hcop hg (secondRayPlus Ψ z)
      (m*(e*r)) c d e (-x.frequency) (fun _ => 1) x.overlap i hi hmc
    dsimp only [e,r] at hz
    apply hw
    simp only [secondSignedSourceWeight,secondCommonWeight,hz,mul_zero]

def actualSecondSignedWeight {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ℂ :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  secondSignedSourceWeight p hp hcop hg Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit*d) c d z x.second

theorem actualSecondSignedWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ‖actualSecondSignedWeight p hp hcop hg Ψ m z x‖ ≤ 1 :=
  secondSignedSourceWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ _ _ _ z x.second

theorem actual_second_nonzero_weight_squarefree
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hw : actualSecondSignedWeight p hp hcop hg Ψ m z x ≠ 0) (u v : Eisˣ) :
    Squarefree (actualSecondChild p u v x).2.1 := by
  let J : Ideal Eis := Ideal.span {jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}
  let C := sourceIdeal p x.firstCommon
  let E := sourceIdeal p x.second.divisor
  let G := sourceIdeal p x.second.sourceCommon
  let V := sourceIdeal p x.second.overlap
  have hj : J ∣ sourceIdeal p x.cube.support := jLabel_span_dvd_source p _ _ _ _
  have hJ : Squarefree J := (sourceIdeal_squarefree p hcop x.cube.support).squarefree_of_dvd hj
  have hC : Squarefree C := sourceIdeal_squarefree p hcop _
  have hG : Squarefree G := sourceIdeal_squarefree p hcop _
  have hV : Squarefree V := sourceIdeal_squarefree p hcop _
  have hJC : IsCoprime J C :=
    (sourceIdeal_coprime_of_disjoint p hcop x.cube.support x.firstCommon hCB.symm).of_isCoprime_of_dvd_left hj
  have hdg : E ∣ G := sourceIdeal_dvd p _ _ hE
  have hcspan : Ideal.span {(∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} = C*J :=
    (Ideal.span_singleton_mul_span_singleton _ _).symm
  obtain ⟨hgmask,hvmask⟩ := secondSignedSourceWeight_nonzero_masks p hp hcop hg Ψ _ _ _ z x.second hE hw
  rw [hcspan] at hgmask hvmask
  change IsCoprime G (C*J) at hgmask
  change IsCoprime V (G*(C*J)) at hvmask
  have heJC : IsCoprime E (J*C) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : J*C*E ∣ G*(C*J) := by
    obtain ⟨r,hr⟩ := hdg
    refine ⟨r,?_⟩
    rw [hr]
    ring
  have hvJCE := hvmask.of_isCoprime_of_dvd_right hdiv
  change Squarefree (J*C*E*V)
  exact squarefree_mul_iff.mpr ⟨hvJCE.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨heJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime,hJ,hC⟩,hG.squarefree_of_dvd hdg⟩,hV⟩

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0580

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondPuncture
Source SHA256: b1f2b91c006bf26df3084a25f6f14064d389f14757c19a8a9013a7ced748951e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0581


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem rowCoprimeMask_radical_generator (S : Finset ι) (a : Eis) :
    rowCoprimeMask (fun i => Ideal.span {p i}) S a =
      rowCoprimeMask (fun i => Ideal.span {p i}) S
        (ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical) := by
  have he (i : ι) : a ∈ Ideal.span {p i} ↔
      ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical ∈ Ideal.span {p i} := by
    rw [←Ideal.span_singleton_le_iff_mem,←Ideal.span_singleton_le_iff_mem,
      ConcretePrimeRowBridge.span_idealGenerator]
    exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.symm
  simp only [rowCoprimeMask,he]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_radical_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ
        (ConcretePrimeRowBridge.idealGenerator (Ideal.span {m}).radical) f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn,
    ←rowCoprimeMask_radical_generator p]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_le_radical_primeProduct (B : Finset ι) (v : ι → ℕ) :
    sourceIdeal p B ≤ (Ideal.span {primeProduct p B v} : Ideal Eis).radical := by
  simp only [sourceIdeal,primeProduct,FiniteGaussPhase.span_finset_prod,←Ideal.span_singleton_pow]
  induction B using Finset.induction_on with
  | empty => simp
  | @insert i B hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Ideal.radical_mul]
    apply le_inf
    · apply Ideal.mul_le_left.trans
      by_cases hv : v i = 0
      · rw [hv,pow_zero,Ideal.one_eq_top]
        exact le_trans le_top Ideal.le_radical
      · rw [Ideal.radical_pow _ hv]
        exact Ideal.le_radical
    · exact Ideal.mul_le_right.trans ih

theorem actual_second_q0_radical_norm (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0.radical : ℝ) ≤
      primeProductNorm p x.cube.support := by
  have hd := Ideal.absNorm_dvd_absNorm_of_le (sourceIdeal_le_radical_primeProduct p x.cube.support
    (fun i => b0Exponent (x.cube.leftExponent i+x.cube.rightExponent i) (x.cube.leftBit i) (x.cube.rightBit i)))
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (sourceIdeal_ne_zero p hp x.cube.support))) hd
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}).radical : ℝ) ≤ _
  have he : (Ideal.absNorm (sourceIdeal p x.cube.support) : ℝ) = primeProductNorm p x.cube.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ x.cube.support,p i)).symm
  rw [←he]
  exact_mod_cast hb

def actualSecondRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  ConcretePrimeRowBridge.idealGenerator (Ideal.span {actualSecondPuncture m γ}).radical

theorem secondCanonicalPolynomial_radical_puncture
    (F : Finset ι) (Ψ : InverseSecondFibers.OuterTriple → Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : InverseSecondFibers.OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondPuncture m) slots lists a W X c =
      secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondRadicalPuncture m) slots lists a W X c :=
  finiteCanonicalMarkedRow_radical_puncture p hp hcop hg F (Ψ c.1) _ _ _ slots lists a (W c.1) X

theorem radical_product_norm_le (I J B R : Ideal Eis) (hI : I ≠ 0) (hB : B ≠ 0)
    (hR : R ≠ 0) (hBJ : B ≤ J.radical) :
    (Ideal.absNorm (I*J*R).radical : ℝ) ≤
      (Ideal.absNorm I.radical : ℝ)*Ideal.absNorm B*Ideal.absNorm R := by
  have hi : I.radical ≠ 0 := by
    intro he
    apply hI
    exact le_antisymm (he ▸ Ideal.le_radical) bot_le
  have hle : I.radical*B*R ≤ (I*J*R).radical := by
    rw [Ideal.radical_mul,Ideal.radical_mul]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact Ideal.mul_le_left.trans Ideal.mul_le_left
    · exact (Ideal.mul_le_left.trans Ideal.mul_le_right).trans hBJ
    · exact Ideal.mul_le_right.trans Ideal.le_radical
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (mul_ne_zero (mul_ne_zero hi hB) hR))) (Ideal.absNorm_dvd_absNorm_of_le hle)
  simpa only [map_mul,Nat.cast_mul] using (show (Ideal.absNorm (I*J*R).radical : ℝ) ≤
    Ideal.absNorm (I.radical*B*R) from by exact_mod_cast hb)

include hp in

theorem actual_second_radical_puncture_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,ConcretePrimeRowBridge.span_idealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn x.cube.support,←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_le_radical_primeProduct p _ _)

def actualSecondInheritedPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ

def actualSecondInheritedRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondRadicalPuncture (m*ConcretePrimeRowBridge.idealGenerator γ.quotient) γ

include hp in

theorem actual_second_inherited_puncture_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_norm p hp hpr x hE u v
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) hm'
  change ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*ConcretePrimeRowBridge.idealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,ConcretePrimeRowBridge.span_idealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (primeProductNorm_pos p hp _).le) (primeProductNorm_pos p hp _).le

include hp in

theorem actualSecondTriples_q0_radical_bound
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn)) (B : ℝ)
    (hB : ∀ x ∈ source, primeProductNorm p x.cube.support ≤ B) :
    ∀ γ ∈ actualSecondTriples p u v source, (Ideal.absNorm γ.q0.radical : ℝ) ≤ B := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact (actual_second_q0_radical_norm p hp x u v).trans (hB x hx)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0581

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondParentLists
Source SHA256: 40b033f6d9fea2ab178751e9ce35b6c75a16f12347eb098d8dd20f7452127c88
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0582


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def actualSecondRawInheritedPuncture {Jo Jn : ℕ} (m : O) (x : MarkedSecondSource ι Jo Jn) : O :=
  ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*b0Label p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    secondExpansionQuotient p x.second

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_parent_deleted_prime_killed {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (_hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (m : O) (i : ι)
    (hi : i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient) :
    actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x∈Ideal.span {p i} := by
  rcases hi with hi|hi
  · have hv : ∀ j∈x.cube.support,0<x.cube.leftExponent j+x.cube.rightExponent j := by
      intro j hj
      simp only [CubeCoordinates.support,Finset.mem_union,Finsupp.mem_support_iff] at hj
      omega
    have hk := actual_second_extracted_support_killed p
      x.cube.support x.firstCommon x.second.sourceCommon x.second.divisor x.second.overlap
      (x.cube.support∪x.firstCommon) hE Finset.subset_union_left
      (fun j=>x.cube.leftExponent j+x.cube.rightExponent j) x.cube.leftBit x.cube.rightBit hv
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) i hi
    simpa only [actualSecondRawInheritedPuncture,actualSecondRawLabel,
      secondExpansionQuotient_of_subset p x.second hE] using hk
  · have hq : ConcretePrimeRowBridge.idealGenerator x.quotient∈Ideal.span {p i} := by
      apply (Ideal.dvd_iff_le.mp hi)
      have hmem : ConcretePrimeRowBridge.idealGenerator x.quotient∈
          Ideal.span {ConcretePrimeRowBridge.idealGenerator x.quotient} := Ideal.subset_span (by simp)
      simpa only [ConcretePrimeRowBridge.span_idealGenerator] using hmem
    unfold actualSecondRawInheritedPuncture
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _
      (Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hq)))

theorem actual_second_parent_lists_restore {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon)
    (deleted : Finset ι)
    (hdeleted : ∀ i∈deleted,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : O→*ℂ) (m k : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots (fun j=>lists j\deleted) a W X =
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots lists a W X := by
  apply finiteCanonicalMarkedRow_restore_lists p hp hcop hg
  exact fun i hi=>actual_parent_deleted_prime_killed p x hb hE m i (hdeleted i hi)

theorem actual_second_parent_lists_restore_quotient {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (D : Finset ι)
    (hq : x.quotient=sourceIdeal p D) (deleted : Finset ι)
    (hdeleted : deleted⊆(x.cube.support∪x.firstCommon)∪D)
    (pool : Finset ι) (Ψ : O→*ℂ) (m k : O) (slots : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots (fun j=>lists j\deleted) a W X =
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ
      (actualSecondRawInheritedPuncture p m x) (actualSecondRawLabel p x) k
      slots lists a W X := by
  apply actual_second_parent_lists_restore p hp hcop hg x hb hE deleted
  intro i hi
  rcases Finset.mem_union.mp (hdeleted hi) with hi|hi
  · exact Or.inl hi
  · right
    rw [hq]
    exact InverseInitialArithmetic.source_prime_dvd p D i hi

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0582

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondPunctureBudget
Source SHA256: 3d9d472342f0949e234ab4af69b5fc264ba1169428b479cd8d6e3bd616240ce9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0583


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_eq_div (E G : Finset ι) (hE : E ⊆ G) :
    primeProductNorm p (G\E) = primeProductNorm p G/primeProductNorm p E := by
  have he : primeProductNorm p G = primeProductNorm p E*primeProductNorm p (G\E) := by
    rw [←primeProductNorm_union p E (G\E) Finset.disjoint_sdiff,Finset.union_sdiff_of_subset hE]
  rw [he]
  field_simp [(primeProductNorm_pos p hp E).ne']

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_residual_norm_power_bound (E G : Finset ι) (hE : E ⊆ G)
    (Z g theta eta : ℝ) (hZ : 0 < Z)
    (hg : primeProductNorm p G ≤ Z^(g+eta))
    (hd : Z^(theta-eta) ≤ primeProductNorm p E) :
    primeProductNorm p (G\E) ≤ Z^(g-theta+2*eta) := by
  rw [second_residual_norm_eq_div p hp E G hE]
  calc
    _ ≤ Z^(g+eta)/Z^(theta-eta) := div_le_div₀ (Real.rpow_pos_of_pos hZ _).le hg
      (Real.rpow_pos_of_pos hZ _) hd
    _ = Z^((g+eta)-(theta-eta)) := (Real.rpow_sub hZ _ _).symm
    _ = _ := by congr 1; ring

include hp in

theorem actual_second_puncture_power_budget
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  apply (actual_second_inherited_puncture_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hb0 := (primeProductNorm_pos p hp x.cube.support).le
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0583

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSupportedEnergy
Source SHA256: ee7fc4b7e29a4304b91267758d0e781b48059a616383c09ac22ae1ab518e7386
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0584


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem ActualSecondSourceConditions.mono {Jo Jn : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (h : ActualSecondSourceConditions p S)
    (hTS : T ⊆ S) : ActualSecondSourceConditions p T where
  admissible x hx := h.admissible x (hTS hx)
  common_disjoint x hx := h.common_disjoint x (hTS hx)
  first_divisor x hx := h.first_divisor x (hTS hx)
  second_divisor x hx := h.second_divisor x (hTS hx)
  old_support x hx := h.old_support x (hTS hx)
  new_support x hx := h.new_support x (hTS hx)
  quotient_nonzero x hx := h.quotient_nonzero x (hTS hx)

def actualSecondSurvivingSource {Jo : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (source : Finset (MarkedSecondSource ι Jo 0)) : Finset (MarkedSecondSource ι Jo 0) :=
  source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ m z x ≠ 0)

theorem assignedSecondSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S ⊆ T)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    assignedSecondSource S J₁ J₂ L₁ L₂ ⊆ assignedSecondSource T J₁ J₂ L₁ L₂ := by
  intro x hx
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,he⟩ := (mem_assignedSecondSource S J₁ J₂ L₁ L₂ x).mp hx
  exact (mem_assignedSecondSource T J₁ J₂ L₁ L₂ x).mpr ⟨y,hST hy,q₁,hq₁,q₂,hq₂,he⟩

theorem actualSecondTriples_mono {Jo Jn : ℕ} (u v : Eisˣ)
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (hST : S ⊆ T) :
    actualSecondTriples p u v S ⊆ actualSecondTriples p u v T :=
  Finset.image_subset_image hST

theorem actual_second_supported_marked_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := actualSecondSurvivingSource p hp hcop hg Ψ m z source
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ m z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_marked_weighted_count p hp hcop hpr hinj u v S
    (hs.mono p hsub) J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ m z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ m z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ m z x)).trans
          (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (assignedSecondSource_mono hsub J₁ J₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource S J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0584

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondInheritedEnergy
Source SHA256: 50ab4a11d5522c11e2571d3dc4addbeaf0b9922ed0b55338369cfa351ced94e3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0585



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_supported_marked_energy_varying_puncture
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_marked_weighted_count p hp hcop hpr hinj u v S
    (hs.mono p hsub) J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ (m x) z x)).trans
        (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (assignedSecondSource_mono hsub J₁ J₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource S J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0585

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRows
Source SHA256: 45d5340465c285393129a6a3d9c52d68ef9690429a72ea4789b16d4ef0556a70
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0586



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondMultiplier {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor

omit [DecidableEq ι] in
theorem actualSecondMultiplier_ne_zero {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    actualSecondMultiplier p x ≠ 0 := by
  apply mul_ne_zero
  · exact primeSubsetGenerator_ne_zero _ _
  · exact primeSubsetGenerator_ne_zero _ _

include hp in

theorem actual_second_row_norm_sq
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    ‖eisEmbedding (actualSecondChild p u v x).2.2‖^2 =
      ‖eisEmbedding (actualSecondMultiplier p x*x.second.frequency)‖^2 := by
  change ‖eisEmbedding (primaryGenerator (sourceIdeal p x.firstDivisor)*
      primaryGenerator (sourceIdeal p x.second.divisor)*secondUnitFrequency u v x.second.frequency)‖^2 = _
  rw [sourceIdeal_gen p hp hpr,sourceIdeal_gen p hp hpr]
  simp only [map_mul,norm_mul,mul_pow,secondUnitFrequency_norm,actualSecondMultiplier,
    primeSubsetGenerator_norm_eq_productNorm,primeProductNorm]

include hp in

theorem actual_second_row_ball
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) (R : ℝ) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R ↔
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x),
    mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,actual_second_row_norm_sq p hp hpr]

omit [DecidableEq ι] in
theorem actual_second_row_radius_one
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (R : ℝ)
    (hsource : source.Nonempty)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) : 1 ≤ R := by
  obtain ⟨x,hx⟩ := hsource
  by_contra hR
  have he := nonzeroChildFrequencyBall_empty _ (actualSecondMultiplier_ne_zero p x) R (lt_of_not_ge hR)
  simpa [he] using hrows x hx

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0586

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSectorAssembly
Source SHA256: fcba110a22ffdbacd52da4c80814bccb8d5947211d9a7a2bf55cd5e25159d665
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0587



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def SecondPairCanonicalAt {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) : Prop :=
∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}})

theorem exists_second_uniform_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ x ∈ source, SecondPairCanonicalAt (σ:=σ) p hp hcop hg x (sector x).1 (sector x).2 := by
  have he (x : {x // x ∈ source}) :=
    actual_second_separated_pair_canonical p hp hcop hg hpr (σ:=σ) x.val
      (hs.common_disjoint x.val x.property) (hs.first_divisor x.val x.property)
      (hs.second_divisor x.val x.property)
  choose u v hu using he
  let sector := fun x => if hx : x ∈ source then (u ⟨x,hx⟩,v ⟨x,hx⟩) else (1,1)
  refine ⟨sector,?_⟩
  intro x hx
  simpa only [sector,dite_eq_left hx,SecondPairCanonicalAt] using hu ⟨x,hx⟩

def secondSourceSector {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (uv : Eisˣ × Eisˣ) :
    Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => sector x = uv)

omit [DecidableEq ι] in
theorem secondSourceSector_partition {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (H : MarkedSecondSource ι Jo Jn → ℂ) :
    ∑ x ∈ source,H x = ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,H x :=
  (Finset.sum_fiberwise source sector H).symm

theorem second_unit_sector_card : Fintype.card (Eisˣ × Eisˣ) = 36 := by
  have hc : Fintype.card Eisˣ = 6 := by
    simpa only [Nat.card_eq_fintype_card] using PrimaryIdealUnitReindex.card_units_eq_six
  rw [Fintype.card_prod,hc]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0587

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondModeCanonical
Source SHA256: b1bc123f48d8ccc77b0258162e43f29d56596191fcf567c46247cff7de407611
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0588



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondInheritedProfile {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) : SecondProfileData ι :=
  actualMarkedSecondProfileData p x Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅

def secondModeLeft (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : SecondChild → ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4)) X

def secondModeRight (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) (c : SecondChild) : ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) X
    (c.1,c.2.1,-c.2.2)

def secondModeOuter {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2)
    (secondRelativeLog (secondActualNorms p (secondInheritedProfile p x Ψ m z) ∅ ∅) G E V B X)

def secondModeBranch {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondModeOuter p x Ψ m z G E V B X t *
    (star (primeMark J₁ lists₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
      primeMark J₂ lists₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
    star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
    secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x)

theorem second_inherited_mode_canonical {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (hx : SecondPairCanonicalAt (σ:=σ) p hp hcop hg x u v)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) :
    secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t =
    ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t := by
  have he := hx pool Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z ∅ ∅
    (Finset.empty_subset _) (Finset.empty_subset _) slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t
  dsimp only at he
  have hq : (actualSecondChild p u v x).1.quotient = x.quotient := rfl
  simpa only [secondInheritedProfile,secondModeBranch,secondModeOuter,secondModeLeft,secondModeRight,
    secondCanonicalPolynomial,actualSecondInheritedPuncture,actualSecondChild_neg_frequency,
    Finset.empty_union,Finset.mul_sum,mul_assoc,hq] using he

theorem actual_second_modes_common_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ))
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      (∑ x ∈ source,w x * secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t) =
      ∑ uv : Eisˣ × Eisˣ, ∑ x ∈ secondSourceSector source sector uv, w x *
        ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := exists_second_uniform_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t w
  rw [secondSourceSector_partition source sector]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx,hxs⟩ := Finset.mem_filter.mp hx
  congr 1
  have hh := hsector x hx
  rw [hxs] at hh
  exact second_inherited_mode_canonical p hp hcop hg x uv.1 uv.2 hh
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0588

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondModeEnergy
Source SHA256: 167d973f624125214ec5ceb2245c90fba4910740284cc0660ed12ae9a1d8a15a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0589



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_mode_branch_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1) :
    ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ) := by
  let phase := fun x => w x * secondModeOuter p x Ψ m z G E V B X t
  have hphase : ∀ x ∈ source,‖phase x‖ ≤ 1 := by
    intro x hx
    simpa only [phase,norm_mul,secondModeOuter,secondOuterPhase_norm,mul_one] using hw x hx
  have hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
    intro x hx
    exact ⟨hlabels x hx,(actual_second_row_ball p hp hpr x u v R).mp (hrows x hx)⟩
  have he := actual_second_supported_marked_energy_varying_puncture p hp hcop hg hpr hinj hc
    u v source hs Ψ hΨ (fun x => m*ConcretePrimeRowBridge.idealGenerator x.quotient) z
    J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ labels (nonzeroChildFrequencyBall 1 R) hchild
    K ho hJ₁ hJ₂ phase hphase
    (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t)
    (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t)
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [secondModeBranch,phase]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0589

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondModeIntegral
Source SHA256: 067d416d3b8db2c212904a17e6e9a9561245460fe9b68b32fb0f5023af9b83bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0590


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem second_geometric_energy_of_bound (K : ℕ) (labels : Finset (Ideal Eis))
    (rows : Finset Eis) (Γ : Finset OuterTriple) (F G : SecondChild → ℂ)
    (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ Γ,secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ Γ,secondLabelEnergy K labels rows G γ ≤ E) :
    Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ) (hP : ∀ γ ∈ Γ,secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ Γ,tripleDivisorWeight K γ*secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ Γ,tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  calc
    _ ≤ Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) *
        Real.sqrt (E*∑ γ ∈ Γ,tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

theorem actual_second_mode_integral_of_child_bound
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1)
    (gwin : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),
      ∀ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),
      ∀ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),fullProfileDensity gwin b₁ b₂ b₃ t *
      ∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t‖ ≤
      (A * ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ) *
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*
        ‖fullProfileDensity gwin b₁ b₂ b₃ t‖ := by
  let Γ := actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂)
  let mass := ∑ γ ∈ Γ,tripleDivisorWeight K γ
  let H := fun t : Frequency × (Fin 6 → ℝ) => tripleHeight J t.1*coordinateHeight J t.2
  have hH (t : Frequency × (Fin 6 → ℝ)) : 0 ≤ H t := by
    unfold H tripleHeight coordinateHeight
    positivity
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t‖ ≤ (A*H t)*mass := by
    apply (actual_second_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t
      labels hlabels hrows K ho hJ₁ hJ₂ w hw).trans
    exact second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
      Γ _ _ (A*H t) (mul_nonneg hA (hH t)) (hright t) (hleft t)
  have hi := (fullProfileDensity_weighted_integrable gwin b₁ b₂ b₃ J).const_mul (A*mass)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),(A*mass)*(tripleHeight J t.1*coordinateHeight J t.2*
        ‖fullProfileDensity gwin b₁ b₂ b₃ t‖) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by dsimp only [H]; ring)
    _ = _ := by rw [integral_const_mul]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0590

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondModeParentLists
Source SHA256: 0b4cc1506d8e7ed05c9f297197c4f4a34b754579584878f931979401b1a6d3d4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0591



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseInitialArithmetic CompletedGauss InverseSecondFibers JointLogSeparation
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

include hp in
theorem actual_second_canonical_label_span
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Oˣ) :
    Ideal.span {actualSecondRawLabel p x}=
      Ideal.span {primaryGenerator (actualSecondChild p u v x).2.1} := by
  obtain ⟨u₀,v₀,hl,hv⟩ := actual_second_generator_sectors p hp hpr x
  rw [hl,←Ideal.span_singleton_mul_span_singleton]
  simp only [Ideal.span_singleton_eq_top.mpr (Units.isUnit u₀),Ideal.top_mul]
  rfl

theorem secondCanonicalPolynomial_parent_lists_restore
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (u v : Oˣ)
    (deleted : Finset ι)
    (hdeleted : ∀ i∈deleted,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : OuterTriple→O→*ℂ) (m : O)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : OuterTriple→ℝ→ℂ) (X : ℝ) (k : O) :
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots (fun j=>lists j\deleted) a W X ((actualSecondChild p u v x).1,
        (actualSecondChild p u v x).2.1,k) =
    secondCanonicalPolynomial p hp hcop hg pool Ψ (actualSecondInheritedPuncture m)
      slots lists a W X ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,k) := by
  apply finiteCanonicalMarkedRow_restore_lists p hp hcop hg
  intro i hi
  have hk := actual_parent_deleted_prime_killed p x hb hE m i (hdeleted i hi)
  have he : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}=
      Ideal.span {actualSecondInheritedPuncture m (actualSecondChild p u v x).1*
        primaryGenerator (actualSecondChild p u v x).2.1} := by
    rw [←Ideal.span_singleton_mul_span_singleton,←Ideal.span_singleton_mul_span_singleton,
      actual_second_canonical_label_span p hp hpr x u v]
    congr 1
    exact actual_second_puncture_span p hp hpr x hE u v
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient)
  have hk' : Ideal.span {actualSecondRawInheritedPuncture p m x*actualSecondRawLabel p x}≤Ideal.span {p i} :=
    Ideal.span_le.mpr (by intro z hz; rcases Set.mem_singleton_iff.mp hz with rfl; exact hk)
  rw [he] at hk'
  exact hk' (Ideal.subset_span (by simp))

theorem secondModeBranch_parent_lists_restore
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (hb : x.cube.Admissible)
    (hE : x.second.divisor⊆x.second.sourceCommon) (u v : Oˣ)
    (deleted₁ deleted₂ : Finset ι)
    (hd₁ : ∀ i∈deleted₁,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (hd₂ : ∀ i∈deleted₂,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal O)∣x.quotient)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (ω₁ ω₂ : ℝ→ℂ) (G E V B X : ℝ) (t : Frequency×(Fin 6→ℝ)) :
    secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂
      (fun i=>lists₁ i\deleted₁) (fun i=>lists₂ i\deleted₂) a₁ a₂ ω₁ ω₂ G E V B X t =
    secondModeOuter p x Ψ m z G E V B X t *
      (star (primeMark J₁ (fun i=>lists₁ i\deleted₁) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (fun i=>lists₂ i\deleted₂) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
      secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x) := by
  unfold secondModeBranch secondModeLeft secondModeRight
  rw [secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₁ hd₁,
    secondCanonicalPolynomial_parent_lists_restore p hp hcop hg hpr x hb hE u v deleted₂ hd₂]

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0591

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondTripleBounds
Source SHA256: af280e17b21db8efb8697ecdc2c889bc6a3adaab9781c5e5736461f405d5f6c5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0592


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0)

include hp in

theorem actual_second_common_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z g theta eta : ℝ) (hZ : 1 < Z)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    -2*eta ≤ g-theta := by
  have hh : Z^(theta-eta) ≤ Z^(g+eta) :=
    hD.trans ((primeProductNorm_mono p hp hE).trans hG)
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  linarith

include hp in

theorem actual_second_label_center
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Z ell j eta : ℝ) (hZ : 1 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    j ≤ 2*ell+3*eta := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _).le h1 h2).1
  have hh := hJ.trans hb
  rw [←Real.rpow_mul_natCast (zero_lt_one.trans hZ).le] at hh
  have hh' := (Real.rpow_le_rpow_left_iff hZ).mp hh
  norm_num at hh'
  linarith

variable [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_q0_power_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (Z ell R j eta : ℝ) (hZ : 0 < Z)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hactive : primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) := by
  have hb := (cube_label_norm_bounds p hp x.cube.support x.cube.leftExponent x.cube.rightExponent
    x.cube.leftBit x.cube.rightBit x.cube.support_pos (Z^(ell+eta))
      (Real.rpow_pos_of_pos hZ _).le h1 h2).2.2
  have ha : ‖eisEmbedding (∏ i ∈ cubeActiveSupport x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖ ≤
      Z^((R+eta)/2) := by
    apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_pos_of_pos hZ _).le).mp
    rw [←Real.rpow_mul_natCast hZ.le]
    norm_num
    simpa only [primeProductNorm,map_prod,norm_prod] using hactive
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) : ℝ) ≤ _
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  apply hb.trans
  calc
    _ ≤ (Z^(ell+eta)*Z^((R+eta)/2))/Z^(j-eta) :=
      div_le_div₀ (by positivity) (mul_le_mul_of_nonneg_left ha (by positivity))
        (Real.rpow_pos_of_pos hZ _) hJ
    _ = Z^((ell+eta)+(R+eta)/2-(j-eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_sub hZ]
    _ = _ := by congr 1; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0592

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondActualMass
Source SHA256: 0ad31e3f20a6f82758c322fc35288fb41a549fe7d42c7d2fbb511761634bfd86
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0593


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma nonzero_ideal_norm_one (I : Ideal Eis) (hI : I ≠ 0) : 1 ≤ (Ideal.absNorm I : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

theorem triple_normalized_mass_source_bounds (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      0 < B → 0 < T → 0 < R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro Γ B T R hB hT hR hz hn
  rcases Γ.eq_empty_or_nonempty with he|⟨γ,hγ⟩
  · subst Γ
    simp only [Finset.sum_empty,mul_zero]
    positivity
  · obtain ⟨hq,ht,hr⟩ := hz γ hγ
    obtain ⟨hqb,htb,hrb⟩ := hn γ hγ
    exact hb Γ B T R ((nonzero_ideal_norm_one _ hq).trans hqb)
      ((nonzero_ideal_norm_one _ ht).trans htb) ((nonzero_ideal_norm_one _ hr).trans hrb) hz hn

theorem actual_second_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (u v : Eisˣ)
      (Z ell R j t g theta eta : ℝ), 0 < Z →
      (∀ x ∈ source, x.quotient ≠ 0) →
      (∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta)) →
      (∀ x ∈ source, Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x ∈ source, (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta)) →
      (∀ x ∈ source, primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta)) →
      (∀ x ∈ source, Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      Z^(-(ell+R/2-j+t+g-theta+11*eta/2)) *
        (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*ε) := by
  obtain ⟨C,hC,hb⟩ := triple_normalized_mass_source_bounds K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hz : ∀ γ ∈ actualSecondTriples p u v source,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0 := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    exact (actualSecondChild_nonzero p hp u v x (ht x hx)).2
  have hn : ∀ γ ∈ actualSecondTriples p u v source,
      (Ideal.absNorm γ.q0 : ℝ) ≤ Z^(ell+R/2-j+5*eta/2) ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ Z^(t+eta) ∧
      (Ideal.absNorm γ.residual : ℝ) ≤ Z^(g-theta+2*eta) := by
    intro γ hγ
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
    refine ⟨actual_second_q0_power_bound p hp x u v Z ell R j eta hZ
      (h1 x hx) (h2 x hx) (ha x hx) (hJ x hx),hT x hx,?_⟩
    have hr := second_residual_norm_power_bound p hp _ _ (hE x hx) Z g theta eta hZ (hG x hx) (hD x hx)
    change (Ideal.absNorm (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) : ℝ) ≤ _
    simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hr
  have hm := hb (actualSecondTriples p u v source)
    (Z^(ell+R/2-j+5*eta/2)) (Z^(t+eta)) (Z^(g-theta+2*eta))
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hz hn
  have he : Z^(ell+R/2-j+5*eta/2)*Z^(t+eta)*Z^(g-theta+2*eta) =
      Z^(ell+R/2-j+t+g-theta+11*eta/2) := by
    rw [←Real.rpow_add hZ,←Real.rpow_add hZ]
    congr 1
    ring
  rw [he,←Real.rpow_mul hZ.le,←Real.rpow_neg hZ.le] at hm
  exact hm

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0593

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondAdmissible
Source SHA256: a15439b2eb1afce2fa638260eabe92009bd272cd8c009fad158c88b76305166f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0594



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_inherited_puncture_ne_zero
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    actualSecondInheritedPuncture m (actualSecondChild p u v x).1 ≠ 0 := by
  change ((m*ConcretePrimeRowBridge.idealGenerator x.quotient)*
    primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}))*
    primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor)) ≠ 0
  rw [show primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero _ ht))
    (primeProduct_ne_zero p hp _ _)) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

lemma radicalGenerator_ne_zero (a : Eis) (ha : a ≠ 0) :
    ConcretePrimeRowBridge.idealGenerator (Ideal.span {a}).radical ≠ 0 := by
  apply ConcretePrimeRowBridge.idealGenerator_ne_zero
  intro hz
  apply Ideal.span_singleton_eq_bot.not.mpr ha
  apply le_antisymm _ bot_le
  exact (Ideal.le_radical : (Ideal.span {a} : Ideal Eis) ≤ (Ideal.span {a}).radical).trans (le_of_eq hz)

def actualSecondPunctureWidth (Z : ℝ) (m : Eis) (γ : OuterTriple) : ℝ :=
  Real.logb Z (‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2)

include hp in
theorem actual_second_puncture_width_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_budget p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ hB hT hG hD

include hp in

theorem actual_second_child_margins
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (hB : primeProductNorm p x.cube.support ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_bound p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ hB hT hG hD
  unfold decrease
  linarith

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_row_decrease
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (Z M ell A t g theta V j eta d : ℝ) (hZ : 1 < Z)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hterminal : d ≤ ell+V) (heta : eta ≤ d/16)
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hJ : Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    3*d/2 ≤ M-childM M ell A t g theta V j eta :=
  child_row_decrease hA ht (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hterminal heta

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0594

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondOriginalMass
Source SHA256: 38e65e0dfbb7674c510b290d692efa4d65f271ac65cd96e2ebfa8b237ee27941
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0595


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic (sourceIdeal)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem actual_second_original_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ι : Type} [DecidableEq ι] (p : ι → Eis)
      (_hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (u v : Eisˣ)
      (Z ell R j t g theta eta : ℝ), 0 < Z →
      (∀ x ∈ source, x.quotient ≠ 0) →
      (∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x ∈ source, primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(R+eta)) →
      (∀ x ∈ source, Z^(j-eta) ≤ ‖eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x ∈ source, (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta)) →
      (∀ x ∈ source, primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta)) →
      (∀ x ∈ source, Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∑ γ ∈ actualSecondTriples p u v source,tripleDivisorWeight K γ) ≤
        C*Z^((ell+R/2-j+t+g-theta+11*eta/2)*(1+ε)) := by
  obtain ⟨C,hC,hb⟩ := actual_second_normalized_mass K ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ Jo Jn source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  have hm := hb p hp source u v Z ell R j t g theta eta hZ ht hE h1 h2 ha hJ hT hG hD
  let c := ell+R/2-j+t+g-theta+11*eta/2
  calc
    _ = Z^c * (Z^(-c)*(∑ γ∈actualSecondTriples p u v source,tripleDivisorWeight K γ)) := by
      rw [←mul_assoc,←Real.rpow_add hZ,add_neg_cancel,Real.rpow_zero,one_mul]
    _ ≤ Z^c*(C*Z^(c*ε)) := mul_le_mul_of_nonneg_left hm (Real.rpow_pos_of_pos hZ _).le
    _ = _ := by
      rw [mul_left_comm,←Real.rpow_add hZ]
      congr 2
      dsimp only [c]
      ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0595

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSharpPuncture
Source SHA256: 05ec768593faed03f5c3fcb05d5575606eee0f5e6bab2f9f6e9628d1c9b9d346
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0596


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in

theorem actual_second_radical_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,FiniteGaussPhase.span_finset_prod]
  rw [eisEmbedding_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,ConcretePrimeRowBridge.span_idealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _))
    (sourceIdeal_ne_zero p hp _) Ideal.le_radical

include hp in

theorem actual_second_inherited_puncture_q0_norm
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ConcreteTraceCRT.eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (ConcretePrimeRowBridge.idealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_q0_norm p hp hpr x hE u v
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) hm'
  change ‖ConcreteTraceCRT.eisEmbedding (actualSecondRadicalPuncture
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*ConcretePrimeRowBridge.idealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,ConcretePrimeRowBridge.span_idealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (Nat.cast_nonneg _)) (primeProductNorm_pos p hp _).le

include hp in

theorem actual_second_q0_cube_bound
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (B : ℝ) (hB : 0 ≤ B)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0 : ℝ) ≤ B := by
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) : ℝ) ≤ B
  rw [←eisEmbedding_norm_sq_eq_absNorm_span]
  exact (cube_label_norm_bounds p hp _ _ _ _ _ x.cube.support_pos B hB h1 h2).2.1

include hp in
theorem actual_second_puncture_power_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 0 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    ‖eisEmbedding (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      Z^(Q+ell+t+g-theta+4*eta) := by
  have hr := second_residual_norm_power_bound p hp _ _ hE Z g theta eta hZ hG hD
  have hb := actual_second_q0_cube_bound p hp x u v _ (Real.rpow_pos_of_pos hZ _).le h1 h2
  apply (actual_second_inherited_puncture_q0_norm p hp hpr x hE ht u v m hm).trans
  calc
    _ ≤ (Z^Q*Z^(t+eta))*Z^(ell+eta)*Z^(g-theta+2*eta) := by
      have hr0 := (primeProductNorm_pos p hp (x.second.sourceCommon\x.second.divisor)).le
      gcongr
    _ = Z^((Q+(t+eta))+(ell+eta)+(g-theta+2*eta)) := by
      rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
    _ = _ := by congr 1; ring

include hp in
theorem actual_second_puncture_width_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z Q ell t g theta eta : ℝ) (hZ : 1 < Z)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    actualSecondPunctureWidth Z m (actualSecondChild p u v x).1 ≤ Q+ell+t+g-theta+4*eta := by
  have hp0 := actual_second_inherited_puncture_ne_zero p hp hpr x ht u v m hm
  have hr0 := radicalGenerator_ne_zero _ hp0
  change actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1 ≠ 0 at hr0
  apply (Real.logb_le_iff_le_rpow hZ (sq_pos_of_pos
    (norm_pos_iff.mpr (ConcreteTraceCRT.eisEmbedding_ne_zero hr0)))).mpr
  exact actual_second_puncture_power_from_cubes p hp hpr x hE ht u v m hm
    Z Q ell t g theta eta (zero_lt_one.trans hZ) hQ h1 h2 hT hG hD

include hp in

theorem actual_second_child_margins_from_cubes
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht0 : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0)
    (Z F M Q z c ell A t g theta V j delta eta : ℝ) (hZ : 1 < Z)
    (hparent : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) ≤ Z^Q)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta))
    (hT : (Ideal.absNorm x.quotient : ℝ) ≤ Z^(t+eta))
    (hG : primeProductNorm p x.second.sourceCommon ≤ Z^(g+eta))
    (hD : Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta)
      (actualSecondPunctureWidth Z m (actualSecondChild p u v x).1) z (c-7*eta) := by
  apply child_margins hparent hA ht hV hj
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD) hdelta heta
  have hwidth := actual_second_puncture_width_from_cubes p hp hpr x hE ht0 u v m hm
    Z Q ell t g theta eta hZ hQ h1 h2 hT hG hD
  unfold decrease
  linarith

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0596

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondVaryingLists
Source SHA256: d9d50510bd8903ac769021366fe31351147866e0c778420d00bc9c388bf4f4a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0597


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open InverseSecondFibers
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def varyingAssignedGate {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : Prop :=
  (∀ i hi,x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))∈L₁ (eraseSecondSlots x) i) ∧
  (∀ i hi,x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))∈L₂ (eraseSecondSlots x) i)

omit [DecidableEq ι] in
lemma varyingAssignedGate_attach {Jo : ℕ} (J₁ J₂ : Finset σ)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i∈J₁,ι)×(∀ i∈J₂,ι)) :
    varyingAssignedGate J₁ J₂ L₁ L₂ (attachPairedSlots J₁ J₂ (x,q)) ↔
      q.1∈J₁.pi (L₁ x) ∧ q.2∈J₂.pi (L₂ x) := by
  simp only [varyingAssignedGate,attachPairedSlots,erase_attachSecondSlots]
  simp only [attachSecondSlots,pairedSlotAssignment,
    Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,Finset.mem_pi]

def varyingAssignedSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :=
  (assignedSecondSource source J₁ J₂ base₁ base₂).filter (varyingAssignedGate J₁ J₂ L₁ L₂)

theorem varyingAssignedSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S⊆T)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι) :
    varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂⊆
      varyingAssignedSource T J₁ J₂ base₁ base₂ L₁ L₂ := by
  exact Finset.filter_subset_filter _ (assignedSecondSource_mono hST J₁ J₂ base₁ base₂)

theorem varyingAssignedSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card)→ℂ) :
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,F x =
      ∑ y∈source,∑ q∈(J₁.pi (fun i=>L₁ y i∩(y.second.sourceCommon∪y.second.overlap)))×ˢ
        (J₂.pi (fun i=>L₂ y i∩(y.second.sourceCommon∪y.second.overlap))),F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [varyingAssignedSource,Finset.sum_filter,assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  congr 1
  ext q
  simp only [Finset.mem_filter,Finset.mem_product,varyingAssignedGate_attach,Finset.mem_pi,Finset.mem_inter]
  constructor
  · rintro ⟨⟨h₁,h₂⟩,h₃,h₄⟩
    exact ⟨fun i hi=>⟨h₃ i hi,(h₁ i hi).2⟩,fun i hi=>⟨h₄ i hi,(h₂ i hi).2⟩⟩
  · rintro ⟨h₁,h₂⟩
    exact ⟨⟨fun i hi=>⟨hL₁ y hy i hi (h₁ i hi).1,(h₁ i hi).2⟩,
      fun i hi=>⟨hL₂ y hy i hi (h₂ i hi).1,(h₂ i hi).2⟩⟩,
      fun i hi=>(h₁ i hi).1,fun i hi=>(h₂ i hi).1⟩

theorem varyingAssignedSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ) (w P : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈source,w y*(star (primeMark J₁ (L₁ y) a₁ (y.second.sourceCommon∪y.second.overlap))*
      primeMark J₂ (L₂ y) a₂ (y.second.sourceCommon∪y.second.overlap))*P y) =
    ∑ x∈varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x)*P (eraseSecondSlots x) := by
  rw [varyingAssignedSource_sum source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

variable (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem actual_second_varying_lists_weighted_count
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {Jo : ℕ} (u v : Oˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ→Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i)
    (a₁ a₂ : σ→ι→ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈base₁ i,‖a₁ i q‖≤1)
    (ha₂ : ∀ i∈J₂,∀ q∈base₂ i,‖a₂ i q‖≤1)
    (labels : Finset (Ideal O)) (rows : Finset O)
    (hchild : ∀ x∈source,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows)
    (K : ℕ) (ho : Jo≤2*K) (hJ₁ : J₁.card≤K) (hJ₂ : J₂.card≤K)
    (w : MarkedSecondSource ι Jo 0→ℂ) (hw : ∀ x∈source,‖w x‖≤1) (F G : SecondChild→ℂ) :
    ‖∑ x∈source,w x*(star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap))*
      primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap))*
      F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x))‖ ≤
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows F γ)*
    Real.sqrt (∑ γ∈actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
      tripleDivisorWeight K γ*secondLabelEnergy K labels rows G γ) := by
  let S := varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂
  have hsub : S⊆assignedSecondSource source J₁ J₂ base₁ base₂ := Finset.filter_subset _ _
  have hs' : ActualSecondSourceConditions p S :=
    (assignedSecondSource_conditions p source hs J₁ J₂ base₁ base₂).mono p hsub
  have herase : ∀ x∈S,eraseSecondSlots x∈source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ base₁ base₂ x).mp (hsub hx)
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card)=>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hw' : ∀ x∈S,‖w' x‖≤1 := by
    intro x hx
    rw [show w' x=w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ base₁ base₂ a₁ a₂ ha₁ ha₂ x (hsub hx))
  have hc' : ∀ x∈S,(actualSecondChild p u v x).2.1∈labels ∧ (actualSecondChild p u v x).2.2∈rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := varyingAssignedSource_sum_marks source J₁ J₂ base₁ base₂ L₁ L₂ hL₁ hL₂ a₁ a₂ w
    (fun x=>F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0597

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondVaryingSupported
Source SHA256: becc9e336e902e415ecf34739f1acf1fef1025fcdc089fc2f8890bd11f319059
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0598



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_supported_varying_lists_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (base₁ base₂ : σ → Finset ι)
    (L₁ L₂ : MarkedSecondSource ι Jo 0→σ→Finset ι)
    (hL₁ : ∀ x∈source,∀ i∈J₁,L₁ x i⊆base₁ i)
    (hL₂ : ∀ x∈source,∀ i∈J₂,L₂ x i⊆base₂ i) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ base₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ base₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource
          source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hp hcop hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ (L₁ x) a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ (L₂ x) a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hp hcop hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_varying_lists_weighted_count p hp hpr hcop hinj u v S
    (hs.mono p hsub) J₁ J₂ base₁ base₂ L₁ L₂
    (fun x hx=>hL₁ x (hsub hx)) (fun x hx=>hL₂ x (hsub hx)) a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hp hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hp hcop hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hcop hg hinj hc Ψ hΨ (m x) z x)).trans
          (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (varyingAssignedSource_mono hsub J₁ J₂ base₁ base₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource S J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ base₁ base₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0598

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedModeEnergy
Source SHA256: d5d7b8c156e125beb37c1094c18de7a8c30bafa4f22adc2a15190f3809bbc8ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0599




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_mode_branch_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1) :
    ‖∑ x ∈ source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (varyingAssignedSource source J₁ J₂ lists₁ lists₂
        (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ) := by
  let phase := fun x => w x * secondModeOuter p x Ψ m z G E V B X t
  have hphase : ∀ x ∈ source,‖phase x‖ ≤ 1 := by
    intro x hx
    simpa only [phase,norm_mul,secondModeOuter,secondOuterPhase_norm,mul_one] using hw x hx
  have hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
    intro x hx
    exact ⟨hlabels x hx,(actual_second_row_ball p hp hpr x u v R).mp (hrows x hx)⟩
  have he := actual_second_supported_varying_lists_energy p hp hcop hg hpr hinj hc
    u v source hs Ψ hΨ (fun x => m*ConcretePrimeRowBridge.idealGenerator x.quotient) z
    J₁ J₂ lists₁ lists₂ (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)
    (fun _ _ _ _=>Finset.sdiff_subset) (fun _ _ _ _=>Finset.sdiff_subset) a₁ a₂ ha₁ ha₂ labels (nonzeroChildFrequencyBall 1 R) hchild
    K ho hJ₁ hJ₂ phase hphase
    (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t)
    (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t)
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  rw [secondModeBranch_parent_lists_restore p hp hcop hg hpr x (hs.admissible x hx)
    (hs.second_divisor x hx) u v (deleted₁ x) (deleted₂ x) (hd₁ x hx) (hd₂ x hx)]
  dsimp only [phase]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0599

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondWholeMass
Source SHA256: 2ee36e75715446b40947c7324ea84e5e63ef652f2297e695e0f1a51410f4707b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0600


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem actualSecondChild_outer_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).1 = (actualSecondChild p 1 1 x).1 := rfl

theorem actualSecondChild_label_units {Jo Jn : ℕ} (u v : Eisˣ)
    (x : MarkedSecondSource ι Jo Jn) :
    (actualSecondChild p u v x).2.1 = (actualSecondChild p 1 1 x).2.1 := rfl

theorem actualSecondTriples_units {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) :
    actualSecondTriples p u v source = actualSecondTriples p 1 1 source := rfl

theorem assigned_second_triples_subset {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂) ⊆
      actualSecondTriples p 1 1 source := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  exact Finset.mem_image.mpr ⟨y,hy,rfl⟩

theorem assigned_second_mass_le_original {Jo : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (K : ℕ) :
    (∑ γ∈actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),tripleDivisorWeight K γ) ≤
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (assigned_second_triples_subset p u v source J₁ J₂ L₁ L₂)
    (fun γ _ _ => tripleDivisorWeight_nonneg K γ)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0600

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedOriginalBound
Source SHA256: 6bd280792da08363aa0adfe055e11b5c8215b868f288b4fbe458d130e19ee286
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0601




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_mode_original_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈J₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈J₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖∑ x∈source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤ A * ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  have hlabels' : ∀ x∈source,(actualSecondChild p u v x).2.1 ∈ labels := by
    intro x hx
    rw [actualSecondChild_label_units]
    exact hlabels x hx
  have hΓ := (actualSecondTriples_mono p u v
    (show varyingAssignedSource source J₁ J₂ lists₁ lists₂
      (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x)⊆
      assignedSecondSource source J₁ J₂ lists₁ lists₂ from Finset.filter_subset _ _)).trans
      (assigned_second_triples_subset p u v source J₁ J₂ lists₁ lists₂)
  apply (actual_second_deleted_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
    slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels
    hlabels' hrows K ho hJ₁ hJ₂ w hw).trans
  apply (second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
    _ _ _ A hA (fun γ hγ => hright γ (hΓ hγ)) (fun γ hγ => hleft γ (hΓ hγ))).trans
  exact mul_le_mul_of_nonneg_left
    (Finset.sum_le_sum_of_subset_of_nonneg hΓ (fun γ _ _=>tripleDivisorWeight_nonneg K γ)) hA

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0601

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedAllModes
Source SHA256: ab553d0c6965ef1d98b928c8379c398442e8b323ee34b60bf585b82f09424e48
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0602



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondDeletedFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
          ω₁ ω₂ G E V B X t

theorem secondDeletedFullModeSum_physical {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) :
    secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t =
    ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
      (w x*actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
        ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t := by
  unfold secondDeletedFullModeSum
  apply Finset.sum_congr rfl
  intro uv huv
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem actual_second_deleted_all_modes_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t‖ ≤
    36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  let mass := ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hbound (uv : Eisˣ × Eisˣ) (J₁ : Finset σ) (hJ₁ : J₁∈slots₁.powerset)
      (J₂ : Finset σ) (hJ₂ : J₂∈slots₂.powerset) :
      ‖∑ x∈secondSourceSector source sector uv,
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t‖ ≤ A*mass := by
    have hsub : secondSourceSector source sector uv ⊆ source := Finset.filter_subset _ _
    have ht := actualSecondTriples_mono p 1 1 hsub
    have h := actual_second_deleted_mode_original_bound p hp hcop hg hpr hinj hc uv.1 uv.2
      (secondSourceSector source sector uv) (hs.mono p hsub) pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      (fun x hx=>hd₁ x (hsub hx)) (fun x hx=>hd₂ x (hsub hx))
      (fun i hi => ha₁ i (Finset.mem_powerset.mp hJ₁ hi))
      (fun i hi => ha₂ i (Finset.mem_powerset.mp hJ₂ hi)) ω₁ ω₂ G E V B X R t labels
      (fun x hx => hlabels x (hsub hx)) (fun x hx => hrows x (hsub hx)) K ho
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₁)).trans hslots₁)
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₂)).trans hslots₂)
      w (fun x hx => hw x (hsub hx)) A hA
      (fun γ hγ => hleft J₁ hJ₁ γ (ht hγ)) (fun γ hγ => hright J₂ hJ₂ γ (ht hγ))
    exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun γ _ _ => tripleDivisorWeight_nonneg K γ)) hA)
  calc
    _ ≤ ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
        ‖∑ x∈secondSourceSector source sector uv,
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
              ω₁ ω₂ G E V B X t‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro uv huv
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact norm_sum_le _ _
    _ ≤ ∑ _uv : Eisˣ × Eisˣ,∑ _J₁∈slots₁.powerset,∑ _J₂∈slots₂.powerset,A*mass := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact Finset.sum_le_sum (fun J₂ hJ₂ => hbound uv J₁ hJ₁ J₂ hJ₂)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,
        second_unit_sector_card,Nat.cast_pow,Nat.cast_ofNat,mass]
      ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0602

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedAllIntegral
Source SHA256: 5e40bb81923e3459a2fb3ddf89f05299171ca4791c088cc5049615012a6b65c3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0603


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedAllIntegralUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_all_modes_integral
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
    (hd₁ : ∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (hd₂ : ∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨
      (Ideal.span {p i}:Ideal Eis)∣x.quotient)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ)
    (hDensity : Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J t.1*coordinateHeight J t.2*‖density t‖))
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),density t*secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
      ω₁ ω₂ G E V B X w t‖ ≤
    (36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖ := by
  let C := 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
    ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
        ω₁ ω₂ G E V B X w t‖ ≤ C*(tripleHeight J t.1*coordinateHeight J t.2) := by
    have hh := actual_second_deleted_all_modes_bound p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels hlabels hrows
      K ho hslots₁ hslots₂ w hw (A*(tripleHeight J t.1*coordinateHeight J t.2))
      (by unfold tripleHeight coordinateHeight; positivity) (hleft t) (hright t)
    exact hh.trans_eq (by dsimp only [C]; ring)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),C*(tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul C)
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0603

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondOriginalBound
Source SHA256: fe75c148cce8c5a693cbc10003e703d570feccc17c8fe915d666d936ee7ef226
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0604



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_mode_original_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈J₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈J₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖∑ x∈source,actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤ A * ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  have hlabels' : ∀ x∈source,(actualSecondChild p u v x).2.1 ∈ labels := by
    intro x hx
    rw [actualSecondChild_label_units]
    exact hlabels x hx
  have hΓ := assigned_second_triples_subset p u v source J₁ J₂ lists₁ lists₂
  apply (actual_second_mode_branch_energy p hp hcop hg hpr hinj hc u v source hs pool Ψ hΨ m z
    slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels
    hlabels' hrows K ho hJ₁ hJ₂ w hw).trans
  apply (second_geometric_energy_of_bound K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
    _ _ _ A hA (fun γ hγ => hright γ (hΓ hγ)) (fun γ hγ => hleft γ (hΓ hγ))).trans
  exact mul_le_mul_of_nonneg_left (assigned_second_mass_le_original p u v source J₁ J₂ lists₁ lists₂ K) hA

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0604

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondAllModes
Source SHA256: d519c095def945927fca82d9ce467e2b2b7664fbd43c9a5e8ea7ce6c64fba8bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0605



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondAllModesUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondFullModeSum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
    ∑ x∈secondSourceSector source sector uv,
      actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x * w x *
        secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
          ω₁ ω₂ G E V B X t

theorem secondFullModeSum_physical {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (w : MarkedSecondSource ι Jo 0 → ℂ)
    (t : Frequency × (Fin 6 → ℝ)) :
    secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t =
    ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
      (w x*actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
        ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  unfold secondFullModeSum
  apply Finset.sum_congr rfl
  intro uv huv
  simp only [Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem actual_second_all_modes_bound
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A)
    (hleft : ∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A)
    (hright : ∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A) :
    ‖secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t‖ ≤
    36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ := by
  let mass := ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hbound (uv : Eisˣ × Eisˣ) (J₁ : Finset σ) (hJ₁ : J₁∈slots₁.powerset)
      (J₂ : Finset σ) (hJ₂ : J₂∈slots₂.powerset) :
      ‖∑ x∈secondSourceSector source sector uv,
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t‖ ≤ A*mass := by
    have hsub : secondSourceSector source sector uv ⊆ source := Finset.filter_subset _ _
    have ht := actualSecondTriples_mono p 1 1 hsub
    have h := actual_second_mode_original_bound p hp hcop hg hpr hinj hc uv.1 uv.2
      (secondSourceSector source sector uv) (hs.mono p hsub) pool Ψ hΨ m z
      slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
      (fun i hi => ha₁ i (Finset.mem_powerset.mp hJ₁ hi))
      (fun i hi => ha₂ i (Finset.mem_powerset.mp hJ₂ hi)) ω₁ ω₂ G E V B X R t labels
      (fun x hx => hlabels x (hsub hx)) (fun x hx => hrows x (hsub hx)) K ho
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₁)).trans hslots₁)
      ((Finset.card_le_card (Finset.mem_powerset.mp hJ₂)).trans hslots₂)
      w (fun x hx => hw x (hsub hx)) A hA
      (fun γ hγ => hleft J₁ hJ₁ γ (ht hγ)) (fun γ hγ => hright J₂ hJ₂ γ (ht hγ))
    exact h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ht
      (fun γ _ _ => tripleDivisorWeight_nonneg K γ)) hA)
  calc
    _ ≤ ∑ uv : Eisˣ × Eisˣ,∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
        ‖∑ x∈secondSourceSector source sector uv,
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*w x*
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
              ω₁ ω₂ G E V B X t‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro uv huv
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact norm_sum_le _ _
    _ ≤ ∑ _uv : Eisˣ × Eisˣ,∑ _J₁∈slots₁.powerset,∑ _J₂∈slots₂.powerset,A*mass := by
      apply Finset.sum_le_sum
      intro uv huv
      apply Finset.sum_le_sum
      intro J₁ hJ₁
      exact Finset.sum_le_sum (fun J₂ hJ₂ => hbound uv J₁ hJ₁ J₂ hJ₂)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,
        second_unit_sector_card,Nat.cast_pow,Nat.cast_ofNat,mass]
      ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0605

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondAllIntegral
Source SHA256: 07662c3c7abefa239ee36ea62aee4359dbf00e7fe12b11f7e3896f0a97f63c52
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0606


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondAllIntegralUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_all_modes_integral
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ)
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels)
    (hrows : ∀ x∈source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hslots₁ : slots₁.card ≤ K) (hslots₂ : slots₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x∈source,‖w x‖ ≤ 1)
    (A : ℝ) (hA : 0 ≤ A) (J : ℕ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ)
    (hDensity : Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
      tripleHeight J t.1*coordinateHeight J t.2*‖density t‖))
    (hleft : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2))
    (hright : ∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
      secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
        (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤ A*(tripleHeight J t.1*coordinateHeight J t.2)) :
    ‖∫ t : Frequency × (Fin 6 → ℝ),density t*secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
      ω₁ ω₂ G E V B X w t‖ ≤
    (36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
      ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
      ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖ := by
  let C := 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
    ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ
  have hb (t : Frequency × (Fin 6 → ℝ)) :
      ‖secondFullModeSum p hp hcop hg source sector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X w t‖ ≤ C*(tripleHeight J t.1*coordinateHeight J t.2) := by
    have hh := actual_second_all_modes_bound p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ ω₁ ω₂ G E V B X R t labels hlabels hrows
      K ho hslots₁ hslots₂ w hw (A*(tripleHeight J t.1*coordinateHeight J t.2))
      (by unfold tripleHeight coordinateHeight; positivity) (hleft t) (hright t)
    exact hh.trans_eq (by dsimp only [C]; ring)
  calc
    _ ≤ ∫ t : Frequency × (Fin 6 → ℝ),C*(tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul C)
      filter_upwards with t
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb t) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0606

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SourceDepth
Source SHA256: 0783a444f955a496e43c57c5511d8dc6aab875ffe3e58d7492c1cabc74faaaee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0607


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

include hp in

theorem actual_second_childF_upper {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor⊆x.second.sourceCommon)
    (Z F ell A t g theta V j delta eta : ℝ) (hZ : 1<Z)
    (hA : 0≤A) (ht : 0≤t) (hell : 0≤ell) (hV : 0≤V) (hdelta : delta≤6*eta)
    (hG : primeProductNorm p x.second.sourceCommon≤Z^(g+eta))
    (hD : Z^(theta-eta)≤primeProductNorm p x.second.divisor)
    (h1 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta))
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) :
    childF F ell A t g theta V j delta≤F+11*eta :=
  childF_upper hA ht hell hV
    (actual_second_common_center p hp x hE Z g theta eta hZ hG hD)
    (actual_second_label_center p hp x Z ell j eta hZ h1 h2 hJ) hdelta

include hp in

theorem actual_source_path_lengths
    (Jo Jn : ℕ→ℕ) (x : (k : ℕ)→MarkedSecondSource ι (Jo k) (Jn k))
    (F M ell A t g theta V j delta : ℕ→ℝ) (Z eta d : ℝ) (hZ : 1<Z)
    (n : ℕ) (heta : eta≤d/16)
    (hsource : ∀ k<n,
      (x k).second.divisor⊆(x k).second.sourceCommon ∧
      0≤A k ∧ 0≤t k ∧ 0≤ell k ∧ 0≤V k ∧ delta k≤6*eta ∧ d≤ell k+V k ∧
      primeProductNorm p (x k).second.sourceCommon≤Z^(g k+eta) ∧
      Z^(theta k-eta)≤primeProductNorm p (x k).second.divisor ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.leftExponent)‖^2≤Z^(ell k+eta) ∧
      ‖eisEmbedding (primeProduct p (x k).cube.support (x k).cube.rightExponent)‖^2≤Z^(ell k+eta) ∧
      Z^(j k-eta)≤‖eisEmbedding (jLabel p (x k).cube.support
        (fun i=>(x k).cube.leftExponent i+(x k).cube.rightExponent i)
        (x k).cube.leftBit (x k).cube.rightBit)‖^2)
    (hF : ∀ k<n,F (k+1)=childF (F k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) (delta k))
    (hM : ∀ k<n,M (k+1)=childM (M k) (ell k) (A k) (t k) (g k) (theta k) (V k) (j k) eta) :
    F n≤F 0+11*(n:ℝ)*eta ∧ M n+3*(n:ℝ)*d/2≤M 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hlt : n<n+1 := Nat.lt_succ_self n
    obtain ⟨he,ha,ht,hl,hv,hd,hterm,hg,hdiv,h1,h2,hj⟩ := hsource n hlt
    have hi := ih (fun k hk=>hsource k (Nat.lt_trans hk hlt))
      (fun k hk=>hF k (Nat.lt_trans hk hlt)) (fun k hk=>hM k (Nat.lt_trans hk hlt))
    have hf := actual_second_childF_upper p hp (x n) he Z (F n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) (delta n) eta hZ ha ht hl hv hd hg hdiv h1 h2 hj
    have hm := actual_second_row_decrease p hp (x n) he Z (M n) (ell n) (A n) (t n)
      (g n) (theta n) (V n) (j n) eta d hZ ha ht hterm heta hg hdiv h1 h2 hj
    rw [←hF n hlt] at hf
    rw [←hM n hlt] at hm
    push_cast
    constructor <;> linarith [hi.1,hi.2]

theorem source_depth_caps (F M N V F0 M0 eta : ℝ) (n D : ℕ) (hn : n≤D)
    (heta : 0≤eta) (hF : F≤F0+11*(n:ℝ)*eta) (_hM : 0≤M) (hMm : M≤M0)
    (hN : 0≤N) (hV : 0≤V) (hsum : F=N+V) :
    N≤F0+11*(D:ℝ)*eta ∧ V≤F0+11*(D:ℝ)*eta ∧ M≤M0 := by
  have hn' : (n:ℝ)≤D := by exact_mod_cast hn
  have hmul := mul_le_mul_of_nonneg_right hn' heta
  constructor
  · linarith
  constructor
  · linarith
  · exact hMm

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0607

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialClippedColumns
Source SHA256: 1ece818208c68fc5d43e20cc861e985cfbd068ac579a6630ec2661254ddf23ce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0608




namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge JointLogSeparation
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open SevenEighths.InverseMoment
namespace SevenEighths.InverseInitialClippedColumns
local notation "Eis" => ActualEisensteinCubic.O

def clippedTest (w : ℝ → ℂ) (c h : ℝ) : ℝ → ℂ :=
  childLogTest (fun x => w (c*x)) h

theorem clippedTest_eq_source (w : ℝ → ℂ) (c h x : ℝ) :
    clippedTest w c h x = InverseInitialProfile.clippedSource w c h x := by
  unfold clippedTest childLogTest InverseInitialProfile.clippedSource
  ring

theorem child_test_clipping (w : ℝ → ℂ) {Z q : ℝ} (hZ : 0 < Z) (hq : 0 < q)
    (N h : ℝ) :
    childLogTest w h (q/Z^N) = logPhase h (Real.log (Z^(max 0 N-N))) *
      clippedTest w (Z^(max 0 N-N)) h (q/Z^(max 0 N)) := by
  rw [clippedTest_eq_source]
  simpa only [childLogTest,mul_comm] using
    InverseInitialProfile.clipped_column_source_identity w hZ hq N h

section Arithmetic
variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) : Finset (Finset ι) :=
  pool.powerset.filter (fun U => w (primeProductNorm p U/X) ≠ 0)

omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem mem_freshColumns (pool : Finset ι) (w : ℝ → ℂ) (X : ℝ) (U : Finset ι) :
    U ∈ freshColumns p pool w X ↔ U ⊆ pool ∧ w (primeProductNorm p U/X) ≠ 0 := by
  simp [freshColumns]

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_clipping_range (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    1 ≤ Z^(max 0 N-N) ∧ Z^(max 0 N-N) ≤ b := by
  obtain ⟨U,hU⟩ := hn
  exact InverseClippingProfiles.clipping_ratio_of_column_witness w Z N
    (primeProductNorm p U) a b hZ (primeProductNorm_ge_one p hp U) hb hw
    ((mem_freshColumns p pool w (Z^N) U).mp hU).2

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem freshColumns_initial_clipping_shift (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N η : ℝ) (hZ : 1 < Z) (hb : 1 ≤ b)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty)
    (hthreshold : Real.log b ≤ 3*η*Real.log Z) :
    0 ≤ max 0 N-N ∧ max 0 N-N ≤ 3*η := by
  have hc := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hz : 0 < Z := zero_lt_one.trans hZ
  have hl := Real.log_le_log (Real.rpow_pos_of_pos hz _) hc.2
  rw [Real.log_rpow hz] at hl
  refine ⟨sub_nonneg.mpr (le_max_right _ _), ?_⟩
  exact (mul_le_mul_iff_left₀ (Real.log_pos hZ)).mp (hl.trans hthreshold)

include hp in
omit [DecidableEq ι] [∀ i, (Ideal.span {p i}).IsMaximal] in
theorem clippedTest_support_of_freshColumns (pool : Finset ι) (w : ℝ → ℂ)
    (a b Z N h : ℝ) (ha : 0 < a) (hb : 1 ≤ b) (hZ : 1 < Z)
    (hw : Function.support w ⊆ Set.Icc a b)
    (hn : (freshColumns p pool w (Z^N)).Nonempty) :
    Function.support (clippedTest w (Z^(max 0 N-N)) h) ⊆ Set.Icc (a/b) b := by
  obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool w a b Z N hZ hb hw hn
  have hs := InverseClippingProfiles.clipped_positive_support w a b _ ha hc hcb hw
  intro x hx
  exact hs (mul_ne_zero_iff.mp hx).1

theorem canonical_row_zero_of_freshColumns_empty
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ) (he : freshColumns p pool w X = ∅) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X = 0 := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  apply Finset.sum_eq_zero
  intro U hU
  have hw : w (primeProductNorm p U/X) = 0 := by
    by_contra hw
    have hu : U ∈ freshColumns p pool w X := Finset.mem_filter.mpr ⟨hU,hw⟩
    rw [he] at hu
    exact Finset.notMem_empty U hu
  simp only [secondChildColumn,childLogTest,hw,zero_mul,mul_zero]

theorem canonical_row_nonzero_freshColumns
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) (X h : ℝ)
    (hn : finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) X ≠ 0) : (freshColumns p pool w X).Nonempty := by
  by_contra he
  exact hn (canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m f k
    slots lists a w X h (Finset.not_nonempty_iff_eq_empty.mp he))

theorem canonical_row_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N) =
      logPhase h (Real.log (Z^(max 0 N-N))) *
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
          (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold finiteCanonicalMarkedRow fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  simp only [secondChildColumn]
  rw [child_test_clipping w hZ (primeProductNorm_pos p hp U) N h]
  ring

theorem canonical_row_clipping_norm
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (childLogTest w h) (Z^N)‖ =
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N))‖ := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots lists a w hZ N h,
    norm_mul,logPhase_norm,one_mul]

def columnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
      slots lists a W X‖^2

theorem columnEnergy_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) := by
  unfold columnEnergy
  simp_rw [canonical_row_clipping_norm p hp hcop hg pool Ψ m _ _ slots lists a w hZ N h]

theorem canonical_pair_clipping
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ h₁) (Z^N) *
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ (-h₂)) (Z^N)) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) h₁) (Z^(max 0 N)) *
      star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) (-h₂)) (Z^(max 0 N)))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

theorem canonical_pair_clipping_left_conjugate
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m f k : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (w₁ w₂ : ℝ → ℂ)
    {Z : ℝ} (hZ : 0 < Z) (N h₁ h₂ : ℝ) :
    star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
      (childLogTest w₁ (-h₁)) (Z^N)) *
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
      (childLogTest w₂ h₂) (Z^N) =
    logPhase (h₁+h₂) (Real.log (Z^(max 0 N-N))) *
      (star (finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁
        (clippedTest w₁ (Z^(max 0 N-N)) (-h₁)) (Z^(max 0 N))) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂
        (clippedTest w₂ (Z^(max 0 N-N)) h₂) (Z^(max 0 N))) := by
  rw [canonical_row_clipping p hp hcop hg pool Ψ m f k slots₁ lists₁ a₁ w₁ hZ,
    canonical_row_clipping p hp hcop hg pool Ψ m f k slots₂ lists₂ a₂ w₂ hZ]
  simp only [star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,
    logPhase_add_frequency]
  ring

def normalizedColumnEnergy (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) : ℝ :=
  ∑ f ∈ labels, D f * ∑ k ∈ rows,
    ‖((Z^(-F/2) : ℝ) : ℂ) *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator f) k
        slots lists a W X‖^2

theorem columnEnergy_normalization
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X : ℝ) {Z : ℝ} (hZ : 0 < Z) (F : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X =
      Z^F * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D W X Z F := by
  have hr : Z^F * (Z^(-F/2))^2 = 1 := by
    rw [← Real.rpow_mul_natCast hZ.le, ← Real.rpow_add hZ]
    rw [show F+(-F/2)*(2:ℕ) = 0 by ring, Real.rpow_zero]
  unfold columnEnergy normalizedColumnEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f hf
  rw [← mul_assoc, mul_comm (Z^F) (D f), mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hZ _),mul_pow,← mul_assoc,hr,one_mul]

theorem initial_columnEnergy_clipping_normalized
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (w : ℝ → ℂ) {Z : ℝ} (hZ : 0 < Z) (N V h : ℝ) :
    columnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest w h) (Z^N) =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a
        labels rows D (clippedTest w (Z^(max 0 N-N)) h) (Z^(max 0 N)) Z (max 0 N+V) := by
  rw [columnEnergy_clipping p hp hcop hg pool Ψ m slots lists a labels rows D w hZ N h]
  exact columnEnergy_normalization p hp hcop hg pool Ψ m slots lists a labels rows D
    _ _ hZ _

end Arithmetic

def leftHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 4+z.1.1-z.1.2.2
def rightHeight (z : Frequency × (Fin 6 → ℝ)) : ℝ := z.2 5+z.1.2.1-z.1.2.2

theorem leftHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    leftHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 4 := by
  simp [leftHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

theorem rightHeight_eq (z : Frequency × (Fin 6 → ℝ)) :
    rightHeight z = profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2 5 := by
  simp [rightHeight,profileHeight,secondLeftSlope,secondRightSlope,secondKernelSlope]
  ring

def clippingPhase (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) : ℂ :=
  logPhase (leftHeight z+rightHeight z) (Real.log c)

theorem clippingPhase_norm (c : ℝ) (z : Frequency × (Fin 6 → ℝ)) :
    ‖clippingPhase c z‖ = 1 := logPhase_norm _ _

theorem clippingPhase_continuous (c : ℝ) : Continuous (clippingPhase c) := by
  unfold clippingPhase leftHeight rightHeight logPhase
  fun_prop

theorem fresh_pair_mode_clipping (w₁ w₂ : ℝ → ℂ)
    {Z q₁ q₂ : ℝ} (hZ : 0 < Z) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (N : ℝ) (y : Fin 6 → ℝ) (z : Frequency × (Fin 6 → ℝ))
    (hy₁ : y 4 = Real.log (q₁/Z^N)) (hy₂ : y 5 = Real.log (q₂/Z^N)) :
    (w₁ (q₁/Z^N)*star (w₂ (q₂/Z^N))) *
      pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y z.1 z.2 =
    secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
      clippingPhase (Z^(max 0 N-N)) z *
      (clippedTest w₁ (Z^(max 0 N-N)) (leftHeight z) (q₁/Z^(max 0 N)) *
      star (clippedTest w₂ (Z^(max 0 N-N)) (-rightHeight z) (q₂/Z^(max 0 N)))) := by
  rw [second_mode_split,← leftHeight_eq,← rightHeight_eq,hy₁,hy₂]
  have h1 := child_test_clipping w₁ hZ hq₁ N (leftHeight z)
  have h2 := child_test_clipping w₂ hZ hq₂ N (-rightHeight z)
  calc
    _ = secondOuterPhase
        (profileHeight secondLeftSlope secondRightSlope secondKernelSlope z.1 z.2) y *
        (childLogTest w₁ (leftHeight z) (q₁/Z^N) *
          star (childLogTest w₂ (-rightHeight z) (q₂/Z^N))) := by
      simp only [childLogTest,star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg]
      ring
    _ = _ := by
      rw [h1,h2]
      simp only [clippingPhase,star_mul,SecondPassIntegration.logPhase_conjugate,
        neg_neg,logPhase_add_frequency]
      ring

theorem child_height_moment_bound (K : ℕ) (z : Frequency × (Fin 6 → ℝ)) :
    (1+‖leftHeight z‖)^K * (1+‖rightHeight z‖)^K ≤
      tripleHeight (2*K) z.1 * coordinateHeight (2*K) z.2 := by
  have hh := InverseAmbientProfileTower.inherited_pair_weight_bound 4 5 0 K z
  simpa only [InverseAmbientProfileTower.ambientWeight,
    InverseAmbientProfileTower.inheritedLeft,InverseAmbientProfileTower.inheritedRight,
    leftHeight,rightHeight,norm_neg,pow_zero,Finset.prod_const_one,
    mul_one,one_mul,zero_add,tripleHeight,coordinateHeight] using hh

def outerCutoff (ψ : Fin 4 → ℝ → ℂ) (x : Fin 6 → ℝ) : ℂ :=
  ψ 0 (x 0)*ψ 1 (x 1)*ψ 2 (x 2)*ψ 3 (x 3)

def retainedCutoffs (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ) : Fin 6 → ℝ → ℂ :=
  ![ψ 0,ψ 1,ψ 2,ψ 3,w₁,w₂]

theorem retainedCutoffs_nonzero (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (x : Fin 6 → ℝ) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, retainedCutoffs ψ w₁ w₂ i (x i) ≠ 0 := by
  have h := mul_ne_zero_iff.mp ho
  have h' := mul_ne_zero_iff.mp h.1
  have h'' := mul_ne_zero_iff.mp h'.1
  intro i
  fin_cases i <;> simp only [retainedCutoffs]
  · exact h''.1
  · exact h''.2
  · exact h'.2
  · exact h.2
  · exact h₁
  · exact h₂

theorem larger_windows_one (ψ : Fin 4 → ℝ → ℂ) (w₁ w₂ : ℝ → ℂ)
    (Ω : Fin 6 → ℝ → ℂ)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    (x : Fin 6 → ℝ) (hx : ∀ i, 0 < x i) (ho : outerCutoff ψ x ≠ 0)
    (h₁ : w₁ (x 4) ≠ 0) (h₂ : w₂ (x 5) ≠ 0) :
    ∀ i, Ω i (Real.exp (Real.log (x i))) = 1 := by
  intro i
  rw [Real.exp_log (hx i)]
  exact hΩ i (x i) (retainedCutoffs_nonzero ψ w₁ w₂ x ho h₁ h₂ i)

theorem retained_physical_kernel_restore
    (W₁ W₂ w₁ w₂ : ℝ → ℂ) (Φ : 𝓢(ℝ, ℂ))
    (ψ : Fin 4 → ℝ → ℂ) (Ω : Fin 6 → ℝ → ℂ)
    (a b A₀ B₀ A₂ B₂ : ℝ) (hA₀ : 0 < A₀) (hA₂ : 0 < A₂)
    (hW₁ : Function.support W₁ ⊆ Set.Icc a b)
    (hW₂ : Function.support W₂ ⊆ Set.Icc a b)
    (hψ₀ : ∀ x, ψ 0 x ≠ 0 → x ∈ Set.Icc A₀ B₀)
    (hψ₂ : ∀ x, ψ 2 x ≠ 0 → x ∈ Set.Icc A₂ B₂)
    (hw₁ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₁ x = 1)
    (hw₂ : ∀ x ∈ Set.Icc (a/(B₀*B₂)) (b/(A₀*A₂)), w₂ x = 1)
    (hΩ : ∀ i x, retainedCutoffs ψ w₁ w₂ i x ≠ 0 → Ω i x = 1)
    {Z : ℝ} (hZ : 0 < Z) (D B v m θ H η : ℝ)
    (q : Fin 6 → ℝ) (hq : ∀ i, 0 < q i) :
    let x := InverseInitialProfile.relativeNorm q Z D B v θ H
    outerCutoff ψ x * InverseInitialProfile.physicalKernel W₁ W₂ Φ Z D m q =
      (Z^(InverseInitialProfile.prefactorCenter m D B θ+3*η) : ℝ) *
        outerCutoff ψ x * (w₁ (x 4)*w₂ (x 5)) *
        InverseInitialProfile.normalizedProfile W₁ W₂ Φ (fun i y => Ω i (Real.exp y))
          (Z^(InverseInitialProfile.radialCenter m H θ D B)) (η*Real.log Z)
          (InverseInitialProfile.relativeLog q Z D B v θ H) := by
  dsimp only
  let x := InverseInitialProfile.relativeNorm q Z D B v θ H
  have hx : ∀ i, 0 < x i := InverseInitialProfile.relativeNorm_pos q hq hZ D B v θ H
  by_cases ho : outerCutoff ψ x = 0
  · change outerCutoff ψ x * _ = _ * outerCutoff ψ x * _ * _
    simp only [ho,zero_mul,mul_zero]
  have hc : ψ 0 (x 0) ≠ 0 := ((mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).1 |> mul_ne_zero_iff.mp).1
  have hs : ψ 2 (x 2) ≠ 0 := (mul_ne_zero_iff.mp (mul_ne_zero_iff.mp ho).1).2
  have h1 : W₁ (x 0*x 2*x 4) ≠ 0 → w₁ (x 4) = 1 :=
    fresh_window_eq_one W₁ w₁ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 4)
      hW₁ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 4).le hw₁
  have h2 : W₂ (x 0*x 2*x 5) ≠ 0 → w₂ (x 5) = 1 :=
    fresh_window_eq_one W₂ w₂ a b A₀ B₀ A₂ B₂ (x 0) (x 2) (x 5)
      hW₂ hA₀ hA₂ (hψ₀ _ hc) (hψ₂ _ hs) (hx 5).le hw₂
  have hcut : w₁ (x 4) ≠ 0 → w₂ (x 5) ≠ 0 →
      ∀ i, Ω i (Real.exp (InverseInitialProfile.relativeLog q Z D B v θ H i)) = 1 := by
    intro hleft hright
    exact larger_windows_one ψ w₁ w₂ Ω hΩ x hx ho hleft hright
  have he := InverseInitialProfile.initial_kernel_restore W₁ W₂ w₁ w₂ Φ
    (fun i y => Ω i (Real.exp y)) hZ D B v m θ H η q hq h1 h2 hcut
  rw [he]
  ring

end SevenEighths.InverseInitialClippedColumns

end

end OAI
end OAIOriginalModule0608

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondNormalizedEnergy
Source SHA256: 4f4ab449662ea2821707fe9dbebc9cc60be14de3019a7a9c86c7d35a32b65db9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0609



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open JointLogSeparation IdealMobiusDivisorSum InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma child_ball_neg (R : ℝ) (k : Eis) :
    -k ∈ nonzeroChildFrequencyBall 1 R ↔ k ∈ nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,map_neg,norm_neg]

lemma child_ball_sum_neg {β : Type*} [AddCommMonoid β] (R : ℝ) (F : Eis → β) :
    ∑ k ∈ nonzeroChildFrequencyBall 1 R,F (-k) =
      ∑ k ∈ nonzeroChildFrequencyBall 1 R,F k := by
  apply Finset.sum_bij (fun k _ => -k)
  · intro k hk
    exact (child_ball_neg R k).mpr hk
  · intro a ha b hb he
    exact neg_injective he
  · intro b hb
    exact ⟨-b,(child_ball_neg R b).mpr hb,neg_neg b⟩
  · intro k hk
    rfl

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondLabelWeight (K : ℕ) (f : Ideal Eis) : ℝ := ((idealDivisors f).card : ℝ)^(9+4*K)

theorem second_left_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels rows (secondModeLeft p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K) ω hZ N V _

theorem second_right_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (R : ℝ) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (ω : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (clippedTest ω (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  have he : secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a ω (Z^N) t) γ =
      columnEnergy p hp hcop hg pool (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ)
        slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N) := by
    unfold secondLabelEnergy columnEnergy
    apply Finset.sum_congr rfl
    intro f hf
    simp only [secondLabelWeight,secondModeRight,secondCanonicalPolynomial]
    apply congrArg (fun a : ℝ => ((idealDivisors f).card : ℝ)^(9+4*K)*a)
    exact child_ball_sum_neg (β:=ℝ) R (fun k => ‖finiteCanonicalMarkedRow p hp hcop hg pool
      (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ) (primaryGenerator f) k
      slots lists a (childLogTest ω ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N)‖^2)
  rw [he]
  exact initial_columnEnergy_clipping_normalized p hp hcop hg pool (secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R)
    (secondLabelWeight K) ω hZ N V _

omit [DecidableEq σ] in
theorem normalized_child_energy_radical_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D W X Z F =
    normalizedColumnEnergy p hp hcop hg pool Ψ
      (ConcretePrimeRowBridge.idealGenerator (Ideal.span {m}).radical)
      slots lists a labels rows D W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_congr rfl
  intro f hf
  apply congrArg (fun x : ℝ => D f*x)
  apply Finset.sum_congr rfl
  intro k hk
  rw [finiteCanonicalMarkedRow_radical_puncture p hp hcop hg pool Ψ m (primaryGenerator f) k slots lists a W X]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0609

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOverlapInputFourier
Source SHA256: 68751f7d738215cf4c0387bc5ce65ffb0f77cf4d5ac5144b09c8960c6c62b3e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0610




namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialOverlapInputFourier
open InverseMoment InverseInitialOverlapFourier InverseInitialArithmetic InverseInitialRayAttachment
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_integral (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (H : Finset ι→ℝ→ℂ) (hH : ∀A∈F.powerset,Integrable (H A)) :
    inputConjugateRow p hg F Ψ j 1 1 (fun A=>∫t:ℝ,H A t) u =
      ∫t:ℝ,inputConjugateRow p hg F Ψ j 1 1 (fun A=>H A t) u := by
  rw [initial_input_row p hg]
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  have he (A:Finset ι) (t:ℝ) :
      supportMobius (fun i=>Ideal.span {p i}) A*
        (Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*H A t)*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)=
      (supportMobius (fun i=>Ideal.span {p i}) A*Ψ (∏i∈A,p i)*
        rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
        star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u))*H A t := by ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun A hA=>(hH A hA).const_mul _)]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro A hA
  ring

theorem original_overlap_input
    (hp : ∀i,p i≠0) (F : Finset ι) (Ψ : Eis→*ℂ) (j u : Eis)
    (W : ℝ→ℂ) (a₀ b₀ : ℝ) (ha₀ : 0<a₀)
    (hs : Function.support W⊆Set.Icc a₀ b₀) (hW : ContDiff ℝ ∞ W)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (y : σ→ι→ℝ) (hy : ∀i∈slots,∀q∈lists i,0<y i q)
    (wFresh : ℝ→ℂ) (Z D yj : ℝ) (hZ : 0<Z) (hj : 0<yj) :
    ((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
      (fun A=>wFresh (primeProductNorm p A/Z^D)*
        ∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) u =
      ∫t:ℝ,density (CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW) (Real.log yj) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p
            (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))))
            (childLogTest wFresh t) Z D) u) := by
  let g := CubicReflectionKernel.logSchwartz W a₀ b₀ ha₀ hs hW
  let H : Finset ι→ℝ→ℂ := fun A t=>density g (Real.log yj) t*
    (primeMark slots lists (fun i q=>a i q*logPhase (-t) (Real.log (y i q))) A*
      childLogTest wFresh t (primeProductNorm p A/Z^D))
  have hH (A:Finset ι) : Integrable (H A) := by
    have hi := (overlap_mode_integrable g slots lists a (fun i q=>Real.log (y i q))
      A (Real.log yj) (Real.log (primeProductNorm p A/Z^D))).const_mul
      (wFresh (primeProductNorm p A/Z^D))
    convert hi using 1
    funext t
    dsimp [H,childLogTest]
    ring
  have he (A:Finset ι) :
      wFresh (primeProductNorm p A/Z^D)*
        (∑q∈slots.pi lists,
          (∏i∈slots.attach,if q i.val i.property∈A then a i.val (q i.val i.property) else 0)*
          W (yj*(primeProductNorm p A/Z^D)/(∏i∈slots.attach,y i.val (q i.val i.property)))) =
      ∫t:ℝ,H A t := by
    rw [actual_overlap_separation W a₀ b₀ ha₀ hs hW slots lists a y hy A yj
      (primeProductNorm p A/Z^D) hj
      (div_pos (primeProductNorm_pos p hp A) (Real.rpow_pos_of_pos hZ D)),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    dsimp [H,childLogTest,g]
    ring
  simp_rw [he]
  rw [input_integral p hg F Ψ j u H (fun A _=>hH A),←integral_const_mul]
  apply integral_congr_ae
  filter_upwards with t
  dsimp only [H]
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum,initialTest]
  apply Finset.sum_congr rfl
  intro A hA
  ring

end SevenEighths.InverseInitialOverlapInputFourier

end

end OAI
end OAIOriginalModule0610

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOverlapEnergy
Source SHA256: 47a0b4f8f2d98822d59081c2d763c4315dedf739bc2e94a61d4ef7c40ca03b51
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0611



namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapEnergy
open InverseInitialOverlapFourier InverseMoment

theorem polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density g xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density g xj t*φ k t‖^2)≤C*E := by
  obtain ⟨C,hC,hint⟩ := density_moment g J
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro κ inst xj φ E hE hφ hbound
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density g xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density g xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density g xj t‖ := by
    rw [show b t=density g xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h]
      using (hint xj).1
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C := by
    simpa only [hbnorm,h]
      using (hint xj).2
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapEnergy

end

end OAI
end OAIOriginalModule0611

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialMarkedInputEnergy
Source SHA256: 963b1507663c7b0dddcbc3522d1409c129228c5822443a7e37e35e3af3b93ab5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0612


namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic
open FirstPassCubeLabels
namespace SevenEighths.InverseInitialMarkedInputEnergy
open InverseMoment InverseInitialOverlapFourier InverseInitialOverlapEnergy
open InverseInitialRayAttachment InverseInitialArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem marked_input_integrable (g:𝓢(ℝ,ℂ))(F:Finset ι)(Ψ:Eis→*ℂ)(j u:Eis)
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
    (wFresh:ℝ→ℂ)(Z D xj:ℝ) :
    Integrable (fun t:ℝ=>density g xj t*
      (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u)) := by
  simp_rw [initial_input_row p hg]
  unfold supportConjugateSum
  simp only [Finset.mul_sum]
  apply integrable_finsetSum
  intro A hA
  have hh := (overlap_mode_integrable g I L a y A xj
    (Real.log (primeProductNorm p A/Z^D))).const_mul
    (((Z^(-D/2):ℝ):ℂ)*supportMobius (fun i=>Ideal.span {p i}) A*
      Ψ (∏i∈A,p i)*rowCoprimeMask (fun i=>Ideal.span {p i}) A j*
      star (finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg A u)*
      wFresh (primeProductNorm p A/Z^D))
  convert hh using 1
  funext t
  unfold initialTest childLogTest
  ring

theorem marked_input_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(F:Finset ι)(Ψ:Eis→*ℂ)(j:Eis)(rows:Finset Eis)
      (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(y:σ→ι→ℝ)
      (wFresh:ℝ→ℂ)(Z D xj E:ℝ),0≤E→
      (∀t,(∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
        (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
          (childLogTest wFresh t) Z D) u‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑u∈rows,‖∫t:ℝ,density g xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
          (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
            (childLogTest wFresh t) Z D) u)‖^2)≤C*E := by
  obtain ⟨C,hC,htransfer⟩ := polynomial_measure_energy g J
  refine ⟨C,hC,?_⟩
  intro F Ψ j rows I L a y wFresh Z D xj E hE henergy
  let ψ : Eis→ℝ→ℂ := fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg F Ψ j 1 1
    (initialTest p (primeMark I L (fun i q=>a i q*logPhase (-t) (y i q)))
      (childLogTest wFresh t) Z D) u
  let φ : rows→ℝ→ℂ := fun u t=>ψ u.val t
  have hh := htransfer xj φ E hE
    (fun u=>marked_input_integrable p hg g F Ψ j u.val I L a y wFresh Z D xj)
    (fun t=>by
      exact (Finset.sum_coe_sort rows (fun u=>‖ψ u t‖^2)).le.trans (henergy t))
  exact (Finset.sum_coe_sort rows
    (fun u=>‖∫t:ℝ,density g xj t*ψ u t‖^2)).symm.le.trans hh

end SevenEighths.InverseInitialMarkedInputEnergy

end

end OAI
end OAIOriginalModule0612

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOverlapHeight
Source SHA256: bb71fe1932b6a02cb11923bedfea4b5313238438f369d48e164da1f286edfae2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0613




namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap FourierTransform
open MeasureTheory FourierBridge
namespace SevenEighths.InverseInitialOverlapHeight
open InverseInitialOverlapFourier InverseMoment JointLogSeparation

theorem twisted_polynomial_measure_energy (g:𝓢(ℝ,ℂ))(J:ℕ) :
    ∃C:ℝ,0≤C ∧ ∀(θ:ℝ),∀{κ:Type*}[Fintype κ](xj:ℝ)(φ:κ→ℝ→ℂ)(E:ℝ),
      0≤E→(∀k,Integrable (fun t=>density (frequencyTwist g θ) xj t*φ k t))→
      (∀t,(∑k,‖φ k t‖^2)≤E*((1+‖t‖)^J)^2)→
      (∑k,‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ k t‖^2)≤C*E*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)) := by
  obtain ⟨C,hC,hboundMoment⟩ := frequencyTwist_fourier_moment J g
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro θ κ inst xj φ E hE hφ hbound
  have hint:=AnalyticBridge.schwartz_fourier_one_plus_integrable (frequencyTwist g θ) J
  let h : ℝ→ℝ := fun t=>(1+‖t‖)^J
  have hp (t:ℝ) : 0<h t := by dsimp [h];positivity
  let b : ℝ→ℂ := fun t=>density (frequencyTwist g θ) xj t*(h t:ℂ)
  let f : κ→ℝ→ℂ := fun k t=>φ k t/(h t:ℂ)
  have he (k:κ)(t:ℝ) : b t*f k t=density (frequencyTwist g θ) xj t*φ k t := by
    dsimp [b,f]
    have hn : (h t:ℂ)≠0 := by exact_mod_cast (hp t).ne'
    field_simp
  have hbnorm (t:ℝ) : ‖b t‖=h t*‖density (frequencyTwist g θ) xj t‖ := by
    rw [show b t=density (frequencyTwist g θ) xj t*(h t:ℂ) from rfl,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),mul_comm]
  have hb : Integrable (fun t=>‖b t‖) := by
    simpa only [hbnorm,h,density_norm]
      using hint
  have hf : ∀k,Integrable (fun t=>b t*f k t) := by
    intro k
    simpa only [he] using hφ k
  have henergy (t:ℝ) : (∑k,‖f k t‖^2)≤E := by
    simp only [f,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hp t),div_pow,←Finset.sum_div]
    apply (div_le_iff₀ (sq_pos_of_pos (hp t))).mpr
    exact hbound t
  have hbint : (∫t:ℝ,‖b t‖)≤C*(1+‖θ‖)^(J+(volume:Measure ℝ).integrablePower) := by
    simpa only [hbnorm,h,density_norm]
      using hboundMoment θ
  have hb0 : 0≤∫t:ℝ,‖b t‖ := integral_nonneg fun _=>norm_nonneg _
  have hh := common_measure_energy volume b f E hE hb hf henergy
  simp only [he] at hh
  exact hh.trans (by
    simpa only [mul_pow,←pow_mul,Nat.mul_comm,mul_assoc,mul_left_comm,mul_comm] using
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hb0 hbint 2) hE)

end SevenEighths.InverseInitialOverlapHeight

end

end OAI
end OAIOriginalModule0613

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialPhysicalMeasure
Source SHA256: f8c30dfe6e3c01cb7c26f0cae5b1c0016e57abe0f3e12765bf12c81c251bb009
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0614



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseInitialPhysicalMeasure
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open FirstPassCubeLabels FirstCauchyArithmetic SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialRayAttachment
open InverseInitialKernelBridge InverseInitialProfile InverseInitialClippedColumns
open MeasureTheory FourierBridge JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Point (ι : Type*) where
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  left : Finset ι
  right : Finset ι
  frequency : O

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,goodLambda∉Ideal.span {p i})

def divisor (x : Point ι) : O := primeSubsetGenerator (fun i=>Ideal.span {p i}) x.divisor

def quotient (x : Point ι) : O := primaryGenerator (sourceIdeal p (x.common\x.divisor))

def coordinates (x : Point ι) : Fin 6 → ℝ :=
  physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor)
    (sourceIdeal p x.overlap) (sourceIdeal p x.left) (sourceIdeal p x.right) x.frequency

structure Valid (x : Point ι) : Prop where
  divisor_subset : x.divisor⊆x.common
  overlap_left : Disjoint x.overlap x.left
  overlap_right : Disjoint x.overlap x.right
  frequency_nonzero : x.frequency≠0

include hp in
omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem coordinates_pos (x : Point ι) (hx : Valid x) : ∀ i,0<coordinates p x i :=
  physicalCoordinates_pos _ _ _ _ _ _ (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _) hx.frequency_nonzero

omit [DecidableEq ι] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem divisor_span (x : Point ι) : Ideal.span {divisor p x}=sourceIdeal p x.divisor := by
  simpa only [divisor,sourceIdeal,FiniteGaussPhase.span_finset_prod] using
    pairDivisor_span (fun i=>Ideal.span {p i}) x.divisor

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem quotient_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    Ideal.span {quotient p x}=sourceIdeal p (x.common\x.divisor) := by
  rw [quotient,sourceIdeal_gen p hp hpr]
  rfl

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem common_span (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) (hx : Valid x) :
    Ideal.span {divisor p x*quotient p x}=sourceIdeal p x.common := by
  rw [←Ideal.span_singleton_mul_span_singleton,divisor_span p,quotient_span p hp hpr,
    ←sourceIdeal_union p _ _ (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
    Finset.union_sdiff_of_subset hx.divisor_subset]

include hp in
def unitSector (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) : Oˣ :=
  Classical.choose (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

include hp in
omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem unitSector_spec (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι) :
    divisor p x=(unitSector p hp hpr x:O)*primaryGenerator (sourceIdeal p x.divisor) :=
  Classical.choose_spec (generator_eq_unit_primary (sourceIdeal p x.divisor) (divisor p x)
    (divisor_span p x) (by rw [sourceIdeal_gen p hp hpr]; exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))

theorem child_normalized (hpr : ∀ i,goodLambda^2∣p i-1) (x : Point ι)
    (Ψ : O →* ℂ) (j h : O) (H : Finset ι→ℂ) (N : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (divisor p x*∏ i∈x.overlap,p i) (divisor p x*h) H N =
    secondChildColumn p hp hcop hg Ψ (j*quotient p x)
      (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
      (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h)) H N := by
  obtain ⟨u,hu,he⟩ := initial_poisson_child_normalized p hp hcop hg hpr
    x.common x.divisor x.overlap Ψ j (divisor p x) (quotient p x) h
    (divisor_span p x) (quotient_span p hp hpr x)
  have hgen : primaryGenerator (sourceIdeal p x.divisor)≠0 := by
    rw [sourceIdeal_gen p hp hpr];exact Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hu' : u=unitSector p hp hpr x := Units.val_injective
    (mul_right_cancel₀ hgen (hu.symm.trans (unitSector_spec p hp hpr x)))
  simpa only [hu',quotient] using he H N

include hp hcop hg in
theorem column_extraction (hpr : ∀ i,goodLambda^2∣p i-1)
    (x : Point ι) (hx : Valid x) (Ψ : O →* ℂ) (j h : O)
    (σ : Finset ι→ℂ) (N : Finset ι) (hN : Disjoint x.overlap N) :
    initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h
      (fun A=>σ (x.common∪A)) (x.overlap∪N) =
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h (fun _=>1) x.overlap *
      secondChildColumn p hp hcop hg Ψ (j*quotient p x)
        (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
        (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
        (fun A=>σ (x.common∪(x.overlap∪A))) N := by
  have hm (A : Finset ι) :
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*∏ i∈x.common,p i)=
      rowCoprimeMask (fun i=>Ideal.span {p i}) A (j*(divisor p x*quotient p x)) :=
    rowCoprimeMask_mul_eq_of_span_eq _ A j (common_span p hp hpr x hx).symm
  have hc (H : Finset ι→ℂ) (A : Finset ι) :
      initialColumn p hp hcop hg Ψ j (∏ i∈x.common,p i) (divisor p x) h H A =
      initialColumn p hp hcop hg Ψ j (divisor p x*quotient p x) (divisor p x) h H A := by
    simp only [initialColumn,hm]
  rw [hc,initial_common_extraction p hp hcop hg hpr Ψ j (quotient p x) (divisor p x) h _ _ _ hN,
    ←hc,child_normalized p hp hcop hg hpr]

def outerCoefficient (Ψ : O →* ℂ) (j : O) (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ *
    star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) x.frequency (fun _=>1) x.overlap) *
    initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
      (divisor p x) (-x.frequency) (fun _=>1) x.overlap

def canonicalColumn (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ) (x : Point ι) (h : O)
    (H : Finset ι→ℂ) (N : Finset ι) : ℂ :=
  secondChildColumn p hp hcop hg Ψ (j*quotient p x)
    (primaryGenerator (sourceIdeal p x.divisor*sourceIdeal p x.overlap))
    (primaryGenerator (sourceIdeal p x.divisor)*((unitSector p hp hpr x:O)^5*h))
    (fun A=>σ (x.common∪(x.overlap∪A))*H A) N

def physicalTerm (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (ρ : SecondRayIndex) : ℂ :=
  (initialBeta p Ψ j x.common * (UniqueFactorizationMonoid.moebius (sourceIdeal p x.divisor):ℂ) *
    supportMobius (fun i=>Ideal.span {p i}) x.overlap * secondRayCoefficient ρ) *
  star (initialColumn p hp hcop hg (secondRayMinus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) x.frequency (fun A=>σ (x.common∪A)) (x.overlap∪x.left)) *
  initialColumn p hp hcop hg (secondRayPlus Ψ ρ) j (∏ i∈x.common,p i)
    (divisor p x) (-x.frequency) (fun A=>σ (x.common∪A)) (x.overlap∪x.right) *
  physicalKernel W₁ W₂ Φ Z D m
    (physicalCoordinates (sourceIdeal p x.common) (sourceIdeal p x.divisor) 1
      (sourceIdeal p (x.overlap∪x.left)) (sourceIdeal p (x.overlap∪x.right)) x.frequency)

include hp hcop hg in
theorem physicalTerm_extracted (hpr : ∀ i,goodLambda^2∣p i-1)
    (Ψ : O →* ℂ) (j : O) (σ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m : ℝ)
    (x : Point ι) (hx : Valid x) (ρ : SecondRayIndex) :
    physicalTerm p hp hcop hg Ψ j σ W₁ W₂ Φ Z D m x ρ =
      outerCoefficient p hp hcop hg Ψ j x ρ *
      star (canonicalColumn p hp hcop hg hpr (secondRayMinus Ψ ρ) j σ x x.frequency (fun _=>1) x.left) *
      canonicalColumn p hp hcop hg hpr (secondRayPlus Ψ ρ) j σ x (-x.frequency) (fun _=>1) x.right *
      physicalKernel W₁ W₂ Φ Z D m (coordinates p x) := by
  unfold physicalTerm
  rw [column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_left,
    column_extraction p hp hcop hg hpr x hx _ _ _ σ _ hx.overlap_right,
    sourceIdeal_union p _ _ hx.overlap_left,sourceIdeal_union p _ _ hx.overlap_right,
