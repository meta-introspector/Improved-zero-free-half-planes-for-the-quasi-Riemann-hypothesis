
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
    (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hne : (fixedSlotTupleSet L F).Nonempty)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (hL : Pairwise (fun i j => Disjoint (L i) (L j))) (hprime : ∀ i,∀ P∈L i,Prime P)
    (D : ∀ P : (fixedSlotTupleSet L F).image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (G.reflected K hK (fixedTupleFamily L F hne hmax hgood P.val)).generator N a c mode)
    (p : supportedSlotChoices L F K)

def activeChoiceControlled :
      ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  castControlled (congrArg (fun S => (G.reflected K hK S).generator)
    (fixedTupleFamily_at_choice L F hne hmax hgood hL hprime p.val p.property.2))
    (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1)

lemma activeChoiceControlled_value
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
      (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨∏ i,(p.val i).val,Finset.mem_image.mpr
      ⟨fun i => (p.val i).val,(mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩,rfl⟩⟩ p.property.1) s
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_ne_zero hc
      (G.reflected K hK (fixedTupleFamily L F hne hmax hgood (∏ i,(p.val i).val))).generator_good
      (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) W X := by
  exact mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

theorem literalWholeRow_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : τ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (w : ∀ i,L i→ℂ) :
    literalWholeRow G K hK (fixedTupleFamily L F hne hmax hgood) j
      ((fixedSlotTupleSet L F).image slotTupleProduct) D s hc W θ X r
      (slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w))=
    ∑ p : supportedSlotChoices L F K,r K*(∏ i,w i (p.val i))*
      mixedReflectedValue (activeChoiceControlled G K hK L F hne hmax hgood hL hprime D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent j) (slotIndices τ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X := by
  let e := supportedSlotProductEquiv L F hL hprime K
  unfold literalWholeRow
  rw [←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  rw [activeChoiceControlled_value G K hK L F hne hmax hgood hL hprime D p s hc j]
  have hcft : slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (e p).val.val=∏ i,w i (p.val i) := by
    change slotProductCoefficient (fixedSlotTupleSet L F) (fixedTupleCoefficient L w)
      (slotTupleProduct (fun i => (p.val i).val))=_
    rw [slotProductCoefficient_at_product (fixedSlotTupleSet L F)
      (fixedSlotTupleSet_product_injective L F hL hprime) (fixedTupleCoefficient L w)
      (fun i => (p.val i).val) ((mem_fixedSlotTupleSet L F _).mpr ⟨fun i => (p.val i).property,p.property.2⟩)]
    exact fixedTupleCoefficient_at L w p.val
  rw [hcft]
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1110

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.GlobalEnergy
Source SHA256: 1d521dd84eba041efc02d2c193ef601912c317853e7f5b8855217d34ee61b316
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1111


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

lemma fullRaySector_subset (N : Eis) (rows : Finset (Ideal Eis)) (r : Eis⧸Ideal.span {N^2}) :
    fullRaySector N rows r⊆rows := Finset.filter_subset _ _

theorem literal_global_sector_energy [Fintype (Eis⧸Ideal.span {N^2})]
    (F : PrimeFamily φ) (rows Pset : Finset (Ideal Eis))
    (S : Ideal Eis→PrimeFamily σ) (hrows : ∀ K∈rows,Admissible K) (jF : φ→ℕ)
    (D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (F.reflected K.val (hrows K.val K.property) (S P.val)).generator N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (W : ℝ→ℂ) (θ X : ℝ) (r aw : Ideal Eis→ℂ) (B : ℝ)
    (hsector : ∀ r₀ p₀ : Eis⧸Ideal.span {N^2},
      ∃ E : SectorArithmetic (N:=N) F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
        (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) s hc,
        (∀ (K : fullRaySector N rows r₀) (P : fullRaySector N Pset p₀) hp,
          E.completion K P hp=D ⟨K.val,(fullRaySector_subset N rows r₀ K.property)⟩
            ⟨P.val,(fullRaySector_subset N Pset p₀ P.property)⟩ hp) ∧
        (∑ K : fullRaySector N rows r₀,‖literalWholeRow F K.val
          (hrows K.val (fullRaySector_subset N rows r₀ K.property)) S jF (fullRaySector N Pset p₀)
          (E.completion K) s hc W θ X r aw‖^2)≤B) :
    (∑ K : rows,‖literalWholeRow F K.val (hrows K.val K.property) S jF Pset
      (D K) s hc W θ X r aw‖^2)≤(Fintype.card (Eis⧸Ideal.span {N^2}):ℝ)^3*B := by
  let f := literalPairEntry F rows Pset S hrows jF D s hc W θ X r aw
  have hs (r₀ p₀ : Eis⧸Ideal.span {N^2}) :
      (∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,f K P‖^2)≤B := by
    obtain ⟨E,hE,hbound⟩ := hsector r₀ p₀
    have he : (∑ K : fullRaySector N rows r₀,‖literalWholeRow F K.val
          (hrows K.val (fullRaySector_subset N rows r₀ K.property)) S jF (fullRaySector N Pset p₀)
          (E.completion K) s hc W θ X r aw‖^2)=
        ∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,f K P‖^2 := by
      let fl := literalPairEntry F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
        (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) jF E.completion s hc W θ X r aw
      calc
        _ = ∑ K : fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,fl K.val P‖^2 := by
          apply Finset.sum_congr rfl
          intro K hK
          apply congrArg (fun z : ℂ => ‖z‖^2)
          exact literalWholeRow_eq_pairs F (fullRaySector N rows r₀) (fullRaySector N Pset p₀) S
            (fun K hK => hrows K (fullRaySector_subset N rows r₀ hK)) jF E.completion s hc W θ X r aw K
        _ = ∑ K∈fullRaySector N rows r₀,‖∑ P∈fullRaySector N Pset p₀,fl K P‖^2 :=
          Finset.sum_coe_sort _ (fun K => ‖∑ P∈fullRaySector N Pset p₀,fl K P‖^2)
        _ = _ := by
          apply Finset.sum_congr rfl
          intro K hK
          apply congrArg (fun z : ℂ => ‖z‖^2)
          apply Finset.sum_congr rfl
          intro P hP
          exact literalPairEntry_restrict F rows Pset (fullRaySector N rows r₀) (fullRaySector N Pset p₀)
            (fullRaySector_subset N rows r₀) (fullRaySector_subset N Pset p₀) S hrows jF D s hc E hE W θ X r aw K P hK hP
    rw [←he]
    exact hbound
  have hh := full_ray_sector_energy N rows Pset f B hs
  have he : (∑ K : rows,‖literalWholeRow F K.val (hrows K.val K.property) S jF Pset
      (D K) s hc W θ X r aw‖^2)=∑ K∈rows,‖∑ P∈Pset,f K P‖^2 := by
    calc
      _ = ∑ K : rows,‖∑ P∈Pset,f K.val P‖^2 := by
        apply Finset.sum_congr rfl
        intro K hK
        exact congrArg (fun z : ℂ => ‖z‖^2) (literalWholeRow_eq_pairs F rows Pset S hrows jF D s hc W θ X r aw K)
      _ = _ := Finset.sum_coe_sort rows (fun K => ‖∑ P∈Pset,f K P‖^2)
  rw [he]
  exact hh
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1111

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.MarkedTuples
Source SHA256: 7c9638130c35c55264bdad6d8bbdb80c6c28c132d704bbf83df8141605606327
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1112




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
lemma sum_subtype_dite_decidable {α : Type*} [Fintype α] (p : α→Prop) [DecidablePred p]
    (f : ∀ x,p x→ℂ) :
    (∑ x : {x // p x},f x.val x.property)=∑ x,if h:p x then f x h else 0 := by
  have hh := Fintype.sum_subtype_add_sum_subtype p (fun x => if h:p x then f x h else 0)
  have hz : (∑ x : {x // ¬p x},if h:p x.val then f x.val h else 0)=0 := by
    apply Finset.sum_eq_zero
    intro x hx
    exact dite_eq_right x.property
  rw [hz,add_zero] at hh
  simpa only [Subtype.property,dite_eq_left] using hh

variable {σ : Type*} [Fintype σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable {α : Type*} [Fintype α] (Sp : α→PrimeFamily σ)
local notation "E" => D.primeFiberEquiv R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
local notation "K" => rowResidualPart I (Ideal.span (Set.singleton m)*F)
local notation "hK" => rowResidualPart_admissible I (Ideal.span (Set.singleton m)*F) hbad

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_tuple_reflection
    (hS : ∀ p,Pairwise (Function.onFun IsCoprime (Sp p).ideal))
    (hSodd : ∀ p i,ringChar (Eis⧸(Sp p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (Sp p) Q).ideal i))
    (C : ∀ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : α→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : α,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),∑ T : Finset σ,
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ p : {p : α // ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val},
          (∏ t∈(Finset.univ:Finset σ)\T,(Ideal.absNorm ((Sp p.val).ideal t):ℂ)⁻¹)*w p.val*
          mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected K hK ((Sp p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex K) T) W X := by
  let good := fun p : α => ∀ P : FreePrimeIndex D.movingIdeal (Q*Ideal.span {(72:Eis)}),∀ i,(Sp p).ideal i≠P.val.val
  let row := fun p : α => markedCompletedT (rowTwist Ψ m f z) W X
    (fun A => ∏ i,if (Sp p).ideal i∣A then (1:ℂ) else 0)
  have hzrow (p : α) (hp : ¬good p) : row p=0 := by
    simp only [good,not_forall,not_not] at hp
    obtain ⟨P,i,he⟩ := hp
    exact actual_marked_row_overlap_zero D (Sp p) Ψ Q hmLam hm2 P i he W X
  have hrestrict : (∑ p : α,w p*row p)=∑ p : {p // good p},w p.val*row p.val := by
    calc
      _ = ∑ p : α,if h:good p then w p*row p else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        by_cases hg : good p
        · rw [dite_eq_left hg]
        · rw [dite_eq_right hg,hzrow p hg,mul_zero]
      _ = _ := (sum_subtype_dite_decidable good (fun p _ => w p*row p)).symm
  change (∑ p : α,w p*row p)=_
  rw [hrestrict]
  have he (p : {p // good p}) := actual_marked_selected_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (Sp p.val) (hS p.val) (hSodd p.val) p.property Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ G N hN
    (hNp p.val) (C p) W hWcompact lo hi hlo hsupp hW X hX
  dsimp only [row]
  simp_rw [he]
  simp only [Finset.mul_sum,frozenInactiveWeight]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h hh
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro p hp
  ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1112

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.InactiveSource
Source SHA256: c6b2582c6276aa824c3a70762dcb7cd7e8a11cf2d826e72f90ca104e0d03e693
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1113



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ : Type*} [Fintype σ] [DecidableEq σ]

lemma supported_inactive_sum_eq (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis)
    (K : rows) (w : ∀ i,L i→ℂ)
    (f : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ) :
    (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f b)=
    ∑ b : ∀ i : {i // i∉T},L i.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
        (if hk:K.val∈inactiveRowSet rows L T F b then f ⟨b,(Finset.mem_filter.mp hk).2⟩ else 0) := by
  let ok := fun b : ∀ i : {i // i∉T},L i.val =>
    IsCoprime K.val (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠F j
  let wt := fun b : ∀ i : {i // i∉T},L i.val =>
    (∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i))
  have he := sum_subtype_dite_decidable ok (fun b hb => wt b*f ⟨b,hb⟩)
  change (∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,wt b.val*f b)=_
  calc
    _ = ∑ b,if hb:ok b then wt b*f ⟨b,hb⟩ else 0 := he
    _ = _ := by
      apply Finset.sum_congr rfl
      intro b hb
      by_cases hc : ok b
      · have hk : K.val∈inactiveRowSet rows L T F b := Finset.mem_filter.mpr ⟨K.property,hc⟩
        simp only [dite_eq_left hc,dite_eq_left hk,wt]
      · have hk : K.val∉inactiveRowSet rows L T F b := fun h => hc (Finset.mem_filter.mp h).2
        simp only [dite_eq_right hc,dite_eq_right hk,mul_zero]

theorem supported_inactive_source_energy (rows : Finset (Ideal Eis))
    (L : σ→Finset (Ideal Eis)) (T : Finset σ) (F : φ→Ideal Eis) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (w : ∀ i,L i→ℂ) (hw : ∀ i P,‖w i P‖≤1)
    (f : ∀ K : rows,supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val→ℂ)
    (E : ℝ) (hE : 0≤E)
    (hf : ∀ b : ∀ i : {i // i∉T},L i.val,
      (∑ K : inactiveRowSet rows L T F b,
        ‖f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩‖^2)≤E) :
    (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)≤
    (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*E := by
  let g := fun (b : ∀ i : {i // i∉T},L i.val) (K : inactiveRowSet rows L T F b) =>
    f ⟨K.val,(Finset.mem_filter.mp K.property).1⟩ ⟨b,(Finset.mem_filter.mp K.property).2⟩
  have he := original_inactive_restricted_energy rows L T F H hzero hH w hw g E hE hf
  have hh : (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val) F K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*f K b‖^2)=
      ∑ K∈rows,‖∑ b : ∀ i : {i // i∉T},L i.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b i)))*
          (if hk:K∈inactiveRowSet rows L T F b then g b ⟨K,hk⟩ else 0)‖^2 := by
    rw [←Finset.sum_coe_sort rows]
    apply Finset.sum_congr rfl
    intro K hK
    rw [supported_inactive_sum_eq rows L T F K w (f K)]
  exact hh.trans_le he
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1113

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalSplitReflection
Source SHA256: f2f5ab334fc503bc8c3475301fa11a6af32536a31edfedab510f673be0b8bf8c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1114



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

theorem actual_marked_slot_split_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L,
      ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    let physical := fun (h : Eis⧸Ideal.span {c})
      (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})))
      (T : Finset σ) (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L) =>
      mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*physical h A T
                  ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a)) := by
  dsimp only
  rw [actual_marked_tuple_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    (fun p : ∀ i,L i => slotChoiceFamily L hmax hgood p) hS hSodd Ψ hΨnorm hQ hΨperiod hmLam hm2
    c hc hcQ G N hN hNp C (fun p => ∏ i,w i (p i)) W hWcompact lo hi hlo hsupp hW X hX]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  congr 1
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  have hs :=
    (original_supported_slot_sum D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask
      L hmax hgood T w (fun p => mixedReflectedValue (C p h A T) (G h).shape
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_ne_zero
            (G h).denominator_ne_zero
            (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad) ((slotChoiceFamily L hmax hgood p.val).restrict T)).generator_good
            (reflectedExponent (fun b : A => completedLocalExponent R F b.val.val))
            (slotIndices A (PrimeIndex (rowResidualPart I (Ideal.span {m}*F))) T) W X))
  convert hs using 1
  apply Finset.sum_congr rfl
  intro p hp
  congr 1
  congr 1
  apply Finset.prod_congr (by ext; simp only [Finset.mem_sdiff,Finset.mem_univ])
  intro t ht
  rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1114

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalActiveReflection
Source SHA256: 83f88188c824395ae882fa5147b29c93af9e6c1e035051d4bbef08880fa37d3a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1115



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ] {m f z : Eis} (D : GoodMaskRowData m f z)
variable (R I F Q : Ideal Eis) (hR : R≠0) (hI : I≠0) (hF : Squarefree F)
    (hm : m≠0) (hf : Ideal.span {f}=F) (hz : Ideal.span {z}=I)
    (hbad : ∀ P∈fixedBadPrimes, P∣Ideal.span {m}*F)
    (hcop : IsCoprime (Q*Ideal.span {(72:Eis)}) (rowResidualPart I (Ideal.span {m}*F)))
    (hpow : rowPowerfulPart R=rowPowerfulPart I)
    (hmask : rowMaskPart R (Ideal.span {m}*F)=rowMaskPart I (Ideal.span {m}*F))
variable (L : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

include hR hI hF hm hf hz hbad hcop hpow hmask

theorem actual_marked_active_reflection
    (hS : ∀ p : ∀ i,L i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily L hmax hgood p).ideal))
    (hSodd : ∀ p : ∀ i,L i,∀ i,ringChar (Eis⧸(slotChoiceFamily L hmax hgood p).ideal i)≠2)
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hQ : Q≠0)
    (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (c : Eis) (hc : c≠0) [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}≤Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (N : Eis) (hN : ∀ h,(9:Eis)*(G h).c0∣N)
    (hNp : ∀ p : ∀ i,L i,∀ i,IsCoprime (Ideal.span {N}) ((markedRowFamily D (slotChoiceFamily L hmax hgood p) Q).ideal i))
    (C : ∀ h : Eis⧸Ideal.span {c},
      ∀ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
      ∀ T : Finset σ,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ∀ p : supportedSlotChoices (fun i : T => L i.val)
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal) (rowResidualPart I (Ideal.span {m}*F)),
      ControlledStratumArithmetic
        (((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A).reflected
          (rowResidualPart I (Ideal.span {m}*F)) (rowResidualPart_admissible I (Ideal.span {m}*F) hbad)
          (slotChoiceFamily (fun i : T => L i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
        N (G h).a0 (G h).c0 (G h).mode)
    (w : ∀ i,L i→ℂ) (W : ℝ→ℂ) (hWcompact : HasCompactSupport W)
    (lo hi : ℝ) (hlo : 0<lo) (hsupp : Function.support W⊆Set.Icc lo hi)
    (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X) :
    (∑ p : ∀ i,L i,(∏ i,w i (p i))*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (slotChoiceFamily L hmax hgood p).ideal i∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*
      ∑ A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
        frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
        ∑ T : Finset σ,
          ∑ b : supportedSlotChoices (fun i : {i // i∉T} => L i.val)
            ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
            (rowResidualPart I (Ideal.span {m}*F)),
            ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
              ∑ a : supportedSlotChoices (fun i : T => L i.val)
                ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal)
                (rowResidualPart I (Ideal.span {m}*F)),
                (∏ i : T,w i.val (a.val i))*
                  originalSplitPhysical R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
                    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
                    T (C h A T) (G h).shape (G h).denominator_ne_zero
                    (fun b : A => completedLocalExponent R F b.val.val) W X (b,a) := by
  let Call := fun (p : originalSlotChoices D (Q*Ideal.span {(72:Eis)}) L)
    (h : Eis⧸Ideal.span {c})
    (A : Finset (FreeReflection.pool R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}))) (T : Finset σ) =>
      originalSplitControlled D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
        ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T) p
  rw [actual_marked_slot_split_reflection D R I F Q hR hI hF hm hf hz hbad hcop hpow hmask
    L hmax hgood hS hSodd Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ G N hN hNp Call
    w W hWcompact lo hi hlo hsupp hW X hX]
  dsimp only
  apply congrArg (fun z : ℂ => thetaDerivativeScalar⁻¹*z)
  apply Finset.sum_congr rfl
  intro h hh
  apply congrArg (fun z : ℂ => fixedThetaRowCoeff c hc (D.fixedFactor Ψ Q) h*z)
  apply Finset.sum_congr rfl
  intro A hA
  apply congrArg (fun z : ℂ => frozenInactiveWeight R F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*z)
  apply Finset.sum_congr rfl
  intro T hT
  apply Finset.sum_congr rfl
  intro b hb
  apply congrArg (fun z : ℂ =>
    ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*z)
  apply Finset.sum_congr rfl
  intro a ha
  apply congrArg (fun z : ℂ => (∏ i : T,w i.val (a.val i))*z)
  dsimp only [Call]
  have hv := originalSplitControlled_physical D R I F (Q*Ideal.span {(72:Eis)})
    hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood
    ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).symm (b,a))
    (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X
  exact hv.trans (congrArg
    (originalSplitPhysical R I F (Q*Ideal.span {(72:Eis)}) hbad L hmax hgood
      ((poolPrimeFamily R (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A) T (C h A T)
      (G h).shape (G h).denominator_ne_zero (fun b : A => completedLocalExponent R F b.val.val) W X)
    ((originalSlotSplit D R I F (Q*Ideal.span {(72:Eis)}) hR hI hF hm hf hz hbad hcop hpow hmask L hmax hgood T).apply_symm_apply (b,a)))

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1115

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.PunctureAbsorption
Source SHA256: afaaafa52eed40a8409baa65b591ad57ff74a3d0c9b6ab531b66128811ebcab6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1116


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem rowTwist_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0) :
    rowTwist Ψ (m*B) f z=rowTwist Ψ m f z := by
  ext n
  by_cases hn : Supported (Ideal.span {n})
  · rw [rowTwist_extract_sixth_mask Ψ (m*B) f z n hn,rowTwist_extract_sixth_mask Ψ m f z n hn]
    by_cases hb : IsCoprime B n
    · change Ψ n*(if IsCoprime (m*B) n then (1:ℂ) else 0)*_=
        Ψ n*(if IsCoprime m n then (1:ℂ) else 0)*_
      simp only [IsCoprime.mul_left_iff,hb,and_true]
    · rw [hΨzero n hb]
      simp only [zero_mul]
  · rw [rowTwist_zero_of_not_supported Ψ (m*B) f z n
        (dvd_mul_of_dvd_left hmLam B) (dvd_mul_of_dvd_left hm2 B) hn,
      rowTwist_zero_of_not_supported Ψ m f z n hmLam hm2 hn]

lemma markedCompletedT_absorb_puncture (Ψ : Eis→*ℂ) (m B f z : Eis)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (hΨzero : ∀ n,¬IsCoprime B n → Ψ n=0)
    (W : ℝ→ℂ) (X : ℝ) (mark : Ideal Eis→ℂ) :
    markedCompletedT (rowTwist Ψ (m*B) f z) W X mark=
      markedCompletedT (rowTwist Ψ m f z) W X mark := by
  rw [rowTwist_absorb_puncture Ψ m B f z hmLam hm2 hΨzero]

lemma rowResidualPart_coprime_period (I F Q : Ideal Eis) (m : Eis)
    (hQ : Q∣Ideal.span {m}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m}*F)) := by
  exact (squarefreeResidualPart_coprime (rowSimplePart I) (Ideal.span {m}*F)).symm.of_isCoprime_of_dvd_left
    (dvd_mul_of_dvd_left hQ F)

lemma rowResidualPart_coprime_enlarged_period (I F Q : Ideal Eis) (m B : Eis)
    (hQ : Q∣Ideal.span {B}) :
    IsCoprime Q (rowResidualPart I (Ideal.span {m*B}*F)) := by
  apply rowResidualPart_coprime_period I F Q (m*B)
  rw [←Ideal.span_singleton_mul_span_singleton]
  exact dvd_mul_of_dvd_right hQ _

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1116

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.PuncturedMarks
Source SHA256: 23864d5cb76ed076dff385473ec44764e69c0f90297232a6863cef6627290afd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1117


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma markedCompletedT_zero_punctured (Ψ : Eis→*ℂ) (m f z : Eis)
    (P : Ideal Eis) (hP : Prime P) (hm : m∈P)
    (W : ℝ→ℂ) (X : ℝ) (d : Ideal Eis→ℂ) (hd : ∀ A,¬P∣A → d A=0) :
    markedCompletedT (rowTwist Ψ m f z) W X d=0 := by
  have hz (I J : Ideal Eis) : summand (rowTwist Ψ m f z) W X I J*d (I*J^3)=0 := by
    by_cases hdiv : P∣I*J^3
    · rcases hP.dvd_mul.mp hdiv with hI|hJ
      · have hz := CanonicalRowCompletion.columnWeight_zero_of_mask Ψ m f z hP hI hm
        simp only [summand,hz,zero_div,zero_mul]
      · have hz := cubeWeight_zero_of_prime_mask Ψ m f z hP (hP.dvd_of_dvd_pow hJ) hm
        simp only [summand,hz,mul_zero,zero_mul]
    · rw [hd _ hdiv,mul_zero]
  simp only [markedCompletedT,hz,tsum_zero]

lemma markedCompletedT_zero_punctured_slot {σ : Type*} [Fintype σ]
    (S : PrimeFamily σ) (i : σ) (Ψ : Eis→*ℂ) (m f z : Eis) (hm : m∈S.ideal i)
    (W : ℝ→ℂ) (X : ℝ) :
    markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ j,if S.ideal j∣A then (1:ℂ) else 0)=0 := by
  apply markedCompletedT_zero_punctured Ψ m f z (S.ideal i)
    (Ideal.prime_of_isPrime (NeZero.ne (S.ideal i)) inferInstance) hm W X
  intro A hA
  exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1117

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalRetainedSlots
Source SHA256: c7d632dfe389b8a393596ffdc1d4d73f7d9a653a33770c3aa7507a26938cd2ee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1118



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {α σ : Type*} [Fintype σ]

def punctureRetainedTuples (tuples : Finset α) (S : α→PrimeFamily σ) (m : Eis) : Finset α :=
  tuples.filter (fun p => ∀ i,m∉(S p).ideal i)

theorem original_tuple_filter_puncture (tuples : Finset α) (S : α→PrimeFamily σ)
    (w : α→ℂ) (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) :
    (∑ p∈tuples,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0))=
    ∑ p∈punctureRetainedTuples tuples S m,w p*markedCompletedT (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (S p).ideal i∣A then (1:ℂ) else 0) := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro p hp hpbad
  have hh : ¬∀ i,m∉(S p).ideal i := fun h => hpbad (Finset.mem_filter.mpr ⟨hp,h⟩)
  push Not at hh
  obtain ⟨i,hi⟩ := hh
  rw [markedCompletedT_zero_punctured_slot (S p) i Ψ m f z hi W X,mul_zero]

lemma retained_slot_period (tuples : Finset α) (S : α→PrimeFamily σ)
    (m : Eis) (Q : Ideal Eis) (hQ : Q∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) (i : σ) :
    IsCoprime Q ((S p).ideal i) := by
  apply (maximal_coprime_of_not_dvd _ _ ?_).symm
  intro h
  have hd := dvd_trans h hQ
  exact (Finset.mem_filter.mp hp).2 i ((Ideal.dvd_iff_le.mp hd) (Ideal.subset_span (by simp)))

lemma retained_markedRowFamily_period {m f z : Eis} (D : GoodMaskRowData m f z)
    (tuples : Finset α) (S : α→PrimeFamily σ) (Q : Ideal Eis) (c : Eis)
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (hpuncture : Q*Ideal.span {(72:Eis)}∣Ideal.span {m})
    (p : α) (hp : p∈punctureRetainedTuples tuples S m) :
    ∀ i,IsCoprime (Ideal.span {(9:Eis)*c}) ((markedRowFamily D (S p) Q).ideal i) := by
  exact markedRowFamily_period D (S p) Q
    (fun i => retained_slot_period tuples S m _ hpuncture p hp i) c hcQ

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1118

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.PunctureLists
Source SHA256: 08817b2b6358d12a7d2b19e41960a0aeaef94d781c137e7a3272d425ada03a4f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1119




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def punctureLists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) : σ→Finset (Ideal Eis) :=
  fun i => (lists i).filter (fun P => P∉S)

def punctureListLift (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (p : ∀ i,punctureLists lists S i) : ∀ i,lists i :=
  fun i => ⟨(p i).val,(Finset.mem_filter.mp (p i).property).1⟩

def punctureListEquiv (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis)) :
    (∀ i,punctureLists lists S i) ≃ {p : ∀ i,lists i // ∀ i,(p i).val∉S} where
  toFun p := ⟨punctureListLift lists S p,fun i => (Finset.mem_filter.mp (p i).property).2⟩
  invFun p i := ⟨(p.val i).val,Finset.mem_filter.mpr ⟨(p.val i).property,p.property i⟩⟩
  left_inv _p := rfl
  right_inv _p := rfl

lemma sum_puncture_lists (lists : σ→Finset (Ideal Eis)) (S : Finset (Ideal Eis))
    (f : (∀ i,lists i)→ℂ) (hz : ∀ p,(∃ i,(p i).val∈S) → f p=0) :
    (∑ p : ∀ i,lists i,f p)=∑ p : ∀ i,punctureLists lists S i,f (punctureListLift lists S p) := by
  have he := (punctureListEquiv lists S).sum_comp (fun p => f p.val)
  have hs := sum_subtype_dite_decidable (fun p : ∀ i,lists i => ∀ i,(p i).val∉S) (fun p _ => f p)
  calc
    _ = ∑ p : ∀ i,lists i,if h:∀ i,(p i).val∉S then f p else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      split_ifs with h
      · rfl
      · exact hz p (by simpa only [not_forall,not_not] using h)
    _ = ∑ p : {p : ∀ i,lists i // ∀ i,(p i).val∉S},f p.val := hs.symm
    _ = _ := he.symm

theorem original_completed_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P) (S : Finset (Ideal Eis))
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists S i,(∏ i,w i (punctureListLift lists S p i))*markedCompletedT
      (rowTwist Ψ (m*excludedGenerator S) f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists S
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m*excludedGenerator S∈(p i).val := (p i).val.mul_mem_left m (excludedGenerator_mem S hi)
  have hz := markedCompletedT_zero_punctured Ψ (m*excludedGenerator S) f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1119

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowPunctureLists
Source SHA256: 0fdf324818742c123a0fffbbe203ffad6f36f7f4f8bbda2bb427660298328e4d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1120



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def actualPuncturePrimes (lists : σ→Finset (Ideal Eis)) (m : Eis) : Finset (Ideal Eis) :=
  (Finset.univ.biUnion lists).filter (fun P => m∈P)

omit [DecidableEq σ] in
lemma actualPuncturePrimes_mem (lists : σ→Finset (Ideal Eis)) (m : Eis)
    (i : σ) (P : Ideal Eis) (hP : P∈lists i) :
    P∈actualPuncturePrimes lists m ↔ m∈P := by
  simp only [actualPuncturePrimes,Finset.mem_filter]
  exact and_iff_right (Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hP⟩)

lemma puncture_period_coprime (Q : Ideal Eis) (m : Eis) (hQ : Q∣Ideal.span {m})
    (P : Ideal Eis) (hP : P.IsMaximal) (hm : m∉P) : IsCoprime Q P := by
  let : P.IsMaximal := hP
  have hp : ¬P∣Ideal.span {m} := by
    intro h
    exact hm ((Ideal.dvd_iff_le.mp h) (Ideal.subset_span (Set.mem_singleton m)))
  exact (maximal_coprime_of_not_dvd P (Ideal.span {m}) hp).symm.of_isCoprime_of_dvd_left hQ

theorem original_completed_actual_puncture_lists (lists : σ→Finset (Ideal Eis))
    (hprime : ∀ i,∀ P∈lists i,Prime P)
    (Ψ : Eis→*ℂ) (m f z : Eis) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    ∑ p : ∀ i,punctureLists lists (actualPuncturePrimes lists m) i,
      (∏ i,w i (punctureListLift lists (actualPuncturePrimes lists m) p i))*markedCompletedT
      (rowTwist Ψ m f z) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0) := by
  apply sum_puncture_lists lists (actualPuncturePrimes lists m)
  intro p hp
  obtain ⟨i,hi⟩ := hp
  have hm : m∈(p i).val := (Finset.mem_filter.mp hi).2
  have hz := markedCompletedT_zero_punctured Ψ m f z (p i).val
    (hprime i _ (p i).property) hm W X (fun A => ∏ j,if (p j).val∣A then (1:ℂ) else 0)
    (fun A hA => Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hA))
  exact mul_eq_zero_of_right _ hz
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1120

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.TupleDyads
Source SHA256: f32fa9c04e86386e2d49937029abc3c758596f3ee35366bfed565ffa96a37efa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1121



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def activeTupleDyad (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (i : Fin (columnDyadicLength H+1)) : Finset (σ→Ideal Eis) :=
  tuples.filter fun p => divisorDyadicLabel H (slotTupleProduct p)=i

omit [DecidableEq σ] in
lemma sum_activeTupleDyads {A : Type*} [AddCommMonoid A]
    (tuples : Finset (σ→Ideal Eis)) (H : ℝ) (f : (σ→Ideal Eis)→A) :
    (∑ p∈tuples,f p)=∑ i : Fin (columnDyadicLength H+1),∑ p∈activeTupleDyad tuples H i,f p := by
  exact (Finset.sum_fiberwise tuples (fun p => divisorDyadicLabel H (slotTupleProduct p)) f).symm

omit [DecidableEq σ] in
lemma activeTupleDyad_bounds (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (p : σ→Ideal Eis) (hp : p∈activeTupleDyad tuples H i) :
    divisorDyadicScale i.val≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  obtain ⟨hpt,he⟩ := Finset.mem_filter.mp hp
  have hh := divisorDyadicLabel_bounds H (slotTupleProduct p) (hn p hpt).1 (hn p hpt).2
  rw [he] at hh
  constructor
  · exact max_le (hn p hpt).1 hh.1.le
  · have ht : (2:ℝ)^i.val/2≤divisorDyadicScale i.val := le_max_right _ _
    linarith [hh.2]

omit [DecidableEq σ] in
lemma activeTupleDyad_scale_le (tuples : Finset (σ→Ideal Eis)) (H : ℝ)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    divisorDyadicScale i.val≤H := by
  obtain ⟨p,hp⟩ := hi
  exact (activeTupleDyad_bounds tuples H hn i p hp).1.trans (hn p (Finset.mem_filter.mp hp).1).2

omit [DecidableEq σ] in
lemma activeTupleDyad_width (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    0≤Real.logb Z (divisorDyadicScale i.val) ∧ Real.logb Z (divisorDyadicScale i.val)≤z := by
  have hs := divisorDyadicScale_ge_one i.val
  have hp : 0<divisorDyadicScale i.val := lt_of_lt_of_le zero_lt_one hs
  constructor
  · have hh := Real.logb_le_logb_of_le hZ zero_lt_one hs
    simpa only [Real.logb_one] using hh
  · have hh := Real.logb_le_logb_of_le hZ hp ((activeTupleDyad_scale_le tuples H hn i hi).trans hH)
    rwa [Real.logb_rpow (lt_trans zero_lt_one hZ) (ne_of_gt hZ)] at hh
omit [DecidableEq σ] in
lemma slotTupleProduct_norm_bound (L : σ→Finset (Ideal Eis)) (H : σ→ℝ)
    (hzero : ∀ i,∀ P∈L i,P≠0) (hH : ∀ i,∀ P∈L i,(Ideal.absNorm P:ℝ)≤H i)
    (p : σ→Ideal Eis) (hp : ∀ i,p i∈L i) :
    1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤∏ i,H i := by
  have hn : slotTupleProduct p≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hzero i _ (hp i))
  refine ⟨QuadraticMainBoundary.norm_one_le hn,?_⟩
  change (Ideal.absNorm (∏ i,p i):ℝ)≤_
  rw [map_prod,Nat.cast_prod]
  exact Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _) (fun i _ => hH i _ (hp i))

omit [DecidableEq σ] in
lemma activeTupleDyad_energy_scale (tuples : Finset (σ→Ideal Eis)) (H Z z : ℝ)
    (hZ : 1<Z) (hH : H≤Z^z)
    (hn : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤H)
    (i : Fin (columnDyadicLength H+1)) (hi : (activeTupleDyad tuples H i).Nonempty) :
    2≤2*divisorDyadicScale i.val ∧
      0≤Real.logb Z ((2*divisorDyadicScale i.val)/2) ∧
      Real.logb Z ((2*divisorDyadicScale i.val)/2)≤z ∧
      ∀ p∈activeTupleDyad tuples H i,
        (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
          (Ideal.absNorm (slotTupleProduct p):ℝ)≤2*divisorDyadicScale i.val := by
  have hw := activeTupleDyad_width tuples H Z z hZ hH hn i hi
  have hs := divisorDyadicScale_ge_one i.val
  rw [show (2*divisorDyadicScale i.val)/2=divisorDyadicScale i.val by ring]
  exact ⟨by linarith,hw.1,hw.2,activeTupleDyad_bounds tuples H hn i⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1121

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalCellBounds
Source SHA256: 977f088549218a897986d0381623c113530b604988899b0f99e0c49354130041
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1122



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma original_residual_norm_bounds (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) :
    ∀ K∈originalResidualRows rows J Q,
      1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤
        U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)) := by
  intro K hK
  have hr := originalResidualRows_range rows J Q hbad U hrows K hK
  exact ⟨QuadraticMainBoundary.norm_one_le hr.1.1,hr.2⟩

theorem original_residual_cell_representative (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U)
    (H : ℝ) (hH : H=U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)))
    (i : Fin (columnDyadicLength H+1))
    (hi : (divisorDyadicBin (originalResidualRows rows J Q) H i).Nonempty) :
    ∃ I∈rows,I≠0 ∧ rowPowerfulPart J=rowPowerfulPart I ∧ rowMaskPart J Q=rowMaskPart I Q ∧
      (Ideal.absNorm I:ℝ)≤U ∧
      divisorDyadicScale i.val≤(Ideal.absNorm (rowResidualPart I Q):ℝ) ∧
      (Ideal.absNorm (rowResidualPart I Q):ℝ)≤2*divisorDyadicScale i.val := by
  obtain ⟨K,hK⟩ := hi
  have hKT := (Finset.mem_filter.mp hK).1
  have hr := originalResidualRows_reconstruct rows J Q (fun I hI => (hrows I hI).1) K hKT
  obtain ⟨hI,hp,hm⟩ := Finset.mem_filter.mp hr.1
  refine ⟨reconstructFiberRow J Q K,hI,(hrows _ hI).1,hp.symm,hm.symm,(hrows _ hI).2,?_⟩
  rw [hr.2]
  apply divisorDyadicBin_bounds _ H _ i K hK
  intro D hD
  rw [hH]
  exact original_residual_norm_bounds rows J Q hbad U hrows D hD

lemma original_residual_cell_scale_cap (rows : Finset (Ideal Eis)) (J Q : Ideal Eis)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (U H Z L : ℝ)
    (hrows : ∀ I∈rows,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U)
    (hH : H=U/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J Q):ℝ)))
    (hZ : 2≤Z) (hcap : H≤Z^L)
    (i : Fin (columnDyadicLength H+1))
    (hi : (divisorDyadicBin (originalResidualRows rows J Q) H i).Nonempty) :
    1≤2*divisorDyadicScale i.val ∧ 2*divisorDyadicScale i.val≤Z^(L+1) := by
  have hz : 0<Z := by linarith
  have hs := divisorDyadicScale_ge_one i.val
  have hh : divisorDyadicScale i.val≤H := by
    apply divisorDyadicBin_scale_le _ H _ i hi
    intro D hD
    rw [hH]
    exact original_residual_norm_bounds rows J Q hbad U hrows D hD
  refine ⟨by linarith,?_⟩
  calc
    _ ≤ Z*Z^L := mul_le_mul hZ (hh.trans hcap) (by linarith) hz.le
    _ = _ := by rw [Real.rpow_add hz,Real.rpow_one];ring

lemma dyadic_canonical_lower (Z QK : ℝ) (hZ : 1<Z) (hQK : 0<QK)
    (K : Ideal Eis) (hK : QK/2≤(Ideal.absNorm K:ℝ)) :
    Z^(Real.logb Z QK)/2≤(Ideal.absNorm K:ℝ) := by
  rw [Real.rpow_logb (lt_trans zero_lt_one hZ) (ne_of_gt hZ) hQK]
  exact hK

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1122

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CellArithmetic
Source SHA256: aa59dbd1b2db9c63c6a924ea4dce56133d480a2bbc9fc2663d199d77da352325
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1123






namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma residual_level_coprime (K Q₀ : Ideal Eis) (hK : Admissible K)
    (c : Eis) (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hcop : IsCoprime Q₀ K) :
    IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  rw [←PrimeFamily.residual_product K hK]
  apply IsCoprime.prod_right_iff.mpr
  intro i hi
  exact (PrimeFamily.residual K hK).level_coprime Q₀ c hc
    (fun i => hcop.of_isCoprime_of_dvd_right (PrimeFamily.residual_dvd K hK i)) i

lemma original_residual_completion_conditions (rows : Finset (Ideal Eis)) (J Q Q₀ : Ideal Eis)
    (hJ : J≠0) (hQ : Q≠0) (hrows : ∀ I∈rows,I≠0)
    (hbad : ∀ P∈fixedBadPrimes,P∣Q) (hperiod : Q₀∣Q)
    (A : Finset (FreeReflection.pool J Q Q₀)) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) :
    ∀ K∈originalResidualRows rows J Q,
      Admissible K ∧
      (∀ b : A,IsCoprime (((poolPrimeFamily J Q Q₀).restrict A).ideal b) K) ∧
      IsCoprime (Ideal.span {(9:Eis)*c}) K := by
  intro K hK
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp hK
  subst K
  obtain ⟨hi,hp,hm⟩ := Finset.mem_filter.mp hI
  have hk := rowResidualPart_admissible I Q hbad
  refine ⟨hk,?_,?_⟩
  · intro b
    exact poolPrimeFamily_fiber_row_coprime J I Q Q₀ hJ (hrows I hi) hQ hp.symm hm.symm b.val
  · apply residual_level_coprime _ Q₀ hk c hc
    exact (squarefreeResidualPart_coprime (rowSimplePart I) Q).symm.of_isCoprime_of_dvd_left hperiod

variable {φ σ : Type*} [Fintype σ] [DecidableEq σ]

theorem original_tuple_cell_conditions (Frozen : PrimeFamily φ)
    (hFrozen : Pairwise (Function.onFun IsCoprime Frozen.ideal))
    (L : σ→Finset (Ideal Eis)) (hL : Pairwise (fun i j => Disjoint (L i) (L j)))
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)
    (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
    (hsub : tuples⊆fixedSlotTupleSet L Frozen.ideal)
    (N : Eis) (hFN : ∀ b,IsCoprime (Ideal.span {N}) (Frozen.ideal b))
    (hFodd : ∀ b,ringChar (Eis⧸Frozen.ideal b)≠2)
    (hLN : ∀ i,∀ P∈L i,IsCoprime (Ideal.span {N}) P)
    (hLodd : ∀ i,∀ P∈L i,ringChar (Eis⧸P)≠2) :
    let S := tuplePrimeFamily tuples hne
      (fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i))
      (fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i))
    ∀ P∈tuples.image slotTupleProduct,
      (∏ i,(S P).ideal i)=P ∧
      Pairwise (Function.onFun IsCoprime (Frozen.sum (S P)).ideal) ∧
      (∀ b,IsCoprime (Ideal.span {N}) ((Frozen.sum (S P)).ideal b)) ∧
      (∀ b,ringChar (Eis⧸(Frozen.sum (S P)).ideal b)≠2) := by
  dsimp only
  let hm := fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i)
  let hg := fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1 i)
  have hs : ∀ p∈tuples,∀ i,p i∈L i := fun p hp => ((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).1
  intro P hP
  refine ⟨tuplePrimeFamily_product tuples hne hm hg P hP,?_,?_,?_⟩
  · exact tuplePrimeFamily_sum_pairwise Frozen hFrozen L hL tuples hne hs hm hg
      (fun p hp => ((mem_fixedSlotTupleSet L Frozen.ideal p).mp (hsub hp)).2) P
  · intro b
    cases b with
    | inl b => exact hFN b
    | inr b => exact hLN b _ (hs _ (tupleRepresentative_mem tuples hne P) b)
  · intro b
    cases b with
    | inl b => exact hFodd b
    | inr b => exact hLodd b _ (hs _ (tupleRepresentative_mem tuples hne P) b)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1123

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CanonicalCellArithmetic
Source SHA256: f14e33fa05fae52b9e978349b06586f5515121e4f492c092a287667993e0a04c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1124



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma canonical_retained_slot_not_excluded {α σ : Type*} [Fintype σ]
    (tuples : Finset α) (S : α→PrimeFamily σ) (q : ℕ) (m : Eis)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) (i : σ) :
    (S p).ideal i∉reflectionExcludedPrimes q := by
  intro hi
  have hm : ActualFiber.maskElement q m∈(S p).ideal i :=
    Ideal.mul_mem_left _ m (excludedGenerator_mem _ hi)
  exact (Finset.mem_filter.mp hp).2 i hm

lemma canonical_retained_slot_free_period {α σ : Type*} [Fintype σ]
    (tuples : Finset α) (S : α→PrimeFamily σ) (q : ℕ) (hq : q≠0) (m : Eis)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) (i : σ) :
    IsCoprime (ActualFiber.freeConductor q) ((S p).ideal i) := by
  have hc := reflectionConductor_coprime_of_not_excluded q hq ((S p).ideal i)
    (canonical_retained_slot_not_excluded tuples S q m p hp i)
  rw [reflectionConductor_ideal] at hc
  exact hc.of_isCoprime_of_dvd_left (dvd_mul_left _ (Ideal.span {(9:Eis)}))

lemma canonical_retained_marked_period {α σ : Type*} [Fintype σ]
    (q : ℕ) (hq : q≠0) (m f z : Eis) (D : GoodMaskRowData (ActualFiber.maskElement q m) f z)
    (tuples : Finset α) (S : α→PrimeFamily σ)
    (p : α) (hp : p∈punctureRetainedTuples tuples S (ActualFiber.maskElement q m)) :
    ∀ i,IsCoprime (Ideal.span {(9:Eis)*reflectionConductor q})
      ((markedRowFamily D (S p) (CanonicalCoefficientClass.fixedBaseConductor q)).ideal i) := by
  exact markedRowFamily_period D (S p) (CanonicalCoefficientClass.fixedBaseConductor q)
    (fun i => canonical_retained_slot_free_period tuples S q hq m p hp i)
    (reflectionConductor q) (reflectionConductor_ideal q)

theorem canonical_original_cell_conditions (q : ℕ) (hq : q≠0) (m : Eis) (hm : m≠0)
    (rows : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : F≠0)
    (hrows : ∀ I∈rows,I≠0)
    (A : Finset (FreeReflection.pool J (ActualFiber.maskIdeal q m F) (ActualFiber.freeConductor q))) :
    ∀ K∈originalResidualRows rows J (ActualFiber.maskIdeal q m F),
      Admissible K ∧
      (∀ b : A,IsCoprime (((poolPrimeFamily J (ActualFiber.maskIdeal q m F)
        (ActualFiber.freeConductor q)).restrict A).ideal b) K) ∧
      IsCoprime (Ideal.span {(9:Eis)*reflectionConductor q}) K := by
  intro K hK
  obtain ⟨I,hI,he⟩ := Finset.mem_image.mp hK
  subst K
  obtain ⟨hi,hp,hmask⟩ := Finset.mem_filter.mp hI
  have hk := rowResidualPart_admissible I _ (ActualFiber.mask_bad q m F)
  refine ⟨hk,?_,?_⟩
  · intro b
    exact poolPrimeFamily_fiber_row_coprime J I _ _ hJ (hrows I hi)
      (ActualFiber.maskIdeal_ne_zero q m hm F hF) hp.symm hmask.symm b.val
  · exact residual_level_coprime _ (ActualFiber.freeConductor q) hk (reflectionConductor q)
      (reflectionConductor_ideal q) (residual_coprime_free_base q hq m F I)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1124

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.TupleMembers
Source SHA256: 18c5006b8083163e70d92873c158493eb648a464f28316cc71ce36c2cde5c008
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1125




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable (tuples : Finset (σ→Ideal Eis))
    (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)

def memberTupleFamily (p : tuples) : PrimeFamily σ where
  ideal := p.val
  maximal := hmax p.val p.property
  good := hgood p.val p.property

lemma tuplePrimeFamily_at_member (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))) (p : tuples) :
    tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val)=memberTupleFamily tuples hmax hgood p := by
  apply PrimeFamily.eq_of_ideal_eq
  exact tuplePrimeFamily_at_product tuples hne hmax hgood hinj p.val p.property

variable {N a c : Eis} {mode : Bool}
    (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K) (hne : tuples.Nonempty)
    (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
    (D : ∀ P : tuples.image slotTupleProduct,IsCoprime K P.val→
      ControlledStratumArithmetic (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode)

def memberTupleControlled (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  castControlled (congrArg (fun S => (F.reflected K hK S).generator)
    (tuplePrimeFamily_at_member tuples hmax hgood hne hinj p))
    (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp)

lemma memberTupleControlled_value (p : tuples) (hp : IsCoprime K (slotTupleProduct p.val))
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (X : ℝ) :
    mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X=
    mixedReflectedValue (D ⟨slotTupleProduct p.val,Finset.mem_image.mpr ⟨p.val,p.property,rfl⟩⟩ hp) s
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_ne_zero hc
      (F.reflected K hK (tuplePrimeFamily tuples hne hmax hgood (slotTupleProduct p.val))).generator_good
      (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) W X :=
  mixedReflectedValue_cast _ _ s _ _ hc _ _ _ _ W X

def memberTupleRow
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) : ℂ :=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0

theorem literalWholeRow_eq_member_tuples
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (j : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ) :
    literalWholeRow F K hK (tuplePrimeFamily tuples hne hmax hgood) j
      (tuples.image slotTupleProduct) D s hc W θ X r (slotProductCoefficient tuples aw)=
    ∑ p : tuples,if hp:IsCoprime K (slotTupleProduct p.val) then
      r K*aw p.val*mixedReflectedValue (memberTupleControlled tuples hmax hgood F K hK hne hinj D p hp) s
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
        (F.reflected K hK (memberTupleFamily tuples hmax hgood p)).generator_good
        (reflectedExponent j) (slotIndices φ (PrimeIndex K) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  let hr : ∀ k∈({K}:Finset (Ideal Eis)),Admissible k := fun k hk => (Finset.mem_singleton.mp hk).symm ▸ hK
  let Ds : ∀ k : ({K}:Finset (Ideal Eis)),∀ P : tuples.image slotTupleProduct,IsCoprime k.val P.val→
      ControlledStratumArithmetic (F.reflected k.val (hr k.val k.property)
        (tuplePrimeFamily tuples hne hmax hgood P.val)).generator N a c mode := by
    intro k
    rcases k with ⟨k,hk⟩
    have hh := Finset.mem_singleton.mp hk
    subst k
    exact D
  have he := literalWholeRow_eq_active_tuples F {K} tuples hne hmax hgood hinj
    hr j Ds s hc W θ X r aw ⟨K,Finset.mem_singleton_self K⟩
  convert he using 1
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hk : IsCoprime K (slotTupleProduct p.val)
  · simp only [dite_eq_left hk]
    rw [memberTupleControlled_value]
  · simp only [dite_eq_right hk]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1125

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.DyadSelection
Source SHA256: af7bd81db95d88b04f98c372ee0cec3af00ed9010d50dcb73cd1c64044a76d95
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1126



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ] [DecidableEq σ] {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

omit [DecidableEq σ] in
lemma activeTupleDyad_subset (i : Fin (columnDyadicLength Hslot+1)) : activeTupleDyad tuples Hslot i⊆tuples :=
  Finset.filter_subset _ _

lemma divisorDyadicBin_subset (i : Fin (columnDyadicLength Hrow+1)) : divisorDyadicBin rows Hrow i⊆rows :=
  Finset.filter_subset _ _

variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)

def dyadicTupleControlled (K : rows) (p : tuples) (hp : IsCoprime K.val (slotTupleProduct p.val)) :
    ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
      (memberTupleFamily tuples hmax hgood p)).generator N a c mode :=
  C (divisorDyadicLabel Hrow K.val) (divisorDyadicLabel Hslot (slotTupleProduct p.val))
    ⟨K.val,Finset.mem_filter.mpr ⟨K.property,rfl⟩⟩ ⟨p.val,Finset.mem_filter.mpr ⟨p.property,rfl⟩⟩ hp

omit [DecidableEq σ] in
lemma dyadicTupleControlled_at (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j)
    (hp : IsCoprime K.val (slotTupleProduct p.val)) :
    dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C
      ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
      ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩ hp=C i j K p hp := by
  rcases K with ⟨K,hK⟩
  rcases p with ⟨p,hpT⟩
  have hi := (Finset.mem_filter.mp hK).2
  have hj := (Finset.mem_filter.mp hpT).2
  subst i
  subst j
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1126

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.DyadReassembly
Source SHA256: eaf2d0276cf3f3189af7c5a4af383a3b18ff69db32e9ecd0d67598d3a44760b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1127



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

lemma dependent_sum_filter_partition {α β A : Type*} [Fintype β] [DecidableEq β] [AddCommMonoid A]
    (T : Finset α) (label : α→β) (f : T→A) :
    (∑ p : T,f p)=∑ j : β,∑ p : T.filter (fun p => label p=j),f ⟨p.val,(Finset.mem_filter.mp p.property).1⟩ := by
  let g : α→A := fun p => if hp:p∈T then f ⟨p,hp⟩ else 0
  have h := Finset.sum_fiberwise T label g
  calc
    _ = ∑ p∈T,g p := by
      symm
      rw [←Finset.sum_coe_sort T]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g,dite_eq_left p.property]
    _ = ∑ j,∑ p∈T.filter (fun p => label p=j),g p := h.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [←Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro p hp
      simp only [g,dite_eq_left (Finset.mem_filter.mp p.property).1]

theorem dependent_partition_energy {α β ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (rows : Finset α) (tuples : Finset β) (rowLabel : α→ι) (slotLabel : β→κ)
    (f : rows→tuples→ℂ) :
    (∑ k : rows,‖∑ p : tuples,f k p‖^2)≤
      (Fintype.card κ:ℝ)*∑ i : ι,∑ j : κ,
        ∑ k : rows.filter (fun k => rowLabel k=i),
          ‖∑ p : tuples.filter (fun p => slotLabel p=j),
            f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩
              ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2 := by
  rw [dependent_sum_filter_partition rows rowLabel]
  calc
    _ ≤ ∑ i : ι,(Fintype.card κ:ℝ)*∑ j : κ,
        ∑ k : rows.filter (fun k => rowLabel k=i),
          ‖∑ p : tuples.filter (fun p => slotLabel p=j),
            f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩
              ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2 := by
      apply Finset.sum_le_sum
      intro i hi
      let g := fun (j : κ) (k : rows.filter (fun k => rowLabel k=i)) =>
        ∑ p : tuples.filter (fun p => slotLabel p=j),
          f ⟨k.val,(Finset.mem_filter.mp k.property).1⟩ ⟨p.val,(Finset.mem_filter.mp p.property).1⟩
      have he := weighted_finite_row_energy (Finset.univ : Finset κ)
        (Finset.univ : Finset (rows.filter (fun k => rowLabel k=i))) (fun _ => (1:ℂ)) g
      simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at he
      convert he using 1
      apply Finset.sum_congr rfl
      intro k hk
      congr 2
      exact dependent_sum_filter_partition tuples slotLabel _
    _ = _ := by rw [Finset.mul_sum]

variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)
variable (C : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode)
variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (θ X : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)

def dyadicPhysicalTerm (K : rows) (p : tuples) : ℂ :=
  if hp:IsCoprime K.val (slotTupleProduct p.val) then
    r K.val*aw p.val*mixedReflectedValue
      (dyadicTupleControlled G rows hrows tuples hmax hgood Hrow Hslot C K p hp) s
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_ne_zero hc
      (G.reflected K.val (hrows K.val K.property) (memberTupleFamily tuples hmax hgood p)).generator_good
      (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

lemma dyadicPhysicalTerm_at (i : Fin (columnDyadicLength Hrow+1))
    (j : Fin (columnDyadicLength Hslot+1))
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) :
    dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
      ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
      ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue (C i j K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0 := by
  unfold dyadicPhysicalTerm
  split_ifs with hp
  · rw [dyadicTupleControlled_at]
  · rfl

theorem dyadic_physical_energy (E : ℝ)
    (hE : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (∑ K : rows.filter (fun K => divisorDyadicLabel Hrow K=i),
        ‖∑ p : tuples.filter (fun p => divisorDyadicLabel Hslot (slotTupleProduct p)=j),
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw
            ⟨K.val,(Finset.mem_filter.mp K.property).1⟩
            ⟨p.val,(Finset.mem_filter.mp p.property).1⟩‖^2)≤E) :
    (∑ K : rows,‖∑ p : tuples,
      dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw K p‖^2)≤
      (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E := by
  have he := dependent_partition_energy rows tuples (divisorDyadicLabel Hrow)
    (fun p => divisorDyadicLabel Hslot (slotTupleProduct p))
    (dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot C s hc jF W θ X r aw)
  apply he.trans
  have hb := Finset.sum_le_sum (s:=Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hE i j))
  apply (mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg (Fintype.card (Fin (columnDyadicLength Hslot+1))))).trans_eq
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_add,Nat.cast_one]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1127

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.DyadCompletionEnergy
Source SHA256: d3105a7b3e83afd1269d82041fff2c8ac194bf67f3f06772fc5131d002edfb20
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1128


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {φ σ : Type*} [Fintype φ] [Fintype σ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily φ) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (tuples : Finset (σ→Ideal Eis)) (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
    (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i) (Hrow Hslot : ℝ)

abbrev CellCompletion (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1)) :=
    ∀ K : divisorDyadicBin rows Hrow i,∀ p : activeTupleDyad tuples Hslot j,
      IsCoprime K.val (slotTupleProduct p.val)→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
        (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator N a c mode

variable (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : φ→ℕ) (W : ℝ→ℂ) (X : ℝ)

def cellPhysicalTerm (i : Fin (columnDyadicLength Hrow+1)) (j : Fin (columnDyadicLength Hslot+1))
    (D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j)
    (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ)
    (K : divisorDyadicBin rows Hrow i) (p : activeTupleDyad tuples Hslot j) : ℂ :=
    if hp:IsCoprime K.val (slotTupleProduct p.val) then
      r K.val*aw p.val*mixedReflectedValue (D K p hp) s
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val (divisorDyadicBin_subset rows Hrow i K.property))
          (memberTupleFamily tuples hmax hgood ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩)).generator_good
        (reflectedExponent jF) (slotIndices φ (PrimeIndex K.val) σ) (CompletedHeight.normTwistedSource W θ) X else 0

theorem physical_dyad_selection_energy (E : ℝ→ℝ) (hE : ∀ θ,0≤E θ)
    (he : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      (divisorDyadicBin rows Hrow i).Nonempty → (activeTupleDyad tuples Hslot j).Nonempty →
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤E θ) :
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : rows,‖∑ p : tuples,
          dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw K p‖^2)≤
          (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*E θ := by
  have hall : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      ∃ D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j,
      ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
        (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
        (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)≤E θ := by
    intro i j
    by_cases hi : (divisorDyadicBin rows Hrow i).Nonempty
    · by_cases hj : (activeTupleDyad tuples Hslot j).Nonempty
      · exact he i j hi hj
      · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
          fun K p hp => (hj ⟨p.val,p.property⟩).elim
        refine ⟨D,?_⟩
        intro θ r aw hr haw
        have hzero : ∀ K : divisorDyadicBin rows Hrow i,
            (∑ p : activeTupleDyad tuples Hslot j,
              cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p)=0 := by
          intro K
          apply Finset.sum_eq_zero
          intro p hp
          exact (hj ⟨p.val,p.property⟩).elim
        simp_rw [hzero,norm_zero,zero_pow (by norm_num : (2:ℕ)≠0),Finset.sum_const_zero]
        exact hE θ
    · let D : CellCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G rows hrows tuples hmax hgood Hrow Hslot i j :=
        fun K p hp => (hi ⟨K.val,K.property⟩).elim
      refine ⟨D,?_⟩
      intro θ r aw hr haw
      have hzero : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
          cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j D θ r aw K p‖^2)=0 := by
        apply Finset.sum_eq_zero
        intro K hK
        exact (hi ⟨K.val,K.property⟩).elim
      rw [hzero]
      exact hE θ
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ r aw hr haw
  apply dyadic_physical_energy G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw (E θ)
  intro i j
  have hid : (∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
      dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw
        ⟨K.val,divisorDyadicBin_subset rows Hrow i K.property⟩
        ⟨p.val,activeTupleDyad_subset tuples Hslot j p.property⟩‖^2)=
      ∑ K : divisorDyadicBin rows Hrow i,‖∑ p : activeTupleDyad tuples Hslot j,
        cellPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot s hc jF W X i j (D i j) θ r aw K p‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    apply congrArg (fun z : ℂ => ‖z‖^2)
    apply Finset.sum_congr rfl
    intro p hp
    exact dyadicPhysicalTerm_at G rows hrows tuples hmax hgood Hrow Hslot D s hc jF W θ X r aw i j K p
  exact hid.trans_le (hD i j θ r aw hr haw)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1128

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.MemberChoiceTransport
Source SHA256: a8b9e85db4f365531263c825c6ce4b2656f5d68b81360aac17bc0c6ce341185f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1129




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable (L : σ→Finset (Ideal Eis)) (F : φ→Ideal Eis)
    (hmax : ∀ i,∀ P∈L i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈L i,ConcretePrimeRowBridge.goodLambda∉P)

abbrev originalTupleMax : ∀ p∈fixedSlotTupleSet L F,∀ i,(p i).IsMaximal :=
  fun p hp i => hmax i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)
abbrev originalTupleGood : ∀ p∈fixedSlotTupleSet L F,∀ i,ConcretePrimeRowBridge.goodLambda∉p i :=
  fun p hp i => hgood i _ (((mem_fixedSlotTupleSet L F p).mp hp).1 i)

variable {N a c : Eis} {mode : Bool} (G : PrimeFamily τ) (K : Ideal Eis) (hK : Admissible K)
variable (D : ∀ p : fixedSlotTupleSet L F,IsCoprime K (slotTupleProduct p.val)→
    ControlledStratumArithmetic (G.reflected K hK
      (memberTupleFamily (fixedSlotTupleSet L F) (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator N a c mode)

def memberChoiceControlled (p : supportedSlotChoices L F K) :
    ControlledStratumArithmetic (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator N a c mode :=
  D ((supportedSlotTupleEquiv L F K) p).val ((supportedSlotTupleEquiv L F K) p).property

theorem member_source_eq_original_choices
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (r : ℂ) (w : ∀ i,L i→ℂ) :
    (∑ p : fixedSlotTupleSet L F,if hp:IsCoprime K (slotTupleProduct p.val) then
      r*fixedTupleCoefficient L w p.val*mixedReflectedValue (D p hp) s
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
        (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
          (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X else 0)=
    ∑ p : supportedSlotChoices L F K,r*(∏ i,w i (p.val i))*
      mixedReflectedValue (memberChoiceControlled L F hmax hgood G K hK D p) s
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_ne_zero hc
        (G.reflected K hK (slotChoiceFamily L hmax hgood p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X := by
  let e := supportedSlotTupleEquiv L F K
  have he := sum_subtype_dite_decidable (fun p : fixedSlotTupleSet L F => IsCoprime K (slotTupleProduct p.val))
    (fun p hp => r*fixedTupleCoefficient L w p.val*mixedReflectedValue (D p hp) s
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_ne_zero hc
      (G.reflected K hK (memberTupleFamily (fixedSlotTupleSet L F)
        (originalTupleMax L F hmax) (originalTupleGood L F hgood) p)).generator_good
      (reflectedExponent jF) (slotIndices τ (PrimeIndex K) σ) W X)
  rw [←he,←e.sum_comp]
  apply Finset.sum_congr rfl
  intro p hp
  change r*fixedTupleCoefficient L w (fun i => (p.val i).val)*_=_
  rw [fixedTupleCoefficient_at]
  rfl
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1129

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.WholeTail
Source SHA256: bdee4285448932994f16fab31d76dce5385d84c4401b6c12ba99e151c0f352a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1130



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe u v
variable {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ] {N a c : Eis} {mode : Bool}

theorem original_family_whole_tail (lo hi : ℝ) (hlo : 0<lo) (A : ℕ)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) :
    ∃ (degree : ℕ) (C : ℝ), 0<C ∧
    ∀ {φ : Type u} {σ : Type v} [Fintype φ] [Fintype σ]
      (F : PrimeFamily φ) (K : Ideal Eis) (hK : Admissible K)
      (S : Ideal Eis→PrimeFamily σ) (jF : φ→ℕ) (Pset : Finset (Ideal Eis))
      (D : ∀ P : Pset, IsCoprime K P.val →
        ControlledStratumArithmetic (F.reflected K hK (S P.val)).generator N a c mode)
      (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0),
      (9:Eis)*c∣N → (if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c-1) →
      (∀ P∈Pset, ∀ i, ringChar (Eis⧸(F.reflected K hK (S P)).ideal i)≠2) →
      (∀ i,jF i<6) → (∀ P∈Pset,(∏ j,(S P).ideal j)=P) →
      (∀ P∈Pset,CubicSieve.Admissible P) →
    ∀ (θ X T QK QP : ℝ) (r aw : Ideal Eis→ℂ),
      0<X → 0<T → 0<QK → 0<QP →
      (Ideal.absNorm K:ℝ)≤QK → (∀ P∈Pset,(Ideal.absNorm P:ℝ)≤QP) →
      ‖r K‖≤1 → (∀ P∈Pset,‖aw P‖≤1) →
      ‖literalWholeRow F K hK S jF Pset D s hc W θ X r aw-
        (fixedRadialCoefficientScalar*s.stratumShapeFactor (c*primaryGenerator (∏ i,F.ideal i)))*
          ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale F s X QK QP) (16*T),
            literalDyadicRow F K hK S jF Pset D s hc u i W θ X
              (fun K => r K*shapeArgument (primaryGenerator K))
              (fun P => aw P*shapeArgument (primaryGenerator P))‖≤
        (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*Pset.card*
          (C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
            T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹) := by
  obtain ⟨degree,C,hC,hbound⟩ := original_family_row_tail
    (N:=N) (a:=a) (c:=c) (mode:=mode) lo hi hlo A W hWs hW
  refine ⟨degree,C,hC,?_⟩
  intro φ σ _ _ F K hK S jF Pset D s hc hN hbase hchar hj hprod hPad θ X T QK QP r aw hX hT hQK hQP hKr hPr hr haw
  let : Finite Eisˣ := PrimaryIdealUnitReindex.finite_units
  let : Fintype Eisˣ := Fintype.ofFinite _
  let J := retainedDyads (familyRawScale F s X QK QP) (16*T)
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let E := C*(1+‖θ‖)^degree*((Ideal.absNorm (∏ i,F.ideal i):ℝ)*QK*QP)*
    T^(-(A:ℝ))*(familyRawScale F s X QK QP^2)⁻¹
  have hb (v : Eisˣ) :
      ‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
        ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖≤Pset.card*E :=
    hbound F K hK S jF Pset D s hc hN hbase hchar hj hprod v θ X T QK QP rr aa hX hT hQK hQP hKr hPr
      (by simpa only [rr,row_shape_weight_norm r K hK] using hr)
      (fun P hp => by simpa only [aa,slot_shape_weight_norm aw P (hPad P hp)] using haw P hp)
  have hcard : Fintype.card Eisˣ=6 := by
    rw [←Nat.card_eq_fintype_card]
    exact PrimaryIdealUnitReindex.card_units_eq_six
  rw [literalWholeRow_eq_dyadic F K hK S jF Pset D s hc hN hbase hchar hj hprod W lo hi hlo hWs hW θ X hX r aw]
  rw [←mul_sub,norm_mul, norm_mul,stratumShapeFactor_frozen_norm]
  simp only [tsum_fintype]
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*
        ∑ v : Eisˣ,‖(∑' i,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa)-
          ∑ i∈J,literalDyadicRow F K hK S jF Pset D s hc v i W θ X rr aa‖ := by
      exact mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c‖)*∑ _v : Eisˣ,Pset.card*E := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hb v)) (by positivity)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,hcard,nsmul_eq_mul]; dsimp only [E]; ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1130

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.FullEnergyBasic
Source SHA256: 694be1f98d6ca40d33c2cddee0bcbca5273b5341a4f382b54dcde970a57fb97d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1131



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
noncomputable section

lemma norm_sq_le_retained (f g : ℂ) (E : ℝ) (_hE : 0≤E) (hf : ‖f-g‖≤E) :
    ‖f‖^2≤2*‖g‖^2+2*E^2 := by
  have hh : ‖f‖≤‖g‖+E := by
    calc
      _ = ‖g+(f-g)‖ := by congr 1;ring
      _ ≤ ‖g‖+‖f-g‖ := norm_add_le _ _
      _ ≤ _ := add_le_add_right hf _
  have hsq := pow_le_pow_left₀ (norm_nonneg f) hh 2
  nlinarith [sq_nonneg (‖g‖-E)]

lemma row_energy_le_retained {α : Type*} (rows : Finset α) (f g : α→ℂ) (E : ℝ)
    (hE : 0≤E) (hf : ∀ k∈rows,‖f k-g k‖≤E) :
    (∑ k∈rows,‖f k‖^2)≤2*(∑ k∈rows,‖g k‖^2)+2*rows.card*E^2 := by
  calc
    _ ≤ ∑ k∈rows, (2*‖g k‖^2+2*E^2) := Finset.sum_le_sum (fun k hk => norm_sq_le_retained (f k) (g k) E hE (hf k hk))
    _ = _ := by simp only [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul];ring
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1131

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowFull
Source SHA256: a1227e6f139a2100457ab74e43b3e0df2e501207110e36c8f6bd65a8612719a5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1132



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_full_energy
    (Adecay : ℕ) (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool) :
    ∃ (degree degreeTail : ℕ) (C Ctail Z₀ : ℝ), 0<C ∧ 0<Ctail ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2)+
          2*rows.card*(Pset.card*Ctail*(1+‖θ‖)^degreeTail*
            ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*
            (familyRawScale G s X QK QP^2)⁻¹)^2 := by
  obtain ⟨degree,Cm,Z₀,hCm,hZ₀,henergy⟩ := original_low_sector_retained_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct,hCt,htail⟩ := original_family_whole_tail
    (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) lo hi hlo Adecay W hWs hW
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let Ctail := 6*Cshape*Ct+1
  have hshape : 0≤Cshape := by dsimp [Cshape];positivity
  have hCtail : 0<Ctail := by dsimp [Ctail];positivity
  refine ⟨degree,degreeTail,2*Cshape^2*Cm+1,Ctail,Z₀,by positivity,hCtail,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c₀*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X rr aa
  let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ W θ X r aw
  let Et := (Pset.card:ℝ)*Ctail*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hEt : 0≤Et := by dsimp [Et];positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul,stratumShapeFactor_frozen_norm]
  have hmain := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ rr aa hqk hqp hKr hPr
    (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
    (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
    have hh := htail G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ hNlevel hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X (Z^δ) QK QP r aw hX
      (Real.rpow_pos_of_pos hzpos _) hQK hQP (hKr K.val K.property).2
      (fun P hP => (hPr P hP).2.2) (hr K.val K.property) haw
    apply hh.trans
    change _ ≤ Et
    dsimp only [Et,Ctail,Cshape]
    have he : (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Pset.card*
        (Ct*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)=
      Pset.card*(6*(‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Ct)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by ring
    rw [he]
    gcongr
    linarith only
  have hh := row_energy_le_retained (Finset.univ:Finset rows) f (fun K => Φ*g K) Et hEt (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  apply hh.trans
  calc
    _ ≤ 2*(Cshape^2*(Cm*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2)))+2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      dsimp only [Et]
      have hp : 0≤(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
      nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1132

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowFullBudget
Source SHA256: a1ac56a2ebbdca9acdbdfdc73a3edc7b08521ae74e03b3c7f0654bf53b098c5f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1133



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_sector_full_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤(5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨Adecay,htail⟩ := actual_finite_source_tail_budget s Lcap δ saving hδ
  obtain ⟨degree,degreeTail,Cm,Ct,Z₀,hCm,hCt,hZ₀,henergy⟩ := original_low_sector_full_energy
    (Nlevel:=Nlevel) Adecay ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2
  let deg := max degree (degreeTail*2)
  refine ⟨deg,Cm+2*Ct^2*cusp^4+1,max Z₀ 128,by positivity,
    lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J Q Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have h128 : 128≤Z := (le_max_right _ _).trans hZ
  have hs := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    ((le_max_left _ _).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hscap hpool
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have ht := htail G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
    (fun K hK => ⟨(hrows K hK).1,(hKr K hK).2⟩)
    (fun P hP => ⟨(hPr P hP).1.1.ne_zero,(hPr P hP).2.2⟩) hFcap hKcap hPcap hXi
  have hheight : 1≤1+‖θ‖ := by linarith only [norm_nonneg θ]
  have hdm : (1+‖θ‖)^degree≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_left _ _)
  have hdt : (1+‖θ‖)^(degreeTail*2)≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_right _ _)
  have he := Real.rpow_le_rpow_of_exponent_le hz'.le hexp
  apply hs.trans
  have htailbound : 2*rows.card*(Pset.card*Ct*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2≤
      (2*Ct^2*cusp^4)*(1+‖θ‖)^deg*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
    calc
      _ = (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*
          (rows.card*(Pset.card*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
            (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2) := by rw [pow_mul];ring
      _ ≤ (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (2*Ct^2*(1+‖θ‖)^deg)*(cusp^4*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2)) := by gcongr
      _ = _ := by ring
  have hmain : Cm*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2)≤
      Cm*(1+‖θ‖)^deg*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by gcongr
  apply (add_le_add hmain htailbound).trans
  have hp : 0≤(1+‖θ‖)^deg*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1133

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowGlobalBudget
Source SHA256: 3f906eb418d730b374f2ef7911edae2ef71e0a507ec6f6e75877f2af05e8742f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1134



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_global_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤(5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (D K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_sector_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  let q := (Fintype.card (Eis⧸Ideal.span {Nlevel^2}):ℝ)
  have hq : 0≤q := Nat.cast_nonneg _
  refine ⟨degree,q^3*C+1,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J Q Q₀).restrict_pairwise (poolPrimeFamily_pairwise J Q Q₀) A
  obtain ⟨D,hD⟩ := exists_global_sector_completion G rows Pset S hrows s hc₀ hNlevel hbase hac hpair hGN
    hrowcop hprod hScop (fun P hP b => hSN P hP (Sum.inr b))
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hs := literal_global_sector_energy G rows Pset S hrows j D s hc₀ W θ X r aw
    (C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2)) (by
      intro r₀ p₀
      obtain ⟨E,hE⟩ := hD r₀ p₀
      refine ⟨E,hE,?_⟩
      exact henergy J I F Q Q₀ hJ hI hQ hpower hmask A
        Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
        hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
        hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
        hFcap hscap hpool (fullRaySector Nlevel rows r₀) (fullRaySector Nlevel Pset p₀) S
        (fun K hK => hrows K (Finset.mem_filter.mp hK).1) E hGN hGchar
        (fun K hK => hrowcop K (Finset.mem_filter.mp hK).1)
        (fun P hP => hprod P (Finset.mem_filter.mp hP).1)
        (fun P hP => hScop P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSN P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSchar P (Finset.mem_filter.mp hP).1)
        θ r aw hqk hqp
        (fun K hK => hKr K (Finset.mem_filter.mp hK).1)
        (fun P hP => hPr P (Finset.mem_filter.mp hP).1)
        (fun K hK => hr K (Finset.mem_filter.mp hK).1)
        (fun P hP => haw P (Finset.mem_filter.mp hP).1))
  apply hs.trans
  change q^3*(C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2))≤_
  have hp : 0≤(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by positivity
  nlinarith
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1134

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowMemberBudget
Source SHA256: 00b880e032afc93b380daf839b84e3679d3b7df0dc2ac7ddc1119f2337ed7197
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1135




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_low_member_tuple_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤(5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_low_global_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool rows tuples hne hmax hgood hinj
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J Q Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  obtain ⟨D,hD⟩ := henergy J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have he := hD θ r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
    (fun P hP => slotProductCoefficient_norm tuples hinj aw haw P hP)
  convert he using 1
  apply Finset.sum_congr rfl
  intro K hK
  congr 2
  exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw).symm
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1135

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.LowMemberGeometry
Source SHA256: 2db3174d00ef320ffa37d18178ad41dd3be0a8dbcdc3781852979ea85ed52ba7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1136




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem original_low_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i)) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F Q Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hQ : Q≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J Q=rowMaskPart I Q →
    ∀ (A : Finset (FreeReflection.pool J Q Q₀))
      (Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^(5/6-2*d) →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I Q):ℝ) →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      normWidth Z (rowPowerfulPart I)≤O₀+η → normWidth Z Q≤η →
      0≤d → d≤1/6 → ell0≤1/6-d+η → 0≤O₀ → za≤ell0+η → |shift|≤η →
      Nstar=1+ell0+shift → H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤δ → δ≤η → QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤(5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2 →
      let G := (poolPrimeFamily J Q Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^((5/6-2*d)+200*η+π+κ+ρ*Lpool-O₀/2) := by
  have hb (i : γ) := original_low_member_tuple_full_budget (Nlevel:=Nlevel)
    ε hε lo hi hlo W hWs hW (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i)
    ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  choose degree C Z₀ hC hZ₀ henergy using hb
  let degreeAll := ∑ i,degree i
  let CAll := (∑ i,C i)+1
  let ZAll := (∑ i,|Z₀ i|)+2
  have hn (i : γ) : degree i≤degreeAll := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hc (i : γ) : C i≤CAll := by
    have hh : C i≤∑ j,C j := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp only [CAll]
    linarith
  have hz (i : γ) : Z₀ i≤ZAll := by
    have hh : |Z₀ i|≤∑ j,|Z₀ j| := Finset.single_le_sum (fun j _ => abs_nonneg (Z₀ j)) (Finset.mem_univ i)
    have hh' := le_abs_self (Z₀ i)
    dsimp only [ZAll]
    linarith
  have hCA : 0<CAll := by
    have hh : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp only [CAll]
    linarith
  have hZA : 1<ZAll := by
    have hh : 0≤∑ i,|Z₀ i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp only [ZAll]
    linarith
  refine ⟨degreeAll,CAll,ZAll,hCA,hZA,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    hZ hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := henergy i J I F Q Q₀ hJ hI hQ hpower hmask A
    Z O₀ H za Nstar d ell0 shift π Ck CO CH X QK QP Lrow Lslot
    ((hz i).trans hZ) hCk hCO hCH hX hQK hQP hk hpow hrow hlogH hPowUpper hQwidth hd hd1 hell0 hO hzcap hshift
    hNs heH heza heN hδ0 hδη hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  apply (hD θ r aw hqk hqp hKr hPr hr haw).trans
  have hZpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZA hZ)
  have hheight : 1≤1+‖θ‖ := by linarith [norm_nonneg θ]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
  exact mul_le_mul (hc i) (pow_le_pow_right₀ hheight (hn i)) (by positivity) hCA.le
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1136

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.OriginalFull
Source SHA256: 452b30d5c3aeae1f1caecd5bcbe455ff3cff0ec17372db01d1f8aa6d78474618
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1137



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_full_energy
    (Adecay : ℕ) (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool) :
    ∃ (degree degreeTail : ℕ) (C Ctail Z₀ : ℝ), 0<C ∧ 0<Ctail ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)+
          2*rows.card*(Pset.card*Ctail*(1+‖θ‖)^degreeTail*
            ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*
            (familyRawScale G s X QK QP^2)⁻¹)^2 := by
  obtain ⟨degree,Cm,Z₀,hCm,hZ₀,henergy⟩ := original_sector_retained_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  obtain ⟨degreeTail,Ct,hCt,htail⟩ := original_family_whole_tail
    (N:=Nlevel) (a:=a) (c:=c₀) (mode:=mode) lo hi hlo Adecay W hWs hW
  let Cshape := ‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖
  let Ctail := 6*Cshape*Ct+1
  have hshape : 0≤Cshape := by dsimp [Cshape];positivity
  have hCtail : 0<Ctail := by dsimp [Ctail];positivity
  refine ⟨degree,degreeTail,2*Cshape^2*Cm+1,Ctail,Z₀,by positivity,hCtail,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget
  dsimp only
  intro hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  let rr := fun K => r K*shapeArgument (primaryGenerator K)
  let aa := fun P => aw P*shapeArgument (primaryGenerator P)
  let Φ := fixedRadialCoefficientScalar*s.stratumShapeFactor (c₀*primaryGenerator (∏ b,G.ideal b))
  let g := fun K : rows => ∑' u : Eisˣ,∑ i∈retainedDyads (familyRawScale G s X QK QP) (16*Z^δ),
    literalDyadicRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ u i W θ X rr aa
  let f := fun K : rows => literalWholeRow G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ W θ X r aw
  let Et := (Pset.card:ℝ)*Ctail*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
    (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hEt : 0≤Et := by dsimp [Et];positivity
  have hΦ : ‖Φ‖=Cshape := by
    dsimp only [Φ,Cshape]
    rw [norm_mul,stratumShapeFactor_frozen_norm]
  have hmain := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap hpool hsmall
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ rr aa hqk hqp hKr hPr
    (fun K hK => by simpa only [rr,row_shape_weight_norm r K (hrows K hK)] using hr K hK)
    (fun P hP => by simpa only [aa,slot_shape_weight_norm aw P (hPr P hP).1] using haw P hP)
  have hrem (K : rows) : ‖f K-Φ*g K‖≤Et := by
    have hodd : ∀ P∈Pset,∀ b,ringChar (Eis⧸(G.reflected K.val (hrows K.val K.property) (S P)).ideal b)≠2 := by
      intro P hP b
      rcases b with b | b | b
      · exact hGchar b
      · exact ((hrows K.val K.property).2.2 b.val (Multiset.mem_toFinset.mp b.property)).2
      · exact hSchar P hP (Sum.inr b)
    have hj : ∀ b : A,j b<6 := by intro b;exact Nat.mod_lt _ (by norm_num)
    have hh := htail G K.val (hrows K.val K.property) S j Pset (E.completion K) s hc₀ hNlevel hbase
      hodd hj hprod (fun P hP => (hPr P hP).1) θ X (Z^δ) QK QP r aw hX
      (Real.rpow_pos_of_pos hzpos _) hQK hQP (hKr K.val K.property).2
      (fun P hP => (hPr P hP).2.2) (hr K.val K.property) haw
    apply hh.trans
    change _ ≤ Et
    dsimp only [Et,Ctail,Cshape]
    have he : (6*‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Pset.card*
        (Ct*(1+‖θ‖)^degreeTail*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)=
      Pset.card*(6*(‖fixedRadialCoefficientScalar‖*‖s.stratumShapeFactor c₀‖)*Ct)*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹ := by ring
    rw [he]
    gcongr
    linarith only
  have hh := row_energy_le_retained (Finset.univ:Finset rows) f (fun K => Φ*g K) Et hEt (fun K _ => hrem K)
  simp only [norm_mul,mul_pow,hΦ,←Finset.mul_sum,Finset.card_univ,Fintype.card_coe] at hh
  apply hh.trans
  calc
    _ ≤ 2*(Cshape^2*(Cm*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)))+2*rows.card*Et^2 := by gcongr
    _ ≤ _ := by
      dsimp only [Et]
      have hp : 0≤(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by positivity
      nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1137

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.FullBudget
Source SHA256: 66de89623690d1b141091c4a6a627ba8e50ef1066917e32d1d4aa4000dcbfe70
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1138



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_sector_full_budget
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K)
      (E : SectorArithmetic (N:=Nlevel) G rows Pset S hrows s hc₀),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (E.completion K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨Adecay,htail⟩ := actual_finite_source_tail_budget s Lcap δ saving hδ
  obtain ⟨degree,degreeTail,Cm,Ct,Z₀,hCm,hCt,hZ₀,henergy⟩ := original_sector_full_energy
    (Nlevel:=Nlevel) Adecay ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool
  let cusp := 27*(sourceCuspScale s.index)^2*(Ideal.absNorm (Ideal.span {c₀}):ℝ)^2
  let deg := max degree (degreeTail*2)
  refine ⟨deg,Cm+2*Ct^2*cusp^4+1,max Z₀ 128,by positivity,
    lt_of_lt_of_le hZ₀ (le_max_left _ _),?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool hsmall rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hz' : 1<Z := lt_of_lt_of_le hZ₀ ((le_max_left _ _).trans hZ)
  have hzpos : 0<Z := lt_trans zero_lt_one hz'
  have h128 : 128≤Z := (le_max_right _ _).trans hZ
  have hs := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    ((le_max_left _ _).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hscap hpool hsmall
    rows Pset S hrows E hGN hGchar hrowcop hprod hScop hSN hSchar θ r aw hqk hqp hKr hPr hr haw
  have ht := htail G rows Pset Z X QK QP h128 hX hqk (by linarith only [hqp])
    (fun K hK => ⟨(hrows K hK).1,(hKr K hK).2⟩)
    (fun P hP => ⟨(hPr P hP).1.1.ne_zero,(hPr P hP).2.2⟩) hFcap hKcap hPcap hXi
  have hheight : 1≤1+‖θ‖ := by linarith only [norm_nonneg θ]
  have hdm : (1+‖θ‖)^degree≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_left _ _)
  have hdt : (1+‖θ‖)^(degreeTail*2)≤(1+‖θ‖)^deg := pow_le_pow_right₀ hheight (le_max_right _ _)
  have he := Real.rpow_le_rpow_of_exponent_le hz'.le hexp
  apply hs.trans
  have htailbound : 2*rows.card*(Pset.card*Ct*(1+‖θ‖)^degreeTail*
        ((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*(Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2≤
      (2*Ct^2*cusp^4)*(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by
    calc
      _ = (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*
          (rows.card*(Pset.card*((Ideal.absNorm (∏ b,G.ideal b):ℝ)*QK*QP)*
            (Z^δ)^(-(Adecay:ℝ))*(familyRawScale G s X QK QP^2)⁻¹)^2) := by rw [pow_mul];ring
      _ ≤ (2*Ct^2*(1+‖θ‖)^(degreeTail*2))*(cusp^4*Z^(-saving)) := by
        exact mul_le_mul_of_nonneg_left ht (by positivity)
      _ ≤ (2*Ct^2*(1+‖θ‖)^deg)*(cusp^4*Z^(F₀-3*cstar/16-O₀/2)) := by gcongr
      _ = _ := by ring
  have hmain : Cm*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)≤
      Cm*(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by gcongr
  apply (add_le_add hmain htailbound).trans
  have hp : 0≤(1+‖θ‖)^deg*Z^(F₀-3*cstar/16-O₀/2) := by positivity
  nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1138

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.GlobalBudget
Source SHA256: cb1218539a8c5309b7b0ec14946749dc3acfa71d0ffb942ac8a131fcde125525
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1139



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_global_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows Pset : Finset (Ideal Eis)) (S : Ideal Eis→PrimeFamily σ)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r aw : Ideal Eis→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ P∈Pset,‖aw P‖≤1) →
      (∑ K : rows,‖literalWholeRow G K.val (hrows K.val K.property) S j Pset
        (D K) s hc₀ W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_sector_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  let q := (Fintype.card (Eis⧸Ideal.span {Nlevel^2}):ℝ)
  have hq : 0≤q := Nat.cast_nonneg _
  refine ⟨degree,q^3*C+1,Z₀,by positivity,hZ₀,?_⟩
  intro σ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool hsmall rows Pset S hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  have hpair := (poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A
  obtain ⟨D,hD⟩ := exists_global_sector_completion G rows Pset S hrows s hc₀ hNlevel hbase hac hpair hGN
    hrowcop hprod hScop (fun P hP b => hSN P hP (Sum.inr b))
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  have hs := literal_global_sector_energy G rows Pset S hrows j D s hc₀ W θ X r aw
    (C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2)) (by
      intro r₀ p₀
      obtain ⟨E,hE⟩ := hD r₀ p₀
      refine ⟨E,hE,?_⟩
      exact henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
        Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
        hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
        heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
        hFcap hscap hpool hsmall (fullRaySector Nlevel rows r₀) (fullRaySector Nlevel Pset p₀) S
        (fun K hK => hrows K (Finset.mem_filter.mp hK).1) E hGN hGchar
        (fun K hK => hrowcop K (Finset.mem_filter.mp hK).1)
        (fun P hP => hprod P (Finset.mem_filter.mp hP).1)
        (fun P hP => hScop P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSN P (Finset.mem_filter.mp hP).1)
        (fun P hP => hSchar P (Finset.mem_filter.mp hP).1)
        θ r aw hqk hqp
        (fun K hK => hKr K (Finset.mem_filter.mp hK).1)
        (fun P hP => hPr P (Finset.mem_filter.mp hP).1)
        (fun K hK => hr K (Finset.mem_filter.mp hK).1)
        (fun P hP => haw P (Finset.mem_filter.mp hP).1))
  apply hs.trans
  change q^3*(C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2))≤_
  have hp : 0≤(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by positivity
  nlinarith only [hp]
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1139

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.MemberBudget
Source SHA256: 9bc1ec8a7fa4a9f4856e9c1acf7a168139bb64d653e46986c6205d9a41bd3011
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1140




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel a c₀ : Eis} {mode : Bool}

theorem original_member_tuple_full_budget
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c₀ mode)) (hc₀ : c₀≠0)
    (hNlevel : (9:Eis)*c₀∣Nlevel)
    (hbase : if mode then ConcretePrimeRowBridge.goodLambda^2∣a-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀-1)
    (hac : IsCoprime a c₀) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,henergy⟩ := original_global_full_budget
    (Nlevel:=Nlevel) ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hηpos
    κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro σ _ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
  dsimp only
  intro hFcap hscap hpool hsmall rows tuples hne hmax hgood hinj
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let j := fun b : A => completedLocalExponent J F b.val.val
  obtain ⟨D,hD⟩ := henergy J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hz hzcap hc hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool hsmall rows (tuples.image slotTupleProduct) (tuplePrimeFamily tuples hne hmax hgood)
    hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  have he := hD θ r (slotProductCoefficient tuples aw) hqk hqp hKr hPr hr
    (fun P hP => slotProductCoefficient_norm tuples hinj aw haw P hP)
  convert he using 1
  apply Finset.sum_congr rfl
  intro K hK
  congr 2
  exact (literalWholeRow_eq_member_tuples tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw).symm
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1140

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.MemberGeometry
Source SHA256: 7fe6a5601512da70806482bcbbd51d4db834027f22e6645af40f391ffdf8a6f8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1141




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem original_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (ε : ℝ) (hε : 0<ε) (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i)) (ρ : ℝ) (hρ : 0<ρ) (η : ℝ) (hηpos : 0<η)
    (κ δ Lscale Lpool : ℝ) (hκ : 0<κ) (hδL : 0≤δ+Lscale) (hLpool : 0≤Lpool)
    (Lcap saving : ℝ) (hδ : 0<δ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ), 0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ], ∀ (J I F B R Q₀ : Ideal Eis) (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hB : B≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot : ℝ),
      Z₀≤Z → 0<Ck → 0<CO → 0<CH → 0<Cf → 0<X → 0<QK → 0<QP →
      (Ideal.absNorm I:ℝ)≤Ck*Z^M →
      Z^O₀/CO≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      Z^H/CH≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      (Ideal.absNorm F:ℝ)≤Cf*Z^V →
      Real.log (CH*Ck*CO)/Real.log Z≤η →
      Real.log (widthConstant B Ck CO CH Cf)/Real.log Z≤η →
      CanonicalMargins F₀ M (normWidth Z R) z₀ margin → F₀=N+V →
      Nstar=N-3*hhat → V≤d → hhat≤d+η →
      H=Real.logb Z QK → za=Real.logb Z (QP/2) → Nstar=Real.logb Z X →
      0≤M → 0≤O₀ → 0≤za → za≤z₀ →
      0<cstar → cstar/2≤margin → d≤cstar/200 →
      η≤cstar/1000 → δ+η≤cstar/1000 → π≤cstar/1000 →
      QK≤Z^Lrow → (QP/2)≤Z^Lslot →
      Real.logb Z 16≤η → ε*(Lrow+Lslot+2*(δ+Lscale+η))+η/2≤π →
      X⁻¹≤Z^Lcap → QK≤Z^Lcap → QP≤Z^Lcap → -saving≤F₀-3*cstar/16-O₀/2 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lcap →
      (familyRawScale G s X QK QP)⁻¹≤Z^Lscale →
      (Ideal.absNorm (∏ b,G.ideal b):ℝ)≤Z^Lpool → κ+ρ*Lpool≤cstar/16 →
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ X r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(F₀-3*cstar/16-O₀/2) := by
  have hb (i : γ) := original_member_tuple_full_budget (Nlevel:=Nlevel)
    ε hε lo hi hlo W hWs hW (s i) (hc₀ i) (hNlevel i) (hbase i) (hac i)
    ρ hρ η hηpos κ δ Lscale Lpool hκ hδL hLpool Lcap saving hδ
  choose degree C Z₀ hC hZ₀ henergy using hb
  let degreeAll := ∑ i,degree i
  let CAll := (∑ i,C i)+1
  let ZAll := (∑ i,|Z₀ i|)+2
  have hn (i : γ) : degree i≤degreeAll := Finset.single_le_sum (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hc (i : γ) : C i≤CAll := by
    have hh : C i≤∑ j,C j := Finset.single_le_sum (fun j _ => (hC j).le) (Finset.mem_univ i)
    dsimp only [CAll]
    linarith
  have hz (i : γ) : Z₀ i≤ZAll := by
    have hh : |Z₀ i|≤∑ j,|Z₀ j| := Finset.single_le_sum (fun j _ => abs_nonneg (Z₀ j)) (Finset.mem_univ i)
    have hh' := le_abs_self (Z₀ i)
    dsimp only [ZAll]
    linarith
  have hCA : 0<CAll := by
    have hh : 0≤∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
    dsimp only [CAll]
    linarith
  have hZA : 1<ZAll := by
    have hh : 0≤∑ i,|Z₀ i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
    dsimp only [ZAll]
    linarith
  refine ⟨degreeAll,CAll,ZAll,hCA,hZA,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    hZ hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hzwidth hzcap hcstar hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool hsmall rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  obtain ⟨D,hD⟩ := henergy i J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z F₀ N V M z₀ margin cstar O₀ H za Nstar hhat d π Ck CO CH Cf X QK QP Lrow Lslot
    ((hz i).trans hZ) hCk hCO hCH hCf hX hQK hQP hk hpow hrow hf hlogH hlogT hinv hF₀ hscale hV hh
    heH heza heN hM hO hzwidth hzcap hcstar hmargin hd hη hτ hπ hrowcap hslotcap hconst hbudget hXi hKcap hPcap hexp
    hFcap hscap hpool hsmall rows tuples hne hmax hgood hinj hrows hGN hGchar hrowcop hprod hScop hSN hSchar
  refine ⟨D,?_⟩
  intro θ r aw hqk hqp hKr hPr hr haw
  apply (hD θ r aw hqk hqp hKr hPr hr haw).trans
  have hZpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZA hZ)
  have hheight : 1≤1+‖θ‖ := by linarith [norm_nonneg θ]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZpos.le _)
  exact mul_le_mul (hc i) (pow_le_pow_right₀ hheight (hn i)) (by positivity) hCA.le
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1141

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CanonicalEnergy
Source SHA256: c5e330498d8281b6574cfd7c8d18cd85a5f6f7e6c89611673bbba307b410cf78
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1142




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_member_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ i : γ,
      let a := a i
      let c₀ := c₀ i
      let mode := mode i
      let s := s i
      let hc₀ := hc₀ i
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J I F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hI : I≠0) (_hF : F≠0) (_hR : R≠0),
      rowPowerfulPart J=rowPowerfulPart I → rowMaskPart J (B*F*R)=rowMaskPart I (B*F*R) →
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d QK QP : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm I:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart I):ℝ) →
      QK/2≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) →
      1≤QK → QK≤2*Z^M → 2≤QP → QP/2≤Z^z₀ →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let j := fun b : A => completedLocalExponent J F b.val.val
    ∀ (rows : Finset (Ideal Eis)) (tuples : Finset (σ→Ideal Eis)) (hne : tuples.Nonempty)
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis))),
      let S := tuplePrimeFamily tuples hne hmax hgood
      let Pset := tuples.image slotTupleProduct
      ∀ (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ P∈Pset,(∏ b,(S P).ideal b)=P) →
      (∀ P∈Pset,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal)) →
      (∀ P∈Pset,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b)) →
      (∀ P∈Pset,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2) →
    ∃ D : ∀ K : rows,∀ P : Pset,IsCoprime K.val P.val→
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property) (S P.val)).generator Nlevel a c₀ mode,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      1≤QK → 2≤QP →
      (∀ K∈rows,QK/2≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤QK) →
      (∀ P∈Pset,CubicSieve.Admissible P ∧ QP/2≤(Ideal.absNorm P:ℝ) ∧ (Ideal.absNorm P:ℝ)≤QP) →
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖memberTupleRow tuples hmax hgood G K.val (hrows K.val K.property) hne hinj (D K) s hc₀ j W θ (Z^(N-3*hhat)) r aw‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2) := by
  let Lcap := 4*L+2
  have hLc : 0≤Lcap := by dsimp [Lcap];positivity
  obtain ⟨ε,ρ,κ,δ,π,hε,hρ,hκ,hδ,hδL,hηsmall,hδη,hπ,hbudget,hsmall⟩ :=
    canonical_reflection_parameters Lcap cstar η hLc hcstar hη hη1 hηc
  obtain ⟨degree,C,Z₁,hC,hZ₁,henergy⟩ := original_member_geometry_uniform a c₀ mode
    ε hε lo hi hlo W hWs hW s hc₀ hNlevel hbase hac ρ hρ η hη
    κ δ (7*Lcap+1) Lcap hκ hδL hLc Lcap 1 hδ
  obtain ⟨Z₂,hZ₂,hscale⟩ := geometry_source_scale_cap a c₀ mode s
  obtain ⟨Z₃,hZ₃,hwidth⟩ := width_error_threshold B hB 1 1 2 1 η
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hη
  obtain ⟨Z₄,hZ₄,hlog⟩ := constant_log_error 16 η (by norm_num) hη
  let Z₀ := max Z₁ (max Z₂ (max Z₃ (max Z₄ (max 2 (Ideal.absNorm B:ℝ)))))
  have hz1 : Z₁≤Z₀ := le_max_left _ _
  have hz2 : Z₂≤Z₀ := (le_max_left _ _).trans (le_max_right _ _)
  have hz3 : Z₃≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hz4 : Z₄≤Z₀ := (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hz5 : max 2 (Ideal.absNorm B:ℝ)≤Z₀ :=
    (le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  refine ⟨degree,C,Z₀,hC,hZ₁.trans_le hz1,?_⟩
  intro i
  dsimp only
  intro σ _ _ J I F R Q₀ hJ hI hF hR hpower hmask A
    Z N V M z₀ margin O₀ hhat d QK QP hZ hN hM hMc hVc hzc hhc
    hIn hFn hRn hO hOM hOn hKr hK1 hKc hP2 hPc hinv hmargin hVd hhd hd
  have hZ1 : 1<Z := lt_of_lt_of_le hZ₁ (hz1.trans hZ)
  have hZp : 0<Z := lt_trans zero_lt_one hZ1
  have hZ2 : 2≤Z := (le_max_left _ _).trans (hz5.trans hZ)
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_max_right _ _).trans (hz5.trans hZ)
  have hKp : 0<QK := lt_of_lt_of_le zero_lt_one hK1
  have hPp : 0<QP := by linarith
  have hPc' : QP≤2*Z^z₀ := by linarith
  obtain ⟨hFc,hKcap,hPcap,hXi⟩ := canonical_actual_arithmetic_caps L hL
    J I B F R Q₀ hJ hI hB hF hR hpower hmask A
    Z M V L z₀ N hhat QK QP hZ2 hBn hIn hFn hRn hMc hVc (le_refl _) hzc hN hhc hKc hPc'
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  have hXp : 0<Z^(N-3*hhat) := Real.rpow_pos_of_pos hZp _
  have hsc := hscale i G Z (Z^(N-3*hhat)) QK QP Lcap (hz2.trans hZ)
    hXp hKp.le hPp.le hFc hKcap hPcap hXi
  have hw := hwidth Z (hz3.trans hZ)
  have hza : 0≤Real.logb Z (QP/2) := Real.logb_nonneg hZ1 (by linarith)
  have hzac : Real.logb Z (QP/2)≤z₀ := by
    have he := Real.logb_le_logb_of_le hZ1 (by linarith : 0<QP/2) hPc
    rwa [Real.logb_rpow hZp (ne_of_gt hZ1)] at he
  have hzt : 0≤z₀ := hza.trans hzac
  have ht := canonical_reflected_target_positive (N+V) M (normWidth Z R) z₀ margin cstar O₀
    hinv hM (normWidth_nonneg Z hZ1 R hR) hzt hcstar hmargin hOM
  have hc := henergy i (σ:=σ) J I F B R Q₀ hJ hI hF hB hR hpower hmask A
    Z (N+V) N V M z₀ margin cstar O₀ (Real.logb Z QK) (Real.logb Z (QP/2))
    (N-3*hhat) hhat d π 1 1 2 1 (Z^(N-3*hhat)) QK QP Lcap Lcap
    (hz1.trans hZ) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hXp hKp hPp
    (by simpa using hIn) (by simpa using hOn) (dyadic_canonical_lower Z QK hZ1 hKp _ hKr)
    (by simpa using hFn) hw.1 hw.2 hinv rfl rfl hVd hhd rfl rfl
    (by rw [Real.logb_rpow hZp (ne_of_gt hZ1)]) hM hO hza hzac hcstar hmargin hd
    hηsmall hδη hπ hKcap (by linarith : QP/2≤Z^Lcap)
    (hlog Z (hz4.trans hZ)) hbudget hXi hKcap hPcap (by linarith : -1≤N+V-3*cstar/16-O₀/2)
    hFc hsc hFc hsmall
  exact hc
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1142

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CanonicalDyads
Source SHA256: e7cefc5b486ade4cddcdf58febcdd9c522697865bf397ec195839e3422faf6f0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1143



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_dyadic_geometry_uniform
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
      let Hslot := Z^z₀
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (tuples : Finset (σ→Ideal Eis))
      (hmax : ∀ p∈tuples,∀ i,(p i).IsMaximal)
      (hgood : ∀ p∈tuples,∀ i,ConcretePrimeRowBridge.goodLambda∉p i)
      (_hinj : Set.InjOn slotTupleProduct (↑tuples : Set (σ→Ideal Eis)))
      (hrows : ∀ K∈rows,Admissible K),
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hmax hgood p)).ideal)) →
      (∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)) →
      (∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hmax hgood p)).ideal b)≠2) →
      (∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot) →
    ∃ D : ∀ i : Fin (columnDyadicLength Hrow+1),∀ j : Fin (columnDyadicLength Hslot+1),
      CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g) G rows hrows tuples hmax hgood Hrow Hslot i j,
    ∀ (θ : ℝ) (r : Ideal Eis→ℂ) (aw : (σ→Ideal Eis)→ℂ),
      (∀ K∈rows,‖r K‖≤1) → (∀ p∈tuples,‖aw p‖≤1) →
      (∑ K : rows,‖∑ p : tuples,
        dyadicPhysicalTerm G rows hrows tuples hmax hgood Hrow Hslot D (s g) (hc₀ g) jF W θ (Z^(N-3*hhat)) r aw K p‖^2)≤
        (columnDyadicLength Hrow+1:ℝ)*(columnDyadicLength Hslot+1:ℝ)^2*
          (C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2)) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_member_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro tuples hmax hgood hinj hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
  let Hslot := Z^z₀
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let jF := fun b : A => completedLocalExponent J F b.val.val
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzp : 0<Z := lt_trans zero_lt_one hz
  have hrowNorm : ∀ K∈rows,1≤(Ideal.absNorm K:ℝ) ∧ (Ideal.absNorm K:ℝ)≤Hrow :=
    fun K hK => original_residual_norm_bounds parents J (B*F*R) hbad (Z^M) hparents K (hsub hK)
  have htupleNorm : ∀ p∈tuples,1≤(Ideal.absNorm (slotTupleProduct p):ℝ) ∧
      (Ideal.absNorm (slotTupleProduct p):ℝ)≤Hslot := fun p hp =>
    ⟨QuadraticMainBoundary.norm_one_le (primaryGenerator_ne_zero_ideal _ (hPnorm p hp).1.2),(hPnorm p hp).2⟩
  apply physical_dyad_selection_energy G rows hrows tuples hmax hgood Hrow Hslot
    (s g) (hc₀ g) jF W (Z^(N-3*hhat)) (fun θ => C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2))
    (fun θ => by positivity)
  intro i j hi hj
  let Rc := divisorDyadicBin rows Hrow i
  let Tc := activeTupleDyad tuples Hslot j
  let hm := fun p hp k => hmax p (activeTupleDyad_subset tuples Hslot j hp) k
  let hg := fun p hp k => hgood p (activeTupleDyad_subset tuples Hslot j hp) k
  have hTc : Tc.Nonempty := hj
  have hRi : ∀ K∈Rc,Admissible K := fun K hK => hrows K (divisorDyadicBin_subset rows Hrow i hK)
  have hti : Set.InjOn slotTupleProduct (↑Tc : Set (σ→Ideal Eis)) :=
    hinj.mono (activeTupleDyad_subset tuples Hslot j)
  have hKr := divisorDyadicBin_bounds rows Hrow hrowNorm i
  have hPr := activeTupleDyad_bounds tuples Hslot htupleNorm j
  obtain ⟨K,hK⟩ := hi
  obtain ⟨I,hI,heI⟩ := Finset.mem_image.mp (hsub (divisorDyadicBin_subset rows Hrow i hK))
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  have hI0 := (hparents I hIp).1
  have hIn := (hparents I hIp).2
  have hKlower : (2*divisorDyadicScale i.val)/2≤(Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ) := by
    rw [heI]
    convert (hKr K hK).1 using 1 ; ring
  have hKupper : 2*divisorDyadicScale i.val≤2*Z^M := by
    have hres : (Ideal.absNorm (rowResidualPart I (B*F*R)):ℝ)≤(Ideal.absNorm I:ℝ) := by
      rw [rowResidualPart_norm I (B*F*R) hI0]
      apply div_le_self (Nat.cast_nonneg _)
      exact one_le_mul_of_one_le_of_one_le
        (QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero I))
        (QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart I) (B*F*R)))
    have hs := hKlower.trans (hres.trans hIn)
    linarith
  have hPupper : (2*divisorDyadicScale j.val)/2≤Z^z₀ := by
    convert activeTupleDyad_scale_le tuples Hslot htupleNorm j hj using 1 ; dsimp [Hslot] ; ring
  let S := tuplePrimeFamily Tc hTc hm hg
  have hScop : ∀ P∈Tc.image slotTupleProduct,Pairwise (Function.onFun IsCoprime (G.sum (S P)).ideal) := by
    intro P hP
    exact hpair ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSN : ∀ P∈Tc.image slotTupleProduct,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (S P)).ideal b) := by
    intro P hP
    exact hPN ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  have hSchar : ∀ P∈Tc.image slotTupleProduct,∀ b,ringChar (Eis⧸(G.sum (S P)).ideal b)≠2 := by
    intro P hP
    exact hPchar ⟨tupleRepresentative Tc hTc P,activeTupleDyad_subset tuples Hslot j (tupleRepresentative_mem Tc hTc P)⟩
  obtain ⟨D,hD⟩ := he g J I F R Q₀ hJ hI0 hF hR hpow.symm hmask.symm A
    Z N V M z₀ margin O₀ hhat d (2*divisorDyadicScale i.val) (2*divisorDyadicScale j.val)
    hZ hN hM hMc hVc hzc hhc hIn hFn hRn hO hOM (by rw [hpow];exact hOn) hKlower
    (by linarith [divisorDyadicScale_ge_one i.val]) hKupper
    (by linarith [divisorDyadicScale_ge_one j.val]) hPupper hinv hmargin hVd hhd hd
    Rc Tc hTc hm hg hti hRi hGN hGchar
    (fun K hK => hrowcop K (divisorDyadicBin_subset rows Hrow i hK))
    (tuplePrimeFamily_product Tc hTc hm hg) hScop hSN hSchar
  let Dc : CellCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
      G rows hrows tuples hmax hgood Hrow Hslot i j := fun K p hp =>
    memberTupleControlled Tc hm hg G K.val (hRi K.val K.property) hTc hti (D K) p hp
  refine ⟨Dc,?_⟩
  intro θ r aw hr haw
  have hb := hD θ r aw (by linarith [divisorDyadicScale_ge_one i.val])
    (by linarith [divisorDyadicScale_ge_one j.val])
    (fun K hK => by convert hKr K hK using 1 ; ring_nf)
    (by
      intro P hP
      obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hP
      refine ⟨(hPnorm p (activeTupleDyad_subset tuples Hslot j hp)).1,?_⟩
      convert hPr p hp using 1 ; ring_nf)
    (fun K hK => hr K (divisorDyadicBin_subset rows Hrow i hK))
    (fun p hp => haw p (activeTupleDyad_subset tuples Hslot j hp))
  exact hb
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1143

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CanonicalChoiceEnergy
Source SHA256: 50339ed6e48b0836ffe9290bfcbc850057786eb2df1cacf542d91400ecf6b7ab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1144




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_original_choice_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ K : rows,∀ p : supportedSlotChoices lists (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily lists hmax hgood p.val)).generator Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ p : supportedSlotChoices lists (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
        (∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) σ)
          (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_dyadic_geometry_uniform a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  obtain ⟨Cb,hCb,hbins⟩ := actual_dyad_count_budget L (cstar/32) hL (by positivity)
  refine ⟨degree,Cb*C,Z₀,mul_pos hCb hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH hprod hGN hGchar hrowcop hLN hLchar
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let FF := (poolPrimeFamily J (B*F*R) Q₀).ideal
  let tuples := fixedSlotTupleSet lists FF
  let hm := originalTupleMax lists FF hmax
  let hg := originalTupleGood lists FF hgood
  have htuples : ∀ p∈tuples,∀ i,p i∈lists i := fun p hp => ((mem_fixedSlotTupleSet lists FF p).mp hp).1
  have hpair : ∀ p : tuples,Pairwise (Function.onFun IsCoprime (G.sum (memberTupleFamily tuples hm hg p)).ideal) := by
    intro p
    apply PrimeFamily.sum_pairwise G _ ((poolPrimeFamily J (B*F*R) Q₀).restrict_pairwise (poolPrimeFamily_pairwise J (B*F*R) Q₀) A)
    · intro i j hij
      apply Ideal.isCoprime_of_isMaximal
      intro heq
      change p.val i=p.val j at heq
      exact Finset.disjoint_left.mp (hdis hij) (htuples p.val p.property i)
        (heq.symm ▸ htuples p.val p.property j)
    · intro f i
      apply Ideal.isCoprime_of_isMaximal
      exact (((mem_fixedSlotTupleSet lists FF p.val).mp p.property).2 f.val i).symm
  have hPN : ∀ p : tuples,∀ b,IsCoprime (Ideal.span {Nlevel}) ((G.sum (memberTupleFamily tuples hm hg p)).ideal b) := by
    intro p b
    cases b with
    | inl f => exact hGN f
    | inr i => exact hLN i _ (htuples p.val p.property i)
  have hPchar : ∀ p : tuples,∀ b,ringChar (Eis⧸(G.sum (memberTupleFamily tuples hm hg p)).ideal b)≠2 := by
    intro p b
    cases b with
    | inl f => exact hGchar f
    | inr i => exact hLchar i _ (htuples p.val p.property i)
  have hPnorm : ∀ p∈tuples,CubicSieve.Admissible (slotTupleProduct p) ∧ (Ideal.absNorm (slotTupleProduct p):ℝ)≤Z^z₀ := by
    intro p hp
    refine ⟨slotTupleProduct_admissible lists hdis hprime ?_ p (htuples p hp),?_⟩
    · intro i P hPi
      let : P.IsMaximal := hmax i P hPi
      exact (primaryPrime_eq_primaryGenerator P).symm ▸ primaryPrime_ne_zero P (hgood i P hPi)
    · exact (slotTupleProduct_norm_bound lists H (fun i P hPi => (hprime i P hPi).ne_zero) hH p (htuples p hp)).2.trans hprod
  let Hrow := Z^M/((Ideal.absNorm (rowPowerfulPart J):ℝ)*(Ideal.absNorm (rowMaskPart J (B*F*R)):ℝ))
  let Hslot := Z^z₀
  obtain ⟨Dc,hDc⟩ := he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
    hZ hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
    parents rows hparents hsub hbad tuples hm hg (fixedSlotTupleSet_product_injective lists FF hdis hprime)
    hrows hGN hGchar hrowcop hpair hPN hPchar hPnorm
  let D := fun (K : rows) (p : supportedSlotChoices lists FF K.val) =>
    memberChoiceControlled lists FF hmax hgood G K.val (hrows K.val K.property)
      (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K) p
  refine ⟨D,?_⟩
  intro θ w hw
  have hsource (K : rows) :
      (∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc (s g) (hc₀ g)
        (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(N-3*hhat)) (fun _ => 1)
        (fixedTupleCoefficient lists w) K p)=
      ∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) := by
    simpa only [dyadicPhysicalTerm,D,one_mul] using member_source_eq_original_choices lists FF hmax hgood G K.val
      (hrows K.val K.property) (dyadicTupleControlled G rows hrows tuples hm hg Hrow Hslot Dc K)
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) 1 w
  have hb := hDc θ (fun _ => 1) (fixedTupleCoefficient lists w) (by simp) (fun p hp => fixedTupleCoefficient_norm lists w hw p)
  have hid : (∑ K : rows,‖∑ p : tuples,dyadicPhysicalTerm G rows hrows tuples hm hg Hrow Hslot Dc
      (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val) W θ (Z^(N-3*hhat))
      (fun _ => 1) (fixedTupleCoefficient lists w) K p‖^2)=
      ∑ K : rows,‖∑ p : supportedSlotChoices lists FF K.val,(∏ i,w i (p.val i))*mixedReflectedValue (D K p) (s g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_ne_zero (hc₀ g)
        (G.reflected K.val (hrows K.val K.property) (slotChoiceFamily lists hmax hgood p.val)).generator_good
        (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) σ)
        (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))‖^2 := by
    apply Finset.sum_congr rfl
    intro K hK
    exact congrArg (fun z : ℂ => ‖z‖^2) (hsource K)
  apply (hid.symm.trans_le hb).trans
  have hz : 1<Z := lt_of_lt_of_le hZ₀ hZ
  have hzpos : 0<Z := lt_trans zero_lt_one hz
  have hp : (1:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := QuadraticMainBoundary.norm_one_le (rowPowerfulPart_ne_zero J)
  have hm' : (1:ℝ)≤Ideal.absNorm (rowMaskPart J (B*F*R)) :=
    QuadraticMainBoundary.norm_one_le (squarefreeMaskPart_ne_zero (rowSimplePart J) (B*F*R))
  have hRpos : 0<Hrow := by dsimp [Hrow];positivity
  have hScap : Hslot≤Z^L := Real.rpow_le_rpow_of_exponent_le hz.le hzc
  have hRcap : Hrow≤Z^L := by
    exact (div_le_self (Real.rpow_nonneg hzpos.le _) (one_le_mul_of_one_le_of_one_le hp hm')).trans
      (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
  have hcount := hbins Z Hrow Hslot hz.le hRpos (Real.rpow_pos_of_pos hzpos _) hRcap hScap
  calc
    _ ≤ (Cb*Z^(cstar/32))*(C*(1+‖θ‖)^degree*Z^(N+V-3*cstar/16-O₀/2)) :=
      mul_le_mul_of_nonneg_right hcount (by positivity)
    _ = (Cb*C)*(1+‖θ‖)^degree*Z^(cstar/32+(N+V-3*cstar/16-O₀/2)) := by
      rw [Real.rpow_add hzpos];ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1144

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CanonicalInactiveEnergy
Source SHA256: 14e10baf53b6f186f3b11f10051093eda16b8662632e77f51ebd6d3a1a3cec06
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1145



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

lemma inactiveRows_mem {σ φ : Type*} [Fintype σ] [DecidableEq σ]
    (rows : Finset (Ideal Eis)) (lists : σ→Finset (Ideal Eis)) (T : Finset σ)
    (FF : φ→Ideal Eis) (b : ∀ i : {i // i∉T},lists i.val) (K : Ideal Eis) :
    K∈inactiveRowSet rows lists T FF b ↔ K∈rows ∧
      IsCoprime K (∏ i : {i // i∉T},(b i).val) ∧ ∀ j i,(b i).val≠FF j := by
  exact Finset.mem_filter

theorem canonical_original_inactive_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ g : γ,∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (A : Finset (FreeReflection.pool J (B*F*R) Q₀))
      (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
      let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
      let jF := fun b : A => completedLocalExponent J F b.val.val
    ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) (G.ideal f)) →
      (∀ f,ringChar (Eis⧸G.ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime (G.ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∀ T : Finset σ,
    ∃ D : ∀ K : rows,
      ∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator
          Nlevel (a g) (c₀ g) (mode g),
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ), (∀ i P,‖w i P‖≤1) →
      (∑ K : rows,‖∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val)
        (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
        ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
        ∑ p : supportedSlotChoices (fun i : T => lists i.val) (poolPrimeFamily J (B*F*R) Q₀).ideal K.val,
          (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
          (G.reflected K.val (hrows K.val K.property)
            (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
          (reflectedExponent jF) (slotIndices A (PrimeIndex K.val) T)
          (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))‖^2)≤
        (∏ i : {i // i∉T},256*(columnDyadicLength (H i.val)+1:ℝ))^2*
          (C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2)) := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_original_choice_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro g σ _ _ J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
  dsimp only
  intro lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar T
  let G := (poolPrimeFamily J (B*F*R) Q₀).restrict A
  let FF := (poolPrimeFamily J (B*F*R) Q₀).ideal
  let rowsb := fun b : ∀ i : {i // i∉T},lists i.val => inactiveRowSet rows lists T FF b
  have hbsub (b : ∀ i : {i // i∉T},lists i.val) : rowsb b⊆rows := by
    intro K hK
    exact ((inactiveRows_mem rows lists T FF b K).mp hK).1
  have hbr (b : ∀ i : {i // i∉T},lists i.val) : ∀ K∈rowsb b,Admissible K := fun K hK => hrows K (hbsub b hK)
  have hdisT : Pairwise (fun i j : T => Disjoint (lists i.val) (lists j.val)) := by
    intro i j hij
    exact hdis (fun hv => hij (Subtype.ext hv))
  have hpT : (∏ i : T,H i.val)≤Z^z₀ := by
    rw [Finset.prod_coe_sort]
    apply le_trans _ hprod
    exact Finset.prod_le_prod_of_subset_of_one_le₀ (Finset.subset_univ T)
      (fun i _ => zero_le_one.trans (hH1 i)) (fun i _ _ => hH1 i)
  have hall := fun b : ∀ i : {i // i∉T},lists i.val =>
    he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
      hZ hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
      parents (rowsb b) hparents ((hbsub b).trans hsub) hbad
      (fun i : T => lists i.val) (fun i : T => H i.val) hdisT
      (fun i => hmax i.val) (fun i => hgood i.val) (fun i => hprime i.val) (hbr b)
      (fun i => hH i.val) hpT hGN hGchar (fun K hK => hrowcop K (hbsub b hK))
      (fun i => hLN i.val) (fun i => hLchar i.val)
  choose Db hDb using hall
  let D := fun (K : rows)
    (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val)
    (p : supportedSlotChoices (fun i : T => lists i.val) FF K.val) =>
      Db b.val ⟨K.val,(inactiveRows_mem rows lists T FF b.val K.val).mpr ⟨K.property,b.property⟩⟩ p
  refine ⟨D,?_⟩
  intro θ w hw
  let f := fun (K : rows) (b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val) =>
    ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) (s g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero (hc₀ g)
      (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
      (reflectedExponent (fun b : A => completedLocalExponent J F b.val.val)) (slotIndices A (PrimeIndex K.val) T)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat))
  have hzpos : 0<Z := lt_trans zero_lt_one (lt_of_lt_of_le hZ₀ hZ)
  apply supported_inactive_source_energy rows lists T FF H (fun i P hP => (hprime i P hP).ne_zero)
    hH w hw f (C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2)) (by positivity)
  intro b
  exact hDb b θ (fun i : T => w i.val) (fun i P => hw i.val P)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1145

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.SourcePhysical
Source SHA256: 38a90282bc1184d5282c79d3a6796749ebe8e2740ea5596b4f40bcebbc81918d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1146


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ φ τ : Type*} [Fintype σ] [DecidableEq σ] [Fintype τ]
variable {N a c : Eis} {mode : Bool}
variable (G : PrimeFamily τ) (FF : φ→Ideal Eis) (rows : Finset (Ideal Eis)) (hrows : ∀ K∈rows,Admissible K)
    (lists : σ→Finset (Ideal Eis)) (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) (T : Finset σ)

abbrev OriginalSplitCompletion :=
    ∀ K : rows,∀ _b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ∀ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
      ControlledStratumArithmetic (G.reflected K.val (hrows K.val K.property)
        (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator N a c mode

def originalInactivePhysical
    (D : OriginalSplitCompletion (N:=N) (a:=a) (c:=c) (mode:=mode) G FF rows hrows lists hmax hgood T)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c≠0)
    (jF : τ→ℕ) (W : ℝ→ℂ) (X : ℝ) (w : ∀ i,lists i→ℂ) (K : rows) : ℂ :=
    ∑ b : supportedSlotChoices (fun i : {i // i∉T} => lists i.val) FF K.val,
      ((∏ i : {i // i∉T},(Ideal.absNorm (b.val i).val:ℂ)⁻¹)*(∏ i : {i // i∉T},w i.val (b.val i)))*
      ∑ p : supportedSlotChoices (fun i : T => lists i.val) FF K.val,
        (∏ i : T,w i.val (p.val i))*mixedReflectedValue (D K b p) s
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_ne_zero hc
        (G.reflected K.val (hrows K.val K.property)
          (slotChoiceFamily (fun i : T => lists i.val) (fun i => hmax i.val) (fun i => hgood i.val) p.val)).generator_good
        (reflectedExponent jF) (slotIndices τ (PrimeIndex K.val) T) W X
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1146

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CanonicalFrozenEnergy
Source SHA256: aaa7a653efdb960c9454de5cafc82c2f4a12a7038ba56487871f8cb854ab9c4c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1147



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v
variable {Nlevel : Eis}

theorem canonical_original_frozen_energy
    {γ : Type*} [Fintype γ] (a c₀ : γ→Eis) (mode : γ→Bool)
    [Fintype (Eis⧸Ideal.span {Nlevel^2})]
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (s : ∀ i,FixedCuspShape (ControlledStratumArithmetic.fixedCusp (a i) (c₀ i) (mode i))) (hc₀ : ∀ i,c₀ i≠0)
    (hNlevel : ∀ i,(9:Eis)*c₀ i∣Nlevel)
    (hbase : ∀ i,if mode i then ConcretePrimeRowBridge.goodLambda^2∣a i-1 else ConcretePrimeRowBridge.goodLambda^2∣c₀ i-1)
    (hac : ∀ i,IsCoprime (a i) (c₀ i))
    (B : Ideal Eis) (hB : B≠0) (L cstar η : ℝ)
    (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η) (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F R Q₀ : Ideal Eis)
      (_hJ : J≠0) (_hF : F≠0) (_hR : R≠0),
    ∀ (Z N V M z₀ margin O₀ hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm J:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm R:ℝ)≤Z^L →
      0≤O₀ → O₀≤M → Z^O₀≤(Ideal.absNorm (rowPowerfulPart J):ℝ) →
      CanonicalMargins (N+V) M (normWidth Z R) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents rows : Finset (Ideal Eis)),
      (∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      rows⊆originalResidualRows parents J (B*F*R) →
      (∀ P∈fixedBadPrimes,P∣B*F*R) →
    Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ)
      (_hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
      (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
      (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
      (_hprime : ∀ i,∀ P∈lists i,Prime P)
      (hrows : ∀ K∈rows,Admissible K),
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
      (∀ f,IsCoprime (Ideal.span {Nlevel}) ((poolPrimeFamily J (B*F*R) Q₀).ideal f)) →
      (∀ f,ringChar (Eis⧸(poolPrimeFamily J (B*F*R) Q₀).ideal f)≠2) →
      (∀ K∈rows,(∀ f,IsCoprime ((poolPrimeFamily J (B*F*R) Q₀).ideal f) K) ∧ IsCoprime (Ideal.span {Nlevel}) K) →
      (∀ i,∀ P∈lists i,IsCoprime (Ideal.span {Nlevel}) P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
    ∃ D : ∀ g : γ,∀ A : Finset (FreeReflection.pool J (B*F*R) Q₀),∀ T : Finset σ,
      OriginalSplitCompletion (N:=Nlevel) (a:=a g) (c:=c₀ g) (mode:=mode g)
        ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (poolPrimeFamily J (B*F*R) Q₀).ideal
        rows hrows lists hmax hgood T,
    ∀ (θ : ℝ) (w : ∀ i,lists i→ℂ) (scalar : γ → rows → ℂ),
      (∀ i P,‖w i P‖≤1) → (∀ g K,‖scalar g K‖≤1) →
      (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
        ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J (B*F*R) Q₀).restrict A) (poolPrimeFamily J (B*F*R) Q₀).ideal
            rows hrows lists hmax hgood T (D g A T) (s g) (hc₀ g)
            (fun b : A => completedLocalExponent J F b.val.val)
            (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K‖^2)≤
        C*(1+‖θ‖)^degree*Z^(N+V-cstar/16-O₀/2) := by
  obtain ⟨degree,C,Z₁,hC,hZ₁,he⟩ := canonical_original_inactive_energy a c₀ mode lo hi hlo W hWs hW
    s hc₀ hNlevel hbase hac B hB L cstar η hL hcstar hη hη1 hηc
  let ε := cstar/(32*(4*L+2))
  have hε : 0<ε := div_pos hcstar (by positivity)
  obtain ⟨Cb,hCb,hcost⟩ := original_source_cost_budget (χ:=γ) rmax ε hε
  let Z₀ := max Z₁ (Ideal.absNorm B:ℝ)
  refine ⟨degree,(‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C,Z₀,by positivity,hZ₁.trans_le (le_max_left _ _),?_⟩
  intro σ _ _ J F R Q₀ hJ hF hR Z N V M z₀ margin O₀ hhat d hZ hN hM hMc hVc hzc hhc
    hJn hFn hRn hO hOM hOn hinv hmargin hVd hhd hd parents rows hparents hsub hbad
    hcard lists H hdis hmax hgood hprime hrows hH1 hH hprod hGN hGchar hrowcop hLN hLchar
  have hz1 : Z₁≤Z := (le_max_left _ _).trans hZ
  have hz : 1<Z := lt_of_lt_of_le hZ₁ hz1
  have hzp : 0<Z := lt_trans zero_lt_one hz
  let FF := (poolPrimeFamily J (B*F*R) Q₀).ideal
  have hall := fun (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) =>
    he g J F R Q₀ hJ hF hR A Z N V M z₀ margin O₀ hhat d
      hz1 hN hM hMc hVc hzc hhc hFn hRn hO hOM hOn hinv hmargin hVd hhd hd
      parents rows hparents hsub hbad lists H hdis hmax hgood hprime hrows hH1 hH hprod
      (fun f => hGN f.val) (fun f => hGchar f.val)
      (fun K hK => ⟨fun f => (hrowcop K hK).1 f.val,(hrowcop K hK).2⟩) hLN hLchar T
  choose D hD using hall
  refine ⟨D,?_⟩
  intro θ w scalar hw hscalar
  let energy := C*(1+‖θ‖)^degree*Z^(N+V-cstar/8-O₀/2)
  let harm := (∏ i,256*(columnDyadicLength (H i)+1:ℝ))^2
  let source := fun (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) (K : rows) =>
    originalInactivePhysical ((poolPrimeFamily J (B*F*R) Q₀).restrict A) FF rows hrows lists hmax hgood T
      (D g A T) (s g) (hc₀ g) (fun b : A => completedLocalExponent J F b.val.val)
      (CompletedHeight.normTwistedSource W θ) (Z^(N-3*hhat)) w K
  have hs (g : γ) (A : Finset (FreeReflection.pool J (B*F*R) Q₀)) (T : Finset σ) :
      (∑ K : rows,‖source g A T K‖^2)≤harm*energy := by
    apply (hD g A T θ w hw).trans
    apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
    apply pow_le_pow_left₀ (by positivity)
    exact subtype_product_le_full (fun i => i∉T) (fun i => 256*(columnDyadicLength (H i)+1:ℝ)) (fun i => by have hn : (0:ℝ)≤columnDyadicLength (H i) := Nat.cast_nonneg _; linarith)
  let Labels := γ×(Finset (FreeReflection.pool J (B*F*R) Q₀)×Finset σ)
  let f := fun (b : Labels) (K : rows) => (scalar b.1 K*frozenInactiveWeight J F (B*F*R) Q₀ b.2.1)*source b.1 b.2.1 b.2.2 K
  have hf (b : Labels) : (∑ K : rows,‖f b K‖^2)≤harm*energy := by
    apply (bounded_row_multiplier_energy Finset.univ _ _ (fun K hK => ?_)).trans (hs b.1 b.2.1 b.2.2)
    rw [norm_mul]
    exact (mul_le_mul (hscalar b.1 K) (frozenInactiveWeight_norm J F (B*F*R) Q₀ b.2.1)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  have hfam := weighted_finite_row_energy_uniform (Finset.univ : Finset Labels) (Finset.univ : Finset rows)
    (fun _ => (1:ℂ)) f (harm*energy) (fun b _ => hf b)
  simp only [one_mul,norm_one,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hfam
  have hid (K : rows) : (∑ b : Labels,f b K)=∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
        ∑ T : Finset σ,source g A T K := by
    simp only [Labels,f,Fintype.sum_prod_type,Finset.mul_sum,mul_assoc]
  have hsource : (∑ K : rows,‖thetaDerivativeScalar⁻¹*∑ g : γ,scalar g K*
      ∑ A : Finset (FreeReflection.pool J (B*F*R) Q₀),frozenInactiveWeight J F (B*F*R) Q₀ A*
        ∑ T : Finset σ,source g A T K‖^2)≤
      ‖thetaDerivativeScalar⁻¹‖^2*(Fintype.card Labels:ℝ)^2*harm*energy := by
    simp_rw [←hid]
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact (mul_le_mul_of_nonneg_left hfam (sq_nonneg _)).trans_eq (by ring)
  apply hsource.trans
  have hBn : (Ideal.absNorm B:ℝ)≤Z := (le_max_right _ _).trans hZ
  have hmaskn := canonical_mask_norm_cap B F R Z V L L hz.le hBn hFn hRn hVc (le_refl _)
  have hJn' : (Ideal.absNorm J:ℝ)≤Z^L := hJn.trans (Real.rpow_le_rpow_of_exponent_le hz.le hMc)
  have hpool : (Ideal.absNorm (J*(B*F*R)):ℝ)≤Z^(3*L+1) := by
    rw [map_mul,Nat.cast_mul]
    calc
      _ ≤ Z^L*Z^(2*L+1) := mul_le_mul hJn' hmaskn (Nat.cast_nonneg _) (Real.rpow_nonneg hzp.le _)
      _ = _ := by rw [←Real.rpow_add hzp];congr 1;ring
  have hbudget : ε*((3*L+1)+L)≤cstar/32 := by
    have heq : ε*(4*L+2)=cstar/32 := by dsimp [ε];field_simp
    have hh := mul_le_mul_of_nonneg_left (show (3*L+1)+L≤4*L+2 by linarith) hε.le
    rwa [heq] at hh
  have hcst := hcost H hcard hH1 J (B*F*R) Q₀ hJ (mul_ne_zero (mul_ne_zero hB hF) hR)
    Z (3*L+1) L (cstar/32) hz hpool
    (hprod.trans (Real.rpow_le_rpow_of_exponent_le hz.le hzc)) hbudget
  calc
    _ = ‖thetaDerivativeScalar⁻¹‖^2*((Fintype.card Labels:ℝ)^2*harm)*energy := by ring
    _ ≤ (‖thetaDerivativeScalar⁻¹‖^2+1)*(Cb*Z^(cstar/32))*energy := by
      apply mul_le_mul_of_nonneg_right _ (by dsimp [energy];positivity)
      exact mul_le_mul (by linarith) hcst (by dsimp [harm];positivity) (by positivity)
    _ = ((‖thetaDerivativeScalar⁻¹‖^2+1)*Cb*C)*(1+‖θ‖)^degree*
        Z^(cstar/32+(N+V-cstar/8-O₀/2)) := by
      dsimp only [energy]
      rw [Real.rpow_add hzp]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hz.le (by linarith)) (by positivity)
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1147

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CompletedFiberSource
Source SHA256: 2d62873a79aed266ba71dac61e92d7f486169e5a85cf2739ed7a4619153734cd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1148




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {σ : Type*} [Fintype σ] [DecidableEq σ]
variable (parents : Finset (Ideal Eis)) (J F : Ideal Eis) (hJ : J≠0) (hF : Squarefree F)
    (m : Eis) (hm : m≠0) (hparents : ∀ I∈parents,I≠0) (v : Eisˣ)
    (hbad : ∀ P∈fixedBadPrimes,P∣Ideal.span {m}*F)

def residualOriginalData (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    GoodMaskRowData m (ConcretePrimeRowBridge.idealGenerator F)
      (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)) :=
  fiberGoodMaskRowData parents J F m hm hF.ne_zero hparents v
    ⟨reconstructFiberRow J (Ideal.span {m}*F) K.val,
      (originalResidualRows_reconstruct parents J (Ideal.span {m}*F) hparents K.val K.property).1⟩

variable (Q : Ideal Eis) (hQ : Q≠0) (c : Eis) (hc : c≠0)
    [Fintype (Eis⧸Ideal.span {c})]
    (hcQ : Ideal.span {c}=Ideal.span {(9:Eis)}*(Q*Ideal.span {(72:Eis)}))
    (G : ∀ h : Eis⧸Ideal.span {c},FixedFourierGeometry c h)
    (hcop : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),IsCoprime (Q*Ideal.span {(72:Eis)}) K)
    (lists : σ→Finset (Ideal Eis))
    (hmax : ∀ i,∀ P∈lists i,P.IsMaximal)
    (hgood : ∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P)
    (hdis : Pairwise (fun i j => Disjoint (lists i) (lists j)))
    (hodd : ∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2)
    (hperiod : ∀ i,∀ P∈lists i,IsCoprime (Q*Ideal.span {(72:Eis)}) P)

abbrev originalResidualAdmissible : ∀ K∈originalResidualRows parents J (Ideal.span {m}*F),Admissible K := by
  intro K hK
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  exact rowResidualPart_admissible I _ hbad

variable (D : ∀ h : Eis⧸Ideal.span {c},∀ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
    ∀ T : Finset σ,OriginalSplitCompletion (N:=(9:Eis)*c) (a:=(G h).a0) (c:=(G h).c0) (mode:=(G h).mode)
      ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
      (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
      (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
      lists hmax hgood T)

include hJ hQ hcQ hcop hdis hodd hperiod

theorem original_completed_residual_source
    (Ψ : Eis→*ℂ) (hΨnorm : ∀ n,‖Ψ n‖≤1) (hΨperiod : CanonicalCoefficientClass.FactorsModulo Q Ψ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:Eis)∣m)
    (W : ℝ→ℂ) (hWcompact : HasCompactSupport W) (lo hi : ℝ) (hlo : 0<lo)
    (hsupp : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W) (X : ℝ) (hX : 0<X)
    (w : ∀ i,lists i→ℂ) (K : originalResidualRows parents J (Ideal.span {m}*F)) :
    (∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
      (rowTwist Ψ m (ConcretePrimeRowBridge.idealGenerator F)
        (v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val))) W X
      (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0))=
    thetaDerivativeScalar⁻¹*∑ h : Eis⧸Ideal.span {c},
      fixedThetaRowCoeff c hc ((residualOriginalData parents J F hF m hm hparents v K).fixedFactor Ψ Q) h*
        ∑ A : Finset (FreeReflection.pool J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})),
          frozenInactiveWeight J F (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)}) A*
          ∑ T : Finset σ,originalInactivePhysical
            ((poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).restrict A)
            (poolPrimeFamily J (Ideal.span {m}*F) (Q*Ideal.span {(72:Eis)})).ideal
            (originalResidualRows parents J (Ideal.span {m}*F)) (originalResidualAdmissible parents J F m hbad)
            lists hmax hgood T (D h A T) (G h).shape (G h).denominator_ne_zero
            (fun b : A => completedLocalExponent J F b.val.val) W X w K := by
  rcases K with ⟨K,hK⟩
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hK
  have hI0 := hparents I (Finset.mem_filter.mp hI).1
  have hrec := reconstructFiberRow_of_original parents J (Ideal.span {m}*F) I hI hI0
  obtain ⟨hIp,hpow,hmask⟩ := Finset.mem_filter.mp hI
  let K : originalResidualRows parents J (Ideal.span {m}*F) :=
    ⟨rowResidualPart I (Ideal.span {m}*F),Finset.mem_image.mpr ⟨I,Finset.mem_filter.mpr ⟨hIp,hpow,hmask⟩,rfl⟩⟩
  let D0 := residualOriginalData parents J F hF m hm hparents v K
  have hz : Ideal.span {v.val*ConcretePrimeRowBridge.idealGenerator (reconstructFiberRow J (Ideal.span {m}*F) K.val)}=I := by
    rw [Ideal.span_singleton_mul_left_unit v.isUnit,ConcretePrimeRowBridge.span_idealGenerator]
    exact hrec
  have hS : ∀ p : ∀ i,lists i,Pairwise (Function.onFun IsCoprime (slotChoiceFamily lists hmax hgood p).ideal) := by
    intro p i j hij
    apply Ideal.isCoprime_of_isMaximal
    intro he
    change (p i).val=(p j).val at he
    exact Finset.disjoint_left.mp (hdis hij) (p i).property (he.symm ▸ (p j).property)
  have he := actual_marked_active_reflection D0 J I F Q hJ hI0 hF hm
    (ConcretePrimeRowBridge.span_idealGenerator F) hz hbad
    (hcop K.val K.property) hpow.symm hmask.symm lists hmax hgood hS
    (fun p i => hodd i _ (p i).property) Ψ hΨnorm hQ hΨperiod hmLam hm2 c hc hcQ.le G ((9:Eis)*c)
    (fun h => mul_dvd_mul_left (9:Eis) (G h).denominator_dvd)
    (fun p => markedRowFamily_period D0 (slotChoiceFamily lists hmax hgood p) Q
      (fun i => hperiod i _ (p i).property) c hcQ)
    (fun h A T b p => D h A T K b p)
    w W hWcompact lo hi hlo hsupp hW X hX
  exact he
end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule1148

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.CompletedCanonicalEnergy
Source SHA256: 3f35018ad5a1574d8bc48ffd977fe47f7d70f5c1829f34a5a0a9bd8a1611a983
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1149




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators ContDiff
open ActualEisensteinCubic CubicEisenstein CompletedGauss CompletedDyadic CanonicalQuadraticSieve CanonicalRowCompletion InverseTerminalWidths InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
universe v

lemma maximal_prime_level_coprime (P : Ideal Eis) (hP : P.IsMaximal)
    (hg : ConcretePrimeRowBridge.goodLambda∉P) (Q₀ : Ideal Eis) (c : Eis)
    (hc : Ideal.span {c}=Ideal.span {(9:Eis)}*Q₀) (hQ : IsCoprime Q₀ P) :
    IsCoprime (Ideal.span {(9:Eis)*c}) P := by
  let S : PrimeFamily Unit := ⟨fun _ => P,fun _ => hP,fun _ => hg⟩
  exact S.level_coprime Q₀ c hc (fun _ => hQ) ()

lemma original_powerful_norm_le (J : Ideal Eis) (hJ : J≠0) :
    (Ideal.absNorm (rowPowerfulPart J):ℝ)≤(Ideal.absNorm J:ℝ) := by
  have he := congrArg (fun I : Ideal Eis => (Ideal.absNorm I:ℝ)) (row_powerful_simple_product J hJ)
  simp only [map_mul,Nat.cast_mul] at he
  have hs := QuadraticMainBoundary.norm_one_le (rowSimplePart_ne_zero J)
  have hp : (0:ℝ)≤Ideal.absNorm (rowPowerfulPart J) := Nat.cast_nonneg _
  nlinarith

theorem canonical_completed_fiber_energy (q : ℕ) (hq : q≠0)
    (lo hi : ℝ) (hlo : 0<lo)
    (W : ℝ→ℂ) (hWs : Function.support W⊆Set.Icc lo hi) (hW : ContDiff ℝ ∞ W)
    (L cstar η : ℝ) (hL : 0≤L) (hcstar : 0<cstar) (hη : 0<η)
    (hη1 : η≤1) (hηc : η≤cstar/100000) (rmax : ℕ) :
    ∃ (degree : ℕ) (C Z₀ : ℝ),0<C ∧ 1<Z₀ ∧
    ∀ {σ : Type v} [Fintype σ] [DecidableEq σ],∀ (J F : Ideal Eis) (_hJ : J≠0) (_hF : Squarefree F)
      (m : Eis) (_hm : m≠0) (Z N V M z₀ margin hhat d : ℝ),
      Z₀≤Z → 0≤N → 0≤M → M≤L → V≤L → z₀≤L → hhat≤L →
      (Ideal.absNorm J:ℝ)≤Z^M → (Ideal.absNorm F:ℝ)≤Z^V → (Ideal.absNorm (Ideal.span {m}):ℝ)≤Z^L →
      CanonicalMargins (N+V) M (normWidth Z (Ideal.span {m})) z₀ margin → cstar/2≤margin →
      V≤d → hhat≤d+η → d≤cstar/200 →
    ∀ (parents : Finset (Ideal Eis)),(∀ I∈parents,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^M) →
      Fintype.card σ≤rmax → ∀ (lists : σ→Finset (Ideal Eis)) (H : σ→ℝ),
      Pairwise (fun i j => Disjoint (lists i) (lists j)) →
      (∀ i,∀ P∈lists i,P.IsMaximal) →
      (∀ i,∀ P∈lists i,ConcretePrimeRowBridge.goodLambda∉P) →
      (∀ i,∀ P∈lists i,Prime P) →
      (∀ i,∀ P∈lists i,ringChar (Eis⧸P)≠2) →
      (∀ i,∀ P∈lists i,P∉reflectionExcludedPrimes q) →
      (∀ i,1≤H i) → (∀ i,∀ P∈lists i,(Ideal.absNorm P:ℝ)≤H i) → (∏ i,H i)≤Z^z₀ →
    ∀ (Ψ : Eis→*ℂ),(∀ n,‖Ψ n‖≤1) → CanonicalCoefficientClass.FactorsModulo (CanonicalCoefficientClass.fixedBaseConductor q) Ψ →
    ∀ (u : Eisˣ) (θ : ℝ) (w : ∀ i,lists i→ℂ),(∀ i P,‖w i P‖≤1) →
      (∑ I∈representativeRowFiber parents J (ActualFiber.maskIdeal q m F),
        ‖∑ p : ∀ i,lists i,(∏ i,w i (p i))*markedCompletedT
          (rowTwist Ψ (ActualFiber.maskElement q m) (ConcretePrimeRowBridge.idealGenerator F)
            (u.val*ConcretePrimeRowBridge.idealGenerator I)) (CompletedHeight.normTwistedSource W θ)
          (Z^(N-3*hhat)) (fun A => ∏ i,if (p i).val∣A then (1:ℂ) else 0)‖^2)≤
      C*(1+‖θ‖)^degree*Z^(N+V-cstar/16)*(Ideal.absNorm (rowPowerfulPart J):ℝ)^(-(1/2:ℝ)) := by
  let Q := CanonicalCoefficientClass.fixedBaseConductor q
  have hQ : Q≠0 := CanonicalCoefficientClass.fixedBaseConductor_ne_zero q hq
  let c := reflectionConductor q
  have hc : c≠0 := reflectionConductor_ne_zero q hq
  let : Finite (Eis⧸Ideal.span {c}) := ConcreteTraceCRT.finite_quotient_span hc
  let : Fintype (Eis⧸Ideal.span {c}) := Fintype.ofFinite _
  let : Finite (Eis⧸Ideal.span {((9:Eis)*c)^2}) :=
    ConcreteTraceCRT.finite_quotient_span (pow_ne_zero 2 (mul_ne_zero (by norm_num) hc))
  let : Fintype (Eis⧸Ideal.span {((9:Eis)*c)^2}) := Fintype.ofFinite _
  let b := excludedGenerator (reflectionExcludedPrimes q)
  let B : Ideal Eis := Ideal.span {b}
  have hb : b≠0 := reflectionExcludedGenerator_ne_zero q
  have hB : B≠0 := Ideal.span_singleton_eq_bot.not.mpr hb
  let E := fixedFourierGeometry c hc
  have hEc : ∀ h,(E h).c0≠0 := fun h => (E h).denominator_ne_zero
  have hEN : ∀ h,(9:Eis)*(E h).c0∣(9:Eis)*c := fun h => mul_dvd_mul_left (9:Eis) (E h).denominator_dvd
  obtain ⟨degree,C,Z₀,hC,hZ₀,he⟩ := canonical_original_frozen_energy
    (fun h => (E h).a0) (fun h => (E h).c0) (fun h => (E h).mode) lo hi hlo W hWs hW
