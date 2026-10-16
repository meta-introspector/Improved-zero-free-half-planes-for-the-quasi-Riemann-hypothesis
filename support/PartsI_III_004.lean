    (idealCoeff_norm_le_one η.inverse I)).trans (slotSchwartz_norm F ζ hζ _)

theorem slotSchwartz_uniform (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀ζ:ℂ,ζ.re∈Set.Icc (0:ℝ) 1 →
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F ζ)≤ C*(1+‖ζ.im‖)^J := by
  obtain ⟨J,C,hC,hbound⟩:=interpolatedProfile_uniform (fun x=> conj (F.W x)) 1 2 (by norm_num)
    (conjugate_source_support F) (conjugate_source_smooth F) S
  refine ⟨J,C,hC,?_⟩
  intro ζ hζ
  have hh:=hbound (1-ζ.re) ⟨by linarith [hζ.2],by linarith [hζ.1]⟩ (-ζ.im)
  simpa only [slotSchwartz,norm_neg] using hh

theorem slotSchwartz_height_uniform (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(S:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤ height →
      (∀i,(ζ i).re=17/50) → (∀i,|(ζ i).im|≤ height) → ∀i,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz F (ζ i))≤ C*(1+height)^J := by
  obtain ⟨J,C,hC,hbound⟩:=slotSchwartz_uniform F S
  refine ⟨J,C,hC,?_⟩
  intro ι ζ height hheight hreal him i
  refine (hbound (ζ i) (by rw [hreal i];norm_num)).trans ?_
  apply mul_le_mul_of_nonneg_left _ hC.le
  exact pow_le_pow_left₀ (by positivity) (by simp only [Real.norm_eq_abs];linarith [him i]) J

theorem physical_positive_row {ι:Type*}[Fintype ι][DecidableEq ι]
    (F:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(S:ι→Finset (Ideal O))(P:ι→ℝ)(ζ:ι→ℂ)(t X₁ X₂:ℝ):
    positiveSlotRow η m A z W₁ W₂ S (fun i=> physicalSlotCoefficient η₀ F.W (P i) (ζ i)) P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S
        (fun i I=> idealCoeff η₀.inverse I*slotSchwartz F (ζ i) ((I.absNorm:ℝ)/P i)) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_coefficient F η₀ (P i) (ζ i) I

end SevenEighths.PerturbedCenteredMomentDetectorPlainSlotProfile

end

end OAI

end LocalModule120
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainSlotProfile -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainCapacity -/
section LocalModule121

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainCapacity
open OAI.SevenEighths.CenteredMomentDetectorPlainSlotProfile
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators ContDiff ComplexConjugate
namespace SevenEighths.PerturbedCenteredMomentDetectorPlainCapacity
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot HeckePrimeAnnular
open CenteredMomentNaturalRowSource CenteredMomentSecondHeightFamily
open CenteredMomentDetectorDictionary PerturbedCenteredMomentDetectorPlainSlotProfile
local notation "O"=> HeckeFamily.O
variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}

theorem physical_annular_all (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η₀:Character)
    (P:ℝ)(hP:0< P)(ζ:ℂ)(I:Ideal O):
    physicalSlotCoefficient η₀ S.W P ζ I=
      idealCoeff η₀.inverse I*annularWeight (fun x=> conj (S.W x)) P (1-ζ.re) (-ζ.im) I := by
  by_cases hI:I=0
  · subst I
    have hw:S.W 0=0:=by
      by_contra hh
      have hs:=S.complex_support hh
      norm_num at hs
    simp [physicalSlotCoefficient,annularWeight,hw]
  · exact physicalSlotCoefficient_annular η₀ S.W P ζ I hI hP

theorem selected_physical_annular {ι:Type*}
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(J:Finset ι)(η η₀:Character)(m A z:O)
    (W₁ W₂:ℝ→ℂ)(pools:ι→Finset (Ideal O))(P:ι→ℝ)(hP:∀i,0< P i)
    (ζ:ι→ℂ)(t X₁ X₂:ℝ):
    selectedProduct J η m A z W₁ W₂ pools
      (fun i=> physicalSlotCoefficient η₀ S.W (P i) (ζ i)) P t X₁ X₂=
    selectedProduct J η m A z W₁ W₂ pools
      (fun i I=> idealCoeff η₀.inverse I*
        annularWeight (fun x=> conj (S.W x)) (P i) (1-(ζ i).re) (-(ζ i).im) I) P t X₁ X₂ := by
  congr 1
  funext i I
  exact physical_annular_all S η₀ (P i) (hP i) (ζ i) I

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
include hH

theorem physical_capacity_removal {ι:Type*}[Fintype ι][DecidableEq ι]
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(Lmod Lslot ε κ:ℝ)
    (hLm:0≤ Lmod)(hLs:0≤ Lslot)(hε:0<ε)
    (hbeta:(51/100:ℝ)≤ beta)(hκ:2*beta-1≤κ):
    ∃degree:ℕ,∃C:ℝ,0< C ∧ ∀η₀:Character,∃Z₀:ℝ,1< Z₀ ∧
    ∀(J:Finset ι)(w:ι→ℝ)(n₁ n₂ width mesh:ℝ),0≤ mesh →
      (∀i,0≤ w i) → (∀i,w i≤ mesh) → (∀i,w i≤ Lslot) →
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤ width) ∧
      κ*(∑i∈R,w i)≤ CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh ∧
    ∀Z:ℝ,Z₀≤ Z → ∀η:Character,∀z:O,z≠0 → ∀F:NaturalRow η z,
      (F.character.modulus.absNorm:ℝ)≤ Z^Lmod →
    ∀Q:Ideal O,Q≤ M → Q≤η₀.modulus → ¬FixedInducingRow η Q fixedBadMask 1 z →
    ∀(ζ:ι→ℂ)(t V:ℝ),(∀i,(ζ i).re∈Set.Icc (0:ℝ) 1) → 0≤ V → (∀i,|(ζ i).im|≤ V) →
    ∀(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ),
      let P:=fun i=> Z^(w i)
      let pools:=fun i=> primePool M H 2 (P i)
      let coeff:=fun i=> physicalSlotCoefficient η₀ S.W (P i) (ζ i)
      ‖selectedProduct J η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+CenteredMomentLiveCapacity.excess J w n₁ n₂ width κ/6+κ*mesh)*
          ‖selectedProduct (J\R) η fixedBadMask 1 z W₁ W₂ pools coeff P t X₁ X₂‖^2 := by
  obtain ⟨degree,C,hC,hbound⟩:=CenteredMomentRelativeCapacityRemoval.actual_relative_capacity_removal
    M H hH (ι:=ι) (fun _ x=> conj (S.W x)) (fun _=>1) (fun _=>2) (fun _=> by norm_num)
    (fun _=> conjugate_source_support S) (fun _=> Complex.conjCLE.contDiff.comp (S.W.smooth ⊤))
    Lmod Lslot ε 0 1 κ hLm hLs hε hbeta hκ
  refine ⟨degree,C,hC,?_⟩
  intro η₀
  obtain ⟨Z₀,hZ₀,hbound⟩:=hbound (fun _=>η₀.inverse)
  refine ⟨Z₀,hZ₀,?_⟩
  intro J w n₁ n₂ width mesh hmesh hw hwm hwcap
  obtain ⟨R,hR,hremaining,hcost,henergy⟩:=hbound J w n₁ n₂ width mesh hmesh hw hwm hwcap
  refine ⟨R,hR,hremaining,hcost,?_⟩
  intro Z hZ η z hz F hcond Q hQM hQη hex ζ t V hζ hV him W₁ W₂ X₁ X₂
  dsimp only
  have hZp:0< Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  have hP (i:ι):0< Z^(w i):=Real.rpow_pos_of_pos hZp _
  rw [selected_physical_annular S J η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂,
    selected_physical_annular S (J\R) η η₀ fixedBadMask 1 z W₁ W₂ _ _ hP ζ t X₁ X₂]
  exact henergy Z hZ η z hz F hcond Q hQM (fun _=> hQη) hex
    (fun i=>1-(ζ i).re) (fun i=>-(ζ i).im) t V
    (fun i=> by linarith [(hζ i).2]) (fun i=> by linarith [(hζ i).1]) hV
    (fun i=> by simpa only [abs_neg] using him i) W₁ W₂ X₁ X₂

end SevenEighths.PerturbedCenteredMomentDetectorPlainCapacity

end

end OAI

end LocalModule121
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainCapacity -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainMarkedState -/
section LocalModule122

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainCapacity
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState
open OAI.SevenEighths.CenteredMomentDetectorPlainSlotProfile
open OAI.SevenEighths.CenteredMomentDetectorPlainStateDictionary
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap ComplexConjugate Topology ContDiff
open Filter

namespace SevenEighths.PerturbedCenteredMomentDetectorPlainMarkedState
open HeckeFamily HeckeDyadic HeckeDetectorRawFiber HeckeDetectorBatch HeckePrimeAnnular
open HeckeInverseAmplification HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorPlainStateDictionary PerturbedCenteredMomentDetectorPlainExceptional
open CenteredMomentDetectorPlainFiberSource PerturbedCenteredMomentDetectorPlainCapacity
open PerturbedCenteredMomentDetectorPlainSlotProfile PerturbedCenteredMomentDetectorEnergyInitialState
open CenteredMomentDetectorDictionary CenteredMomentEnergyState CenteredMomentEnergyBands
open CenteredMomentInductionEnergy CenteredMomentRetainedEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFiniteProfileExceptional PerturbedCenteredMomentNaturalFixedRaySource
open ConcretePrimeRowBridge ProbeHighRowFamily
local notation "O" => HeckeFamily.O
variable {M:Ideal O}{H:Subgroup (O⧸M)ˣ}{Label Slot:Type*}
variable {U a ε tstar T allowance:ℝ}{i:ℕ}
variable {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}

theorem source_slot_coefficient (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(η:Character)(s:Slot)
    (hreal:(F.external s).re=17/50)(hU:0< U)(I:Ideal O):
    idealCoeff η.inverse I*slotWindow F s ((I.absNorm:ℝ)/(U^(F.widths s)))=
      idealCoeff η.inverse I*annularWeight (fun x=> conj (S.W x))
        (U^(F.widths s)) (33/50) (-(F.external s).im) I := by
  have he:=physical_annular_all S η (U^(F.widths s)) (Real.rpow_pos_of_pos hU _)
    (F.external s) I
  rw [hreal] at he
  norm_num at he
  simpa only [physicalSlotCoefficient,slotWindow,hprofile] using he

theorem retained_eq_initial_energy (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (hprofile:∀s x,F.profile s x=S.W x)(hupper:∀s,F.upper s=2)
    (η:Character)(Q:Ideal O)(selected:Finset Slot)
    (hreal:∀s∈selected,(F.external s).re=17/50)
    (Φ:𝓢(ℝ,ℂ))(bΦ δ:ℝ)(hU:1≤ U)(hδ:0≤δ)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^δ)(j k:ℕ)(σ t:ℝ):
    let state:=initialState η Q Φ bΦ U δ hU hδ hs hp hη
    PerturbedCenteredMomentDetectorPlainExceptional.retainedSourceEnergy state.radial.keep F η selected j k σ t Φ=
      energy state.character state.mask 1 0
        ((detectorProfiles F.reverse j k σ t).profile 0)
        ((detectorProfiles F.reverse j k σ t).profile 1)
        (fun s:selected=> CenteredMomentPrimeSlot.primePool M H 2 (U^(F.widths s.val)))
        (fun (s:selected) I=> idealCoeff η.inverse I*
          annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
            (-(F.external s.val).im) I)
        (fun s:selected=> U^(F.widths s.val)) (U^F.m) (U^F.m)
        state.radial.keep state.radial.profile state.radial.scale := by
  dsimp only
  change CenteredMomentDetectorPlainExceptional.retainedSourceEnergy
    (initialState η Q Φ bΦ U δ hU hδ hs hp hη).radial.keep F η selected j k σ t Φ = _
  rw [CenteredMomentDetectorPlainStateDictionary.retainedSourceEnergy_eq_energy _ _ _ _ _ _ _ _ _ (zero_lt_one.trans_le hU)]
  have hc:(fun (s:selected) I=> idealCoeff η.inverse I*
      slotWindow F s.val ((I.absNorm:ℝ)/(U^(F.widths s.val))))=
      (fun (s:selected) I=> idealCoeff η.inverse I*
        annularWeight (fun x=> conj (S.W x)) (U^(F.widths s.val)) (33/50)
          (-(F.external s.val).im) I):=by
    funext s I
    exact source_slot_coefficient S F hprofile η s.val (hreal s.val s.property)
      (zero_lt_one.trans_le hU) I
  rw [hc]
  simp only [hupper,plainProfile_eq_detectorSchwartz,initialState,NaturalState.mask,
    detectorProfiles,reduceIte,Fin.one_eq_zero_iff]
  norm_num

theorem plain_length_eq [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U):
    length U (U^F.m)=F.m := by
  have hm:0≤ F.m:=(F.lengths hU).2.2.2.2
  rw [length,max_eq_right (Real.one_le_rpow hU.le hm),
    Real.logb_rpow (zero_lt_one.trans hU) hU.ne']

theorem marked_capacity [NeZero M]
    (F:Fiber M H Label Slot U a ε tstar T allowance i)(hU:1< U)
    (selected:Finset Slot)(κ δ:ℝ)(hδ:0≤δ)
    (hcap:2*F.m+6*κ*(∑s∈selected,F.widths s)≤1):
    length U (U^F.m)+length U (U^F.m)+6*κ*(∑s:selected,F.widths s.val)≤1+δ := by
  rw [plain_length_eq F hU,Finset.sum_coe_sort]
  linarith

theorem selected_widths (F:Fiber M H Label Slot U a ε tstar T allowance i)
    (selected:Finset Slot)(hselected:selected⊆F.slots):
    (∀s:selected,0< F.widths s.val) ∧ (∀s:selected,F.widths s.val≤ F.mesh) :=
  ⟨fun s=> F.widths_pos s.val (hselected s.property),
    fun s=> F.widths_mesh s.val (hselected s.property)⟩

theorem source_profile_uniform (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(Hsemin:Finset (ℕ×ℕ)):
    ∃J:ℕ,∃C:ℝ,0< C ∧ ∀{ι:Type*}(ζ:ι→ℂ)(height:ℝ),0≤ height→
      (∀s,(ζ s).re=17/50)→(∀s,|(ζ s).im|≤ height)→∀s,
      Hsemin.sup (schwartzSeminormFamily ℝ ℝ ℂ) (slotSchwartz S (ζ s))≤
        C*(1+height)^J :=
  slotSchwartz_height_uniform S Hsemin

theorem source_relative_fixed_gates (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character):
    internalQ (sourceFixedIdeal S) η≠0 ∧
    internalQ (sourceFixedIdeal S) η≤ S.modulus ∧
    internalQ (sourceFixedIdeal S) η≤η.inverse.modulus ∧
    internalQ (sourceFixedIdeal S) η≤ Ideal.span {(72:O)} :=
  source_fixed_gates S η

theorem fixed_window_data (S:RHZeroFreeExtension.AnalyticHigh.SourceData D):
    Function.support (fun x=> conj (S.W x))⊆Set.Icc (1:ℝ) 2 ∧
    ContDiff ℝ ∞ (fun x=> conj (S.W x)) ∧ ∀x,‖conj (S.W x)‖≤1 := by
  refine ⟨conjugate_source_support S,
    Complex.conjCLE.contDiff.comp (S.W.smooth ⊤),?_⟩
  intro x
  rw [RCLike.norm_conj,S.complex_eq,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (S.bounded x).1]
  exact (S.bounded x).2

theorem source_batch_marked_initial (S:RHZeroFreeExtension.AnalyticHigh.SourceData D):
    ∃bΦ:ℝ,0< bΦ ∧ ∀η:Character,∀δ:ℝ,0<δ→
      ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
      ∀bin label J K,∀hne:(B.fiberRows bin label J K).Nonempty,
      ∀selected:Finset (Fin D.N),selected⊆B.slots→
      let F:=B.fiber bin label J K hne;
      2*F.m+6*(3/4)*(∑s∈selected,F.widths s)≤1→
      let η₀:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label;
      ∃state:NaturalState (Z^d) 0 bΦ,
        state.character=η₀ ∧ state.fixedModulus=internalQ (sourceFixedIdeal S) η₀ ∧
        state.puncture=1 ∧ state.radial.profile=radialMajorant ∧ state.radial.scale=Z^d ∧
        state.radial.keep=initialKeep η₀ (internalQ (sourceFixedIdeal S) η₀) ∧
        state.width=1+δ ∧
        length (Z^d) ((Z^d)^F.m)+length (Z^d) ((Z^d)^F.m)+
          6*(3/4)*(∑s:selected,F.widths s.val)≤ state.width ∧
        (∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ F.mesh) ∧
        ∀j k:ℕ,∀σ t:ℝ,
        (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
          ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
          ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
          energy state.character state.mask 1 0
            ((detectorProfiles F.reverse j k σ t).profile 0)
            ((detectorProfiles F.reverse j k σ t).profile 1)
            (fun s:selected=> CenteredMomentPrimeSlot.primePool S.modulus ⊤ 2 ((Z^d)^(F.widths s.val)))
            (fun (s:selected) I=> idealCoeff η₀.inverse I*
              annularWeight (fun x=> conj (S.W x)) ((Z^d)^(F.widths s.val)) (33/50)
                (-(F.external s.val).im) I)
            (fun s:selected=>(Z^d)^(F.widths s.val)) ((Z^d)^F.m) ((Z^d)^F.m)
            state.radial.keep state.radial.profile state.radial.scale := by
  obtain ⟨bΦ,hbΦ,hs⟩:=radialMajorant_support_bound
  refine ⟨bΦ,hbΦ,?_⟩
  intro η δ hδ
  filter_upwards [source_label_modulus_eventually S η δ hδ,source_batch_plain_retained S η] with Z hz hr
  refine ⟨hz.1,?_⟩
  intro rows hrows d hd a ε tstar T allowance i B hB hdata hprofile hwidth hupper hreal
    bin label J K hne selected hselected F hcap η₀
  have hdpos:0< d:=by linarith
  have hU:1< Z^d:=Real.one_lt_rpow hz.1 hdpos
  have hη:(η₀.modulus.absNorm:ℝ)≤(Z^d)^δ:=hz.2 label d hd
  let state:=initialState η₀ (internalQ (sourceFixedIdeal S) η₀) radialMajorant bΦ
    (Z^d) δ hU.le hδ.le hs radialMajorant_nonneg hη
  refine ⟨state,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_,?_⟩
  · exact marked_capacity F hU selected _ δ hδ.le hcap
  · intro s
    exact ⟨F.widths_pos s.val (hselected s.property),F.widths_mesh s.val (hselected s.property)⟩
  · intro j k σ t
    have hb:=hr.2 rows hrows d hdpos.ne' a ε tstar T allowance i B hB hdata hprofile hwidth
      bin label J K hne selected j k σ t
    have hprof:∀s x,F.profile s x=S.W x:=by
      intro s x
      change B.profile s x=S.W x
      rw [hprofile,S.complex_eq]
    have he:=retained_eq_initial_energy S F hprof hupper η₀ (internalQ (sourceFixedIdeal S) η₀) selected
      (fun s _=> hreal s) radialMajorant bΦ δ hU.le hδ.le hs radialMajorant_nonneg hη j k σ t
    exact hb.trans_eq he

end SevenEighths.PerturbedCenteredMomentDetectorPlainMarkedState

end

end OAI

end LocalModule122
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainMarkedState -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainMomentParameters -/
section LocalModule123

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.PerturbedCenteredMomentDetectorPlainMomentParameters
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open CenteredMomentDetectorDictionary
open CenteredMomentEnergyState CenteredMomentEnergyBands
open PerturbedCenteredMomentDetectorEnergyInitialState PerturbedCenteredMomentDetectorPlainMarkedState
open CenteredMomentDetectorPlainUnmarkedState PerturbedCenteredMomentNaturalFixedRaySource
local notation "O" => HeckeFamily.O

variable {Δ:ℝ}

def delta (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ):ℝ := D.t/4
def stageError (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ):ℝ := D.t/4
def kappaPlain (_D:RHZeroFreeExtension.AnalyticHigh.HighData Δ):ℝ := 3/4

theorem fixed_parameters (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ):
    0< delta D ∧ delta D≤1/4 ∧ 0< stageError D ∧
    delta D+stageError D≤ D.t ∧ 3/4≤ kappaPlain D ∧ 0< kappaPlain D := by
  dsimp [delta,stageError,kappaPlain]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_small]
  constructor
  · exact div_pos D.t_pos (by norm_num)
  constructor
  · linarith [D.t_pos]
  constructor <;> linarith

lemma source_base_gt_one (_D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ)≤ d):1< Z^d :=
  Real.one_lt_rpow hZ (by linarith)

lemma witness_length_cap (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ):
    1/2+75*D.ε≤(23/40:ℝ) := by linarith [D.epsilon_small]

lemma original_width_bounds (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)(d:ℝ)
    (hd:(1/200:ℝ)≤ d)(s:Fin D.N):0< D.ell s/d ∧ D.ell s/d≤ D.t := by
  have hdpos:0< d:=by linarith
  refine ⟨div_pos (D.slots_bounds s).1 hdpos,(div_le_iff₀ hdpos).mpr ?_⟩
  have hs: D.ell s≤(1/200:ℝ)*D.t:=(D.slots_bounds s).2.2
  nlinarith [D.t_pos]

variable {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
variable {U a tstar T heightAllowance:ℝ}{i:ℕ}

theorem actual_fiber_lengths (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)(hU:1< U):
    0≤ F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧ length U (U^F.m)=F.m := by
  have hm:=F.lengths hU
  have hcap:=hm.2.2.1.trans (witness_length_cap D)
  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact PerturbedCenteredMomentDetectorPlainMarkedState.plain_length_eq F hU

theorem batch_fiber_parameters (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ)≤ d)
    (B:Batch M H Label (Fin D.N) (Z^d) a D.ε tstar T heightAllowance i)
    (hwidth:B.widths=(fun s=> D.ell s/d))
    (bin label J K)(hne:(B.fiberRows bin label J K).Nonempty):
    let F:=B.fiber bin label J K hne;
    1< Z^d ∧ 0≤ F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤(Z^d)^F.m ∧ (Z^d)^F.m≤ Z^d ∧ length (Z^d) ((Z^d)^F.m)=F.m ∧
    (∀s,0< F.widths s ∧ F.widths s≤ D.t) ∧
    (∀selected:Finset (Fin D.N),∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ D.t) := by
  dsimp only
  have hU:=source_base_gt_one D Z d hZ hd
  have hf:=actual_fiber_lengths D (B.fiber bin label J K hne) hU
  have hw:∀s,0<(B.fiber bin label J K hne).widths s ∧
      (B.fiber bin label J K hne).widths s≤ D.t:=by
    intro s
    change 0< B.widths s ∧ B.widths s≤ D.t
    rw [hwidth]
    exact original_width_bounds D d hd s
  exact ⟨hU,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
    hw,fun _ s=> hw s.val⟩

lemma width_bands (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)(m:ℝ)(hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤ max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  have hδ:0< delta D:=(fixed_parameters D).1
  have hd:delta D≤1/4:=(fixed_parameters D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem marked_state_admission (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D))
    (selected:Finset (Fin D.N))
    (hcap:2*F.m+6*(kappaPlain D)*(∑s∈selected,F.widths s)≤1):
    let s:=initialState η Q Φ bΦ U (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=1+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧
    length U (U^F.m)+length U (U^F.m)+
      6*(kappaPlain D)*(∑s:selected,F.widths s.val)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hw.1,hw.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  exact PerturbedCenteredMomentDetectorPlainMarkedState.marked_capacity F hU selected (kappaPlain D) (delta D) (fixed_parameters D).1.le hcap

theorem unmarked_state_admission (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D)):
    let s:=state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧ 2*length U (U^F.m)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (fixed_parameters D).1.le)

theorem source_label_fixed_allowance (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤ d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^(delta D) :=
  source_label_modulus_eventually S η (delta D) (fixed_parameters D).1

lemma final_exponent_budget (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)(base:ℝ):
    base+delta D+stageError D≤ base+D.t := by
  linarith [(fixed_parameters D).2.2.2.1]

end SevenEighths.PerturbedCenteredMomentDetectorPlainMomentParameters

end

end OAI

end LocalModule123
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainMomentParameters -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainMarkedFineField -/
section LocalModule124

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainMarkedFineField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.PerturbedProbeDetectorPlainMarkedFineField
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open PerturbedCenteredMomentDetectorEnergyInitialState PerturbedCenteredMomentDetectorPlainMarkedState
open PerturbedCenteredMomentDetectorPlainMomentParameters PerturbedCenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=> HeckeFamily.O

def PositiveFineSourceInput {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}(S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(mesh:ℝ):Prop:=
  ∀bΦ:ℝ,0< bΦ→∃degree:ℕ,∃seminorms:Finset (ℕ×ℕ),
    ∀η₀:Character,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      PositiveAt (α:=Fin D.N) S.modulus ⊤ le_top (fun x=> conj (S.W x))
        2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 (stageError D)
        (kappaPlain D) U η₀ (sourceFixedIdeal S) degree seminorms C

theorem source_batch_plain_marked_fine {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)(mesh:ℝ)(hmesh:0< mesh)(hfine:∀j,D.ell j≤ mesh/200)
    (henergy:PositiveFineSourceInput S mesh):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height→(∀s,|(B.external s).im|≤ height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots→
      2*F.m+6*(3/4)*(∑s∈selected,F.widths s)≤1→
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t):=by
  obtain ⟨bΦ,hbΦ,hsource⟩:=source_batch_marked_initial S
  obtain ⟨degree,seminorms,henergy⟩:=henergy bΦ hbΦ
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩:=
    CenteredMomentDetectorPlainProfileControl.source_height_factor seminorms
  refine ⟨J+degree,?_⟩
  intro η
  let data:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η
  choose C hC hbound using fun label=> henergy (data label)
  choose U₀ hU₀ using fun label=> Filter.eventually_atTop.mp (hbound label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0< Csum:=by
    have h:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤ Csum:=by
    have h:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le)
      (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→U₀ label≤ Z^d:=by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  let Cfinal:=Csum*(1+diagonalControl radialMajorant)*Cprofile
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  refine ⟨Cfinal,by dsimp [Cfinal];positivity,?_⟩
  filter_upwards [hsource η (delta D) (fixed_parameters D).1,hscale] with Z hs hscale
  refine ⟨hs.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap j k hjk σ hσ t ht
  have hU:1< Z^d:=source_base_gt_one D Z d hs.1 hd
  obtain ⟨state,hchar,hQ,hpuncture,hΦ,hK,hkeep,hwidthstate,hcapacity,hwidths,hrow⟩:=
    hs.2 rows hrows d hd a D.ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected hcap
  have hf:=actual_fiber_lengths D F hU
  have hstate:state.width≤2:=by rw [hwidthstate];exact (width_bands D F.m hf.2.2.1).2.1
  have hw (s:selected):0≤ F.widths s.val:=(hwidths s).1.le
  have hwcap (s:selected):F.widths s.val≤ mesh:=by
    change B.widths s.val≤ mesh
    rw [hwidth]
    exact (RHZeroFreeExtension.AnalyticHigh.fine_slot_widths D (fun _=> mesh) hmesh hfine d hd s.val).2
  have hpos:=hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=> F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im)
    0 height hw hwcap (fun _=> le_rfl) (fun _=> le_rfl) hheight
    (fun s=> by change |-(B.external s.val).im|≤ height; simpa only [abs_neg] using hexternal s.val)
    state hQ hstate (detectorProfiles F.reverse j k σ t) ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1) hcapacity
  have heq:=CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character (data label) (fun (_:selected)=>1) state.mask 1
    ((detectorProfiles F.reverse j k σ t).profile 0)
    ((detectorProfiles F.reverse j k σ t).profile 1)
    (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=> HeckePrimeAnnular.annularWeight (fun x=> conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hnorm:=hprofile degree F.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hp:0≤(detectorProfiles F.reverse j k σ t).control seminorms ^2:=sq_nonneg _
  have hexp:state.width+stageError D≤1+D.t:=by
    rw [hwidthstate];linarith [(fixed_parameters D).2.2.2.1]
  calc
    _≤_:=hrow j k σ t
    _≤ C label*diagonalControl state.radial.profile*
        (detectorProfiles F.reverse j k σ t).control seminorms ^2*
        (1+|(0:ℝ)|+height)^degree*(Z^d)^(state.width+stageError D):=by
      exact heq.le.trans hpos
    _≤(Cfinal*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
      rw [hΦ]
      have hpow:=Real.rpow_le_rpow_of_exponent_le hU.le hexp
      calc
        _=(C label*diagonalControl radialMajorant)*
          ((detectorProfiles F.reverse j k σ t).control seminorms ^2*
            (1+|(0:ℝ)|+height)^degree)*(Z^d)^(state.width+stageError D):=by ring
        _≤(Csum*(1+diagonalControl radialMajorant))*
          (Cprofile*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
          apply mul_le_mul _ hpow (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
          apply mul_le_mul _ hnorm (by positivity) (by positivity)
          exact mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
        _=_:=by dsimp [Cfinal];ring
end SevenEighths.PerturbedProbeDetectorPlainMarkedFineField

end

end OAI

end LocalModule124
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainMarkedFineField -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainUnmarkedField -/
section LocalModule125

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainProfileControl
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.PerturbedProbeDetectorPlainUnmarkedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary PerturbedCenteredMomentDetectorEnergyInitialState
open PerturbedCenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open PerturbedCenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands PerturbedCenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def radialSupportUpper : ℝ := Classical.choose radialMajorant_support_bound

theorem radialSupportUpper_spec : 0< radialSupportUpper ∧
    Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic radialSupportUpper :=
  Classical.choose_spec radialMajorant_support_bound

lemma unmarked_power_eq (U m e:ℝ)(hU:1≤ U):
    U^(max 1 (2*m)+e)=max U ((U^m)^2)*U^e := by
  have hpos:0< U:=zero_lt_one.trans_le hU
  rw [Real.rpow_add hpos]
  congr 1
  have hs:(U^m)^2=U^(2*m):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hpos.le]
    congr 1
    norm_num
    ring
  rw [hs]
  by_cases hm:1≤2*m
  · rw [max_eq_right hm,max_eq_right]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm
  · have hm':2*m≤1:=le_of_not_ge hm
    rw [max_eq_left hm',max_eq_left]
    · exact Real.rpow_one U
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm'

variable {Δ:ℝ}

theorem retained_unmarked_bound (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
    {U a tstar T heightAllowance:ℝ}{i:ℕ}
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(hU:1< U)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D))
    (degree:ℕ)(S:Finset (ℕ×ℕ))(A:ℝ)
    (hzero:ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D) U degree S A)
    (j k:ℕ)(σ t:ℝ):
    CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤
      A*diagonalControl radialMajorant*(detectorProfiles F.reverse j k σ t).control S ^2*
        U^(max 1 (2*F.m)+delta D+stageError D) := by
  let s:=state F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hs:=unmarked_state_admission D F η Q radialMajorant radialSupportUpper hU
    radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hwidth:s.width=max 1 (2*F.m)+delta D:=hs.2.2.2.2.2.2.1
  have hband:s.width≤2:=hs.2.2.2.2.2.2.2.2.1
  have hscale:1≤ U^F.m ∧ U^F.m≤ U:=⟨hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz:=hzero s rfl hband (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  change CenteredMomentDetectorPlainExceptional.retainedSourceEnergy
    (CenteredMomentDetectorEnergyInitialState.initialKeep η Q) F η ∅ j k σ t radialMajorant ≤ _
  rw [actual_source_eq F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad:s.radial.profile=radialMajorant:=rfl
  simpa only [hwidth,hrad,norm_zero,add_zero,one_pow,mul_one,
    CenteredMomentDetectorEnergyInitialState.detectorProfiles,
    PerturbedCenteredMomentDetectorEnergyInitialState.detectorProfiles] using hz

theorem source_batch_plain_unmarked (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀Q:Ideal O,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤ height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=> sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=> internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=> henergy (Q label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0≤∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0< Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0< C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→
      ZeroAt (Q label) (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained S η,source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1< Z^d:=source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤ CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one,
      CenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      PerturbedCenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      CenteredMomentDetectorEnergyInitialState.initialKeep,
      PerturbedCenteredMomentDetectorEnergyInitialState.initialKeep] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+delta D+stageError D)≤
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget D _)
  have hfinal:value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.PerturbedProbeDetectorPlainUnmarkedField

end

end OAI

end LocalModule125
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainUnmarkedField -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.DetectorPlainUnmarkedRestrictedField -/
section LocalModule126

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainProfileControl
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedField
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.PerturbedProbeDetectorPlainUnmarkedRestrictedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary PerturbedCenteredMomentDetectorEnergyInitialState
open PerturbedCenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open PerturbedCenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands PerturbedCenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

open PerturbedProbeDetectorPlainUnmarkedField
variable {Δ:ℝ}

theorem source_zero_from_gated (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,
      Q≤ S.modulus→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ Q η₀) (1/4) (9/4) PerturbedProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (D.t/4)
          U degree control A):
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) PerturbedProbeDetectorPlainUnmarkedField.radialSupportUpper
          0 1 2 (D.t/4) U degree control A:=by
  obtain ⟨degree,control,henergy⟩:=henergy
  refine ⟨degree,control,?_⟩
  intro η₀
  exact henergy η₀ (sourceFixedIdeal S) (sourceFixedIdeal_le_modulus S)
    (source_fixed_gates S η₀).1
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top S) η₀)
    (source_fixed_gates S η₀).2.2.2

theorem source_batch_plain_unmarked (D:RHZeroFreeExtension.AnalyticHigh.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) PerturbedProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤ height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=> sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=> internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=> henergy (η₀ label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0≤∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0< Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0< C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→
      ZeroAt (Q label) (1/4) (9/4) PerturbedProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained S η,source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1< Z^d:=source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤ CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one,
      CenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      PerturbedCenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      CenteredMomentDetectorEnergyInitialState.initialKeep,
      PerturbedCenteredMomentDetectorEnergyInitialState.initialKeep] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+delta D+stageError D)≤
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget D _)
  have hfinal:value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [PerturbedProbeDetectorPlainUnmarkedField.unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.PerturbedProbeDetectorPlainUnmarkedRestrictedField

end

end OAI

end LocalModule126
/- END RHZeroFreeExtension.moment_adapters.DetectorPlainUnmarkedRestrictedField -/

/- BEGIN original module RHZeroFreeExtension.moment_adapters.FinalAssemblyCertifiedBands -/
section LocalModule127

set_option linter.unusedVariables false
namespace OAI

noncomputable section
open OAI.SevenEighths
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.PerturbedProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule PerturbedCenteredMomentDetectorPlainMomentParameters
open CenteredMomentNaturalFixedRaySource
open PerturbedCenteredMomentDetectorEnergyInitialState PerturbedCenteredMomentNaturalFixedRaySource
open PerturbedProbeDetectorPlainMarkedFineField PerturbedProbeDetectorPlainUnmarkedField
local notation "O"=> HeckeFamily.O

def detectorMesh (_Δ t:ℝ):ℝ:=fineMesh 2 0 1 (3/4) (t/4)

lemma detectorMesh_pos {Δ t:ℝ}(_hΔ:0<Δ)(ht:0< t):0< detectorMesh Δ t:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (3/4) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by linarith) (by positivity)).2.2.2.2.1

def DetectorCertifiedBands:Prop:=
  ∀_hβ:(34999/40000:ℝ)< HeckeZeroSupremum.beta,
  ∀D:RHZeroFreeExtension.AnalyticHigh.HighData (HeckeZeroSupremum.beta-34999/40000),
    (∀j,D.ell j≤ detectorMesh (HeckeZeroSupremum.beta-34999/40000) D.t/200)→
  ∀F:RHZeroFreeExtension.AnalyticHigh.SourceData D,∀bΦ:ℝ,0< bΦ→
    CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (count 2 (stageError D))

theorem plain_inputs {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}(F:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (hcert:∀bΦ:ℝ,0< bΦ→CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=> conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D) (count 2 (stageError D))):
    PositiveFineSourceInput F (detectorMesh Δ D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):=by
  have hp:=fixed_parameters D
  have ht (bΦ:ℝ)(hbΦ:0< bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1 (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0< bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0< Czero ∧ 0< Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 1 2
        (stageError D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (detectorMesh Δ D.t) (33/50) (33/50) 2
        (stageError D) (kappaPlain D) U η₀ (sourceFixedIdeal F) degree control Cpositive:=by
    obtain ⟨degree,control,hbound⟩:=ht bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=hbound η₀ (sourceFixedIdeal F)
      (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
    exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree,control,h⟩:=hactual bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cp,hCp,h.mono (fun U h=> h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=> h.1)⟩

theorem source_moments {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.HighData Δ}(F:RHZeroFreeExtension.AnalyticHigh.SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0< mesh)
    (hfine:∀j,D.ell j≤ mesh/200)
    (hpositive:PositiveFineSourceInput F mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        RHZeroFreeExtension.AnalyticHigh.SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=PerturbedProbeDetectorInverseFields.source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=source_batch_plain_marked_fine F mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=PerturbedProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0< Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0≤ height:=Real.rpow_nonneg hZ.le _
  have hbase:1≤1+height:=by linarith
  have hCi':Ci*(1+height)^Ji≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im|≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=> by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0≤ Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected (by simpa only [mul_zero, add_zero] using hcap) j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

theorem fine_moments_of_certified (h:DetectorCertifiedBands):RHZeroFreeExtension.AnalyticHigh.FineMomentInput:=by
  intro hβ
  let Δ:=HeckeZeroSupremum.beta-34999/40000
  have hΔ:0<Δ:=by dsimp [Δ];linarith
  refine ⟨detectorMesh Δ,fun t ht=> detectorMesh_pos hΔ ht,?_⟩
  intro D hfine F counts
  obtain ⟨hp,hz⟩:=plain_inputs F (h hβ D hfine F)
  exact source_moments F counts (detectorMesh Δ D.t) (detectorMesh_pos hΔ D.t_pos) hfine hp hz

theorem chosen_moments_of_certified (h:DetectorCertifiedBands):RHZeroFreeExtension.AnalyticHigh.ChosenMomentInput:=
  RHZeroFreeExtension.AnalyticHigh.chosen_input_of_fine (fine_moments_of_certified h)


end SevenEighths.PerturbedProbeFinalAssemblyCertifiedBands
end
end OAI

end LocalModule127
/- END RHZeroFreeExtension.moment_adapters.FinalAssemblyCertifiedBands -/

/- BEGIN original module RHZeroFreeExtension.ActualOriginalBoundary -/
section LocalModule128

/-! Recover exactly the original paper's seven-eighths supremum bound from
its actual upstream nonvanishing theorem. This does not assert the extension. -/
namespace RHZeroFreeExtension.ActualOriginalBoundary
noncomputable section
open OAI.SevenEighths HeckeFamily HeckeZeroSupremum

theorem beta_le_seven_eighths : beta ≤ (7 / 8 : ℝ) := by
  apply csSup_le zeroSet_nonempty
  intro x hx
  rcases Set.mem_insert_iff.mp hx with rfl | hx
  · norm_num
  · obtain ⟨chi, s, _hpositive, hpole, hz, rfl⟩ := hx
    by_contra hn
    apply (LFunction_ne_zero_of_seven_eighths_lt_re chi (lt_of_not_ge hn) ?_) hz
    rintro ⟨hc, hs⟩
    rcases hpole with h | h
    · exact h hs
    · exact h hc

#print axioms beta_le_seven_eighths
end
end RHZeroFreeExtension.ActualOriginalBoundary

end LocalModule128
/- END RHZeroFreeExtension.ActualOriginalBoundary -/

/- BEGIN original module RHZeroFreeExtension.ActualDirichletTransfer -/
section LocalModule129

/-! Generic transfer for the actual Hecke and Dirichlet L-functions.
The Hecke nonvanishing premise is explicit; this file does not prove it.
-/

namespace RHZeroFreeExtension.ActualDirichletTransfer

noncomputable section
open OAI.SevenEighths OAI.SevenEighths.HeckeFamily
open OAI.SevenEighths.HeckeDirichlet

theorem dirichlet_nonzero_of_hecke_bound
    (boundary : ℝ) (hboundary : 0 < boundary)
    (hHecke : ∀ (eta : Character) (s : ℂ), boundary < s.re →
      (s ≠ 1 ∨ eta.residue ≠ 1) → LFunction eta s ≠ 0)
    (q : ℕ) [NeZero q] (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : boundary < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    chi.LFunction s ≠ 0 := by
  by_cases hge : 1 ≤ s.re
  · exact chi.LFunction_ne_zero_of_one_le_re (not_and_or.mp hpole) hge
  have hsOne : s ≠ 1 := by intro h; simp [h] at hge
  have hsZero : s ≠ 0 := by
    intro h
    norm_num [h] at hs
    linarith
  have h := hHecke (character chi) s hs (Or.inl hsOne)
  rw [LFunction_eq_dirichlet_product chi hsZero hsOne] at h
  exact (mul_ne_zero_iff.mp h).1

theorem zeta_nonzero_of_hecke_bound
    (boundary : ℝ) (hboundary : 0 < boundary)
    (hHecke : ∀ (eta : Character) (s : ℂ), boundary < s.re →
      (s ≠ 1 ∨ eta.residue ≠ 1) → LFunction eta s ≠ 0)
    (s : ℂ) (hs : boundary < s.re) : riemannZeta s ≠ 0 := by
  by_cases hsOne : s = 1
  · simpa [hsOne] using riemannZeta_one_ne_zero
  have h := dirichlet_nonzero_of_hecke_bound boundary hboundary hHecke 1
    (1 : DirichletCharacter ℂ 1) s hs (by simp [hsOne])
  simpa only [DirichletCharacter.LFunction_modOne_eq] using h

end
end RHZeroFreeExtension.ActualDirichletTransfer

end LocalModule129
/- END RHZeroFreeExtension.ActualDirichletTransfer -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFinalUnconditional -/
section LocalModule130

/-! Actual finite-depth moment construction, using only the imported original
seven-eighths theorem to set kappa=3/4. The improved boundary is a conclusion,
not a supplied moment or nonvanishing contract. The conclusion concerns the
actual finite-residue Hecke family over the Eisenstein field. -/
set_option linter.unusedVariables false
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open OAI OAI.SevenEighths
open HeckeFamily HeckeZeroSupremum
open PerturbedProbeFinalAssemblyCertifiedBands
open PerturbedCenteredMomentDetectorPlainMomentParameters
open PerturbedCenteredMomentDetectorPlainSlotProfile

/-- Construct the actual terminal band from the generic source induction. -/
theorem actual_detector_certified_bands : DetectorCertifiedBands := by
  intro hβ D _hfine F bΦ hbΦ
  have hp := fixed_parameters D
  have hOld := RHZeroFreeExtension.ActualOriginalBoundary.beta_le_seven_eighths
  apply CenteredMomentEnergyCertifiedExistence.terminal_certificate
    (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
    (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

/-- The FineMomentInput is proved by actual source terminal certificates. -/
theorem actual_fine_moment_input : FineMomentInput :=
  fine_moments_of_certified actual_detector_certified_bands

/-- Actual improved supremum bound for the finite-residue Hecke family; no extension contract is
assumed. Depends on the original paper's fully proved imported headline. -/
theorem actual_beta_le_new_boundary : beta ≤ (34999/40000 : ℝ) :=
  beta_le_of_fine_moments actual_fine_moment_input

theorem actual_hecke_nonzero (χ : Character) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ χ.residue ≠ 1) : LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_beta_lt χ (actual_beta_le_new_boundary.trans_lt hs) hpole

theorem actual_dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re) (hexc : ¬ (χ = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s ≠ 0 := by
  let : NeZero q := ⟨hq⟩
  apply RHZeroFreeExtension.ActualDirichletTransfer.dirichlet_nonzero_of_hecke_bound
    (34999/40000) (by norm_num) ?_ q χ s hs hexc
  intro η z hz hp
  exact actual_hecke_nonzero η z hz hp

theorem actual_zeta_nonzero (s : ℂ) (hs : (34999/40000 : ℝ) < s.re) :
    riemannZeta s ≠ 0 := by
  apply RHZeroFreeExtension.ActualDirichletTransfer.zeta_nonzero_of_hecke_bound
    (34999/40000) (by norm_num) ?_ s hs
  intro η z hz hp
  exact actual_hecke_nonzero η z hz hp

#print axioms actual_detector_certified_bands
#print axioms actual_fine_moment_input
#print axioms actual_beta_le_new_boundary
#print axioms actual_hecke_nonzero
#print axioms actual_dirichlet_nonzero
#print axioms actual_zeta_nonzero
end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule130
/- END RHZeroFreeExtension.analytic_high.PerturbedFinalUnconditional -/

/- BEGIN original module geometry.LowGeometry -/
section LocalModule131

/-! Exact real geometry of the conditional zero-free extension.
This file proves arithmetic facts only. It imports no analytic RH hypothesis. -/
noncomputable section
namespace RHLowGeometry

def b : ℝ := 1 / 8
def perturbation : ℝ := 1 / 10000
def ell : ℝ := 5003 / 30000
def lx : ℝ := 21247 / 60000
def ly : ℝ := 28747 / 60000
def h : ℝ := 16253 / 20000
def beta0 : ℝ := 34999 / 40000
def lowExponent : ℝ := 7499 / 40000
def signal (s : ℝ) : ℝ := lx / 2 + s - 1 + h / 6

theorem perturbed_ell : ell = 1 / 6 + perturbation := by
  norm_num [ell, perturbation]

theorem scales : lx = (1 - b - ell) / 2 ∧ ly = (1 + b - ell) / 2 ∧
    h = 1 - lx + ell := by norm_num [lx, ly, h, b, ell]

theorem signal_affine (s : ℝ) : signal s = s - 11 / 16 := by
  unfold signal lx h
  ring

theorem low_exact : lx / 2 + b / 12 = lowExponent := by
  norm_num [lx, b, lowExponent]

theorem signal_at_boundary : signal beta0 = lowExponent := by
  norm_num [signal, lx, h, beta0, lowExponent]

theorem boundary_relation : beta0 = 11 / 12 - ell / 4 := by
  norm_num [beta0, ell]

theorem original_improvement : beta0 = 7 / 8 - 1 / 40000 := by
  norm_num [beta0]

theorem length_slacks :
    0 < lx - ell ∧ 0 < ly - ell ∧ 0 < 1 - 3 * ell ∧ ell < 1 / 5 := by
  norm_num [lx, ly, ell]

theorem gram_slack : ly - ell - 11 * b / 6 = 4991 / 60000 := by
  norm_num [ly, ell, b]

theorem gram_positive : 0 < ly - ell - 11 * b / 6 := by
  norm_num [ly, ell, b]

theorem supply_slacks : 8 / 39 < ell / h ∧ 7 / 37 < ell / h ∧
    0 < 5 * ell - h := by norm_num [ell, h]

theorem rescaled_lengths (d : ℝ) (hd : d ≤ ell) :
    0 < lx - d ∧ 0 < ly - d ∧ 0 < 1 - ell - 2 * d ∧
    0 < ly - d - 11 * b / 6 := by
  have hs := length_slacks
  have hg := gram_positive
  constructor
  · linarith [hs.1]
  constructor
  · linarith [hs.2.1]
  constructor
  · linarith [hs.2.2.1]
  · linarith

/-- The positive-part row-energy loss is absorbed by rescaling. -/
theorem compensated_positive_part (d : ℝ) (hd : 0 ≤ d) :
    -d + max (d + 5 * ell - 1) 0 / 8 ≤ -(7 * d) / 8 := by
  have he : 5 * ell - 1 ≤ 0 := by norm_num [ell]
  have hm : max (d + 5 * ell - 1) 0 ≤ d :=
    max_le (by linarith) hd
  linarith

theorem compensated_nonpositive (d : ℝ) (hd : 0 ≤ d) :
    -d + max (d + 5 * ell - 1) 0 / 8 ≤ 0 := by
  have hh := compensated_positive_part d hd
  linarith

/-- Exact identity governing the perturbed reflected-row branch. -/
theorem reflected_length_identity (d : ℝ) :
    1 + 3 * (ell - d) - 2 * (1 - ell - 2 * d) = d + 5 * ell - 1 := by
  ring

/-- Branch reduction, uniformly in every real row-deficit parameter. -/
theorem reflected_branch_bound (d deficit theta error energy : ℝ)
    (hdef : 0 ≤ deficit)
    (hbranch : energy ≤ (1 - ell - 2 * d) +
      (d + 5 * ell - 1 - 2 * deficit + theta) / 4 + error) :
    energy ≤ (1 - ell - 2 * d) + max (d + 5 * ell - 1) 0 / 4 +
      theta / 4 + error := by
  have hm := le_max_left (d + 5 * ell - 1) (0 : ℝ)
  linarith

/-- Exact principal and outer reserves, independent of a target. -/
theorem small_row_reserve :
    ly / 2 - h * (17 / 50 - 1 / 6) - 2 / 100 = 78699 / 1000000 := by
  norm_num [ly, h]

theorem endpoint_reserve :
    1 / 5000 - (45 / 32) * perturbation = (19 / 320000 : ℝ) := by
  norm_num [perturbation]

theorem intermediate_reserve :
    49 / 14400 - (177 / 200) * perturbation = (59657 / 18000000 : ℝ) := by
  norm_num [perturbation]

theorem floor_reserve :
    7 / 1200 - (45 / 32) * perturbation = (1093 / 192000 : ℝ) := by
  norm_num [perturbation]

theorem all_reserves_positive :
    (0 : ℝ) < 78699 / 1000000 ∧ 0 < (19 / 320000 : ℝ) ∧
    0 < (59657 / 18000000 : ℝ) ∧ 0 < (1093 / 192000 : ℝ) := by
  norm_num

/-- Uniform perturbation of any endpoint estimate with the declared slope. -/
theorem perturbed_endpoint_from_slope (oldValue newValue : ℝ)
    (hold : oldValue ≤ -(1 / 5000 : ℝ))
    (hchange : newValue ≤ oldValue + (45 / 32) * perturbation) :
    newValue ≤ -(19 / 320000 : ℝ) := by
  have hr := endpoint_reserve
  linarith

/-- Intermediate/floor bin bounds use only the stated amplitude ranges. -/
theorem intermediate_derivative (delta q : ℝ)
    (hd : delta ≤ 5 / 6) (hq : q ≤ delta / 2) :
    13 / 50 + delta / 4 + q ≤ (177 / 200 : ℝ) := by linarith

theorem intermediate_old_endpoint (delta : ℝ) (hd : delta ≤ 5 / 6) :
    -(529 / 2400 : ℝ) + 25 * delta / 96 ≤ -(49 / 14400 : ℝ) := by
  linarith

theorem moderate_slope (R delta : ℝ)
    (hR : 1 - delta ≤ R) (hd : delta ≤ 5 / 6) :
    (4 / 25 : ℝ) ≤ R + delta / 2 - 17 / 50 := by linarith

theorem intermediate_slope (delta : ℝ) (hd : delta ≤ 5 / 6) :
    0 < (101 / 150 : ℝ) - delta / 6 := by linarith

/-- Existence of a positive fixed extension beyond h with both reserves. -/
theorem extension_exists : ∃ zeta : ℝ, 0 < zeta ∧
    zeta < 5 * ell - h ∧ zeta < (19 / 320000 : ℝ) / 64 := by
  refine ⟨1 / 100000000, ?_⟩
  norm_num [ell, h]


/-- All five good-prime defect powers in the enlarged second region. -/
theorem enlarged_good_exponents (s w z : ℝ) (hs : beta0 ≤ s)
    (hw : 19 / 20 ≤ w) (hz : 33 / 200 ≤ z) :
    -s - w ≤ -(72599 / 40000 : ℝ) ∧
    -s - 6 * z ≤ -(72599 / 40000 : ℝ) ∧
    -w - 6 * z ≤ -(72599 / 40000 : ℝ) ∧
    4 - 6 * s - 6 * z ≤ -(72599 / 40000 : ℝ) ∧
    1 - s - w - 6 * z ≤ -(72599 / 40000 : ℝ) := by
  change (34999 / 40000 : ℝ) ≤ s at hs
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Row-prime boundary powers and the geometric denominator power. -/
theorem enlarged_row_exponents (s w z : ℝ) (hs : beta0 ≤ s)
    (hw : 19 / 20 ≤ w) (hz : 33 / 200 ≤ z) :
    1 - s - w ≤ -(32999 / 40000 : ℝ) ∧
    3 / 2 - 3 * s ≤ -(32999 / 40000 : ℝ) ∧
    2 - 3 * s - w ≤ -(32999 / 40000 : ℝ) ∧
    2 - 4 * s ≤ -(32999 / 40000 : ℝ) ∧
    5 / 2 - 4 * s - w ≤ -(32999 / 40000 : ℝ) ∧
    3 - 6 * s ≤ -(32999 / 40000 : ℝ) ∧
    4 - 6 * s - 6 * z ≤ -(44797 / 20000 : ℝ) := by
  change (34999 / 40000 : ℝ) ≤ s at hs
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

/-- Principal selected-prime error powers in the full residue rectangle. -/
theorem principal_error_exponents (s w z : ℝ) (hs : beta0 ≤ s)
    (hw : 19 / 20 ≤ w) (hz : 33 / 200 ≤ z) :
    -s ≤ -beta0 ∧ -6 * z ≤ -beta0 ∧
    4 - 5 * s - 6 * z ≤ -beta0 ∧ 1 - w - 6 * z ≤ -beta0 := by
  change (34999 / 40000 : ℝ) ≤ s at hs
  unfold beta0
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith


/-- The original family bound admits the fixed centered-moment parameter. -/
theorem fixed_kappa_admission (beta : ℝ) (hb : beta ≤ 7 / 8) :
    beta ≤ (1 + (3 / 4 : ℝ)) / 2 := by linarith

/-- All retained non-floor detector bins have the declared delta ceiling. -/
theorem detector_delta_ceiling (beta a : ℝ) (hb : beta ≤ 7 / 8)
    (ha : a ≤ beta) : 2 * a - 1 ≤ (3 / 4 : ℝ) := by linarith

/-- The actual delta range is contained in the enlarged certificate rectangle. -/
theorem detector_certificate_ceiling (beta a : ℝ) (hb : beta ≤ 7 / 8)
    (ha : a ≤ beta) : 2 * a - 1 ≤ (5 / 6 : ℝ) := by linarith

end RHLowGeometry

end
end LocalModule131
/- END geometry.LowGeometry -/

/- BEGIN original module geometry.ArithmeticAssembly -/
section LocalModule132

/-! Arithmetic closure only. This theorem does not assert nonvanishing of an
L-function and does not construct the physical estimates used by continuation. -/
open scoped BigOperators
namespace RHZeroFreeExtension.Arithmetic
noncomputable section

theorem count_matches_endpoint (δ x : ℝ) :
    RHCount.long δ (RHCount.t δ x) = RHGeometry.R δ x := by
  simp only [RHCount.long, RHCount.t, RHCount.P, RHCount.A, RHCount.J, RHCount.D,
    RHGeometry.R, RHGeometry.P, RHGeometry.J, RHGeometry.D]
  ring

theorem universal_new_endpoint (δ x : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    RHGeometry.E (5003/30000) δ x ≤ -19/320000 ∧
    RHCount.short δ x (RHCount.t δ x) = RHGeometry.R δ x ∧
    1 ≤ RHCount.t δ x ∧ RHCount.t δ x ≤ 3/2 := by
  refine ⟨RHGeometry.perturbed_endpoint δ x hδ0 hδ1 hx0 hx1, ?_,
    (RHCount.t_range δ x hδ0 hδ1 hx0 hx1).1,
    (RHCount.t_range δ x hδ0 hδ1 hx0 hx1).2⟩
  exact (RHCount.balanced_counts δ x hδ0 hδ1 hx0 hx1).trans
    (count_matches_endpoint δ x)

theorem arbitrarily_small_distinct_perturbed_slots (cap : ℝ) (hcap : 0 < cap) :
    ∃ N : ℕ, 0 < N ∧ ∃ ell : Fin N → ℝ, Function.Injective ell ∧
      (∀ j, 0 < ell j ∧ ell j < cap) ∧ (∑ j, ell j) = (5003/30000 : ℝ) := by
  exact RHSlotLengths.exists_distinct_slot_lengths _ cap (by norm_num) hcap

#print axioms universal_new_endpoint
#print axioms arbitrarily_small_distinct_perturbed_slots
end
end RHZeroFreeExtension.Arithmetic

end LocalModule132
/- END geometry.ArithmeticAssembly -/

/- BEGIN original module RHZeroFreeExtension -/
section LocalModule133

/-! Public entry point for the kernel-checked zero-free extension.
The implementation imports the actual pinned original source theorem and
constructs the new moment input. The public conclusions have no additional
analytic hypothesis; their transitive axioms are propext, Classical.choice
and Quot.sound. Replay with check_extension.sh; exact source hashes and
acceptance logs are recorded under audits/extension_replay/.
-/
namespace RHZeroFreeExtension
noncomputable section
open OAI.SevenEighths HeckeFamily

/-- The supremum used in the manuscript, over the actual finite-residue Hecke family over the Eisenstein field, with
sentinel one half, is at most the exact rational 34999/40000. -/
theorem beta_star_le : HeckeZeroSupremum.beta ≤ (34999/40000 : ℝ) :=
  AnalyticHigh.actual_beta_le_new_boundary

theorem hecke_nonzero (chi : Character) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re)
    (hpole : s ≠ 1 ∨ chi.residue ≠ 1) : LFunction chi s ≠ 0 :=
  AnalyticHigh.actual_hecke_nonzero chi s hs hpole

theorem dirichlet_nonzero (q : ℕ) (hq : q ≠ 0)
    (chi : DirichletCharacter ℂ q) (s : ℂ)
    (hs : (34999/40000 : ℝ) < s.re) (hpole : ¬ (chi = 1 ∧ s = 1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction chi s ≠ 0 :=
  AnalyticHigh.actual_dirichlet_nonzero q hq chi s hs hpole

/-- Classical zero-free assertion away from the pole at one. -/
theorem zeta_nonzero (s : ℂ) (hs : (34999/40000 : ℝ) < s.re) (_hpole : s ≠ 1) :
    riemannZeta s ≠ 0 := AnalyticHigh.actual_zeta_nonzero s hs

#print axioms beta_star_le
#print axioms hecke_nonzero
#print axioms dirichlet_nonzero
#print axioms zeta_nonzero
end
end RHZeroFreeExtension

end LocalModule133
/- END RHZeroFreeExtension -/

/- BEGIN original module geometry.V2Optimization -/
section LocalModule134
/-! Exact algebra of derived_zero_free_extension_v2.tex. No analytic claim is
postulated. This file checks the endpoint and the declared scalar closure. -/
set_option maxHeartbeats 0
namespace RHV2
noncomputable section
def s : ℝ := Real.sqrt 921
lemma s_sq : s^2 = 921 := by norm_num [s, Real.sq_sqrt]
lemma s_bounds : (30347/1000 : ℝ) < s ∧ s < (30348/1000 : ℝ) := by
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  constructor <;> nlinarith [s_sq]
def ell : ℝ := (33+8*s)/1653
def b : ℝ := -4/29+230*s/26709
def x : ℝ := (1-b-ell)/2
def y : ℝ := (1+b-ell)/2
def h : ℝ := (1+b+3*ell)/2
def dc : ℝ := (49-s)/48
def boundary : ℝ := (1507-2*s)/1653
def C0 : ℝ := -1/4+b/6+5*ell/4
def R (d u : ℝ) : ℝ := 1-d+(5/6-d)*d*RHCount.P u/(2*RHCount.J d u)
def E (d u : ℝ) : ℝ := C0+(1/2+ell)*d+ell*(u*d)-h*(1-R d u)
def Q (d v : ℝ) : ℝ :=
  -2*(185+170*v+(-138+12*v+96*v^2)*d)*C0+
  (185+170*v+(-138+12*v+96*v^2)*d)*(b+2*ell*v)*d-
  12*h*(5/6-d)*d*(7+18*v+8*v^2)
def Ac (v : ℝ) : ℝ := ((31824/551 : ℝ) - 36688*s/169157) + (214096*s/169157 + (50916/551 : ℝ)) * v^1 + (347296*s/169157 + (17352/551 : ℝ)) * v^2 + (512*s/551 + (2112/551 : ℝ)) * v^3
def Dc (v : ℝ) : ℝ := (1445960*s/507471 + (-69560/551 : ℝ)) + (504040*s/507471 + (-51290/551 : ℝ)) * v^1 + ((9660/551 : ℝ) - 363760*s/507471) * v^2
def Gc (v : ℝ) : ℝ := ((151700/1653 : ℝ) - 4216150*s/1522413) + ((139400/1653 : ℝ) - 3874300*s/1522413) * v^1
def disc (v : ℝ) : ℝ := (0) + ((3861265032800/279616521 : ℝ) - 122715443200*s/279616521) * v^1 + ((2386327618300/279616521 : ℝ) - 19093999200*s/93205507) * v^2 + (46823488000*s/93205507 + (-3389811480400/279616521 : ℝ)) * v^3 + (4408611200*s/14716659 + (-40221718800/4905553 : ℝ)) * v^4
lemma quadratic_identity (d v : ℝ) : Q d v = Ac v*d^2+Dc v*d+Gc v := by
  simp only [Q, C0, b, ell, h, Ac, Dc, Gc]
  ring
lemma discriminant_identity (v : ℝ) : 4*Ac v*Gc v-(Dc v)^2 = disc v := by
  unfold Ac Gc Dc disc
  ring_nf
  simp only [s_sq]
  ring
lemma complete_square (d v : ℝ) :
    4*Ac v*Q d v = (2*Ac v*d+Dc v)^2+disc v := by
  rw [quadratic_identity, ← discriminant_identity]
  ring
lemma Ac_coeff_0_pos : 0 < ((31824/551 : ℝ) - 36688*s/169157 : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_coeff_1_pos : 0 < (214096*s/169157 + (50916/551 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_coeff_2_pos : 0 < (347296*s/169157 + (17352/551 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_coeff_3_pos : 0 < (512*s/551 + (2112/551 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma Ac_pos (v : ℝ) (hv : 0 ≤ v) : 0 < Ac v := by
  have hc0 := Ac_coeff_0_pos
  have hc1 := Ac_coeff_1_pos
  have hc2 := Ac_coeff_2_pos
  have hc3 := Ac_coeff_3_pos
  have hv2 : 0 ≤ v^2 := sq_nonneg v
  have hv3 : 0 ≤ v^3 := pow_nonneg hv _
  unfold Ac
  positivity
lemma disc_coeff_1_pos : 0 < ((3861265032800/279616521 : ℝ) - 122715443200*s/279616521 : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_coeff_2_pos : 0 < ((2386327618300/279616521 : ℝ) - 19093999200*s/93205507 : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_coeff_3_pos : 0 < (46823488000*s/93205507 + (-3389811480400/279616521 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_coeff_4_pos : 0 < (4408611200*s/14716659 + (-40221718800/4905553 : ℝ) : ℝ) := by
  obtain ⟨hl, hu⟩ := s_bounds
  nlinarith
lemma disc_nonneg (v : ℝ) (hv : 0 ≤ v) : 0 ≤ disc v := by
  have hc1 := disc_coeff_1_pos
  have hc2 := disc_coeff_2_pos
  have hc3 := disc_coeff_3_pos
  have hc4 := disc_coeff_4_pos
  have hv2 : 0 ≤ v^2 := sq_nonneg v
  have hv3 : 0 ≤ v^3 := pow_nonneg hv _
  have hv4 : 0 ≤ v^4 := pow_nonneg hv _
  unfold disc
  positivity
theorem Q_nonneg (d v : ℝ) (hv : 0 ≤ v) : 0 ≤ Q d v := by
  have ha := Ac_pos v hv
  have hh := complete_square d v
  have hd := disc_nonneg v hv
  have hs := sq_nonneg (2*Ac v*d+Dc v)
  have hm : 0 ≤ 4*Ac v*Q d v := by linarith
  exact nonneg_of_mul_nonneg_right hm (by positivity)
lemma exponent_identity (d u : ℝ) (hj : RHCount.J d u ≠ 0) :
    Q d (1/2-u) = 216*RHCount.J d u*(-E d u) := by
  unfold Q E R
  field_simp [hj]
  simp only [RHCount.J, RHCount.D, RHCount.P, RHCount.A, C0, h]
  ring
theorem universal_endpoint (d u : ℝ) (hd0 : 0 ≤ d) (hd1 : d ≤ 5/6)
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1/2) : E d u ≤ 0 := by
  have hjl := RHCount.J_lower d u hd0 hd1 hu0 hu1
  have hj : 0 < RHCount.J d u := by linarith
  have hq := Q_nonneg d (1/2-u) (by linarith)
  rw [exponent_identity d u (ne_of_gt hj)] at hq
  have he : 0 ≤ -E d u := nonneg_of_mul_nonneg_right hq (by positivity)
  linarith
lemma boundary_identity : boundary = 11/12-ell/4 := by unfold boundary ell; ring
lemma critical_quadratic : 288*dc^2-588*dc+185 = 0 := by
  unfold dc
  ring_nf
  simp only [s_sq]
  ring
lemma critical_range : (3/8 : ℝ) < dc ∧ dc < 5/6 := by
  obtain ⟨hl, hu⟩ := s_bounds
  unfold dc
  constructor <;> linarith
lemma critical_count : R dc (1/2) = 2/3 := by
  have hj : RHCount.J dc (1/2) ≠ 0 := by
    have hh := RHCount.J_lower dc (1/2) (by linarith [critical_range.1])
      (le_of_lt critical_range.2) (by norm_num) (by norm_num)
    linarith
  unfold R
  field_simp [hj]
  unfold RHCount.J RHCount.P RHCount.D RHCount.A dc
  ring_nf
  simp only [s_sq]
  ring
lemma critical_endpoint : E dc (1/2) = 0 := by
  unfold E
  rw [critical_count]
  simp only [C0, dc, b, ell, h]
  ring_nf
  simp only [s_sq]
  ring
lemma gate_b_positive : 0 < b := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [b]
  linarith
lemma gate_x_minus_ell : ell < x := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [x, b, ell]
  linarith
lemma gate_y_minus_ell : ell < y := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, b, ell]
  linarith
lemma gate_ell_positive : 0 < ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [ell]
  linarith
lemma gate_h_positive : 0 < h := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_one_minus_three_ell : 3*ell < 1 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [ell]
  linarith
lemma gate_ell_below_one_fifth : ell < 1/5 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [ell]
  linarith
lemma gate_gram_uniform : 0 < y-ell-11*b/6 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, b, ell]
  linarith
lemma gate_supply : h/5 < ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_five_ell_minus_h : h < 5*ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_floor_saving : 0 < -C0-(1/2+3*ell/2)*(1/50) := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [C0, b, ell]
  linarith
lemma gate_intermediate_floor : 0 < -((225*ell+50-75*b)*(1/50)+78*ell-49*b-73)/300 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [b, ell]
  linarith
lemma gate_intermediate_top : 0 < -((225*ell+50-75*b)*(5/6)+78*ell-49*b-73)/300 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [b, ell]
  linarith
lemma gate_small_saving : 0 < y/2-13*h/75-2/100 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, h, b, ell]
  linarith
lemma gate_small_transport : 0 < y/2-13*h/75-2/100-(7/8-boundary) := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, h, b, ell, boundary]
  linarith
lemma gate_principal_y : 0 < y/20 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [y, b, ell]
  linarith
lemma gate_principal_h : 0 < h/600 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [h, b, ell]
  linarith
lemma gate_boundary_domain : 43/50 < boundary := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [boundary]
  linarith
lemma gate_v1_improvement : boundary < 34999/40000 := by
  obtain ⟨hl, hu⟩ := s_bounds
  simp only [boundary]
  linarith
def w0 : ℝ := (4+18*dc)/(9+18*dc)
def wK : ℝ := 2/(9+18*dc)
def wH : ℝ := 3/(9+18*dc)
lemma dual_den_pos : 0 < 9+18*dc := by linarith [critical_range.1]
lemma weights_pos : 0 < w0 ∧ 0 < wK ∧ 0 < wH := by
  have hh := critical_range.1
  have hd := dual_den_pos
  unfold w0 wK wH
  constructor
  · positivity
  constructor <;> positivity
lemma dual_identity (M l B : ℝ) :
    w0*(B-(5/6+M/12-l/6))+
    wK*(B-(1/3+7*M/12+l/3))+
    wH*(B-(1+dc-(1+dc)*M/2+dc*l)) = B-boundary := by
  unfold w0 wK wH
  field_simp [ne_of_gt dual_den_pos]
  unfold dc boundary
  ring_nf
  simp only [s_sq]
  ring
/-- Exact lower obstruction for the three necessary scalar majorants;
this is not a lower bound for the actual arithmetic energy. -/
theorem closure_obstruction (M l B : ℝ)
    (h0 : 5/6+M/12-l/6 ≤ B)
    (hK : 1/3+7*M/12+l/3 ≤ B)
    (hH : 1+dc-(1+dc)*M/2+dc*l ≤ B) : boundary ≤ B := by
  obtain ⟨hp0, hpK, hpH⟩ := weights_pos
  have hsum : 0 ≤ w0*(B-(5/6+M/12-l/6))+
      wK*(B-(1/3+7*M/12+l/3))+
      wH*(B-(1+dc-(1+dc)*M/2+dc*l)) := by positivity
  rw [dual_identity] at hsum
  linarith
lemma count_as_long (d u : ℝ) : R d u = RHCount.long d (RHCount.t d u) := by
  simp only [R, RHCount.long, RHCount.t]
  ring
/-- At the critical bin, every cutoff has count envelope at least 2/3. -/
theorem critical_count_minimax (t : ℝ) :
    (2/3 : ℝ) ≤ max (RHCount.short dc (1/2) t) (RHCount.long dc t) := by
  rw [← critical_count, count_as_long]
  exact RHCount.balance_is_minimax dc (1/2) t
    (by linarith [critical_range.1]) (le_of_lt critical_range.2)
    (by norm_num) (by norm_num)
/-- The three lower scalar faces are all attained at the proposed geometry. -/
theorem scalar_faces_attained :
    5/6+(1-ell)/12-ell/6 = boundary ∧
    1/3+7*(1-ell)/12+ell/3 = boundary ∧
    1+dc-(1+dc)*(1-ell)/2+dc*ell = boundary := by
  simp only [dc, ell, boundary]
  constructor
  · ring
  constructor
  · ring
  · ring_nf
    simp only [s_sq]
    ring
/-- Boundary optimum of the explicitly listed three-face scalar relaxation. -/
theorem scalar_optimum :
    (∀ M l B : ℝ, 5/6+M/12-l/6 ≤ B →
      1/3+7*M/12+l/3 ≤ B →
      1+dc-(1+dc)*M/2+dc*l ≤ B → boundary ≤ B) ∧
    (5/6+(1-ell)/12-ell/6 ≤ boundary ∧
      1/3+7*(1-ell)/12+ell/3 ≤ boundary ∧
      1+dc-(1+dc)*(1-ell)/2+dc*ell ≤ boundary) := by
  exact ⟨closure_obstruction, le_of_eq scalar_faces_attained.1,
    le_of_eq scalar_faces_attained.2.1, le_of_eq scalar_faces_attained.2.2⟩
lemma signal_matching : x/2+b/12 = boundary-(4+b)/6 := by
  simp only [x, ell, b, boundary]
  ring

lemma s_cube : s^3 = 921*s := by
  calc
    s^3 = s^2*s := by ring
    _ = 921*s := by rw [s_sq]
lemma disc_pos (v : ℝ) (hv : 0 < v) : 0 < disc v := by
  have hc1 := disc_coeff_1_pos
  have hc2 := disc_coeff_2_pos
  have hc3 := disc_coeff_3_pos
  have hc4 := disc_coeff_4_pos
  unfold disc
  positivity
lemma Q_at_zero (d : ℝ) : Q d 0 = Ac 0*(d-dc)^2 := by
  simp only [Q, Ac, C0, dc, h, b, ell]
  ring_nf
  simp only [s_sq, s_cube]
  ring
theorem Q_zero_iff (d v : ℝ) (hv : 0 ≤ v) :
    Q d v = 0 ↔ v = 0 ∧ d = dc := by
  constructor
  · intro hq
    have hv0 : v = 0 := by
      by_contra hn
      have hd := disc_pos v (lt_of_le_of_ne hv (Ne.symm hn))
      have hh := complete_square d v
      rw [hq, mul_zero] at hh
      nlinarith [sq_nonneg (2*Ac v*d+Dc v)]
    subst v
    rw [Q_at_zero] at hq
    have ha := Ac_pos 0 (by norm_num)
    have hdsq : (d-dc)^2 = 0 :=
      (mul_eq_zero.mp hq).resolve_left (ne_of_gt ha)
    exact ⟨rfl, by nlinarith [hdsq]⟩
  · rintro ⟨rfl, rfl⟩
    rw [Q_at_zero]
    ring
theorem endpoint_equality_iff (d u : ℝ) (hu1 : u ≤ 1/2)
    (hj : RHCount.J d u ≠ 0) : E d u = 0 ↔ u = 1/2 ∧ d = dc := by
  constructor
  · intro he
    have hq : Q d (1/2-u) = 0 := by rw [exponent_identity d u hj, he]; ring
    obtain ⟨hu, hd⟩ := (Q_zero_iff d (1/2-u) (by linarith)).mp hq
    exact ⟨by linarith, hd⟩
  · rintro ⟨rfl, rfl⟩
    exact critical_endpoint

#print axioms endpoint_equality_iff
#print axioms critical_count_minimax
#print axioms scalar_optimum
#print axioms signal_matching
#print axioms universal_endpoint
#print axioms critical_endpoint
#print axioms critical_count
#print axioms closure_obstruction
#print axioms gate_v1_improvement
end
end RHV2

end LocalModule134
/- END geometry.V2Optimization -/

/- BEGIN original module geometry.V2AnalyticGeometry -/
section LocalModule135
namespace RHV2
noncomputable section
def lowExponent : ℝ := x/2+b/12
def gramExponent : ℝ := x+b/6
lemma analytic_geometry :
    0 < ell ∧ ell < 1/5 ∧ 0 < b ∧ x < y ∧ y < 1 ∧
    0 < lowExponent ∧ 0 < x-b-ell ∧ x+y = 1-ell := by
  obtain ⟨hl, hu⟩ := s_bounds
  dsimp only [ell, b, x, y, lowExponent]
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor <;> try linarith
  constructor
  · linarith
  · ring
lemma lowExponent_signal : lowExponent = boundary-(4+b)/6 := signal_matching
end
end RHV2
macro "v2_geometry" : tactic => `(tactic|
  first
  | (solve | norm_num)
  | (solve | dsimp only [RHV2.x, RHV2.y, RHV2.h, RHV2.ell, RHV2.b,
       RHV2.lowExponent, RHV2.gramExponent, RHV2.boundary]
             obtain ⟨hl, hu⟩ := RHV2.s_bounds
             nlinarith only [hl, hu])
  | (solve | dsimp only [RHV2.x, RHV2.y, RHV2.h, RHV2.ell, RHV2.b,
       RHV2.lowExponent, RHV2.gramExponent, RHV2.boundary]
             ring))
macro "v2_ring" : tactic => `(tactic|
  (dsimp only [RHV2.x, RHV2.y, RHV2.h, RHV2.ell, RHV2.b,
    RHV2.lowExponent, RHV2.gramExponent, RHV2.boundary] <;> ring))

end LocalModule135
/- END geometry.V2AnalyticGeometry -/

/- BEGIN original module analytic_low.V2SourceScales -/
section LocalModule136

namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma v2_source_gram_power (Z δ : ℝ) (hZ : 0< Z) :
    Z^(RHV2.x:ℝ)*(Z^(RHV2.b:ℝ))^(1/6:ℝ)*(Z^(RHV2.y:ℝ))^δ=
      Z^(RHV2.gramExponent+(RHV2.y)*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  v2_ring

lemma v2_source_gram_sqrt_power (Z δ : ℝ) (hZ : 0< Z) :
    Real.sqrt (Z^(RHV2.gramExponent+(RHV2.y)*δ:ℝ))=Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  v2_ring

lemma v2_source_scale_ratio (Z : ℝ) (hZ : 0< Z) :
    Z^(RHV2.y:ℝ)/Z^(RHV2.x:ℝ)=Z^(RHV2.b:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [←Real.rpow_sub hZ]
  v2_geometry

lemma v2_source_scale_square (Z : ℝ) (hZ : 0< Z) :
    Z^((2*RHV2.x-RHV2.y):ℝ)*Z^(RHV2.y:ℝ)=(Z^(RHV2.x:ℝ))^2 := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [←Real.rpow_add hZ,←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  v2_geometry

lemma v2_source_compensated_scale_admissible (q Z L : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(RHV2.b:ℝ)) (hLl : L≤ Z^((2*RHV2.x-RHV2.y):ℝ)) :
    1≤ Z^(RHV2.y:ℝ)/L ∧
    q*Z^(RHV2.x:ℝ)≤ Z^(RHV2.y:ℝ) ∧
    L*Z^(RHV2.y:ℝ)≤ q^2*(Z^(RHV2.x:ℝ))^2 := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  constructor
  · apply (le_div_iff₀ hl).mpr
    simpa using hLl.trans (Real.rpow_le_rpow_of_exponent_le hZ (show ((2*RHV2.x-RHV2.y):ℝ)≤ RHV2.y by v2_geometry))
  constructor
  · apply (le_div_iff₀ (Real.rpow_pos_of_pos hz (RHV2.x))).mp
    rwa [v2_source_scale_ratio Z hz]
  · calc
      _≤ Z^((2*RHV2.x-RHV2.y):ℝ)*Z^(RHV2.y:ℝ) := mul_le_mul_of_nonneg_right hLl (by positivity)
      _=(Z^(RHV2.x:ℝ))^2 := v2_source_scale_square Z hz
      _≤_ := le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)

lemma v2_source_compensated_gram_scale (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(RHV2.b:ℝ)) (hLl : L≤ Z^((2*RHV2.x-RHV2.y):ℝ)) (hδ : 0≤δ) :
    (q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)/(Z^(RHV2.y:ℝ)/L))*
      (1+((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^2/(Z^(RHV2.y:ℝ)/L))*
      (Z^(RHV2.y:ℝ)/L)^δ ≤
        (3*q/L)*Z^(RHV2.gramExponent+(RHV2.y)*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hq0 : 0< q := lt_of_lt_of_le zero_lt_one hq
  have hL0 : 0< L := lt_of_lt_of_le zero_lt_one hL
  obtain ⟨_,hqp,ht⟩ := v2_source_compensated_scale_admissible q Z L hq hZ hL hql hLl
  have hb := compensated_gram_scale_bound q (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) L δ hq0
    (by positivity) (by positivity) hL hδ hqp ht
  apply hb.trans
  have hratio : Z^(RHV2.y:ℝ)/(q*Z^(RHV2.x:ℝ))≤ Z^(RHV2.b:ℝ) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    rw [←v2_source_scale_ratio Z hz]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hp := Real.rpow_le_rpow (by positivity : 0≤ Z^(RHV2.y:ℝ)/(q*Z^(RHV2.x:ℝ))) hratio (show 0≤(1/6:ℝ) by v2_geometry)
  calc
    _≤3*(q*Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.b:ℝ))^(1/6:ℝ)*(Z^(RHV2.y:ℝ))^δ := by gcongr
    _=(3*q/L)*(Z^(RHV2.x:ℝ)*(Z^(RHV2.b:ℝ))^(1/6:ℝ)*(Z^(RHV2.y:ℝ))^δ) := by v2_ring
    _=_ := by rw [v2_source_gram_power Z δ hz]

lemma v2_source_compensated_gram_sqrt (q Z L δ : ℝ) (hq : 1≤ q) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : q≤ Z^(RHV2.b:ℝ)) (hLl : L≤ Z^((2*RHV2.x-RHV2.y):ℝ)) (hδ : 0≤δ) :
    Real.sqrt ((q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)/(Z^(RHV2.y:ℝ)/L))*
      (1+((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^(1/6:ℝ)+
        ((Z^(RHV2.y:ℝ)/L)^2/(q*(Z^(RHV2.x:ℝ)/L)*(Z^(RHV2.y:ℝ)/L)))^2/(Z^(RHV2.y:ℝ)/L))*
      (Z^(RHV2.y:ℝ)/L)^δ) ≤
        Real.sqrt (3*q/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  apply (Real.sqrt_le_sqrt (v2_source_compensated_gram_scale q Z L δ hq hZ hL hql hLl hδ)).trans_eq
  rw [Real.sqrt_mul (by positivity),v2_source_gram_sqrt_power Z δ (lt_of_lt_of_le zero_lt_one hZ)]

lemma v2_lowGramFactor_source_bound (C : CalibrationData) (Z L δ : ℝ) (hZ : 1≤ Z)
    (hL : 1≤ L) (hql : elementNorm C.generator≤ Z^(RHV2.b:ℝ))
    (hLl : L≤ Z^((2*RHV2.x-RHV2.y):ℝ)) (hδ : 0≤δ) :
    lowGramFactor C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) δ≤
      Real.sqrt (3*elementNorm C.generator/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) :=
  v2_source_compensated_gram_sqrt _ Z L δ (calibration_elementNorm_ge_one C) hZ hL hql hLl hδ

lemma v2_eventually_compensated_source_scales (C : CalibrationData) (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧ elementNorm C.generator≤ Z^(RHV2.b:ℝ) ∧
      ∀L : ℝ,1≤ L→L≤ B*Z^(RHV2.ell:ℝ)→
        1≤ Z^(RHV2.y:ℝ)/L ∧
        1≤(Z^(RHV2.y:ℝ)/L)^2/lowPhysicalScale C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) ∧
        ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) δ≤
          Real.sqrt (3*elementNorm C.generator/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hq := (tendsto_rpow_atTop (show 0<(RHV2.b:ℝ) by v2_geometry)).eventually
    (Filter.eventually_ge_atTop (elementNorm C.generator))
  have hb := (tendsto_rpow_atTop (show 0<((3/50):ℝ) by v2_geometry)).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1:ℝ),hq,hb] with Z hZ hq hb
  refine ⟨hZ,hq,?_⟩
  intro L hL hLB
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hl : 0< L := lt_of_lt_of_le zero_lt_one hL
  have hLl : L≤ Z^((2*RHV2.x-RHV2.y):ℝ) := calc
    L≤ B*Z^(RHV2.ell:ℝ) := hLB
    _≤ Z^((3/50):ℝ)*Z^(RHV2.ell:ℝ) := mul_le_mul_of_nonneg_right hb (by positivity)
    _=Z^((3/50+RHV2.ell):ℝ) := by rw [←Real.rpow_add hz]
    _≤ Z^((2*RHV2.x-RHV2.y):ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hZ (by v2_geometry)
  obtain ⟨hy,hp,_⟩ := v2_source_compensated_scale_admissible _ Z L (calibration_elementNorm_ge_one C) hZ hL hq hLl
  refine ⟨hy,?_,fun δ hδ=> v2_lowGramFactor_source_bound C Z L δ hZ hL hq hLl hδ⟩
  rw [lowPhysicalScale,compensated_gram_ratio _ _ _ _ (calibration_elementNorm_pos C)
    (by positivity) (by positivity) hl]
  exact (le_div_iff₀ (mul_pos (calibration_elementNorm_pos C) (by positivity))).mpr (by simpa using hp)

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule136
/- END analytic_low.V2SourceScales -/

/- BEGIN original module analytic_low.V2SlotScales -/
section LocalModule137

namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss
local notation "O" => ActualEisensteinCubic.O

lemma v2_lowUnselectedProduct_norm_bound {K : ℕ} (ell : Fin K→ℝ)
    (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (b Z : ℝ) (hb : 1≤ b) (hZ : 1≤ Z) (slots : Fin K→Finset O)
    (hslots : ∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) :
    elementNorm (∏i : J,(a i).val)≤ b^K*Z^(RHV2.ell:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hsub : ∑i∈J,ell i≤ RHV2.ell :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> hell i)).trans hsum
  have hc : J.card≤ K := by simpa using Finset.card_le_card (Finset.subset_univ J)
  rw [elementNorm_finset_prod]
  calc
    _≤∏i : J,b*Z^(ell i.val) := Finset.prod_le_prod₀ (fun _ _=> by unfold elementNorm;positivity)
      (fun i _=> hslots i.val _ (a i).property)
    _=b^J.card*Z^(∑i∈J,ell i) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_coe,
        ←Real.rpow_sum_of_pos hz,Finset.sum_coe_sort]
    _≤ b^K*Z^(RHV2.ell:ℝ) := mul_le_mul (pow_le_pow_right₀ hb hc)
      (Real.rpow_le_rpow_of_exponent_le hZ hsub) (by positivity) (by positivity)

theorem v2_eventually_original_slot_scales {K : ℕ} (C : CalibrationData) (ell : Fin K→ℝ)
    (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell) (b : ℝ) (hb : 1≤ b) :
    ∀ᶠ Z : ℝ in Filter.atTop,1≤ Z ∧
      ∀(slots : Fin K→Finset O)(_hslots : ∀i x,x∈slots i→x≠0),
      (∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))→
      ∀(J : Finset (Fin K))(a : LowUnselectedTuple slots J),
      let L := elementNorm (∏i : J,(a i).val)
      1≤ Z^(RHV2.y:ℝ)/L ∧
      1≤(Z^(RHV2.y:ℝ)/L)^2/lowPhysicalScale C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) ∧
      ∀δ : ℝ,0≤δ→lowGramFactor C (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) δ≤
        Real.sqrt (3*elementNorm C.generator/L)*Z^(RHV2.lowExponent+((RHV2.y/2))*δ:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  filter_upwards [v2_eventually_compensated_source_scales C (b^K)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro slots hslots hnorm J a
  exact hZ.2.2 _ (lowUnselectedProduct_norm_ge_one slots hslots J a)
    (v2_lowUnselectedProduct_norm_bound ell hell hsum b Z hb hZ.1 slots hnorm J a)

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule137
/- END analytic_low.V2SlotScales -/

/- BEGIN original module analytic_low.V2CentralTuple -/
section LocalModule138

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma v2_compensated_sqrt_factor (q L : ℝ) (hq : 0≤ q) (hL : 0< L) :
    Real.sqrt (3*q/L)=Real.sqrt (3*q)*L^(-(1/2:ℝ)) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [Real.sqrt_div (by positivity)]
  simp only [div_eq_mul_inv,Real.sqrt_eq_rpow,Real.rpow_neg hL.le]

theorem v2_low_central_compensated_tuple (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(X : ℝ),0< X→
      Z^(1+lowSelectedLength ell J-ε/2)≤ X→X≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→∀t : ℝ,
      ‖∑p : ∀i,canonicalSlotSupport (T i),
        compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J*
          compensationRowTest η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J
            (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) X t*
          selectedSlotFactor W (fun i=> Z^(ell i)) (fun i=>(p i).val) J t‖≤
        C*(1+‖t‖)^degree*Z^(RHV2.lowExponent+254*ε) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  obtain ⟨Cg,hCg,hgram⟩ := compensation_tuple_actual_gram ε hε hε1 W0 W1
    a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM S hS hbad
  obtain ⟨degree,Ci,hCi,hinverse⟩ := perturbed_low_physical_inverse_normalized (RHV2.ell) (RHV2.x) (RHV2.y) (by v2_geometry) (by v2_geometry) (by v2_geometry) η S hS hbad ell hell hsum
    a b (a0*a1) (max 1 (b0*b1)) ε ha (mul_pos ha0 ha1)
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hε hε1.le
  obtain ⟨Cu,hCu,hmass⟩ := perturbed_lowUnselectedMass_bound K 1 (by v2_geometry)
  let q := elementNorm (calibrationForSet S hS).generator
  have hq : 0< q := calibration_elementNorm_pos _
  let c := (min 1 a)^K
  have hc : 0< c := by dsimp [c];positivity
  let C0 := Cg*Ci*Real.sqrt (3*q)*c^(-(1/2:ℝ))*Cu
  have hC0 : 0< C0 := by dsimp [C0];positivity
  refine ⟨degree,C0,hC0,?_⟩
  filter_upwards [hinverse,v2_eventually_original_slot_scales (calibrationForSet S hS)
    ell hell hsum (max 1 b) (le_max_left _ _)] with Z hInv hScale
  refine ⟨hInv.1,?_⟩
  intro T hT hout hdis hnorm J X hX hXlo hXhi W hW t
  let slots := fun i=> canonicalSlotSupport (T i)
  let Yp := fun i=> Z^(ell i)
  have hz : 0< Z := lt_trans zero_lt_one hInv.1
  have hslots : ∀i n,n∈slots i→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈slots i→elementNorm n≤ max 1 b*Z^(ell i) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact (hnorm i P hP).2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hs := hScale.2 slots hslots hnormE J
  have hg := hgram K η slots hslots J W Yp (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) X t
    (by positivity) (by positivity) hX (fun p=>(hs p).1) (fun p=>(hs p).2.1)
  apply hg.trans
  let G := Z^(RHV2.lowExponent+((RHV2.y/2))*ε:ℝ)
  let correction := max (lowUnselectedLength ell J+5*(RHV2.ell:ℝ)-1) 0/8
  let V := Ci*(1+‖t‖)^degree*Z^(correction+507*ε/2)
  have hGV : G*V≤ Ci*(1+‖t‖)^degree*Z^(RHV2.lowExponent+254*ε+correction) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    dsimp only [G,V]
    calc
      _=Ci*(1+‖t‖)^degree*(Z^(RHV2.lowExponent+((RHV2.y/2))*ε:ℝ)*Z^(correction+507*ε/2)) := by ring
      _≤_ := by
        obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
        rw [←Real.rpow_add hz]
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Real.rpow_le_rpow_of_exponent_le hInv.1.le (by nlinarith)
  have hterm (p : LowUnselectedTuple slots J) :
      let L := elementNorm (∏i : J,(p i).val)
      let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L)
      ‖lowUnselectedWeight slots J W Yp p‖*((Real.sqrt Q)⁻¹/(2*Real.pi))*
        lowGramFactor (calibrationForSet S hS) (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) ε*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
          (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L)
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (div_pos (by positivity) (lowUnselectedProduct_norm_pos slots hslots J p))
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t)
            η S hS (lowSelectedIdeal slots J) X t)≤
      (Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(RHV2.lowExponent+254*ε))*c^(-(1/2:ℝ))*
        (‖lowUnselectedWeight slots J W Yp p‖*L^(0:ℝ)) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    dsimp only
    let L := elementNorm (∏i : J,(p i).val)
    let Q := lowPhysicalScale (calibrationForSet S hS) (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L)
    have hL := lowUnselectedProduct_norm_pos slots hslots J p
    have hgb := (hs p).2.2 ε hε.le
    have hib := hInv.2 T hT hout hdis hnorm J p X hX hXlo hXhi W hW t
      (div_pos (by positivity) hL) (div_pos (by positivity) hL)
    have hgn : 0≤ lowGramFactor (calibrationForSet S hS) (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) ε := Real.sqrt_nonneg _
    have hh := mul_le_mul_of_nonneg_left hib
      (mul_nonneg (norm_nonneg (lowUnselectedWeight slots J W Yp p)) hgn)
    have hh2 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hgb (norm_nonneg (lowUnselectedWeight slots J W Yp p)))
      (show 0≤ V by dsimp [V];positivity)
    calc
      _=‖lowUnselectedWeight slots J W Yp p‖*
        lowGramFactor (calibrationForSet S hS) (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L) ε*
        (Real.sqrt Q)⁻¹/(2*Real.pi)*
        lowInverseMass (calibrationForSet S hS) (a0*a1) (max 1 (b0*b1)) (mul_pos ha0 ha1)
          (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (Z^(RHV2.x:ℝ)/L) (Z^(RHV2.y:ℝ)/L)
          (div_pos (by positivity) hL) (div_pos (by positivity) hL)
          (lowSelectedInverseRow Finset.univ (lowSelectedWeight η slots J W Yp t) η S hS (lowSelectedIdeal slots J) X t) := by dsimp only [L, Q]; ring
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*(G*V) := by
        obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
        have hh3 := hh.trans hh2
        simp only [G,V,div_eq_mul_inv,mul_assoc] at hh3 ⊢
        convert hh3 using 1 ; congr 7
      _≤(‖lowUnselectedWeight slots J W Yp p‖*Real.sqrt (3*q/L))*
          (Ci*(1+‖t‖)^degree*Z^(RHV2.lowExponent+254*ε+correction)) :=
        mul_le_mul_of_nonneg_left hGV (by positivity)
      _≤_ := by
        obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
        have hnormlo : ∀i n,n∈slots i→a*Z^(ell i)≤ elementNorm n := by
          obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
          intro i n hn
          obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
          rw [primaryTuple_norm P (hT i P hP)]
          exact (hnorm i P hP).1
        have hLlo : c*Z^(lowUnselectedLength ell J)≤ L :=
          lowUnselectedProduct_norm_lower ell a Z ha hz slots hnormlo J p
        have hd := (perturbed_lowLength_bounds (RHV2.ell) ell hell hsum J).1
        have hf := perturbed_compensation_factor (RHV2.ell) Z L c (lowUnselectedLength ell J)
          (by v2_geometry) hInv.1.le hc hd hLlo
        rw [v2_compensated_sqrt_factor q L hq.le hL]
        rw [Real.rpow_add hz]
        have hh := mul_le_mul_of_nonneg_left hf
          (show 0≤ Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(RHV2.lowExponent+254*ε)*‖lowUnselectedWeight slots J W Yp p‖ by positivity)
        simp only [Real.rpow_zero]
        convert hh using 1 <;> ring
  have hh := mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=Finset.univ) (fun p _=> hterm p)) hCg.le
  apply hh.trans
  rw [←Finset.mul_sum]
  have hm := hmass T hT J W Yp hW
  calc
    _≤ Cg*((Ci*Real.sqrt (3*q)*(1+‖t‖)^degree*Z^(RHV2.lowExponent+254*ε))*c^(-(1/2:ℝ))*Cu) := by gcongr
    _=_ := by dsimp [C0];v2_ring

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule138
/- END analytic_low.V2CentralTuple -/

/- BEGIN original module analytic_low.V2GaussianDyad -/
section LocalModule139

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem v2_low_central_gaussian_dyad (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃degree : ℕ,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(U : ℝ),0< U→
      Z^(1+lowSelectedLength ell J-ε/2)≤ U→U≤ Z^(1+lowSelectedLength ell J+ε/2)→
    ∀(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
    ∀(V : SchwartzMap ℝ ℂ)(hV : HasCompactSupport (V:ℝ→ℂ)),
      ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
        W (fun i=> Z^(ell i)) J (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) U
          (Z^(1+lowSelectedLength ell J)) V hV‖≤
        C*Z^(RHV2.lowExponent+254*ε)*gaussianJointMoment V hV degree (U/Z^(1+lowSelectedLength ell J)) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  obtain ⟨degree,C,hC,he⟩ := v2_low_central_compensated_tuple η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  refine ⟨degree,C,hC,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J U hU hlo hhi W hW V hV
  apply lowCommonDyad_norm_of_bound
  intro t
  simpa only [mul_assoc,mul_left_comm,mul_comm] using hZ.2 T hT hout hdis hnorm J U hU hlo hhi W hW t

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule139
/- END analytic_low.V2GaussianDyad -/

/- BEGIN original module analytic_low.V2RemoteMass -/
section LocalModule140
namespace OAI
noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
lemma v2_canonicalTuple_count {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ RHV2.ell) (b Z : ℝ) (hZ : 1≤ Z)
    (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i)) :
    (Fintype.card (∀i,canonicalSlotSupport (T i)):ℝ)≤(128*max 1 b)^K*Z^(RHV2.ell:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  rw [Fintype.card_pi,Nat.cast_prod]
  calc
    _≤∏i,128*(max 1 b*Z^(ell i)) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      apply Finset.prod_le_prod₀ (fun i _=> Nat.cast_nonneg _)
      intro i hi
      simp only [Fintype.card_coe]
      apply canonicalSlot_count _ (hT i) _
        (one_le_mul_of_one_le_of_one_le (le_max_left _ _) (Real.one_le_rpow hZ (hell i)))
      intro P hP
      exact (hnorm i P hP).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _=(128*max 1 b)^K*Z^(∑i,ell i) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      simp_rw [←mul_assoc]
      rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
        ←Real.rpow_sum_of_pos (lt_of_lt_of_le zero_lt_one hZ)]
    _≤_ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hsum) (by positivity)

lemma v2_compensation_scale_mass_bound {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (b Z : ℝ) (hZ : 1≤ Z) (T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val)
    (hnorm : ∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (hW : ∀i x,‖W i x‖≤1) :
    gaussianPhysicalScaleMass C (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
      (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
      (fun p=> Z^(RHV2.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun p=> Z^(RHV2.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
      (fun i : SelectedSlot J=> W i.val)
      (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))≤
        (elementNorm C.generator*(128*max 1 b)^K)*Z := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hp (p : ∀i,canonicalSlotSupport (T i)) (i : Fin K) : (p i).val≠0 :=
    canonicalSlotSupport_nonzero _ (hT i) _ (p i).property
  have hterm (p : ∀i,canonicalSlotSupport (T i)) :
      ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)*
        lowPhysicalScale C (Z^(RHV2.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
          (Z^(RHV2.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))≤
      elementNorm C.generator*Z^((1-RHV2.ell):ℝ) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    have hcoeff : ‖compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J‖*
        (∏i : SelectedSlot J,‖W i.val (elementNorm (p i.val).val/Z^(ell i.val))‖)≤1 := (mul_le_of_le_one_left (Finset.prod_nonneg (fun _ _=> norm_nonneg _)) (compensationSubsetWeight_norm_le_one η W hW _ _ (hp p) J)).trans (Finset.prod_le_one₀ (fun _ _=> norm_nonneg _) (fun (i : SelectedSlot J) _=> hW i.val _))
    have hL := slotProduct_norm_ge_one _ (hp p) J
    rw [perturbed_lowPhysicalScale_source (RHV2.ell) (RHV2.x) (RHV2.y) (by v2_geometry) C Z _ hz]
    rw [show (1-(RHV2.ell:ℝ))=(1-RHV2.ell) by v2_geometry]
    apply (mul_le_of_le_one_left (by unfold elementNorm;positivity) hcoeff).trans
    exact div_le_self (by unfold elementNorm;positivity) (one_le_pow₀ hL)
  unfold gaussianPhysicalScaleMass
  apply (Finset.sum_le_sum (fun p _=> hterm p)).trans
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have hc := mul_le_mul_of_nonneg_right (v2_canonicalTuple_count ell hell hsum b Z hZ T hT hnorm)
    (show 0≤ elementNorm C.generator*Z^((1-RHV2.ell):ℝ) by unfold elementNorm;positivity)
  apply hc.trans_eq
  calc
    _=(elementNorm C.generator*(128*max 1 b)^K)*(Z^(RHV2.ell:ℝ)*Z^((1-RHV2.ell):ℝ)) := by v2_ring
    _=_ := by rw [←Real.rpow_add hz];v2_geometry

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule140
/- END analytic_low.V2RemoteMass -/

/- BEGIN original module analytic_low.V2GaussianRemote -/
section LocalModule141

namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma v2_eventually_low_physical_scales {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i)
    (hsum : ∑i,ell i≤ RHV2.ell) (b : ℝ) :
    ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
      ∀(slots : Fin K→Finset O),(∀i x,x∈slots i→x≠0)→
      (∀i x,x∈slots i→elementNorm x≤ b*Z^(ell i))→
      ∀(J : Finset (Fin K))(p : ∀i,slots i),
      1≤ Z^(RHV2.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) ∧
      1≤ Z^(RHV2.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  filter_upwards [Filter.eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<((RHV2.x-RHV2.ell):ℝ) by v2_geometry)).eventually
      (Filter.eventually_ge_atTop ((max 1 b)^K))] with Z hZ hc
  refine ⟨hZ,?_⟩
  intro slots hn hnorm J p
  have hl : 0< elementNorm (slotProduct (fun i=>(p i).val) J) :=
    slotProduct_norm_pos _ (fun i=> hn i _ (p i).property) J
  have hb := v2_lowUnselectedProduct_norm_bound ell hell hsum (max 1 b) Z (le_max_left _ _) hZ.le
    slots (fun i n hm=>(hnorm i n hm).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
    J (fun i=> p i.val)
  rw [←slotProduct_subtype (fun i=>(p i).val) J] at hb
  have hLX : elementNorm (slotProduct (fun i=>(p i).val) J)≤ Z^(RHV2.x:ℝ) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    apply hb.trans
    calc
      _≤ Z^((RHV2.x-RHV2.ell):ℝ)*Z^(RHV2.ell:ℝ) := mul_le_mul_of_nonneg_right hc (by positivity)
      _=_ := by rw [←Real.rpow_add (lt_trans zero_lt_one hZ)] ; v2_geometry
  constructor
  · exact (one_le_div hl).mpr hLX
  · exact (one_le_div hl).mpr (hLX.trans
      (Real.rpow_le_rpow_of_exponent_le hZ.le (by v2_geometry)))

lemma v2_low_remote_power (Z ell ε : ℝ) (N : ℕ) (hZ : 1≤ Z) (hell : ell≤ RHV2.ell)
    (hN : 9/2≤(ε/2)*(N:ℝ)) :
    Z*(Z^(1+ell))^2/(Z^(ε/2))^N≤ Z^(-1:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hz : 0< Z := lt_of_lt_of_le zero_lt_one hZ
  have hsq : (Z^(1+ell))^2=Z^(2*(1+ell)) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    push_cast
    ring
  have hn : (Z^(ε/2))^N=Z^((ε/2)*(N:ℝ)) := by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
  rw [hsq,hn,show Z*Z^(2*(1+ell))=Z^(1+2*(1+ell)) by rw [Real.rpow_add hz,Real.rpow_one],←Real.rpow_sub hz]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem v2_low_remote_gaussian_dyads (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (b ε : ℝ) (hε : 0<ε) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(η : HeckeFamily.Character)(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→(Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖ else 0
      Summable f ∧ (∑'j : ℕ,f j)≤ C*Z^(-1:ℝ) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  have hep : 0<ε/2 := by nlinarith
  obtain ⟨N,hN⟩ := exists_nat_gt ((9/2:ℝ)/(ε/2))
  have hN' : (9/2:ℝ)≤(ε/2)*(N:ℝ) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    have hh := (div_lt_iff₀ hep).mp hN
    nlinarith
  obtain ⟨Cg,hCg,he⟩ := gaussianPhysicalFamily_remote_polynomial V hV N
    a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1
  let q := elementNorm (calibrationForSet S hS).generator
  let C0 := Cg*(q*(128*max 1 b)^K)
  have hq : 0< q := calibration_elementNorm_pos _
  refine ⟨C0,by dsimp [C0];positivity,?_⟩
  filter_upwards [v2_eventually_low_physical_scales ell hell hsum b] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro η T hT hnorm J W hW
  dsimp only [lowRemote]
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  have hnormE : ∀i n,n∈canonicalSlotSupport (T i)→elementNorm n≤ b*Z^(ell i) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    intro i n hn
    obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hn
    rw [primaryTuple_norm P (hT i P hP)]
    exact hnorm i P hP
  have hs := hZ.2 _ hslots hnormE J
  have hh := he η S hS W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    hW0 hW1 hWB0 hWB1 (Finset.univ : Finset (∀i,canonicalSlotSupport (T i)))
    (fun p=> compensationSubsetWeight η W (fun i=> Z^(ell i)) (fun i=>(p i).val) J)
    (fun p=> Ideal.span {slotProduct (fun i=>(p i).val) (Finset.univ\J)})
    (fun p=> Z^(RHV2.x:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p=> Z^(RHV2.y:ℝ)/elementNorm (slotProduct (fun i=>(p i).val) J))
    (fun p _=>(hs p).1) (fun p _=>(hs p).2)
    (fun i : SelectedSlot J=> W i.val) (fun p i=> elementNorm (p i.val).val/Z^(ell i.val))
    (Z^(1+lowSelectedLength ell J)) (Z^(ε/2)) (by positivity) (Real.one_le_rpow hZ.1.le hep.le)
  simp only [←lowCommonDyad_eq_family] at hh
  refine ⟨?_,?_⟩
  · convert hh.1 using 1
    funext j
    split_ifs with h <;> simp_all only [ite_true, ite_false]
  · have hhFinal := hh.2.trans (show _≤ C0*Z^(-1:ℝ) from by
      have hm := v2_compensation_scale_mass_bound η (calibrationForSet S hS) ell hell hsum b Z hZ.1.le T hT hnorm J W hW
      calc
        _≤ Cg*((q*(128*max 1 b)^K)*Z)*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N := by gcongr
        _=C0*(Z*(Z^(1+lowSelectedLength ell J))^2/(Z^(ε/2))^N) := by dsimp [C0];ring
        _≤_ := mul_le_mul_of_nonneg_left (v2_low_remote_power Z (lowSelectedLength ell J) ε N hZ.1.le
          (by have hb := perturbed_lowLength_bounds (RHV2.ell) ell hell hsum J;nlinarith) hN') (by dsimp [C0];positivity))
    convert hhFinal using 1
    apply tsum_congr
    intro j
    split_ifs with h <;> simp_all only [ite_true, ite_false]

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule141
/- END analytic_low.V2GaussianRemote -/

/- BEGIN original module analytic_low.V2GaussianCentral -/
section LocalModule142

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem v2_low_central_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 M : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hM : 0≤ M)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤ M) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
        ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV‖
      Summable f ∧ (∑'j : ℕ,f j)≤ C*Z^(RHV2.lowExponent+256*ε) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  obtain ⟨degree,C,hC,he⟩ := v2_low_central_gaussian_dyad η S hS hbad ell hell hsum
    a b ε ha hε hε1 W0 W1 a0 b0 a1 b1 M ha0 ha1 hab1 hM hW0 hW1 hW0s hW1s hWM
  obtain ⟨Cm,hCm,hm⟩ := gaussianJointMoment_summed V hV degree ε hε
  refine ⟨C*Cm,mul_pos hC hCm,?_⟩
  filter_upwards [he] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  let R := Z^(1+lowSelectedLength ell J)
  let f := fun j : ℕ=> if lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j) then 0 else
    ‖lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
      W (fun i=> Z^(ell i)) J (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) ((2:ℝ)^j) R V hV‖
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  obtain ⟨hsm,hmb⟩ := hm R (by dsimp [R];positivity)
  have hb (j : ℕ) : f j≤(C*Z^(RHV2.lowExponent+254*ε))*
      (((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    dsimp only [f]
    split_ifs with hj
    · exact mul_nonneg (by positivity) (mul_nonneg (by positivity) (gaussianJointMoment_nonneg V hV degree _))
    · obtain ⟨hlo,hhi⟩ := not_lowRemote_bounds Z (lowSelectedLength ell J) ε ((2:ℝ)^j) hz hj
      apply (hZ.2 T hT hout hdis hnorm J ((2:ℝ)^j) (by positivity) hlo hhi W hW V hV).trans
      have hp : 1≤((2:ℝ)^j)^ε := Real.one_le_rpow (one_le_pow₀ (by v2_geometry)) hε.le
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact le_mul_of_one_le_left (gaussianJointMoment_nonneg V hV degree _) hp
  have hn (j : ℕ) : 0≤ f j := by dsimp [f];split_ifs <;> positivity
  have hsumf := Summable.of_nonneg_of_le hn hb (hsm.mul_left (C*Z^(RHV2.lowExponent+254*ε)))
  refine ⟨hsumf,?_⟩
  calc
    _≤∑'j : ℕ,(C*Z^(RHV2.lowExponent+254*ε))*(((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) :=
      hsumf.tsum_le_tsum hb (hsm.mul_left _)
    _=(C*Z^(RHV2.lowExponent+254*ε))*(∑'j : ℕ,((2:ℝ)^j)^ε*gaussianJointMoment V hV degree ((2:ℝ)^j/R)) := tsum_mul_left
    _≤(C*Z^(RHV2.lowExponent+254*ε))*(Cm*R^ε) := mul_le_mul_of_nonneg_left hmb (by positivity)
    _≤_ := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      dsimp only [R]
      rw [←Real.rpow_mul hz.le]
      calc
        _=(C*Cm)*(Z^(RHV2.lowExponent+254*ε)*Z^((1+lowSelectedLength ell J)*ε)) := by v2_ring
        _≤_ := by
          obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
          rw [←Real.rpow_add hz]
          apply mul_le_mul_of_nonneg_left _ (mul_pos hC hCm).le
          have hh := perturbed_lowLength_bounds (RHV2.ell) ell hell hsum J
          exact Real.rpow_le_rpow_of_exponent_le hZ.1.le (by nlinarith)

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule142
/- END analytic_low.V2GaussianCentral -/

/- BEGIN original module analytic_low.V2GaussianSum -/
section LocalModule143

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem v2_low_all_gaussian_dyads (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
    ∀(J : Finset (Fin K))(W : Fin K→ℝ→ℂ),(∀i x,‖W i x‖≤1)→
      let f := fun j : ℕ=> lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i))
          W (fun i=> Z^(ell i)) J (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) ((2:ℝ)^j)
            (Z^(1+lowSelectedLength ell J)) V hV
      Summable f ∧ ‖∑'j : ℕ,f j‖≤ C*Z^(RHV2.lowExponent+256*ε) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  obtain ⟨Cc,hCc,hcentral⟩ := v2_low_central_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 V hV W0 W1 a0 b0 a1 b1 B1 ha0 ha1 hab1 hB1 hW0 hW1 hW0s hW1s hWB1
  obtain ⟨Cr,hCr,hremote⟩ := v2_low_remote_gaussian_dyads S hS ell hell hsum b ε hε V hV
    W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hB0 hB1 hW0 hW1 hWB0 hWB1
  refine ⟨Cc+Cr,add_pos hCc hCr,?_⟩
  filter_upwards [hcentral,hremote] with Z hc hr
  refine ⟨hc.1,?_⟩
  intro T hT hout hdis hnorm J W hW
  have hc' := hc.2 T hT hout hdis hnorm J W hW
  have hr' := hr.2 η T hT (fun i P hP=>(hnorm i P hP).2) J W hW
  dsimp only at hc' hr' ⊢
  have hh := low_dyad_norm_split _ (fun j=> lowRemote Z (lowSelectedLength ell J) ε ((2:ℝ)^j)) hc'.1 hr'.1
  refine ⟨hh.1,hh.2.trans ?_⟩
  have hp : Z^(-1:ℝ)≤ Z^(RHV2.lowExponent+256*ε) := Real.rpow_le_rpow_of_exponent_le hc.1.le (by nlinarith)
  calc
    _≤ Cc*Z^(RHV2.lowExponent+256*ε)+Cr*Z^(-1:ℝ) := add_le_add hc'.2 hr'.2
    _≤ Cc*Z^(RHV2.lowExponent+256*ε)+Cr*Z^(RHV2.lowExponent+256*ε) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hp hCr.le)
    _=_ := by v2_ring

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule143
/- END analytic_low.V2GaussianSum -/

/- BEGIN original module analytic_low.V2CommonBound -/
section LocalModule144

namespace OAI

noncomputable section
open scoped Classical ContDiff SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem v2_compensatedPhysicalProbe_low (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hsum : ∑i,ell i≤ RHV2.ell)
    (a b ε : ℝ) (ha : 0< a) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,1< Z ∧
    ∀(T : Fin K→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal),(∀i P,P∈T i→Supported P.val)→
      (∀i P,P∈T i→P.val∉S)→Pairwise (fun i j=> Disjoint (T i) (T j))→
      (∀i P,P∈T i→a*Z^(ell i)≤(Ideal.absNorm P.val:ℝ) ∧ (Ideal.absNorm P.val:ℝ)≤ b*Z^(ell i))→
      ‖compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
        (fun i=> canonicalSlotSupport (T i)) W (fun i=> Z^(ell i))
        (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z‖≤ C*Z^(RHV2.lowExponent+256*ε) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  obtain ⟨V,hV,hbudget,hidentity⟩ := compensatedPhysicalProbe_common_gaussian W
    (fun _=>|Real.log a|+|Real.log b|) (fun _=> by positivity)
    (fun i=> low_window_log_support (W i) a b ha (hW i))
  choose C hC he using fun A : Finset (Fin K)=> v2_low_all_gaussian_dyads η S hS hbad ell hell hsum
    a b ε ha hε hε1 (V A) (hV A) W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  let C0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,C A)+1
  have hC0 : 0< C0 := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    have hn := Finset.sum_nonneg (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=>(hC A).le)
    dsimp only [C0]
    nlinarith
  refine ⟨C0,hC0,?_⟩
  filter_upwards [Filter.eventually_all.mpr he] with Z hZ
  have hz1 : 1< Z := (hZ ∅).1
  have hz : 0< Z := lt_trans zero_lt_one hz1
  refine ⟨hz1,?_⟩
  intro T hT hout hdis hnorm
  have hslots : ∀i n,n∈canonicalSlotSupport (T i)→n≠0 := fun i=> canonicalSlotSupport_nonzero _ (hT i)
  rw [hidentity η (calibrationForSet S hS) W0 W1
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW0)
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    _ hslots (fun i=> Z^(ell i)) (fun i=> by positivity)
    (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z (by positivity) (by positivity) hz]
  apply (norm_sum_le _ _).trans
  have hterm (A : Finset (Fin K)) :
      ‖∑'j : ℕ,lowCommonDyad η (calibrationForSet S hS) W0 W1 (fun i=> canonicalSlotSupport (T i)) W
        (fun i=> Z^(ell i)) A (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) ((2:ℝ)^j)
        (Z*∏i∈Finset.univ\A,Z^(ell i)) (V A) (hV A)‖≤ C A*Z^(RHV2.lowExponent+256*ε) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    have hc : Z*(∏i∈Finset.univ\A,Z^(ell i))=Z^(1+lowSelectedLength ell A) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      rw [lowSelectedScale_product ell A Z hz,Real.rpow_add hz,Real.rpow_one]
    rw [hc]
    exact ((hZ A).2 T hT hout hdis hnorm A W hWnorm).2
  have hh := Finset.sum_le_sum (fun A (_ : A∈(Finset.univ : Finset (Fin K)).powerset)=> hterm A)
  apply hh.trans
  rw [←Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right (by dsimp [C0];nlinarith) (Real.rpow_nonneg hz.le _)

theorem v2_original_ray_compensatedPhysicalProbe_low (η : HeckeFamily.Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤ RHV2.ell) (R : Set Id)
    (a b ε : ℝ) (ha : 0< a) (hab : a≤ b) (hε : 0<ε) (hε1 : ε<1)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤1)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=> Z^(ell i))
        (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z‖≤ C*Z^(RHV2.lowExponent+256*ε) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  obtain ⟨C,hC,he⟩ := v2_compensatedPhysicalProbe_low η S hmax hS.bad ell hell hsum
    a b ε ha hε hε1 W hW hWnorm W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨C,hC,?_⟩
  filter_upwards [he,ProbeRaySlots.power_pools_eventually_disjoint R S (fun _=> a) (fun _=> b) ell
    (fun _=> ha) (fun _=> hab) hinj] with Z hZ hd
  have hz : 0< Z := lt_trans zero_lt_one hZ.1
  apply hZ.2 _ (fun i=> ProbeRaySlots.pool_supported R S hS a b (Z^(ell i)))
    (fun i P hP=>((ProbeRaySlots.mem_pool R S a b (Z^(ell i)) P).mp hP).2.2.2)
    (fun i j hij=> hd i j hij)
  intro i P hP
  have hh := ProbeRaySlots.pool_norm_bounds R S ha.le hab (Real.rpow_pos_of_pos hz _) P hP
  simpa only [mul_comm] using And.intro hh.1.le hh.2

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule144
/- END analytic_low.V2CommonBound -/

/- BEGIN original module analytic_low.V2WindowBound -/
section LocalModule145

namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem v2_original_ray_compensatedPhysicalProbe_low_loss
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    {K : ℕ} (ell : Fin K→ℝ) (hell : ∀i,0≤ ell i) (hinj : Function.Injective ell)
    (hsum : ∑i,ell i≤ RHV2.ell) (R : Set Id)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (W : Fin K→ℝ→ℂ) (hW : ∀i,Function.support (W i)⊆Set.Icc a b) (hWnorm : ∀i x,‖W i x‖≤ B)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 B0 B1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hab1 : a1< b1) (hB0 : 0≤ B0) (hB1 : 0≤ B1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hW0s : ContDiff ℝ ∞ W0) (hW1s : ContDiff ℝ ∞ W1)
    (hWB0 : ∀x,‖W0 x‖≤ B0) (hWB1 : ∀x,‖W1 x‖≤ B1) :
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) W (fun i=> Z^(ell i))
        (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z‖≤ C*Z^(RHV2.lowExponent+loss) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  let D := max 1 B
  have hD : 0< D := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hDc : (D:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hD.ne'
  let Wn := fun i x=> W i x/(D:ℂ)
  have hWn : ∀i,Function.support (Wn i)⊆Set.Icc a b := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    intro i x hx
    apply hW i
    intro hz
    exact hx (by dsimp [Wn];rw [hz,zero_div])
  have hn : ∀i x,‖Wn i x‖≤1 := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    intro i x
    dsimp only [Wn]
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
    exact (div_le_one hD).mpr ((hWnorm i x).trans (le_max_right _ _))
  have hscale : (fun i x=>(D:ℂ)*Wn i x)=W := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    funext i x
    dsimp [Wn]
    field_simp
  let ε := min (loss/512) (1/2)
  have he : 0<ε := by dsimp [ε];positivity
  have he1 : ε<1 := lt_of_le_of_lt (min_le_right _ _) (by v2_geometry)
  have heloss : 256*ε≤ loss := by have hh := min_le_left (loss/512) (1/2:ℝ);dsimp only [ε];nlinarith
  intro η
  obtain ⟨C,hC,hbound⟩ := v2_original_ray_compensatedPhysicalProbe_low η S hS hmax ell hell hinj hsum R
    a b ε ha hab he he1 Wn hWn hn W0 W1 a0 b0 a1 b1 B0 B1 ha0 ha1 hab1 hB0 hB1
    hW0 hW1 hW0s hW1s hWB0 hWB1
  refine ⟨D^K*C,by positivity,?_⟩
  filter_upwards [hbound,Filter.eventually_ge_atTop (1:ℝ)] with Z hb hZ
  have heq := compensatedPhysicalProbe_window_scale η (calibrationForSet S hmax) W0 W1
    (fun i=> canonicalSlotSupport (ProbeRaySlots.pool R S a b (Z^(ell i)))) Wn (fun i=> Z^(ell i))
    (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z (D:ℂ)
  rw [hscale] at heq
  rw [heq,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hD]
  calc
    _≤ D^K*(C*Z^(RHV2.lowExponent+256*ε)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _≤ D^K*(C*Z^(RHV2.lowExponent+loss)) := by gcongr
    _=_ := by v2_ring

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule145
/- END analytic_low.V2WindowBound -/

/- BEGIN original module analytic_low.V2Normalized -/
section LocalModule146

namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem v2_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=RHV2.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=> Z^(ell j)
      let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHV2.ell) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=> canonicalSlotSupport (T j)) WC Yp (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z/normer‖≤
        C*Z^(RHV2.lowExponent+loss) := by
  obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤ B := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1< max b1 (a1+1) := lt_of_lt_of_le (by nlinarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.perturbed_actual_ray_normalizer_inverse (RHV2.ell) M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := v2_original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
    (fun j=>(hell j).le) hinj hsum.le (RayQuotient.identityClass M H) a b B (loss/2)
    ha hab (by positivity) WC hWC hWCB W0 W1 a0 b0 a1 (max b1 (a1+1))
    (SchwartzMap.seminorm ℝ 0 0 W0) (SchwartzMap.seminorm ℝ 0 0 W1)
    ha0 ha1 hab1 (by positivity) (by positivity) hW0 hW1' (W0.smooth (⊤ : ℕ∞)) (W1.smooth (⊤ : ℕ∞))
    (SchwartzMap.norm_le_seminorm ℝ W0) (SchwartzMap.norm_le_seminorm ℝ W1) η
  refine ⟨Cp*Cn,by positivity,?_⟩
  filter_upwards [hprobe,hnorm,eventually_gt_atTop (0:ℝ)] with Z hp hn hZ
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  rw [div_eq_mul_inv,norm_mul]
  calc
    _≤(Cp*Z^(RHV2.lowExponent+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(RHV2.lowExponent+loss) := by
      obtain ⟨hLv20,hLv21,hbv2,hxyv2,hyv2,hlowv2,hgapv2,hbalv2⟩ := RHV2.analytic_geometry
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      v2_ring

#print axioms v2_normalized_compensatedPhysicalProbe_low

end SevenEighths.ProbePhysical
end

end OAI

end LocalModule146
/- END analytic_low.V2Normalized -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2EulerRegion -/
section LocalModule147

set_option linter.unusedVariables false

/-! Actual local Euler formulas on the perturbed x-half-plane.
The proofs use upstream coordinate norm estimates and rational denominator
bounds; no perturbed local bound is assumed. The broad summable17/10 bound
is retained, and the narrower second rectangle has exact decay72599/40000.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler

theorem v2_unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (437/500:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(11/5:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(87/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(77/100:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith


lemma v2_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 437/500≤ x.re) (hz : 4/25≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem v2_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedClosed Q A eta v x w z) {x : ℂ|437/500< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := v2_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem v2_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 437/500≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedClosed Q A eta v x w z) {w : ℂ|9/10< w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := v2_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem v2_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 437/500≤ x.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedClosed Q A eta v x w z) {z : ℂ|4/25< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := v2_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule147
/- END RHZeroFreeExtension.analytic_high.V2EulerRegion -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2GlobalCorrection -/
section LocalModule148

set_option linter.unusedVariables false

/-! The genuine upstream idealClosedCorrection and globalClosedCorrection
on the new half-plane. The original summable prime majorant and original
cutoff are reused because the new local theorem retains the same17/10 decay.
No product bound, analyticity, or perturbed contraction is assumed.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbePhysical OAI.ActualEisensteinCubic
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma v2_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply v2_unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem v2_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=> v2_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma v2_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    Multipliable (fun P : {P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z
  let B := fun P : {P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal // P.val∉S}=> globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    v2_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem v2_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> globalClosedCorrection η S x w z) {x : ℂ|437/500< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply v2_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact v2_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem v2_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 437/500≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> globalClosedCorrection η S x w z) {w : ℂ|9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply v2_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact v2_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem v2_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 437/500≤ x.re) (hw : 9/10≤ w.re) :
    AnalyticOnNhd ℂ (fun z=> globalClosedCorrection η S x w z) {z : ℂ|4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply v2_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact v2_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule148
/- END RHZeroFreeExtension.analytic_high.V2GlobalCorrection -/

/- BEGIN original module RHZeroFreeExtension.V2SourceAnalytic -/
section LocalModule149

/-! Genuine source Euler correction at the radical v2 boundary. The wider
rational half-plane Re(s)>437/500 retains the original summable prime bound
and source exclusion tail. No analyticity or product contraction is assumed. -/
namespace RHV2
noncomputable section
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler PrincipalSignalComparison
open RHZeroFreeExtension.AnalyticHigh
lemma correction_boundary_lower : (437/500 : ℝ) < boundary := by v2_geometry

theorem source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) :
    AnalyticOnNhd ℂ (sourceCorrection eta S) {z : ℂ | boundary < z.re} := by
  apply (v2_globalClosedCorrection_analytic_x eta S hS.tail 1 (1/6)
    (by norm_num) (by norm_num)).mono
  intro z hz
  exact lt_trans correction_boundary_lower hz

theorem source_contraction (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) (z : ℂ) (hz : boundary < z.re) :
    ‖sourceCorrection eta S z-1‖ ≤ (1/2 : ℝ) :=
  v2_globalClosedCorrection_bound eta S hS.tail z 1 (1/6)
    (by linarith [correction_boundary_lower]) (by norm_num) (by norm_num)

theorem source_nonzero (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (eta : Character) (z : ℂ) (hz : boundary < z.re) :
    sourceCorrection eta S z ≠ 0 := by
  have hb := source_contraction S hS eta z hz
  intro hn
  rw [hn, zero_sub, norm_neg, norm_one] at hb
  norm_num at hb

#print axioms source_analytic
#print axioms source_contraction
#print axioms source_nonzero
end
end RHV2

end LocalModule149
/- END RHZeroFreeExtension.V2SourceAnalytic -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2FinalSource -/
section LocalModule150
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
def v2_normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=> Z^(ell j)
  let T := fun j=> pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=> canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(RHV2.x:ℝ)) (Z^(RHV2.y:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (RHV2.ell) (slotMass T (residueWeights W Yp)) : ℂ))

theorem v2_normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0< a) (hab : a≤ b) (hloss : 0< loss)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=RHV2.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤ W j y ∧ W j y≤ B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,v2_normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=> Z^(RHV2.lowExponent+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := v2_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=> h.2)⟩

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule150
/- END RHZeroFreeExtension.analytic_high.V2FinalSource -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2HighData -/
section LocalModule151


noncomputable section
open scoped BigOperators
namespace RHZeroFreeExtension.AnalyticHigh.V2
open OAI.SevenEighths.Parameters

structure HighData (Δ : ℝ) where
  t : ℝ
  N : ℕ
  ell : Fin N → ℝ
  rmin : ℝ
  ε : ℝ
  e : ℝ
  κ : ℝ
  cost : ℝ
  eps : ℝ
  sigma : ℝ
  t_pos : 0 < t
  t_delta : t < Δ/4
  t_gap : 1000000*t ≤ Δ
  t_small : t ≤ 1/100000000
  slots_even : Even N
  slots_pos : 0 < N
  slots_injective : Function.Injective ell
  slots_sum : (∑j,ell j)=RHV2.ell
  slots_bounds :  ∀ j,0 < ell j  ∧  (7/8)*rmin ≤ ell j  ∧  ell j ≤ (1/200)*t
  rmin_pos : 0 < rmin
  epsilon_pos : 0 < ε
  epsilon_small : ε ≤ 1/1000
  epsilon_gap : ε < rmin*t
  e_pos : 0 < e
  e_small : e < 1/1000
  kappa_pos : 0 < κ
  kappa_small : κ ≤ 1
  cost_pos : 0 < cost
  eps_pos : 0 < eps
  eps_small : eps ≤ 1
  sigma_pos : 0 < sigma
  detector_budget : 288*e+8*κ+2*cost ≤ ε/2
  phase_budget : 8*e*t+κ ≤ ε
  count_budget : 159*ε+t+t+7*t ≤ 1/32
  central_budget : (RHV2.h)*(159*ε+t+t+7*t)+2*t+(3/2)*(2*t)+
    (26*e+(N+8)*eps+t+(RHV2.ell)*t)+(t+t+t)+t ≤ Δ/2
  geometric_budget : sigma+8*e+t/8 ≤ 1/20
  principal_budget : sigma+t/8 ≤ 1/3000
  window_budget : sigma+e ≤ (RHV2.boundary)*((7/8)*rmin)
  floor_budget : 2*t+26*e+(N+8)*eps+t+(RHV2.ell)*t+t/8+sigma ≤ 1/200
  high_saving : sigma+t/8+t/8 ≤ t
  height_choice :  ∀ J : ℝ,0 ≤ J  →   ∃ τ : ℝ,0 < τ  ∧  τ < (1/200)/2  ∧ 
    4*τ < (1/200)*cost  ∧  τ < t  ∧  2*τ*(1+J) ≤ t  ∧  τ*(2+4*eps) < t

theorem exists_high_data_fine (Δ : ℝ) (hΔ : 0 < Δ) (mesh : ℝ → ℝ)
    (hmesh : ∀ t : ℝ,0 < t → 0 < mesh t) :  ∃ D : HighData Δ, ∀ j,D.ell j ≤ mesh D.t/200 := by
  let t : ℝ := min (Δ/1000000) (1/1000000000000)
  have ht : 0 < t := lt_min (by positivity) (by norm_num)
  have htΔ : t < Δ/4 := by have hh:=min_le_left (Δ/1000000) (1/1000000000000:ℝ);dsimp [t];linarith
  have htTiny : t ≤ 1/1000000000000 := min_le_right _ _
  have ht1 : t ≤ 1/100000000 := by linarith
  let L : ℝ := min t (mesh t)/200
  have hL : 0 < L := div_pos (lt_min ht (hmesh t ht)) (by norm_num)
  obtain ⟨N,hN,hEven,ell,hell,hbounds,hsum⟩ :=
    RHSlotLengths.exists_even_distinct_slot_lengths (RHV2.ell) L RHV2.analytic_geometry.1 hL
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := ⟨⟨0,hN⟩,Finset.mem_univ _⟩
  obtain ⟨j,_hj,hminj⟩ := Finset.exists_min_image Finset.univ ell hne
  let rmin : ℝ := ell j/(2*(7/8))
  have hr : 0 < rmin := div_pos (hbounds j).1 (by norm_num)
  have hlo (k : Fin N) : (7/8:ℝ)*rmin ≤ ell k := by
    have hh := hminj k (Finset.mem_univ k)
    have hi : (7/8:ℝ)*rmin=ell j/2 := by dsimp [rmin];ring
    rw [hi];linarith [(hbounds j).1]
  have hup (k : Fin N) : ell k ≤ t/200 := by
    exact (hbounds k).2.le.trans ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 200)).mpr (min_le_left _ _))
  have hfine (k : Fin N) : ell k ≤ mesh t/200 := by
    exact (hbounds k).2.le.trans ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 200)).mpr (min_le_right _ _))
  let small := t/((N:ℝ)+2000)
  have hsmall : 0 < small := div_pos ht (by positivity)
  have hst : small ≤ t/((N:ℝ)+2000) := le_rfl
  have hst0 : small ≤ t/2000 := hst.trans
    (div_le_div_of_nonneg_left ht.le (by norm_num) (by linarith [Nat.cast_nonneg (α:=ℝ) N]))
  let ellMin := (7/8:ℝ)*rmin
  have hmin : 0 < ellMin := mul_pos (by norm_num) hr
  obtain ⟨ε,e,κ,cost,τ₀,hε,hε1,hεgap,hεa,he,he1,heell,hea,hκ,hκ1,hcost,
    hdet,hphase,_,_,_,_,_⟩ :=
    exists_detector_scales t rmin t (1/200) t ellMin small 0
      ht.le hr ht (by norm_num) ht hmin hsmall (by norm_num)
  let eps := small/2
  have heps : 0 < eps := by dsimp [eps];positivity
  have hepss : eps ≤ small := by dsimp [eps];linarith only [hsmall]
  have heps1 : eps ≤ 1 := by linarith only [hepss, hst0, ht1]
  have heN : ((N:ℝ)+2000)*eps ≤ t := by
    have h := (le_div_iff₀ (show 0 < (N:ℝ)+2000 by positivity)).mp (hepss.trans hst)
    simpa only [mul_comm] using h
  have he8 : ((N:ℝ)+8)*eps ≤ t := by nlinarith only [heN, heps.le]
  have het : 2000*e ≤ t := by linarith only [hea, hst0]
  let sigma := min (t/2) (ellMin/4)
  have hs : 0 < sigma := lt_min (by positivity) (by positivity)
  have hst2 : sigma ≤ t/2 := min_le_left _ _
  have hsell : sigma ≤ ellMin/4 := min_le_right _ _
  refine ⟨{
    t:=t,N:=N,ell:=ell,rmin:=rmin,ε:=ε,e:=e,κ:=κ,cost:=cost,eps:=eps,sigma:=sigma
    t_pos:=ht,t_delta:=htΔ,t_gap:=by
      have hh:=min_le_left (Δ/1000000) (1/1000000000000:ℝ)
      dsimp only [t]
      linarith
    ,t_small:=ht1,slots_even:=hEven,slots_pos:=hN,slots_injective:=hell,slots_sum:=hsum
    slots_bounds:=fun k=>⟨(hbounds k).1,hlo k,by simpa only [div_eq_mul_inv, one_mul, mul_comm] using hup k⟩
    rmin_pos:=hr,epsilon_pos:=hε,epsilon_small:=hε1,epsilon_gap:=hεgap
    e_pos:=he,e_small:=he1,kappa_pos:=hκ,kappa_small:=hκ1,cost_pos:=hcost
    eps_pos:=heps,eps_small:=heps1,sigma_pos:=hs,detector_budget:=by linarith only [hdet]
    phase_budget:=hphase,count_budget:=by linarith only [hεa,hst0,htTiny]
    central_budget:=by
      have hepsL : RHV2.ell*t ≤ t/5 := by nlinarith only [RHV2.analytic_geometry.2.1.le, ht.le]
      have hc : 0 ≤ 159*ε+t+t+7*t := by positivity
      have hh : RHV2.h*(159*ε+t+t+7*t) ≤ 159*ε+t+t+7*t := by
        have hhl : RHV2.h ≤ 1 := by v2_geometry
        nlinarith only [hc, hhl]
      have htgap := min_le_left (Δ/1000000) (1/1000000000000:ℝ)
      change t ≤ Δ/1000000 at htgap
      linarith only [hεa,hst0,het,he8,hepsL,hh,htgap,ht]
    geometric_budget:=by linarith only [hst2, het, htTiny]
    principal_budget:=by linarith only [hst2, htTiny]
    window_budget:=by
      change sigma+e ≤ RHV2.boundary*ellMin
      have hb : (4/5:ℝ) ≤ RHV2.boundary := by v2_geometry
      nlinarith only [hsell, heell, hmin, hb]
    floor_budget:=by
      have hepsL : RHV2.ell*t ≤ t/5 := by nlinarith only [RHV2.analytic_geometry.2.1.le, ht.le]
      linarith only [hst2, het, he8, htTiny, hepsL]
    high_saving:=by linarith only [hst2, ht]
    height_choice:=?_ },?_⟩
  · intro J hJ
    let τ := min ((1/200:ℝ)*cost/16) (min (1/800) (t/(4*(J+7))))
    have htau : 0 < τ := lt_min (by positivity) (lt_min (by norm_num) (by positivity))
    have hτc : τ ≤ (1/200:ℝ)*cost/16 := min_le_left _ _
    have hτd : τ ≤ 1/800 := (min_le_right _ _).trans (min_le_left _ _)
    have hτt : τ ≤ t/(4*(J+7)) := (min_le_right _ _).trans (min_le_right _ _)
    have hτJ : τ*(4*(J+7)) ≤ t := (le_div_iff₀ (by positivity)).mp hτt
    have hprod : 0 ≤ τ*J := mul_nonneg htau.le hJ
    have hprodeps := mul_le_mul_of_nonneg_left heps1 htau.le
    refine ⟨τ,htau,by linarith only [hτd],by linarith only [hτc, hcost],
        by nlinarith only [hτJ, hprod, htau],by nlinarith only [hτJ, hprod, htau],
        by nlinarith only [hτJ, hprod, hprodeps, htau]⟩
  · exact hfine

theorem fine_slot_widths {gap : ℝ} (D : HighData gap) (mesh : ℝ → ℝ)
    (_hmesh : 0 < mesh D.t) (hfine : ∀ j, D.ell j ≤ mesh D.t/200)
    (d : ℝ) (hd : (1/200 : ℝ) ≤ d) (j : Fin D.N) :
    0 < D.ell j/d ∧ D.ell j/d ≤ mesh D.t := by
  have hd0 : 0 < d := by linarith
  refine ⟨div_pos (D.slots_bounds j).1 hd0, (div_le_iff₀ hd0).mpr ?_⟩
  have hh := hfine j
  nlinarith

end RHZeroFreeExtension.AnalyticHigh.V2
end

#print axioms RHZeroFreeExtension.AnalyticHigh.V2.exists_high_data_fine

#print axioms RHZeroFreeExtension.AnalyticHigh.V2.fine_slot_widths

end LocalModule151
/- END RHZeroFreeExtension.analytic_high.V2HighData -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2FinalData -/
section LocalModule152


noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace RHZeroFreeExtension.AnalyticHigh.V2
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
local notation "O" => HeckeFamily.O

structure SourceData {Δ : ℝ} (D : HighData Δ) where
  S : Finset (Ideal O)
  exclusions : SourceExclusions S
  maximal :  ∀ P∈S,P.IsMaximal
  first : FirstTail (4*D.e) S
  w : ℝ → ℝ
  W : SchwartzMap ℝ ℂ
  smooth : ContDiff ℝ ∞ w
  compact : HasCompactSupport w
  support : Function.support w⊆Set.Ioo 1 2
  positive_support : tsupport w⊆Set.Ioi 0
  bounded :  ∀ x,0 ≤ w x  ∧  w x ≤ 1
  nonzero : w≠0
  complex_eq :  ∀ x,W x=(w x:ℂ)
  complex_nonzero : W≠0
  complex_support : Function.support W⊆Set.Icc 1 2
  real :  ∀ x,(W x).im=0
  nonnegative :  ∀ x,0 ≤ (W x).re

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

def SourceData.probe {Δ : ℝ} {D : HighData Δ} (F : SourceData D) (η : Character) : ℝ → ℂ :=
  letI : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  RHZeroFreeExtension.AnalyticHigh.v2_normalizedProbe F.modulus ⊤ F.S F.maximal D.ell 1 2 (fun _=> F.w) F.W F.W η

theorem SourceData.probe_low {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (loss : ℝ) (hloss : 0 < loss) (η : Character) :
    F.probe η=O[atTop](fun Z : ℝ=> Z^(RHV2.lowExponent+loss)) := by
  exact RHZeroFreeExtension.AnalyticHigh.v2_normalizedProbe_low F.modulus ⊤ le_top F.S F.exclusions F.maximal 1 2 1 loss
    (by norm_num) (by norm_num) hloss D.ell (fun j=>(D.slots_bounds j).1) D.slots_injective D.slots_sum
    (fun _=> F.w) (fun _=> F.smooth) (fun _=> F.compact) (fun _=> F.support)
    (fun _=> F.bounded) (fun _=> F.nonzero) F.W F.W 1 2 1 2 (by norm_num) (by norm_num)
    F.complex_support F.complex_support F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero η

end RHZeroFreeExtension.AnalyticHigh.V2

end


#print axioms RHZeroFreeExtension.AnalyticHigh.V2.exists_source_data
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.source_count_parameters
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.SourceData.probe_low

end LocalModule152
/- END RHZeroFreeExtension.analytic_high.V2FinalData -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2FinalMomentInput -/
section LocalModule153


noncomputable section
open scoped Classical BigOperators
open Filter
namespace RHZeroFreeExtension.AnalyticHigh.V2
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
   ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1/200:ℝ) ≤ d  →  d ≤ 7/8  →  51/100 < a  →  a ≤ 1  → 
    ( ∀ u∈rows,u.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm u  ∧ 
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0  ∧  rowNorm u ≤ Z^(d-D.t))  → 
     ∀ i : ℕ, ∀ z : ℂ,z.re=17/50  →  |z.im| ≤ height  → 
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z (0:ℝ)
      (if 2*a-1 ≤ 5/6 then counts.cB else counts.cH)
      (if 2*a-1 ≤ 5/6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBound.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : CountParameters F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0 ≤ Z) (h : SourceMomentBound F counts η Z τ C height) (hC : C ≤ C') :
    SourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z (0:ℝ) _ _ C C' height D.t
    hZ hC (h rows d a hd hd' ha ha' hrows i z hz hzh)

def RawMomentInput : Prop :=
   ∀ _hβ : (RHV2.boundary:ℝ) < HeckeZeroSupremum.beta,
     ∀ D : HighData (HeckeZeroSupremum.beta-RHV2.boundary), ∀ F : SourceData D,
     ∀ counts : CountParameters F.modulus ⊤ D.t,
     ∃ J : ℝ,0 ≤ J  ∧   ∀ η : Character, ∃ C : ℝ,0 < C  ∧ 
       ∀ τ : ℝ,0 < τ  →  τ ≤ 1  →   ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

lemma polynomial_height_absorption (C Z τ J t : ℝ)
    (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hτ : 0 ≤ τ) (hJ : 0 ≤ J) (hbudget : 2*τ*(1+J) ≤ t) :
    C*(1+Z^(2*τ))^J ≤ (C*2^J)*Z^t := by
  have hZp : 0 < Z := zero_lt_one.trans_le hZ
  have hscale : 1 ≤ Z^(2*τ) := Real.one_le_rpow hZ (by positivity)
  calc
    _ ≤ C*(2*Z^(2*τ))^J := by gcongr;linarith
    _=(C*2^J)*Z^(2*τ*J) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
      ring
    _ ≤ (C*2^J)*Z^t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem raw_input_chosen_height (h : RawMomentInput) (hβ : (RHV2.boundary:ℝ) < HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-RHV2.boundary)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
     ∃ τ : ℝ,0 < τ  ∧  τ < (1/200:ℝ)/2  ∧  4*τ < (1/200:ℝ)*D.cost  ∧  τ < D.t  ∧ 
      2*τ ≤ D.t  ∧  τ*(2+4*D.eps) < D.t  ∧ 
       ∀ η : Character, ∃ C : ℝ,0 < C  ∧   ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := h hβ D F counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩ := D.height_choice J hJ
  have htau1 : τ ≤ 1 := by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith) (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ hτJ)

def ChosenMomentInput : Prop :=
  ∀ _hβ : RHV2.boundary < HeckeZeroSupremum.beta,
    ∃ D : HighData (HeckeZeroSupremum.beta-RHV2.boundary), ∃ F : SourceData D,
    ∃ counts : CountParameters F.modulus ⊤ D.t,
    ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
      ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput : Prop :=
  ∀ _hβ : RHV2.boundary < HeckeZeroSupremum.beta,
    ∃ mesh : ℝ → ℝ, (∀ t : ℝ, 0 < t → 0 < mesh t) ∧
      ∀ D : HighData (HeckeZeroSupremum.beta-RHV2.boundary),
      (∀ j, D.ell j ≤ mesh D.t/200) →
      ∀ F : SourceData D, ∀ counts : CountParameters F.modulus ⊤ D.t,
      ∃ J : ℝ, 0 ≤ J ∧ ∀ η : Character, ∃ C : ℝ, 0 < C ∧
        ∀ τ : ℝ, 0 < τ → τ ≤ 1 → ∀ᶠ Z : ℝ in atTop,
          SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h : FineMomentInput) : ChosenMomentInput := by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩ := h hβ
  obtain ⟨D,hD⟩ := exists_high_data_fine (HeckeZeroSupremum.beta-RHV2.boundary) (by linarith) mesh hmesh
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

end RHZeroFreeExtension.AnalyticHigh.V2

end


#print axioms RHZeroFreeExtension.AnalyticHigh.V2.raw_input_chosen_height

end LocalModule153
/- END RHZeroFreeExtension.analytic_high.V2FinalMomentInput -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2TerminalCertificate -/
section LocalModule154

namespace RHZeroFreeExtension.AnalyticHigh.V2
noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate
open OAI OAI.SevenEighths
open CenteredMomentEnergyCertifiedExistence CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyCappedWidthInduction

/-- The original moment induction is specialized at fixed kappa=3/4.  The
original Hecke headline is an explicit premise, not the improved conclusion. -/
theorem fixed_kappa_terminal_certificate {gap : ℝ} (D : HighData gap)
    (F : SourceData D) (hOld : HeckeZeroSupremum.beta ≤ (7/8 : ℝ))
    (hBeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (bPhi : ℝ) (hbPhi : 0 < bPhi) :
    CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
      2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 (3/4) (D.t/4)
      (count 2 (D.t/4)) := by
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 (3/4) (D.t/4)
  · norm_num
  · intro x hx
    have hh : x ∈ Function.support (F.W : ℝ → ℂ) := by
      change conj (F.W x) ≠ 0 at hx
      change F.W x ≠ 0
      intro hz
      exact hx (by rw [hz]; simp)
    exact F.complex_support hh
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbPhi
  · norm_num
  · norm_num
  · norm_num
  · exact div_pos D.t_pos (by norm_num)
  · exact hBeta
  · linarith

end
end RHZeroFreeExtension.AnalyticHigh.V2
#print axioms RHZeroFreeExtension.AnalyticHigh.V2.fixed_kappa_terminal_certificate

end LocalModule154
/- END RHZeroFreeExtension.analytic_high.V2TerminalCertificate -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.V2MomentCertificateAdapters -/
section LocalModule155

-- Adapted data-generic source wrapper from DetectorMomentPrimeGeometry.lean

/-! Actual perturbed source prime geometry. The generic separation, capacity,
large-prime and fixed-character norm results are reused unchanged. Only the
window/SourceData wrappers are rederived at the genuine new slot lengths. -/
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000
namespace OAI
noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.V2HeckeDetectorMomentPrimeGeometry
open HeckeFamily HeckeInverseAmplification InverseInitialDetectorSource
open InverseInitialRawDictionary InverseInitialPhysicalSlots
open HeckeDetectorBatch HeckeDetectorRawFiber HeckeDetectorFiberPartition ProbeHighRowFamily
local notation "O" => HeckeFamily.O

theorem sourceMoment_primeProfile_norm {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.V2.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D) (X : ℝ) (ζ : ℂ) (hz : ζ.re≤1)
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

section Live
variable (M : Ideal O) (H : Subgroup (O ⧸ M)ˣ)

theorem sourceMoment_live_disjoint {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.V2.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D) {ι : Type*} (ell : ι→ℝ)
    (U : ℝ) (hU : 0< U) (s t : ι)
    (hsep : 2*U^(ell s)<1*U^(ell t) ∨ 2*U^(ell t)<1*U^(ell s)) :
    Disjoint (livePrimes M H F.W 2 (U^(ell s))) (livePrimes M H F.W 2 (U^(ell t))) := by
  apply Finset.disjoint_left.mpr
  intro P hs ht
  have hs' := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support P hs
  have ht' := livePrime_data M H F.W 1 2 (U^(ell t))
    (Real.rpow_pos_of_pos hU _) F.complex_support P ht
  rcases hsep with hsep|hsep <;> linarith [hs'.2.2.1,hs'.2.2.2,ht'.2.2.1,ht'.2.2.2]

theorem sourceMoment_live_denominator {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.V2.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (hU : 0< U)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=> livePrimes M H F.W 2 (U^(ell s)))) :
    ‖fixedBase data.η data.m data.f (∏s,p s)‖=1 := by
  rw [map_prod,norm_prod]
  apply Finset.prod_eq_one
  intro s _
  have hs := livePrime_data M H F.W 1 2 (U^(ell s))
    (Real.rpow_pos_of_pos hU _) F.complex_support (p s) (Fintype.mem_piFinset.mp hp s)
  exact sourceMoment_fixedBase_norm_one data (p s) hs.1 ((hlarge s).trans_le hs.2.2.1)

theorem sourceMoment_live_quotient_norm {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.V2.HighData Δ}
    (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D) {ι : Type*} [Fintype ι]
    (data : RowData) (U : ℝ) (ell : ι→ℝ) (ζ : ι→ℂ) (hU : 0< U)
    (hz : ∀s,(ζ s).re=17/50)
    (hlarge : ∀s,((baseCharacter data).modulus.absNorm:ℝ)<1*U^(ell s))
    (p : ι→Ideal O) (hp : p∈Fintype.piFinset (fun s=> livePrimes M H F.W 2 (U^(ell s)))) :
    ‖star (∏s,primeProfile F.W (U^(ell s)) (ζ s) (p s))/
      fixedBase data.η data.m data.f (∏s,p s)‖≤1 := by
  rw [norm_div,norm_star,sourceMoment_live_denominator M H F data U ell hU hlarge p hp,
    div_one,norm_prod]
  exact Finset.prod_le_one₀ (fun s _=> norm_nonneg _)
    (fun s _=> sourceMoment_primeProfile_norm F _ _ (by rw [hz s];norm_num) _)
end Live

section Source
variable (M : Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O⧸M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem sourceMoment_fiber_prime_geometry_eventually
    {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.V2.HighData Δ} (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D)
    (η : Character) (εg : ℝ) (hεg : 0<εg) :
    ∀ᶠ Z : ℝ in atTop,1≤ Z ∧ ∀d : ℝ,1/200≤ d→
      ∀(a ε tstar T allowance : ℝ)(i : ℕ)
      (B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH F.S F.exclusions.prime η→
      B.profile=(fun _ x=>(F.w x:ℂ))→B.upper=(fun _=>2)→
      B.widths=(fun s=> D.ell s/d)→(∀s,(B.external s).re=17/50)→
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
  have hd0 : 0< d := by linarith
  have hu : 0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans_le hsep.1) _
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
    exact sourceMoment_live_disjoint M H F (fun s=> D.ell s/d) (Z^d) hu s t (hs s t hst)
  · intro selected
    change (∀s:selected,1≤2*(Z^d)^(B.widths s)) ∧
      (∏s:selected,2*(Z^d)^(B.widths s))≤(Z^d)^((∑s:selected,B.widths s)+εg) ∧ _
    refine ⟨?_,?_,?_⟩
    · rw [hwidths]
      exact fun s=> hc.1 s
    · rw [hwidths]
      exact hc.2 selected
    · intro p hp
      have hp' : p∈Fintype.piFinset (fun s:selected=> livePrimes M H F.W 2 ((Z^d)^(D.ell s/d))) := by
        change p∈Fintype.piFinset (fun s:selected=> livePrimes M H (B.profile s) (B.upper s) ((Z^d)^(B.widths s))) at hp
        simpa only [hprofile,hupper,hwidths] using hp
      have hl' : ∀s:selected,((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(D.ell s/d) := by
        intro s
        have hh:=hl s
        change ((baseCharacter (B.data j)).modulus.absNorm:ℝ)<1*(Z^d)^(B.widths s) at hh
        simpa only [hwidths] using hh
      have hs' : ∀s t:selected,s≠t→2*(Z^d)^(D.ell s/d)<1*(Z^d)^(D.ell t/d) ∨
          2*(Z^d)^(D.ell t/d)<1*(Z^d)^(D.ell s/d) := by
        intro s t hst
        exact hs s t (fun he=> hst (Subtype.ext he))
      refine ⟨?_,?_,?_,?_,?_⟩
      · exact live_tuple_injective M H (fun _=> F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=> D.ell s/d) (Z^d) hu (fun _=> F.complex_support) hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · exact live_tuple_admissible M H (B.data j) (fun _=> F.W) (fun _=>1) (fun _=>2)
          (fun s:selected=> D.ell s/d) (Z^d) hu (fun _=> F.complex_support) hl' hs' p (by simpa only [Fintype.mem_piFinset] using hp')
      · intro s
        change ((p s).absNorm:ℝ)≤2*(Z^d)^(B.widths s)
        rw [hwidths]
        exact (livePrime_data M H F.W 1 2 ((Z^d)^(D.ell s/d))
          (Real.rpow_pos_of_pos hu _) F.complex_support (p s) (Fintype.mem_piFinset.mp (by simpa only [Fintype.mem_piFinset] using hp') s)).2.2.2
      · exact sourceMoment_live_denominator M H F (B.data j) (Z^d)
          (fun s:selected=> D.ell s/d) hu hl' p (by simpa only [Fintype.mem_piFinset] using hp')
      · change ‖star (∏s:selected,primeProfile (B.profile s) ((Z^d)^(B.widths s)) (B.external s) (p s))/
          fixedBase (B.data j).η (B.data j).m (B.data j).f (∏s:selected,p s)‖≤1
        rw [hprofile,hwidths]
        exact sourceMoment_live_quotient_norm M H F (B.data j) (Z^d)
          (fun s:selected=> D.ell s/d) (fun s:selected=> B.external s) hu (fun s=> hz s) hl' p (by simpa only [Fintype.mem_piFinset] using hp')

end Source
end SevenEighths.V2HeckeDetectorMomentPrimeGeometry
end
end OAI

#print axioms OAI.SevenEighths.V2HeckeDetectorMomentPrimeGeometry.sourceMoment_fiber_prime_geometry_eventually

-- Adapted data-generic source wrapper from NaturalFixedRaySourceFixedIdeal.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators

namespace SevenEighths.V2CenteredMomentNaturalFixedRaySource
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily
open CenteredMomentDetectorDictionary CenteredMomentNaturalRowSource
open CenteredExceptionalProfile CenteredMomentSecondHeightFamily ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O

variable {Δ : ℝ} {D : RHZeroFreeExtension.AnalyticHigh.V2.HighData Δ}

def sourceFixedIdeal (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D) : Ideal O :=
  F.modulus⊓Ideal.span {(72:O)}

lemma sourceFixedIdeal_ne_zero (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D) : sourceFixedIdeal F≠0 :=
  Ideal.inf_ne_bot_of_ne_bot (NeZero.ne F.modulus)
    (Ideal.span_singleton_eq_bot.not.mpr (by norm_num : (72:O)≠0))

lemma sourceFixedIdeal_ne_top (F : RHZeroFreeExtension.AnalyticHigh.V2.SourceData D) : sourceFixedIdeal F≠⊤ := by
  have hmem : Ideal.span {goodLambda}∈F.S := by
    apply F.exclusions.bad
    change Ideal.span {goodLambda}∈({Ideal.span {goodLambda},Ideal.span {(2:O)}} : Finset (Ideal O))
    simp
  have hle : F.modulus≤ Ideal.span {goodLambda} := by
    apply Ideal.dvd_iff_le.mp
    exact Finset.dvd_prod_of_mem (fun P : Ideal O=> P) hmem
  have hprime := (F.maximal _ hmem).isPrime
  intro h
  exact hprime.ne_top (top_le_iff.mp (h ▸ (inf_le_left.trans hle : sourceFixedIdeal F≤ Ideal.span {goodLambda})))
