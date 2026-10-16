    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u P hPS W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

lemma weightedRowOnLines_eq {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z σ υ r t=
      (∏i,W i (((P i).val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      ((P i).val.absNorm:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold weightedRowOnLines continuedRowOnLines continuedPhysicalRowKernel calibratedTupleValue
  simp only [hnorm,Finset.prod_mul_distrib]
  ring

section
variable {K : ℕ} (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)

include he he' hσ hσβ hσ3 hυ hυ3 hr hfirst hR hdis ha0 ha1 hW0 hW1 hX hY hZ in
theorem finitePhysicalRows_eq_integral :
    Integrable (fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      weightedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z σ υ r t) heightMeasure ∧
    finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫t : HeightSpace,(∑u∈R,∑P:(∀i,T i),
          weightedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
            η u W Yp W0 W1 X Y Z σ υ r t) ∂heightMeasure := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z σ υ r
  have hsource (u : FreeRow) (hu : u∈R) (P : ∀i,T i) := rowIntegral_source_lines e σ υ r he he' hσ hσβ hσ3 hυ hυ3 hr
    S hS hmax hfirst (fun i=>(P i).val) (hdis P) (fun i=>hT i _ (P i).property) η u (hR u hu)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hfi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    have heq : f u P=(fun t=>(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t) := by
      funext t
      exact weightedRowOnLines_eq S hS hmax _ _ η u W Yp W0 W1 X Y Z σ υ r t
    rw [heq]
    exact (hsource u hu P).1.const_mul _
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P hP=>hfi u hu P)
  have hi : Integrable (fun t=>∑u∈R,∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ hiu
  refine ⟨hi,?_⟩
  change finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu]
  unfold finitePhysicalRows
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P hP=>hfi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [(hsource u hu P).2]
  have hi' : (∫t,f u P t ∂heightMeasure)=
      (∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        ∫t,continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t ∂heightMeasure := by
    simp_rw [f,weightedRowOnLines_eq]
    exact integral_const_mul _ _
  rw [hi']
  ring

include he he' hσ hσβ hσ3 hυ hυ3 hr hfirst hR hdis ha0 ha1 hW0 hW1 hX hY hZ in
theorem norm_finitePhysicalRows_le_absolute :
    ‖finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)^3‖*
        absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  let f (u : FreeRow) (P : ∀i,T i) := weightedRowOnLines S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z σ υ r
  have hfi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    have hi := continuedPhysicalRowKernel_integrable e σ υ r he he' hσ hσβ hυ hr S hS hmax hfirst
      (fun i=>(P i).val) (hdis P) (fun i=>hT i _ (P i).property) η u (hR u hu)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    have heq : f u P=(fun t=>(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
        continuedRowOnLines S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
          η u W0 W1 X Y Z σ υ r t) := by
      funext t
      exact weightedRowOnLines_eq S hS hmax _ _ η u W Yp W0 W1 X Y Z σ υ r t
    rw [heq]
    exact hi.const_mul _
  let g (t : HeightSpace) := ‖sourceMellinWeight W0 W1 X Y Z
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)‖*
    physicalDyadNorm S hS hmax η R T hT W Yp
      ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
  have hg (t : HeightSpace) : (∑u∈R,∑P:(∀i,T i),‖f u P t‖)=g t := by
    simp only [f,g,weightedRowOnLines,physicalDyadNorm,norm_mul,Finset.mul_sum,mul_assoc]
  have hgi : Integrable g heightMeasure := by
    have hh : Integrable (fun t=>∑u∈R,∑P:(∀i,T i),‖f u P t‖) heightMeasure :=
      integrable_finsetSum R (fun u hu=>integrable_finsetSum Finset.univ (fun P hP=>(hfi u hu P).norm))
    exact hh.congr (Filter.Eventually.of_forall hg)
  obtain ⟨hi,heq⟩ := finitePhysicalRows_eq_integral e σ υ r he he' hσ hσβ hσ3 hυ hυ3 hr S hS hmax
    hfirst η R hR T hT hdis W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hp (t : HeightSpace) : ‖∑u∈R,∑P:(∀i,T i),f u P t‖≤g t := by
    rw [←hg]
    apply (norm_sum_le _ _).trans
    exact Finset.sum_le_sum (fun u hu=>norm_sum_le _ _)
  rw [heq,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact (norm_integral_le_integral_norm _).trans (integral_mono hi.norm hgi hp)

end
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2608

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CanonicalPhysicalRows
Source SHA256: 9e4cbee4b1c67854f46e254023def70567d4ae739469f767dd437fea734bca2e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2609



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical
open CompletedGauss CanonicalQuadraticSieve HeckeInverseAmplification
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem compensatedPhysicalProbe_canonical_slots {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        compensatedTuple η C W0 W1 (fun i=>primaryGenerator (P i).val.val) X Y Z :=
  sum_canonical_weighted_tuples T hT W Yp (fun p=>compensatedTuple η C W0 W1 p X Y Z)

theorem finitePhysicalRows_canonical_slots {K : ℕ} (S : Finset Id) (hmax : ∀P∈S,P.IsMaximal)
    (η : HeckeFamily.Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η R T W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(canonicalSlotSupport (T i))),
        (∏i,W i (elementNorm (p i).val/Yp i))*
          ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_canonical_weighted_tuples T hT W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold ProbeHighRowFamily.finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

theorem compensatedPhysicalProbe_eq_canonical_rows {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hpS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (hSne : S.Nonempty)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedPhysicalProbe η (calibrationForSet S hS) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ∑'u : FreeRow,∑P : (∀i,↥(T i)),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hn (P : ∀i,↥(T i)) (i : Fin K) : primaryGenerator (P i).val.val≠0 :=
    supported_primaryGenerator_ne_zero _ (hT i _ (P i).property)
  have hs (P : ∀i,↥(T i)) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [compensatedPhysicalProbe_canonical_slots η _ W0 W1 T hT W Yp]
  calc
    _ = ∑P : (∀i,↥(T i)),∑'u : FreeRow,(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
      rowIntegral η S (calibrationForSet S hS) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
        apply Finset.sum_congr rfl
        intro P hP
        rw [compensatedTuple_eq_row_triple η S hS hpS hbad hSne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
          _ (hn P) X Y Z hX hY hZ,
          compensatedRowTripleIntegral_eq_tsum η S _ _ (hn P) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
        exact tsum_mul_left.symm
    _ = _ := (Summable.tsum_finsetSum (fun P _=>hs P)).symm

theorem finitePhysicalRows_original_primary_slots {K : ℕ} (S : Finset Id)
    (hmax : ∀P∈S,P.IsMaximal) (η : HeckeFamily.Character) (R : Finset FreeRow)
    (A : Fin K→Finset O) (hp : ∀i a,a∈A i→Prime (Ideal.span {a}))
    (hs : ∀i a,a∈A i→Supported (Ideal.span {a}))
    (hn : ∀i a,a∈A i→ConcretePrimeRowBridge.goodLambda^2∣a-1)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η R
      (fun i=>idealSlotOfPrimary (A i) (hp i)) W Yp W0 W1 X Y Z=
      ∑p : (∀i,↥(A i)),(∏i,W i (elementNorm (p i).val/Yp i))*
        ∑u∈R,rowIntegral η S (calibrationForSet S hmax) (fun i=>(p i).val) W0 W1 X Y Z u := by
  rw [sum_original_primary_weighted_tuples A hp hs hn W Yp
    (fun p=>∑u∈R,rowIntegral η S (calibrationForSet S hmax) p W0 W1 X Y Z u)]
  unfold ProbeHighRowFamily.finitePhysicalRows
  simp_rw [Finset.mul_sum]
  exact Finset.sum_comm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2609

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalPhysical
Source SHA256: 4949ca006c113bf0aaa35143561f9d8d9ef9ee8905a0041c40ecc30f5e3180c2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2610




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds CanonicalQuadraticSieve
open PrincipalMellinResidues ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

lemma slotMultiplier_as_tuples {K : ℕ} (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) (s w z : ℂ) :
    slotMultiplier η Finset.univ T b s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        slotMultiplier η Finset.univ (fun i=>{(P i).val}) (fun _ _=>1) s w z := by
  simp only [slotMultiplier,Finset.sum_singleton,one_mul]
  simp_rw [←Finset.prod_mul_distrib]
  rw [←Fintype.prod_sum (fun i (p : T i)=>b i p.val*localMultiplier η p.val s w z)]
  congr 1
  funext i
  exact (Finset.sum_coe_sort (T i) (fun p=>b i p*localMultiplier η p s w z)).symm

def principalPoolKernel {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) : ℂ :=
  sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s) w z *
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w

lemma principalPoolKernel_as_tuples {K : ℕ} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    principalPoolKernel η S hS T b W0 W1 X Y Z s w z=
      ∑P : (∀i,T i),(∏i,b i (P i).val)*
        principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z s w z := by
  unfold principalPoolKernel sourceMultiplier
  rw [slotMultiplier_as_tuples]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro P hP
  ring

theorem principal_physical_pool_initial {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      ((1/(2*Real.pi):ℝ):ℂ)^3*∫t : HeightSpace,
        principalPoolKernel η S hS T b W0 W1 X Y Z
          ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I) ∂heightMeasure := by
  let F (P : ∀i,T i) (t : HeightSpace) :=
    principalPoolKernel η S hS (fun i=>{(P i).val}) (fun _ _=>1) W0 W1 X Y Z
      ((3:ℂ)+t.1.1*I) ((3:ℂ)+t.2*I) ((2:ℂ)+t.1.2*I)
  have hF (P : ∀i,T i) : Integrable (F P) heightMeasure := by
    apply source_joint_integrable η S hS Finset.univ (fun i=>{(P i).val}) (fun _ _=>1)
      (by intro i hi p hp;simp only [Finset.mem_singleton] at hp;subst p;exact hT i _ (P i).property)
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z 3 2 3 3 hX hY hZ
      (by norm_num) (lt_of_le_of_lt HeckeZeroSupremum.beta_le_one (by norm_num))
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  simp_rw [principalPoolKernel_as_tuples η S hS T b W0 W1 X Y Z]
  rw [integral_finsetSum Finset.univ (fun P _=>(hF P).const_mul (∏i,b i (P i).val)),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  rw [principalRowIntegral_eq_sourceMultiplier η S hS (fun i=>(P i).val) (hdis P)
    (fun i=>hT i _ (P i).property) W0 W1 X Y Z,integral_const_mul]
  dsimp only [F,principalPoolKernel]
  ring

theorem principal_physical_pool_ordered {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (hdis : ∀P:(∀i,T i),Function.Injective (fun i=>(P i).val))
    (b : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal→ℂ) (W0 W1 : SchwartzMap ℝ ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (ha : 7/8<a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta<a) (he : 0<e) (he2 : e≤11/6) :
    let F := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η Finset.univ T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    (∑P : (∀i,T i),(∏i,b i (P i).val)*
      principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)=
      verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => F s w z*LFunction π (6*z)*LFunction π w)))+
      R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => F s 1 z*LFunction π (6*z)))+
      R^2/6*verticalIntegral a (fun s => F s 1 (1/6)) := by
  dsimp only
  rw [principal_physical_pool_initial η S hS T hT hdis b W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  exact ProbePrincipalTransport.source_initial_joint_ordered_at_a η S hS Finset.univ T b
    (fun i _ p hp=>hT i p hp) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e hX hY hZ ha ha3 hβ he he2

lemma finitePhysicalRows_principal {K : ℕ} (S : Finset Id) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) :
    ProbeHighRowFamily.finitePhysicalRows S hmax η {principalFreeRow} T W Yp W0 W1 X Y Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z := by
  simp only [ProbeHighRowFamily.finitePhysicalRows,Finset.sum_singleton,rowIntegral_principal]

theorem compensatedPhysicalProbe_principal_pool_split {K : ℕ} (η : Character)
    (S : Finset Id) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      ProbeHighRowFamily.finitePhysicalRows S hmax η {principalFreeRow} T W Yp W0 W1 X Y Z+
      ∑'u : HeckeInverseAmplification.FreeRow,if u=principalFreeRow then 0 else
        ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
          rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u := by
  have hSne : S.Nonempty := (by simp [fixedBadPrimes] : fixedBadPrimes.Nonempty).mono hS.bad
  rw [compensatedPhysicalProbe_eq_canonical_rows η S hmax hS.prime hS.bad hSne T hT W Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  have hs (P : ∀i,T i) : Summable (fun u : HeckeInverseAmplification.FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (fun i=>supported_primaryGenerator_ne_zero _ (hT i _ (P i).property))
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  rw [(summable_sum (s:=Finset.univ) (fun P _=>hs P)).tsum_eq_add_tsum_ite principalFreeRow]
  simp only [ProbeHighRowFamily.finitePhysicalRows,Finset.sum_singleton]

end SevenEighths.ProbePrincipalPhysical
end

end OAI
end OAIOriginalModule2610

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalPhysicalRemainder
Source SHA256: 0082454b3750c828a2b43fd72a631d790f3e323f336cf3596fa74525801cb922
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2611



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=1/6 → ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤W j x ∧ W j x≤B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤Z → (∀j,480≤c*Z^(ell j)) → (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (HeckeZeroSupremum.beta+e) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ)) (fun j=>Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ := ProbePrincipalRemainderBounds.source_remainders_strict_saving η S hS
    (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ⟨ha.le,ha2⟩
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith
  have hb := hbound ell hell W (fun j _=>hW j) (fun j _=>hsupp j) T (fun j _ p hp=>hT j p hp)
    Z hZ (fun j _=>hthreshold j) (fun j _=>hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ)) W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0 ha (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (HeckeZeroSupremum.beta+e) F=
      verticalIntegral (HeckeZeroSupremum.beta+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000)
  apply hn.trans
  have hCe : C≤C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤Z^(HeckeZeroSupremum.beta-11/16-17/48000) := Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith
end SevenEighths.ProbePrincipalPhysical
end

end OAI
end OAIOriginalModule2611

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PrincipalNormalized
Source SHA256: b98009f4e73427d1ed7fc1d35e124f085f10082e481e0031222f40e3436de397
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2612




namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Complex Filter
namespace SevenEighths.ProbePrincipalNormalized
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual ProbeRaySlots
local notation "Id" => Ideal HeckeFamily.O

lemma normalized_error (A R F N : ℂ) (c d v : ℝ)
    (hc : 0≤c) (hA : ‖A-R‖≤c) (hN : ‖N⁻¹‖≤v)
    (hR : ‖R/N-F‖≤d) : ‖A/N-F‖≤c*v+d := by
  calc
    _ = ‖(A-R)*N⁻¹+(R/N-F)‖ := by congr 1; simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-R)*N⁻¹‖+‖R/N-F‖ := norm_add_le _ _
    _ ≤ c*v+d := by rw [norm_mul];gcongr

theorem actual_ray_principal_comparison {K : ℕ}
    (M : Id) [NeZero M] [Finite (HeckeFamily.O ⧸ M)]
    (H : Subgroup (HeckeFamily.O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B ellMin : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B) (hmin : 0<ellMin)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hdis : Function.Injective ell)
    (hsum : (∑j,ell j)=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j))
    (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c d)
    (hWbounds : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (e nu : ℝ) (he : 0<e) (hehi : e≤1/1000) (hnu : 0<nu)
    (ha : 7/8<HeckeZeroSupremum.beta+e) (ha2 : HeckeZeroSupremum.beta+e≤2) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏p∈S,p)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧
      ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
      C*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C0,hC0,hrem⟩ := ProbePrincipalPhysical.physical_principal_residue_remainder
    η S hS c d B hc hd hB W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 e he hehi ha ha2 (K:=K)
  obtain ⟨D,hD,hres⟩ := normalized_actual_window_residue S hS η ha ha2 (by linarith) (Finset.univ : Finset (Fin K))
  let cs := sourceResidueConstant W0 W1 (∏p∈S,p)
  let C := C0/e*‖cs⁻¹‖+D*c^(-(7/8:ℝ))+1
  refine ⟨C,by dsimp [C];positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply subset_trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy; exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_pool_thresholds (RayQuotient.identityClass M H) S η c d ellMin hc hd hmin ell hell,
    power_ray_mass_and_normalizer M H hH S W c d hc hd hsupp hW hcompact hpos
      (fun j y=>(hWbounds j y).1) hne ell (fun j=>hmin.trans_le (hell j)) nu hnu,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _=>c) (fun _=>d) ell (fun _=>hc) (fun _=>hd) hdis] with Z hthreshold hmass htuple
  rcases hthreshold with ⟨hZ,h480,hsmall,hslot,hpool⟩
  have hZ0 : 0<Z := by linarith
  let T := fun j=>pool (RayQuotient.identityClass M H) S c d (Z^(ell j))
  let normer := cs*(Probe.principalScalar Finset.univ Z (1/6)
    (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
  have hr := hres W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    T W (fun j=>Z^(ell j)) (c*Z^ellMin) (Z^(23/48:ℝ)) Z h480 hsmall
    (fun j _ p _=>(hWbounds j _).1) (fun j _ p hp=>(hpool j p hp).1)
    (fun j _ p hp=>(hpool j p hp).2.1) (fun j _=>hmass.1 j) hZ
  dsimp only at hr ⊢
  refine ⟨hr.1,?_⟩
  have hraw := hrem ell hsum W hWbounds (fun j=>Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self)
    T (fun j p hp=>(hpool j p hp).2.2) htuple Z hZ (fun j=>(hslot j).1) (fun j=>(hslot j).2)
  have hinv : ‖normer⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    dsimp only [normer]
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,norm_real]
    simpa only [hsum,Real.norm_eq_abs,mul_comm] using mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  have hh := normalized_error _ _ _ normer _ _ _ (by positivity) hraw hinv hr.2.2
  have hpw : (c*Z^ellMin)^(-(7/8:ℝ))=c^(-(7/8:ℝ))*Z^(-(7/8:ℝ)*ellMin) := by
    rw [Real.mul_rpow hc.le (Real.rpow_nonneg hZ0.le _),←Real.rpow_mul hZ0.le]
    congr 2;ring
  have heq1 : (C0/e*Z^(HeckeZeroSupremum.beta-11/16-17/48000))*(‖cs⁻¹‖*Z^nu)=
      (C0/e*‖cs⁻¹‖)*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu) := by
    rw [Real.rpow_add hZ0];ring
  have heq2 : D*Z^(HeckeZeroSupremum.beta+e-11/16)*(c*Z^ellMin)^(-(7/8:ℝ))=
      (D*c^(-(7/8:ℝ)))*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by
    rw [hpw]
    rw [show HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin=
      (HeckeZeroSupremum.beta+e-11/16)+(-(7/8:ℝ)*ellMin) by ring,Real.rpow_add hZ0]
    ring
  apply hh.trans
  rw [heq1,heq2]
  have h1 : C0/e*‖cs⁻¹‖≤C := by
    dsimp [C]
    have : 0≤D*c^(-(7/8:ℝ)) := by positivity
    linarith
  have h2 : D*c^(-(7/8:ℝ))≤C := by
    dsimp [C]
    have : 0≤C0/e*‖cs⁻¹‖ := by positivity
    linarith
  calc
    _ ≤ C*Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
        C*Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin) := by gcongr
    _ = _ := by ring
end SevenEighths.ProbePrincipalNormalized
end

end OAI
end OAIOriginalModule2612

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeNormalizer
Source SHA256: d57811850ecae40246f331be0fe5bf0ce0aca3cd0ab9e27f980d28907046529b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2613


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0<c) (hcb : c≤b)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (slotMass T (residueWeights W (fun j=>Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=>Z^(ell j))) Z (1/6) hZ (fun j _=>hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6)
        (slotMass (fun j=>pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=>Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2613

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowNormalized
Source SHA256: 0c6c90b0ffd370ef8a1b0bcf8b39d92950e45248d448ff0360e2be607faaade0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2614



namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem original_normalized_compensatedPhysicalProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : HeckeFamily.Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
        (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer‖≤
        C*Z^(3/16+loss) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin K) : Function.support (WC j)⊆Set.Icc a b := by
    intro y hy
    apply Set.Ioo_subset_Icc_self (hsupp j _)
    intro hz
    exact hy (by dsimp [WC];rw [hz];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hW1' : Function.support W1⊆Set.Icc a1 (max b1 (a1+1)) := by
    intro y hy
    exact ⟨(hW1 hy).1,(hW1 hy).2.trans (le_max_left _ _)⟩
  have hab1 : a1<max b1 (a1+1) := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  obtain ⟨Cn,hCn,hnorm⟩ := ProbeHighRowFamily.actual_ray_normalizer_inverse M H hH S hS a b ha hab
    ell hell hsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 (loss/2) (by positivity)
  intro η
  obtain ⟨Cp,hCp,hprobe⟩ := original_ray_compensatedPhysicalProbe_low_loss S hS hmax ell
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
    _≤(Cp*Z^(3/16+loss/2))*(Cn*Z^(loss/2)) :=
      mul_le_mul hp hn.2 (norm_nonneg _) (by positivity)
    _=(Cp*Cn)*Z^(3/16+loss) := by
      rw [mul_mul_mul_comm,←Real.rpow_add hZ]
      congr 2
      ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule2614

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblySource
Source SHA256: 32d7255e4de3d6709dc2e06d61c52651beca2f34658536a89b5719ec2719ec91
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2615




namespace OAI

noncomputable section
open scoped Classical ContDiff
open Filter Asymptotics
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison PrincipalMellinResidues
open ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

def normalizedProbe {K : ℕ} (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    [NeZero (∏P∈S,P)] (ell : Fin K→ℝ) (a b : ℝ) (W : Fin K→ℝ→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (η : Character) (Z : ℝ) : ℂ :=
  let Yp := fun j=>Z^(ell j)
  let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
    (fun j=>canonicalSlotSupport (T j)) (fun j y=>(W j y:ℂ)) Yp
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z /
    (sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ))

lemma isBigO_rpow_of_eventual_norm_bound (f : ℝ→ℂ) (r : ℝ)
    (h : ∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,‖f Z‖≤C*Z^r) :
    f=O[atTop](fun Z : ℝ=>Z^r) := by
  obtain ⟨C,hC,hb⟩ := h
  refine Asymptotics.IsBigO.of_bound C ?_
  filter_upwards [hb,eventually_ge_atTop (0:ℝ)] with Z hb hZ
  simpa only [Real.norm_eq_abs,abs_of_nonneg (Real.rpow_nonneg hZ r)] using hb

theorem normalizedProbe_low {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (a b B loss : ℝ) (ha : 0<a) (hab : a≤b) (hloss : 0<loss)
    (ell : Fin K→ℝ) (hell : ∀j,0<ell j) (hinj : Function.Injective ell) (hsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo a b)
    (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∀η : Character,normalizedProbe M H S hmax ell a b W W0 W1 η=O[atTop](fun Z : ℝ=>Z^(3/16+loss)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  intro η
  obtain ⟨C,hC,hb⟩ := original_normalized_compensatedPhysicalProbe_low M H hH S hS hmax
    a b B loss ha hab hloss ell hell hinj hsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 η
  apply isBigO_rpow_of_eventual_norm_bound
  exact ⟨C,hC,hb.mono (fun Z h=>h.2)⟩

theorem actual_source_analytic (S : Finset (Ideal O)) (hS : SourceExclusions S) (η : Character) :
    (∀I,idealCoeff (η.excludePrimes S hS.prime) I=
      if IsCoprime I (η.excludePrimes S hS.prime).modulus then idealCoeff η I else 0) ∧
    AnalyticOnNhd ℂ (sourceCorrection η S) {s : ℂ|7/8<s.re} ∧
    (∀s : ℂ,7/8<s.re→‖sourceCorrection η S s-1‖≤1/2) := by
  exact ⟨excludePrimes_mask η S hS.prime,
    (sourceCorrection_differentiable η S hS).analyticOnNhd (Complex.isOpen_re_gt _),
    sourceCorrection_bound η S hS⟩

end SevenEighths.ProbeFinalAssembly
end

end OAI
end OAIOriginalModule2615

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.PhysicalLargeTail
Source SHA256: 0bfd3653b3882b7ea4a6708e3b68ef0bbf8709066fa9c753795a3299949fcbee
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2616



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_original_physical_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,C,hr,hC,hmain⟩ := large_physical_tail_arbitrary_saving K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hgs,hgb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℂ := fun n=>finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r
  have hbnd (n : ℕ) : ‖f n‖≤N*g n := norm_finitePhysicalRows_le_absolute
    (1/2000) 2 2 r (by norm_num) (by norm_num) (by norm_num)
    (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num) (by norm_num) hr
    S hS hmax hfirst η (R n) (fun u hu=>(hR n u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  have hns : Summable (fun n=>‖f n‖) := Summable.of_nonneg_of_le (fun n=>norm_nonneg _) hbnd (hgs.mul_left N)
  refine ⟨hns.of_norm,?_⟩
  calc
    (∑'n,‖f n‖) ≤ ∑'n,N*g n := hns.tsum_le_tsum hbnd (hgs.mul_left N)
    _ = N*(∑'n,g n) := tsum_mul_left
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) := mul_le_mul_of_nonneg_left hgb hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2616

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.PhysicalSmallTail
Source SHA256: 4dba13a1cc28578fb83cd28eaada5eb79f09088c2f88ef0232c73fef634ba8f2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2617



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_original_physical_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_physical_dyads_sum K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  let N : ℝ := ‖((1/(2*Real.pi):ℝ):ℂ)^3‖
  have hN : 0≤N := norm_nonneg _
  refine ⟨(1+N)*C,by positivity,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hmain' := hmain η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let g : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
  have hbnd (n : ℕ) (hn : n∈F) :
      ‖finitePhysicalRows S hmax η (R n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤N*g n := norm_finitePhysicalRows_le_absolute
    e (HeckeZeroSupremum.beta+8*e) (1/2) (17/50) he he' (by linarith) le_rfl
    (by linarith [HeckeZeroSupremum.beta_le_one]) le_rfl (by norm_num) le_rfl
    S hS hmax hfirst η (R n) (fun u hu=>(hR n hn u hu).1) T hT hdis W _ W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 _ _ Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
  calc
    _ ≤ ∑n∈F,N*g n := Finset.sum_le_sum hbnd
    _ = N*∑n∈F,g n := (Finset.mul_sum _ _ _).symm
    _ ≤ N*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)) :=
      mul_le_mul_of_nonneg_left hmain' hN
    _ ≤ (1+N)*(C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)) :=
      mul_le_mul_of_nonneg_right (by linarith : N≤1+N) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2617

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.RowPartition
Source SHA256: 5433506b2b0efcf82066fabbee2e121f64126f997f9fef0bc090ccce2971ab6b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2618



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

def rowNorm (u : FreeRow) : ℝ := (Ideal.span {u.val}:Ideal O).absNorm

lemma rowNorm_ge_one (u : FreeRow) : 1≤rowNorm u := by
  unfold rowNorm
  have hn : (Ideal.span {u.val}:Ideal O)≠⊥ := Ideal.span_singleton_eq_bot.not.mpr u.property.1
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hn)

lemma finite_bounded_freeRows (H : ℝ) : {u : FreeRow | rowNorm u≤H}.Finite := by
  by_contra hs
  obtain ⟨n,hn⟩ := exists_nat_gt (128*max 1 H)
  have hinf : Set.Infinite {u : FreeRow | rowNorm u≤H} := hs
  obtain ⟨T,hT,hcard⟩ := hinf.exists_subset_card_eq n
  have hc := freeRow_count T (max 1 H) (le_max_left _ _) (fun u hu=>(hT hu).trans (le_max_right _ _))
  rw [hcard] at hc
  exact not_le_of_gt hn hc

def boundedFreeRows (H : ℝ) : Finset FreeRow := (finite_bounded_freeRows H).toFinset

@[simp] lemma mem_boundedFreeRows {H : ℝ} {u : FreeRow} : u∈boundedFreeRows H ↔ rowNorm u≤H :=
  Set.Finite.mem_toFinset _

def rowBand (A B : ℝ) : Finset FreeRow := (boundedFreeRows B).filter (fun u=>u.val≠1 ∧ A≤rowNorm u ∧ rowNorm u<B)

@[simp] lemma mem_rowBand {A B : ℝ} {u : FreeRow} :
    u∈rowBand A B ↔ u.val≠1 ∧ A≤rowNorm u ∧ rowNorm u<B := by
  simp only [rowBand,Finset.mem_filter,mem_boundedFreeRows]
  constructor
  · exact And.right
  · intro h
    exact ⟨h.2.2.le,h⟩

def dyadicRows (A : ℝ) (n : ℕ) : Finset FreeRow := rowBand (A*(2:ℝ)^n) (A*(2:ℝ)^(n+1))

lemma mem_dyadicRows {A : ℝ} {n : ℕ} {u : FreeRow} :
    u∈dyadicRows A n ↔ u.val≠1 ∧ A*(2:ℝ)^n≤rowNorm u ∧ rowNorm u<2*(A*(2:ℝ)^n) := by
  simp only [dyadicRows,mem_rowBand,pow_succ]
  ring_nf

lemma dyadicRows_disjoint (A : ℝ) (hA : 0<A) : Pairwise (fun m n=>Disjoint (dyadicRows A m) (dyadicRows A n)) := by
  intro m n hmn
  apply Finset.disjoint_left.mpr
  intro u hm hn
  rw [mem_dyadicRows] at hm hn
  have hpow (j k : ℕ) (hjk : j<k) : 2*(A*(2:ℝ)^j)≤A*(2:ℝ)^k := by
    have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (Nat.succ_le_iff.mpr hjk)
    have := mul_le_mul_of_nonneg_left hh hA.le
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using this
  rcases lt_or_gt_of_ne hmn with h|h
  · exact not_lt_of_ge ((hpow m n h).trans hn.2.1) hm.2.2
  · exact not_lt_of_ge ((hpow n m h).trans hm.2.1) hn.2.2

lemma exists_dyadicRows (A : ℝ) (hA : 0<A) (u : FreeRow) (hu : u.val≠1) (hU : A≤rowNorm u) :
    ∃n : ℕ,u∈dyadicRows A n := by
  obtain ⟨n,hn,hn'⟩ := exists_nat_pow_near ((le_div_iff₀ hA).mpr (by simpa using hU)) (by norm_num : (1:ℝ)<2)
  refine ⟨n,mem_dyadicRows.mpr ⟨hu,?_,?_⟩⟩
  · have hh := (le_div_iff₀ hA).mp hn
    simpa only [mul_comm] using hh
  · have hh := (div_lt_iff₀ hA).mp hn'
    simpa only [pow_succ,mul_assoc,mul_comm,mul_left_comm] using hh

def dyadicRowEquiv (A : ℝ) (hA : 0<A) :
    (Σn : ℕ,dyadicRows A n) ≃ {u : FreeRow // u.val≠1 ∧ A≤rowNorm u} :=
  Equiv.ofBijective (fun p=>⟨p.2.val,(mem_dyadicRows.mp p.2.property).1,
    (le_mul_of_one_le_right hA.le (one_le_pow₀ (by norm_num : (1:ℝ)≤2))).trans (mem_dyadicRows.mp p.2.property).2.1⟩) (by
    constructor
    · rintro ⟨m,u⟩ ⟨n,v⟩ heq
      have huv : u.val=v.val := congrArg Subtype.val heq
      have hmn : m=n := by
        by_contra h
        exact (Finset.disjoint_left.mp (dyadicRows_disjoint A hA h)) u.property (huv.symm ▸ v.property)
      subst n
      exact Sigma.ext rfl (heq_of_eq (Subtype.ext huv))
    · intro u
      obtain ⟨n,hn⟩ := exists_dyadicRows A hA u.val u.property.1 u.property.2
      exact ⟨⟨n,⟨u.val,hn⟩⟩,rfl⟩)

theorem tsum_dyadicRows (A : ℝ) (hA : 0<A) (f : FreeRow→ℂ) (hf : Summable f) :
    Summable (fun n=>∑u∈dyadicRows A n,f u) ∧
      (∑'u : FreeRow,if u.val≠1 ∧ A≤rowNorm u then f u else 0)=
        ∑'n : ℕ,∑u∈dyadicRows A n,f u := by
  let e := dyadicRowEquiv A hA
  have hs : Summable (fun p : Σn : ℕ,dyadicRows A n=>f p.2.val) :=
    e.summable_iff.mpr (hf.subtype (fun u=>u.val≠1 ∧ A≤rowNorm u))
  have heq : (fun n : ℕ=>∑'u : dyadicRows A n,f u.val)=(fun n=>∑u∈dyadicRows A n,f u) := by
    funext n
    exact Finset.tsum_subtype _ _
  refine ⟨by simpa only [heq] using hs.sigma,?_⟩
  calc
    _ = ∑'u : {u : FreeRow // u.val≠1 ∧ A≤rowNorm u},f u.val := by
      have hh := (tsum_subtype {u : FreeRow | u.val≠1 ∧ A≤rowNorm u} f).symm
      convert hh using 1
      · apply tsum_congr
        intro u
        by_cases h : u.val≠1 ∧ A≤rowNorm u
        · simp [h]
        · simp [h]
      · rfl
    _ = ∑'p : Σn : ℕ,dyadicRows A n,f p.2.val := (e.tsum_eq (fun u=>f u.val)).symm
    _ = _ := by rw [hs.tsum_sigma];simp_rw [Finset.tsum_subtype]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2618

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RayCharacterFamily
Source SHA256: 8988c4fc9c63702e32556885cf3790e79dd261d0e8c28a95b44aad0bb5e3b5ce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2619








namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace SevenEighths.ProbeRayCharacterFamily
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def fixedTwistSupport : Finset (Ideal O) :=
  (normalizedFactors (M*Ideal.span {rowMaskElement}*Ideal.span {(72:O)})).toFinset

omit [NeZero M] in
theorem fixedTwistSupport_prime : ∀P∈fixedTwistSupport M,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_twist_base_modulus (θ : RayQuotient.Characters M H) :
    ((fixedSourcePrincipal ∅ (by simp)).product
      (HeckeRayQuotient.character M H hH θ).inverse).modulus=M := by
  change (1:Ideal O)⊓M=M
  simp

theorem large_supported_twists_nonprincipal (u : FreeRow)
    (hs : Supported (Ideal.span {u.val}))
    (hl : (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ)<rowNorm u)
    (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hs
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by simp [r]
  let η := (fixedSourcePrincipal ∅ (by simp)).product
    (HeckeRayQuotient.character M H hH θ).inverse
  let χ := (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).inverse
  have hχ : ∀n,elementCoeff χ n=rowTwist (HeckeRowClosure.elementHom η) rowMaskElement 1 u.val n :=
    HeckePrimeNonprincipal.inverse_twist_elementCoeff _ _ _ _ _ _ (rawRow_elementCoeff u)
  intro hp
  have hprincipal : χ.residue=1 := by
    change (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue⁻¹=1
    exact congrArg Inv.inv hp |>.trans inv_one
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η χ rowMaskElement 1 u.val
    rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _) v⁻¹ 0 0 r hr hv hx hχ hprincipal
    (fun P _=>hspan.symm ▸ u.property.2 P)
  have hη : η.modulus=M := inverse_twist_base_modulus M H hH θ
  rw [hη] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (fixedTwistSupport M) (fixedTwistSupport_prime M) hfixed
  rw [hspan] at hn
  exact not_lt_of_ge (show rowNorm u≤(HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ) by unfold rowNorm;exact_mod_cast hn) hl

theorem raw_twisted_conductor (u : FreeRow) (θ : RayQuotient.Characters M H) :
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm≤
      conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm := by
  have ht := HeckePrimeScale.twisted_modulus_bound M H hH (rawRow u).inverse θ
  change _≤(rawRow u).modulus.absNorm*M.absNorm at ht
  exact ht.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using
    Nat.mul_le_mul_right M.absNorm (rawRow_conductor u))
omit [NeZero M] in
theorem canonical_amplitude_raw (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : fixedBadPrimes⊆S) (u : FreeRow) (W : ℝ→ℂ) (a b D : ℝ)
    (hD : 0<D) (hW : Function.support W⊆Set.Ioo a b)
    (hsmall : ∀P∈S,(P.absNorm:ℝ)≤a*D) (z : ℂ) :
    HeckePrimeRow.canonicalPrimeAmplitude M H u.val W b D z=
      HeckePrimeRay.rayPrimePolynomial M H (rawRow u).inverse W b D (1-z.re) z.im := by
  unfold HeckePrimeRow.canonicalPrimeAmplitude HeckePrimeRay.rayPrimePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hp := (Finset.mem_filter.mp hP).2.1
  have he : -HeckeDyadic.shift (1-z.re) z.im=z-1 := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  simp only [HeckePrimeAnnular.annularWeight,he]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp [hw]
  have hPS : P∉S := by
    intro hPS
    have hh := (lt_div_iff₀ hD).mp (hW hw).1
    have := hsmall P hPS
    linarith
  rw [idealCoeff_inverse_conj,rawRow_prime_outside S hS hbad u ⟨P,hp⟩ hPS]
  exact mul_assoc _ _ _

omit H hH in
theorem large_supported_twists_eventually (d : ℝ) (hd : 0<d) :
    ∀ᶠZ : ℝ in Filter.atTop,∀u : FreeRow,Z^d≤rowNorm u →
      Supported (Ideal.span {u.val}) → ∀(H : Subgroup (O ⧸ M)ˣ)
      (hH : RayOrthogonality.globalUnits M≤H) (θ : RayQuotient.Characters M H),
      (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (Filter.eventually_gt_atTop (HeckeExceptionalRows.bound (fixedTwistSupport M):ℝ))]
    with Z hZ u hu hs H hH θ
  exact large_supported_twists_nonprincipal M H hH u hs (hZ.trans_le hu) θ

omit M H hH in
theorem source_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→Character) (T : ℝ) :
    detectorMaximum ψ T≤detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rcases lt_or_ge (51/100:ℝ) (detectorMaximum ψ T) with hm|hm
  · obtain ⟨j,s,hz,hpole,ht,heq⟩ := detectorMaximum_attained ψ T hm
    rw [←heq]
    exact detector_zero_re_le_maximum (sourceDetectorFamily S hS η u ψ) T (Sum.inr j)
      (by rw [heq];exact hm.le) ht hz hpole
  · exact hm.trans (detectorMaximum_bounds _ T).1

omit M H hH in
theorem source_nonprincipal_maximum_dominates {ι : Type*} [Fintype ι]
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (u : FreeRow)
    (ψ : ι→Character) (hψ : ∀j,(ψ j).residue≠1) (T : ℝ) :
    HeckeDetectorZeros.zeroMaximum ψ hψ T≤detectorMaximum (sourceDetectorFamily S hS η u ψ) T := by
  rw [←detectorMaximum_eq_nonprincipal ψ hψ T]
  exact source_maximum_dominates S hS η u ψ T

end SevenEighths.ProbeRayCharacterFamily

end

end OAI
end OAIOriginalModule2619

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RayPhaseBins
Source SHA256: e9d271f3a6302b5ed50e309b15d2fa670c6e6cccf553b9d815c56f204c3e4b54
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2620



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeRayPhaseBins
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbeRayCharacterFamily
open HeckePrimeAmplitudeBins ProbeRaySlots
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_phase_bins (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (hbad : CanonicalQuadraticSieve.fixedBadPrimes⊆S)
    (W : ℝ→ℂ) (A B : ℝ) (hA : 0<A) (hAB : A≤B)
    (hWs : Function.support W⊆Ioo A B) (hW : ContDiff ℝ ∞ W)
    (R dmin dmax rmin τ ε e κ cost mesh σmin σmax δ : ℝ)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (he : 0<e) (he' : e<1/1000)
    (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax → 2≤Z^d → 2<Z^τ →
    ∀(η : Character) (u : FreeRow),Z^δ≤rowNorm u →
      CanonicalQuadraticSieve.Supported (Ideal.span {u.val}) →
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^d →
    ∀(a : ℝ) (i : ℕ),51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u
        (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse)) (3*(i+1:ℕ)*Z^τ)<a+2*e →
    ∀(r : ℝ) (z : ℂ),rmin≤r → r≤R → σmin≤1-z.re → 1-z.re≤σmax →
      |z.im|+Z^τ/2≤(3*i+2:ℕ)*Z^τ → (3+(3*i+2:ℕ)*Z^τ)^2≤(Z^d)^cost →
    let D := (Z^d)^r
    let Q := HeckePrimeRow.canonicalPrimeAmplitude M H u.val W B D z
    let g := amplitude D (a-1/2) mesh Q
    0≤g ∧ g≤a-1/2 ∧ g∈labels (a-1/2) mesh ∧
      ‖Q‖≤D^(g+mesh) ∧ (0<g → (Z^d)^(2*r*g)≤‖Q‖^2) ∧
      ‖∑P∈pool (RayQuotient.identityClass M H) S A B D,
        W ((P.val.absNorm:ℝ)/D)*(P.val.absNorm:ℂ)^(z-1)*
          (-star (CanonicalRowCompletion.idealRowHom u.val P.val))‖≤D^(z.re-1/2+g+mesh) := by
  have hb := HeckePrimeAmplitudeActual.ray_amplitude_bins M H hH W A B hA
    (hWs.trans Ioo_subset_Icc_self) hW R dmin dmax rmin τ ε e κ cost mesh σmin σmax
    hR hdmin hdmax hrmin hτ hε he he' hκ hcost hmesh hbudget hgap
  have hn := large_supported_twists_eventually M δ hδ
  have ht := ProbeRaySlots.power_fixed_exclusions S A (dmin*rmin) hA (mul_pos hdmin hrmin)
    (fun p : {p : ℝ×ℝ // dmin≤p.1 ∧ rmin≤p.2}=>p.val.1*p.val.2)
    (fun p=>mul_le_mul p.property.1 p.property.2 hrmin.le (hdmin.trans_le p.property.1).le)
  filter_upwards [hb,hn,ht,eventually_ge_atTop (1:ℝ)] with Z hb hn ht hZ
  intro d hd hd' hU hT η u hu hs hcond a i ha ha' hbin r z hr hr' hσ hσ' hf hh
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hD : 0<(Z^d)^r := Real.rpow_pos_of_pos (Real.rpow_pos_of_pos hZp _) _
  have hsmall : ∀P∈S,(P.absNorm:ℝ)≤A*(Z^d)^r := by
    intro P hP
    rw [←Real.rpow_mul hZp.le]
    exact ht ⟨(d,r),hd,hr⟩ P hP
  have hnp := hn u hu hs H hH
  have hzmax := (source_nonprincipal_maximum_dominates S hS η u
    (HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse) hnp _).trans_lt hbin
  have hq (θ : RayQuotient.Characters M H) :
      ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤Z^d :=
    (show ((HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse θ).modulus.absNorm:ℝ)≤
      (conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm:ℝ) by
        exact_mod_cast raw_twisted_conductor M H hH u θ).trans hcond
  have heq := canonical_amplitude_raw M H S hS hbad u W A B ((Z^d)^r) hD hWs hsmall z
  have hbins := hb d hd hd' hU hT (rawRow u).inverse hnp a i ha ha' hzmax
    r (1-z.re) z.im hr hr' hσ hσ' hq hf hh
  rw [←heq] at hbins
  refine ⟨hbins.1,hbins.2.1,hbins.2.2.1,hbins.2.2.2.1,hbins.2.2.2.2,?_⟩
  rw [central_phase_norm M H S u.val W A B ((Z^d)^r) hA hAB hD hWs hsmall z]
  calc
    _ ≤ ((Z^d)^r)^(z.re-1/2)*((Z^d)^r)^(_+mesh) :=
      mul_le_mul_of_nonneg_left hbins.2.2.2.1 (Real.rpow_nonneg hD.le _)
    _ = _ := by rw [←Real.rpow_add hD];congr 1;ring
end SevenEighths.ProbeRayPhaseBins

end

end OAI
end OAIOriginalModule2620

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralRowCost
Source SHA256: 5c145c60cf816384ba3eb73d9a1bc6eb9b943a90dba93c3028845268c2750f32
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2621



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbeCentralRepeatedProduct
open ProbeRowReflectedAllocation ProbeRowRadicalConductor HeckeReciprocalGrowth HeckeDeletionBounds
local notation "O" => HeckeFamily.O

private lemma cost_power_identity (N L A R eps : ℝ) (hN : 0<N) (hL : 0<L) :
    N^A*N^R*L^2*(2*N^2*L^2)^eps=
      (2:ℝ)^eps*N^(A+R+2*eps)*L^(2+2*eps) := by
  have hp : (2*N^2*L^2)^eps=(2:ℝ)^eps*N^(2*eps)*L^(2*eps) := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by positivity) (by positivity)]
    rw [←Real.rpow_two N,←Real.rpow_two L,←Real.rpow_mul hN.le,←Real.rpow_mul hL.le]
  rw [hp]
  calc
    _ = (2:ℝ)^eps*(N^A*N^R*N^(2*eps))*(L^2*L^(2*eps)) := by ring
    _ = _ := by
      rw [←Real.rpow_add hN,←Real.rpow_add hN,←Real.rpow_two L,←Real.rpow_add hL]

theorem central_rowCost_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (e eps : ℝ) (he : 0<e) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow) (a H : ℝ),51/100≤a → a≤1 → 0≤H →
      rowCost S hS u a e eps H≤
        C*rowNorm u^(a-1/2+12*e+4*eps)*(3+H)^(2+2*eps) := by
  let F : ℝ := fixedConductorConstant S
  have hF : 1≤F := by
    dsimp [F]
    exact_mod_cast fixedConductorConstant_pos S hS
  have hFp : 0<F := zero_lt_one.trans_le hF
  refine ⟨(2:ℝ)^eps*F^(1/2+12*e+4*eps),by positivity,?_⟩
  intro u a H ha ha1 hH
  let N : ℝ := F*rowNorm u
  let L : ℝ := 3+H
  let A : ℝ := a-1/2+6*e
  let R : ℝ := 6*e+2*eps
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hN : 0<N := mul_pos hFp hn
  have hL : 0<L := by dsimp [L];linarith
  have hA : 0≤A := by dsimp [A];linarith
  have hR : 0≤R := by dsimp [R];positivity
  have hrad : ((radical (rowCharacter S hS u).modulus).absNorm:ℝ)≤N :=
    original_row_deletion_radical_le S hS u
  have hq : ((rowCharacter S hS u).modulus.absNorm:ℝ)≤N := original_row_conductor_le S hS u
  have hc : presentationComplexity (rowCharacter S hS u) H≤2*N^2*L^2 := by
    unfold presentationComplexity HeckeLogarithmic.complexity
    rw [abs_of_nonneg hH]
    calc
      _ ≤ N*(2*N*L^2) := by
        apply mul_le_mul hrad _ (by positivity) hN.le
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hq (by norm_num)) (sq_nonneg L)
      _ = _ := by ring
  have hrpow := Real.rpow_le_rpow (show (0:ℝ)≤(radical (rowCharacter S hS u).modulus).absNorm by positivity) hrad hR
  have hcpow := Real.rpow_le_rpow (show 0≤presentationComplexity (rowCharacter S hS u) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity) hc heps.le
  have hbound : rowCost S hS u a e eps H≤N^A*N^R*L^2*(2*N^2*L^2)^eps := by
    unfold rowCost
    apply mul_le_mul _ hcpow (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _) (by positivity)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg L)
    exact mul_le_mul_of_nonneg_left hrpow (Real.rpow_nonneg hN.le _)
  rw [cost_power_identity N L A R eps hN hL] at hbound
  have hexp : A+R+2*eps=a-1/2+12*e+4*eps := by dsimp [A,R];ring
  rw [hexp] at hbound
  apply hbound.trans
  dsimp only [N]
  rw [Real.mul_rpow hFp.le hn.le]
  have hf := Real.rpow_le_rpow_of_exponent_le hF
    (show a-1/2+12*e+4*eps≤1/2+12*e+4*eps by linarith)
  calc
    _ = ((2:ℝ)^eps*F^(a-1/2+12*e+4*eps))*rowNorm u^(a-1/2+12*e+4*eps)*L^(2+2*eps) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hL.le _)
      apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hn.le _)
      exact mul_le_mul_of_nonneg_left hf (Real.rpow_nonneg (by norm_num) _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2621

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralTargetCost
Source SHA256: ae448d792907b09c9773ba9ec155558b36580f87ab8efb0daf33121f448dd845
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2622



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth HeckeDeletionBounds
open ProbeRowRadicalConductor
local notation "O" => HeckeFamily.O

lemma presentationComplexity_norm_bound (χ : Character) (H : ℝ) :
    presentationComplexity χ H≤2*(χ.modulus.absNorm:ℝ)^2*(3+|H|)^2 := by
  have hd : radical χ.modulus∣χ.modulus := by
    unfold radical SmoothMobiusCorrection.primeProduct
    rw [SmoothMobiusCorrection.prod_primeSet χ.modulus (fun J : Ideal O=>J)]
    exact IdealMobiusDivisorSum.support_product_dvd χ.modulus_ne_bot (Finset.Subset.refl _)
  have hn : ((radical χ.modulus).absNorm:ℝ)≤χ.modulus.absNorm := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)) (map_dvd Ideal.absNorm hd)
  unfold presentationComplexity HeckeLogarithmic.complexity
  calc
    _ ≤ (χ.modulus.absNorm:ℝ)*(2*χ.modulus.absNorm*(3+|H|)^2) :=
      mul_le_mul_of_nonneg_right hn (by positivity)
    _ = _ := by ring

lemma target_complexity_norm_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H : ℝ) (hH : 0≤H) :
    presentationComplexity ((targetRow η u).excludePrimes S hS) H≤
      2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2 := by
  have hn : (((targetRow η u).excludePrimes S hS).modulus.absNorm:ℝ)≤
      (fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u := by
    unfold rowNorm
    exact_mod_cast (by simpa only [fixedConductorConstant,mul_assoc,mul_comm,mul_left_comm] using
      targetRow_excluded_conductor S hS η u)
  apply (presentationComplexity_norm_bound _ H).trans
  rw [abs_of_nonneg hH]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  exact mul_le_mul_of_nonneg_left ((sq_le_sq₀ (by positivity) (by unfold rowNorm;positivity)).mpr hn) (by norm_num)

lemma target_complexity_power_bound (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (H eps : ℝ) (hH : 0≤H) (heps : 0≤eps) :
    (presentationComplexity ((targetRow η u).excludePrimes S hS) H)^eps≤
      (2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps) := by
  have hb := Real.rpow_le_rpow (show 0≤presentationComplexity ((targetRow η u).excludePrimes S hS) H by
    unfold presentationComplexity HeckeLogarithmic.complexity;positivity)
    (target_complexity_norm_bound S hS η u H hH) heps
  apply hb.trans_eq
  rw [show 2*((fixedConductorConstant S:ℝ)*η.modulus.absNorm*rowNorm u)^2*(3+H)^2=
    (2*(fixedConductorConstant S:ℝ)^2)*(η.modulus.absNorm:ℝ)^2*rowNorm u^2*(3+H)^2 by ring]
  rw [Real.mul_rpow (by unfold rowNorm;positivity) (by positivity),
    Real.mul_rpow (by positivity) (by unfold rowNorm;positivity),Real.mul_rpow (by positivity) (by positivity)]
  rw [←Real.rpow_two (η.modulus.absNorm:ℝ),←Real.rpow_two (rowNorm u),←Real.rpow_two (3+H),
    ←Real.rpow_mul (by positivity : (0:ℝ)≤η.modulus.absNorm),
    ←Real.rpow_mul (rowNorm_ge_one u |>.trans' (by norm_num : (0:ℝ)≤1)),
    ←Real.rpow_mul (by linarith : 0≤3+H)]

theorem centralRemainingScalar_arithmetic_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(3*eps)*(3+H)^(2*eps) := by
  obtain ⟨C,hC,hbound⟩ := centralRemainingScalar_bound e eps he he' heps
  have hF : 0<(fixedConductorConstant S:ℝ) := by exact_mod_cast fixedConductorConstant_pos S hS.prime
  refine ⟨C*(2*(fixedConductorConstant S:ℝ)^2)^eps,by positivity,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hb := hbound S hS hfirst η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  apply hb.trans
  have hc := target_complexity_power_bound S hS.prime η u H eps hh heps.le
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  calc
    _ ≤ C*rowNorm u^eps*((2*(fixedConductorConstant S:ℝ)^2)^eps*(η.modulus.absNorm:ℝ)^(2*eps)*
        rowNorm u^(2*eps)*(3+H)^(2*eps)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by
      rw [show 3*eps=eps+2*eps by ring,Real.rpow_add hn]
      ring

theorem central_remaining_rowCost_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps H≤
        C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+H)^(2+4*eps) := by
  obtain ⟨C0,hC0,h0⟩ := centralRemainingScalar_arithmetic_bound e eps he he' heps S hS hfirst
  obtain ⟨C1,hC1,h1⟩ := central_rowCost_bound S hS.prime e eps he heps
  refine ⟨C0*C1,mul_pos hC0 hC1,?_⟩
  intro η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hh : 0≤H := (abs_nonneg _).trans hxi
  have hn : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hL : 0<3+H := by linarith
  have h0' := h0 η u ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have h1' := h1 u a H ha ha1 hh
  apply (mul_le_mul h0' h1' (ProbeCentralRepeatedProduct.rowCost_nonneg S hS.prime u a e eps H)
    (by positivity)).trans_eq
  have hnp : rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps)=
      rowNorm u^(a-1/2+12*e+7*eps) := by rw [←Real.rpow_add hn];congr 1;ring
  have hlp : (3+H)^(2*eps)*(3+H)^(2+2*eps)=(3+H)^(2+4*eps) := by
    rw [←Real.rpow_add hL];congr 1;ring
  calc
    _ = C0*C1*(η.modulus.absNorm:ℝ)^(2*eps)*
        (rowNorm u^(3*eps)*rowNorm u^(a-1/2+12*e+4*eps))*
        ((3+H)^(2*eps)*(3+H)^(2+2*eps)) := by ring
    _ = _ := by rw [hnp,hlp]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2622

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralPrimeSum
Source SHA256: 5a9d6aae268cee83f99c27c3339291a9a1fcb396128653ba5a2ec2857f34f40d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2623



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralPrimeSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralAllSlots
local notation "O" => HeckeFamily.O

theorem actual_central_prime_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS.prime η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j P,P∈T j→P.val∉S),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 →
      |x.im|≤(3*i+2:ℕ)*T0 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
        (fun j=>hPS j (P j).val (P j).property) W Y x w z‖ ≤
      C*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+eps*(N+8))*
        (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Ca,hCa,hall⟩ := actual_three_branch_slots N e eps c d B he he1 heps hc hd hB
  obtain ⟨Cb,hCb,hcost⟩ := central_remaining_rowCost_bound e eps he he1 heps S hS hfirst
  refine ⟨Ca*Cb,mul_pos hCa hCb,?_⟩
  intro u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hPS hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hxi hwi p hp hphase
  let hs : ∀j P,P∈T j→Supported P.val := fun j P hP=>outside_prime_supported S hS.bad P (hPS j P hP)
  have hinj (P : ∀j,T j) : Function.Injective (fun j=>(P j).val) := by
    intro j l hh
    change (P j).val=(P l).val at hh
    by_contra hne
    exact Finset.disjoint_left.mp (hdis j l hne) (P j).property (by rw [hh];exact (P l).property)
  have ha' := hall S hS.prime hmax hS.bad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
    W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  have hc' := hcost η u twists T0 a ((3*i+2:ℕ)*T0) i hT0 ha ha1 le_rfl hbin x w z hx hw hz hxi
  have hN : 0<rowNorm u := zero_lt_one.trans_le (rowNorm_ge_one u)
  have hy : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (zero_le_one.trans (hY j)) _)
  have hpp : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  rw [calibrated_prime_slots_separate S hS hmax η u T hPS hinj W Y a e x w z
    hfirst ha ha1 he he1.le hx hw hz hQ hη hsmall,centralRowScalar_split,norm_mul,norm_mul]
  have hn := mul_le_mul_of_nonneg_left ha' (norm_nonneg (centralRemainingScalar S hS η u x w z))
  have hc'' := mul_le_mul_of_nonneg_right hc'
    (show 0≤Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) by positivity)
  have hpow : rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1))=
      rowNorm u^(a-1/2+12*e+eps*(N+8)) := by
    rw [←Real.rpow_add hN]
    congr 1
    ring
  calc
    _ = ‖centralRemainingScalar S hS η u x w z‖*
      (‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖) := by ring
    _ ≤ ‖centralRemainingScalar S hS η u x w z‖*
      (Ca*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0)*
        rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hn
    _ = (‖centralRemainingScalar S hS η u x w z‖*ProbeCentralRepeatedProduct.rowCost S hS.prime u a e eps ((3*i+2:ℕ)*T0))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := by ring
    _ ≤ (Cb*(η.modulus.absNorm:ℝ)^(2*eps)*rowNorm u^(a-1/2+12*e+7*eps)*(3+(3*i+2:ℕ)*T0)^(2+4*eps))*
      (Ca*rowNorm u^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j)) := hc''
    _ = _ := by
      calc
        _ = Ca*Cb*(η.modulus.absNorm:ℝ)^(2*eps)*(rowNorm u^(a-1/2+12*e+7*eps)*rowNorm u^(eps*(N+1)))*
          (3+(3*i+2:ℕ)*T0)^(2+4*eps)*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hpow]
end SevenEighths.ProbeCentralPrimeSum

end

end OAI
end OAIOriginalModule2623

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SmallPartition
Source SHA256: dab48be821995c28f6cf8e57afbd1451c99bd3216875e4b3ce0a835c4bff9322
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2624


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def smallDyadicIndices (L : ℝ) : Finset ℕ :=
  (Finset.range (Nat.find (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))).filter (fun n=>(2:ℝ)^n≤L)

@[simp] lemma mem_smallDyadicIndices {L : ℝ} {n : ℕ} : n∈smallDyadicIndices L ↔ (2:ℝ)^n≤L := by
  simp only [smallDyadicIndices,Finset.mem_filter,Finset.mem_range]
  constructor
  · exact And.right
  · intro hn
    refine ⟨?_,hn⟩
    by_contra h
    have hp := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (not_lt.mp h)
    exact not_lt_of_ge (hp.trans hn) (Nat.find_spec (pow_unbounded_of_one_lt L (by norm_num : (1:ℝ)<2)))

def smallDyadicRows (L : ℝ) (n : ℕ) : Finset FreeRow := (dyadicRows 1 n).filter (fun u=>rowNorm u<L)

@[simp] lemma mem_smallDyadicRows {L : ℝ} {n : ℕ} {u : FreeRow} :
    u∈smallDyadicRows L n ↔ u∈dyadicRows 1 n ∧ rowNorm u<L := Finset.mem_filter

lemma smallDyadicRows_disjoint (L : ℝ) : Pairwise (fun m n=>Disjoint (smallDyadicRows L m) (smallDyadicRows L n)) := by
  intro m n hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)

lemma smallDyadicRows_eq_empty {L : ℝ} {n : ℕ} (hn : n∉smallDyadicIndices L) : smallDyadicRows L n=∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  have h := mem_smallDyadicRows.mp hu
  have hlo := (mem_dyadicRows.mp h.1).2.1
  apply hn
  rw [mem_smallDyadicIndices]
  simpa only [one_mul] using hlo.trans h.2.le

lemma small_rows_biUnion (L : ℝ) :
    (smallDyadicIndices L).biUnion (smallDyadicRows L)=rowBand 1 L := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    have hh := mem_smallDyadicRows.mp hu
    have hm := mem_dyadicRows.mp hh.1
    exact mem_rowBand.mpr ⟨hm.1,rowNorm_ge_one u,hh.2⟩
  · intro hu
    have hh := mem_rowBand.mp hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u hh.1 hh.2.1
    refine Finset.mem_biUnion.mpr ⟨n,?_,mem_smallDyadicRows.mpr ⟨hn,hh.2.2⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans hh.2.2.le

lemma sum_small_dyadicRows (L : ℝ) (f : FreeRow→ℂ) :
    (∑u∈rowBand 1 L,f u)=∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u := by
  rw [←small_rows_biUnion L]
  exact Finset.sum_biUnion (fun m hm n hn hmn=>smallDyadicRows_disjoint L hmn)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2624

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFloorDyadic
Source SHA256: cb144cf21f1ba9e638cec7850644b350744ea5a1448186f4b28f53ee45ce059d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2625


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

lemma bounded_dyadic_power_sum (p : ℝ) (hp : 0<p) :
    ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^p)≤C*H^p := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound p (p+1) hp (by linarith)
  refine ⟨(2:ℝ)^(p+1)*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^p≤(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^(p+1)≤(2:ℝ)^(p+1) :=
      Real.rpow_le_rpow hd.le (by linarith) (by linarith)
    unfold CompletedDyadic.kernelTerm
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hd _)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh
      (Real.rpow_nonneg (show (0:ℝ)≤(2:ℝ)^n by positivity) p)
  calc
    _ ≤ ∑n∈F,(2:ℝ)^(p+1)*CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := Finset.sum_le_sum hpoint
    _ = (2:ℝ)^(p+1)*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n := (Finset.mul_sum _ _ _).symm
    _ ≤ (2:ℝ)^(p+1)*∑'n,CompletedDyadic.kernelTerm H⁻¹ p (p+1) n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by positivity)
    _ ≤ (2:ℝ)^(p+1)*(C*(H⁻¹)^(-p)) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

lemma retained_dyadic_partition (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) :
    (smallDyadicIndices H).biUnion (fun n=>rows∩dyadicRows 1 n)=rows := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn,hu⟩ := Finset.mem_biUnion.mp hu
    exact (Finset.mem_inter.mp hu).1
  · intro hu
    obtain ⟨n,hn⟩ := exists_dyadicRows 1 (by norm_num) u (hrows u hu).1 (rowNorm_ge_one u)
    refine Finset.mem_biUnion.mpr ⟨n,?_,Finset.mem_inter.mpr ⟨hu,hn⟩⟩
    rw [mem_smallDyadicIndices]
    have hlo := (mem_dyadicRows.mp hn).2.1
    simpa only [one_mul] using hlo.trans (hrows u hu).2

lemma retained_dyadic_sum {A : Type*} [AddCommMonoid A] (rows : Finset FreeRow) (H : ℝ)
    (hrows : ∀u∈rows,u.val≠1 ∧ rowNorm u≤H) (f : FreeRow→A) :
    (∑u∈rows,f u)=∑n∈smallDyadicIndices H,∑u∈rows∩dyadicRows 1 n,f u := by
  conv_lhs => rw [←retained_dyadic_partition rows H hrows]
  apply Finset.sum_biUnion
  intro m hm n hn hmn
  exact (dyadicRows_disjoint 1 (by norm_num) hmn).mono (Finset.inter_subset_right) (Finset.inter_subset_right)

lemma bounded_freeRow_power_sum (p : ℝ) (hp : -1<p) :
    ∃C : ℝ,0<C ∧ ∀(rows : Finset FreeRow) (H : ℝ),0<H →
      (∀u∈rows,u.val≠1 ∧ rowNorm u≤H) →
      (∑u∈rows,rowNorm u^p)≤C*H^(1+p) := by
  obtain ⟨C,hC,hpow⟩ := bounded_dyadic_power_sum (1+p) (by linarith)
  let A := ProbeSelectedPrimeSums.annularPower 1 2 p
  have hA : 0≤A := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 p (by norm_num)
  refine ⟨256*(A+1)*C,by positivity,?_⟩
  intro rows H hH hrows
  rw [retained_dyadic_sum rows H hrows]
  have hdyad (n : ℕ) : (∑u∈rows∩dyadicRows 1 n,rowNorm u^p)≤256*(A+1)*((2:ℝ)^n)^(1+p) := by
    have hn : ∀u∈rows∩dyadicRows 1 n,(2:ℝ)^n≤rowNorm u ∧ rowNorm u≤2*(2:ℝ)^n := by
      intro u hu
      have hh := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
      simpa only [one_mul] using And.intro hh.1 hh.2.le
    have hb := dyadic_weighted_rows p 0 1 ((2:ℝ)^n) (by norm_num) (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
      (rows∩dyadicRows 1 n) hn (fun u=>rowNorm u^p) (fun u hu=>by simp [rowNorm]) (0:ℂ) rfl
    simp only [frequencyWeight_ideal_norm,Complex.zero_re,neg_zero,Real.rpow_zero,one_mul,sub_zero] at hb
    exact hb.trans (by change 256*1*A*_≤_;gcongr <;> linarith)
  calc
    _ ≤ ∑n∈smallDyadicIndices H,256*(A+1)*((2:ℝ)^n)^(1+p) := Finset.sum_le_sum (fun n _=>hdyad n)
    _ = 256*(A+1)*∑n∈smallDyadicIndices H,((2:ℝ)^n)^(1+p) := (Finset.mul_sum _ _ _).symm
    _ ≤ 256*(A+1)*(C*H^(1+p)) :=
      mul_le_mul_of_nonneg_left (hpow H hH (smallDyadicIndices H) (fun n hn=>mem_smallDyadicIndices.mp hn)) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2625

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ExhaustivePartition
Source SHA256: 64f6cdf6a0948d07fa64651ede430f8da4feb0f6567d92830564a83d929333fb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2626


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

theorem nonprincipal_rows_partition (L U : ℝ) (hL : 1≤L) (hLU : L≤U)
    (f : FreeRow→ℂ) (hf : Summable f) :
    (∑'u : FreeRow,if u.val=1 then 0 else f u)=
      (∑n∈smallDyadicIndices L,∑u∈smallDyadicRows L n,f u)+
        (∑u∈rowBand L U,f u)+(∑'n : ℕ,∑u∈dyadicRows U n,f u) := by
  let g1 := (↑(rowBand 1 L):Set FreeRow).indicator f
  let g2 := (↑(rowBand L U):Set FreeRow).indicator f
  let g3 := {u : FreeRow | u.val≠1 ∧ U≤rowNorm u}.indicator f
  have hg1 : Summable g1 := hf.indicator _
  have hg2 : Summable g2 := hf.indicator _
  have hg3 : Summable g3 := hf.indicator _
  have hpoint (u : FreeRow) : (if u.val=1 then 0 else f u)=g1 u+g2 u+g3 u := by
    have hnorm := rowNorm_ge_one u
    by_cases hu : u.val=1
    · simp [g1,g2,g3,mem_rowBand,hu]
    · by_cases hsmall : rowNorm u<L
      · have hU : ¬U≤rowNorm u := not_le.mpr (hsmall.trans_le hLU)
        have hL' : ¬L≤rowNorm u := not_le.mpr hsmall
        simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hU]
      · have hL' : L≤rowNorm u := le_of_not_gt hsmall
        by_cases hlarge : U≤rowNorm u
        · have hU : ¬rowNorm u<U := not_lt.mpr hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
        · have hU : rowNorm u<U := lt_of_not_ge hlarge
          simp [g1,g2,g3,mem_rowBand,hu,hnorm,hsmall,hL',hlarge,hU]
  have hsum1 : (∑'u,g1 u)=∑u∈rowBand 1 L,f u := by
    rw [tsum_eq_sum (s:=rowBand 1 L) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum2 : (∑'u,g2 u)=∑u∈rowBand L U,f u := by
    rw [tsum_eq_sum (s:=rowBand L U) (fun u hu=>Set.indicator_of_notMem hu f)]
    apply Finset.sum_congr rfl
    intro u hu
    exact Set.indicator_of_mem hu f
  have hsum3 : (∑'u,g3 u)=∑'n : ℕ,∑u∈dyadicRows U n,f u := by
    have hh := (tsum_dyadicRows U (by linarith) f hf).2
    convert hh using 1
    apply tsum_congr
    intro u
    by_cases h : u.val≠1 ∧ U≤rowNorm u <;> simp [g3,h]
  simp_rw [hpoint]
  rw [(hg1.add hg2).tsum_add hg3,hg1.tsum_add hg2,hsum1,hsum2,hsum3,sum_small_dyadicRows]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2626

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.PhysicalPartition
Source SHA256: 25373eaeb09764d700f3df8664919446f24a10fc1a60e629547322b4049cf38f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2627



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CompletedGauss CanonicalQuadraticSieve
local notation "O" => HeckeFamily.O

def physicalRowValue {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (u : FreeRow) : ℂ :=
  ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u

theorem physicalRowValue_summable {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Summable (physicalRowValue S hmax η T W Yp W0 W1 X Y Z) := by
  have hs (P : ∀i,T i) : Summable (fun u : FreeRow=>
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) :=
    (rowIntegral_summable η S _ _ (fun i=>supported_primaryGenerator_ne_zero _ (hT i _ (P i).property))
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).mul_left _
  have hh (F : Finset (∀i,T i)) : Summable (fun u : FreeRow=>∑P∈F,
      (∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        rowIntegral η S (calibrationForSet S hmax) (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z u) := by
    induction F using Finset.induction_on with
    | empty => simp
    | @insert P F hP ih => simpa only [Finset.sum_insert hP] using (hs P).add ih
  exact hh Finset.univ

theorem canonical_physical_probe_partition {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z L U : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (hL : 1≤L) (hLU : L≤U) :
    compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
      (fun i=>canonicalSlotSupport (T i)) W Yp X Y Z=
      (∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z)+
      ((∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W Yp W0 W1 X Y Z)+
        finitePhysicalRows S hmax η (rowBand L U) T W Yp W0 W1 X Y Z+
        (∑'n : ℕ,finitePhysicalRows S hmax η (dyadicRows U n) T W Yp W0 W1 X Y Z)) := by
  let f := physicalRowValue S hmax η T W Yp W0 W1 X Y Z
  have hf := physicalRowValue_summable S hmax η T hT W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [compensatedPhysicalProbe_eq_canonical_rows η S hmax hS.prime hS.bad ((by simp [fixedBadPrimes] : fixedBadPrimes.Nonempty).mono hS.bad) T hT W Yp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ]
  change (∑'u,f u)=_
  rw [hf.tsum_eq_add_tsum_ite principalFreeRow]
  have heq : (fun u : FreeRow=>if u=principalFreeRow then 0 else f u)=
      (fun u : FreeRow=>if u.val=1 then 0 else f u) := by
    funext u
    have hu : u=principalFreeRow ↔ u.val=1 := by
      constructor
      · intro h;subst u;rfl
      · intro h;exact Subtype.ext h
    simp only [hu]
  rw [heq,nonprincipal_rows_partition L U hL hLU f hf]
  congr 1
  · dsimp [f,physicalRowValue]
    simp only [rowIntegral_principal]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2627

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CanonicalTails
Source SHA256: 3e3514944e4f06cb011fd73548f8d1ef63ae9ab6fc087298ccf5060dfdfc80a4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2628



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem canonical_small_original_tail (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := small_original_physical_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  let L := Z^(1/100:ℝ)
  have hrows (n : ℕ) (hn : n∈smallDyadicIndices L) (u : FreeRow) (hu : u∈smallDyadicRows L n) :
      u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n := by
    have hh := mem_dyadicRows.mp (mem_smallDyadicRows.mp hu).1
    exact ⟨hh.1,by simpa only [one_mul,rowNorm] using hh.2.1,by simpa only [one_mul,rowNorm] using hh.2.2.le⟩
  have hbnd := hmain η Z hZ (smallDyadicIndices L) (fun n hn=>mem_smallDyadicIndices.mp hn)
    (smallDyadicRows L) hrows T hT hdis length hl0 hl W hWS hWB
  have heq := sum_small_dyadicRows L (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)
  change finitePhysicalRows S hmax η (rowBand 1 L) T W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z=
    ∑n∈smallDyadicIndices L,finitePhysicalRows S hmax η (smallDyadicRows L n) T W (fun i=>Z^(length i)) W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z at heq
  rw [heq]
  exact (norm_sum_le _ _).trans hbnd

theorem canonical_large_original_tail (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) ∧
      (∑'n,‖finitePhysicalRows S hmax η (dyadicRows (Z^((13/16:ℝ)+ζ)) n) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨C,hC,hmain⟩ := large_original_physical_tail K δ a b B ζ saving hδ hδ' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z hZ T hT hdis length hl0 hl W hWS hWB
  apply hmain η Z hZ (dyadicRows (Z^((13/16:ℝ)+ζ))) _ T hT hdis length hl0 hl W hWS hWB
  intro n u hu
  have hh := mem_dyadicRows.mp hu
  exact ⟨hh.1,hh.2.1,hh.2.2.le⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2628

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CanonicalReduction
Source SHA256: 9648af7dc18efeb4ab569036e5fe50d76f7b85e72e71c41158ffb97d00fd7ed5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2629


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O

def principalPhysicalPool {K : ℕ} (η : Character) (S : Finset (Ideal O))
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Yp i))*
    principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 X Y Z

theorem canonical_probe_minus_central (K : ℕ) (e δ a b B ζ saving : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (_hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finitePhysicalRows S hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤
        C*(η.modulus.absNorm:ℝ)^δ*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨Cs,hCs,hs⟩ := canonical_small_original_tail K e δ a b B he he' hδ hδ' ha hb hB hβ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cl,hCl,hl⟩ := canonical_large_original_tail K δ a b B ζ saving hδ (by linarith) hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨Cs+Cl,add_pos hCs hCl,?_⟩
  intro η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hdec := canonical_physical_probe_partition S hS hmax η T
    (fun i P hP=>outside_prime_supported S hS.bad P (hT i P hP)) W (fun i=>Z^(length i)) W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)) (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (Real.one_le_rpow hZ (by norm_num)) (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  have hs' := hs η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hl' := hl η Z hZ T hT hdis length hl0 hlength W hWS hWB
  have hsmall : (∑n∈smallDyadicIndices (Z^(1/100:ℝ)),finitePhysicalRows S hmax η (smallDyadicRows (Z^(1/100:ℝ)) n)
      T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)=
      finitePhysicalRows S hmax η (rowBand 1 (Z^(1/100:ℝ))) T W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z :=
    (sum_small_dyadicRows (Z^(1/100:ℝ)) (physicalRowValue S hmax η T W (fun i=>Z^(length i)) W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z)).symm
  rw [hsmall] at hdec
  rw [hdec]
  have heq : principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z=
      ∑P : (∀i,T i),(∏i,W i ((Ideal.absNorm (P i).val.val:ℝ)/Z^(length i)))*
        principalRowIntegral η S (fun i=>primaryGenerator (P i).val.val) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z := rfl
  rw [←heq,add_sub_cancel_left]
  rw [show ∀a b c : ℂ,a+b+c-b=a+c from fun a b c=>by ring]
  apply (norm_add_le _ _).trans
  apply (add_le_add hs' ((norm_tsum_le_tsum_norm hl'.1.norm).trans hl'.2)).trans
  calc
    _ ≤ (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+
        (Cs+Cl)*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by gcongr <;> linarith
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2629

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.TailIntegral
Source SHA256: 9b807d2fa4e12716d6439f75d3bba2c0720a1bb9df430311b968619a9a48ab15
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2630


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_tails (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : HeightSpace→ℂ,AEStronglyMeasurable G heightMeasure →
      (∀q,‖G q‖≤A*jointHeight q.1.1 q.1.2 q.2^J) →
      let F := fun q : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q
      Integrable F heightMeasure ∧ ∀T : ℝ,0≤T →
        (∫q : HeightSpace in outsideBox T,‖F q‖ ∂heightMeasure)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/(1+T)^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let S := fun q : HeightSpace=>sourceScale X Y Z ((σ:ℂ)+q.1.1*I)
    ((υ:ℂ)+q.2*I) ((ξ:ℂ)+q.1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp hc
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : HeightSpace) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : HeightSpace) : ‖S q*G q‖≤(E*A)*jointHeight
      q.1.1 q.1.2 q.2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+q.1.1*I) ((υ:ℂ)+q.2*I)
        ((ξ:ℂ)+q.1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ q) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  intro T hT
  have hnorm := congrArg (fun f : HeightSpace→ℂ => ∫q : HeightSpace in outsideBox T,‖f q‖ ∂heightMeasure) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/(1+T)^N := hb T hT
    _ = _ := by dsimp [E];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2630

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.OriginalHeightTail
Source SHA256: 618373b88f7c8a9580a063a1b1ca77255a207f267bc360b564110433a1529125
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2631



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma rowAmplitudeOnLines_first_uniform {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀υ : ℝ,-(1/100:ℝ)≤υ → ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_growth S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro υ hυ t
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

theorem original_x_height_tail {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀υ∈Icc (-(1/100:ℝ)) (1/2),∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀H : ℝ,0≤H →
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H}ᶜ,
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        C*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+H)^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_first_uniform S hS hmax hfirst P hPS η u hu r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r (-(1/100)) (1/2) (by linarith) 2 N
  refine ⟨9*A*D,by positivity,?_⟩
  intro υ hυ X Y Z hX hY hZ H hH
  let G := rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r
  have hG : Measurable G := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  have hb (t : HeightSpace) : ‖G t‖≤(9*A)*jointHeight t.1.1 t.1.2 t.2^2 := by
    have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
      unfold jointHeight
      linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
    apply (hrow υ hυ.1 t).trans
    calc
      _ ≤ A*(3*jointHeight t.1.1 t.1.2 t.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ hυ
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
      ∀T : ℝ,0≤T →
      (∫p : HeightSpace in outsideBox T,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        (9*A)*D*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+T)^N := by
    have hfun : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((r:ℂ)+p.1.2*I)*G p) := by
      funext p
      exact continuedRowOnLines_eq_amplitude ..
    rw [hfun]
    exact ht
  apply le_trans _ (ht'.2 H hH)
  apply setIntegral_mono_set ht'.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
  apply Filter.Eventually.of_forall
  intro p hp
  have hx : H < |p.1.1| := by simpa using hp
  exact Or.inl hx

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2631

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralIntegral
Source SHA256: 7ac09e9a557e9ffffbb6c9028de49f0b04ce6856d6aa07668570dd4e0487596f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2632




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma height_slab_partial_integrable (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    Integrable (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) (volume.prod volume) := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  have hp := (measurePreserving_prodAssoc (volume : Measure ℝ) (volume : Measure ℝ) (volume : Measure ℝ)).symm MeasurableEquiv.prodAssoc
  have hr : Integrable (fun p : ℝ × (ℝ × ℝ)=>(E.indicator f) ((p.1,p.2.1),p.2.2))
      (volume.prod (volume.prod volume)) := hp.integrable_comp_of_integrable hi
  have hj := hr.integral_prod_right
  have heq : (fun q : ℝ×ℝ=>∫x : ℝ,(E.indicator f) ((x,q.1),q.2))=
      (fun q : ℝ×ℝ=>∫x : ℝ in -H..H,f ((x,q.1),q.2)) := by
    funext q
    have hfun : (fun x : ℝ=>(E.indicator f) ((x,q.1),q.2))=
        (Icc (-H) H).indicator (fun x=>f ((x,q.1),q.2)) := by
      funext x
      simp only [Set.indicator_apply,E,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
    rw [hfun,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le (by linarith)]
  exact heq ▸ hj

lemma height_slab_integral_pair (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂heightMeasure)=
      ∫q : ℝ×ℝ,(∫x : ℝ in -H..H,f ((x,q.1),q.2)) ∂volume.prod volume := by
  rw [height_slab_integral_wzx f H hH hf]
  exact (integral_prod_symm _ (height_slab_partial_integrable f H hH hf)).symm

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_central_decomposition {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    IntegrableOn (k (a+16*e)) E heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫p : HeightSpace in E,k (a+16*e) p ∂heightMeasure)+
          I*((∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2)) ∂volume.prod volume)-
            (∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)) ∂volume.prod volume))+
          ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure) := by
  dsimp only
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hleft := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  obtain ⟨C,hC,hjoins⟩ := buffered_horizontal_join_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 0 (17/50) le_rfl
  have hJ (tx : ℝ) (htx : |tx|=H) :
      Integrable (fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) (volume.prod volume) :=
    (hjoins X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx).1
  have hm := hJ (-H) (by rw [abs_neg,abs_of_nonneg hH0])
  have hp := hJ H (abs_of_nonneg hH0)
  have hc := height_slab_partial_integrable _ H hH0 hleft
  refine ⟨hleft,?_⟩
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_pair _ H hH0 hi.integrableOn,
    height_slab_integral_pair _ H hH0 hleft]
  have heq : (fun q : ℝ×ℝ=>∫tx : ℝ in -H..H,k 2 ((tx,q.1),q.2))=
      (fun q : ℝ×ℝ=>(∫tx : ℝ in -H..H,k (a+16*e) ((tx,q.1),q.2))+
        I*((∫v : ℝ in (a+16*e)..2,k v ((-H,q.1),q.2))-(∫v : ℝ in (a+16*e)..2,k v ((H,q.1),q.2)))) := by
    funext q
    have hHT : H≤3*(i+1:ℕ)*B := by
      apply hH.trans
      have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
    simpa only [k,continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat,Complex.ofReal_neg] using
      source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
        ((((1-a-6*e):ℝ):ℂ)+q.2*I) ((17/50:ℂ)+q.1*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT
  rw [heq]
  dsimp only [k] at hm hp ⊢
  have hsplit := integral_add hc ((hm.sub hp).const_mul I)
  simp only [Pi.sub_apply] at hsplit
  rw [hsplit,integral_const_mul]
  congr 1
  exact congrArg (fun z : ℂ=>I*z) (integral_sub hm hp)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2632

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralError
Source SHA256: f58cd582ee8fe0b723cbe46e0d2f9cef1601946783a661c3d2741a251ac11708
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2633


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def centralRowIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

lemma scaleBound_eq_rpow_of_one_le {q lo hi : ℝ} (hq : 1≤q) (hl : lo≤hi) :
    scaleBound q lo hi=q^hi := by
  unfold scaleBound
  rw [max_eq_right (mul_le_mul_of_nonneg_left hl (Real.log_nonneg hq)),
    Real.rpow_def_of_pos (by linarith)]

theorem original_row_central_error {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cj,hCj,hjoin⟩ := buffered_horizontal_join_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl
  obtain ⟨Ct,hCt,htail⟩ := original_x_height_tail S hS hmax (hfirst.mono_parameter (by linarith)) P hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*(2*Cj+Ct),by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hZ0 : 0<Z := by linarith
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let J := fun tx : ℝ=>∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) ∂volume.prod volume
  let tail := ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure
  let A : ℝ := X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1)/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (by positivity) (pow_nonneg (height_pos _).le _)
  have hj (tx : ℝ) (htx : |tx|=H) : ‖J tx‖≤Cj*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := (hjoin X Y Z hX hY hZ0 a B H i ha haTop hB hH hbin tx htx).2
    rw [scaleBound_eq_rpow_of_one_le hZ (by norm_num)] at hb
    convert hb using 1 ; dsimp [J,k,A] ; ring
  have ht : ‖tail‖≤Ct*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := htail (1-a-6*e) ⟨by linarith,by linarith⟩ X Y Z hX hY hZ0 H hH0
    convert hb using 1 ; dsimp [tail,k,E,A,height] ; rw [abs_of_nonneg hH0] ; ring
  have hdec := (rowIntegral_central_decomposition e a B H i he he' ha haTop hB hH0 hH S hS hmax hfirst
    P hP hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ0).2
  have heq : rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
      centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=n*(I*(J (-H)-J H)+tail) := by
    rw [hdec]
    dsimp [centralRowIntegral,n,J,tail,k,E]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(‖J (-H)‖+‖J H‖+‖tail‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg n)
      apply (norm_add_le (I*(J (-H)-J H)) tail).trans
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_sub_le (J (-H)) (J H)) (le_refl ‖tail‖)
    _ ≤ ‖n‖*(Cj*A+Cj*A+Ct*A) := by
      gcongr
      · exact hj (-H) (by rw [abs_neg,abs_of_nonneg hH0])
      · exact hj H (abs_of_nonneg hH0)
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2633

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.UniformSlices
Source SHA256: 11cfc6f15db8b12369f23fd05908b7a148fb3aa5bd25fea11e5a4b205e3d85df
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2634



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_buffered_x_slice_decay (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow σ hσ r ⟨hr,hr1⟩ ((tx,q.1),q.2) htx.le).trans
    calc
      _ ≤ (A*(3+|H|)^2)*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
      _ = _ := by ring
  have ht := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ .s tx (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤
        (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  refine ⟨ht'.1,ht'.2.trans ?_⟩
  have hH0 : 0≤H := htx ▸ abs_nonneg tx
  have hheight : height tx=height H := by simp [height,htx,abs_of_nonneg hH0]
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*(height H)^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2634

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.UniformJoins
Source SHA256: 7e738ab88bd969a34f91fec7367a9e7d9b83eb4ead82cd1507543dac85dc4dba
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2635



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_buffered_horizontal_join_decay (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*contourArithmeticCost η u P*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound0⟩ := uniform_buffered_x_slice_decay (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N r hr hr1
  refine ⟨2*C,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx
  have hbound := hbound0 η u hu P hP hPS ψ
  have hcost := contourArithmeticCost_nonneg η u P
  let A : ℝ := C*contourArithmeticCost η u P*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (mul_nonneg (mul_nonneg hC hcost) (by unfold scaleBound;positivity)) (pow_nonneg (height_pos _).le _)
  have hslice (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :=
    hbound X Y Z hX hY hZ a B H i ha haTop hB hH hbin v ⟨hv.1.le,hv.2⟩ tx htx
  have hnorm (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        v (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤A := by
    apply (hslice v hv).2.trans
    have hz := rpow_le_scaleBound hZ
      (show v+r-1∈Icc ((51/100)+r-1) (2+r-1) by constructor <;> linarith [hv.1,hv.2])
    dsimp [A]
    gcongr
    exact pow_nonneg (height_pos H).le N
  have hm := continuedRow_horizontal_measurable S hS hmax P hPS η u W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ tx (1-a-6*e) r (by linarith)
  obtain ⟨hi,hb⟩ := horizontal_integral_bound
    (fun v q=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2))
    (a+16*e) 2 A (by linarith) hA hm (fun v hv=>(hslice v hv).1) hnorm
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ 2*A := mul_le_mul_of_nonneg_right (by linarith : 2-(a+16*e)≤2) hA
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2635

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.UniformTail
Source SHA256: bba9121f5164d03b90fc85d8710cf01c218966c1fc3f9e5ac04634cee53e88b5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2636




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem uniform_original_x_height_tail (K : ℕ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,∀υ∈Icc (-(1/100:ℝ)) (1/2),∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀H : ℝ,0≤H →
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H}ᶜ,
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+H)^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_first_polynomial K S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r (-(1/100)) (1/2) (by linarith) 2 N
  refine ⟨9*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS υ hυ X Y Z hX hY hZ H hH
  let A := A0*contourArithmeticCost η u P
  have hA := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  have hrow := hrow0 η u hu P hP hPS
  let G := rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r
  have hG : Measurable G := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  have hb (t : HeightSpace) : ‖G t‖≤(9*A)*jointHeight t.1.1 t.1.2 t.2^2 := by
    have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
      unfold jointHeight
      linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
    apply (hrow υ hυ.1 r ⟨hr,hr1⟩ t).trans
    calc
      _ ≤ A*(3*jointHeight t.1.1 t.1.2 t.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ hυ
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
      ∀T : ℝ,0≤T →
      (∫p : HeightSpace in outsideBox T,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p‖ ∂heightMeasure)≤
        (9*A)*D*(X^(1/2-r)*Z^(2+r-1)*Y^(υ-1))/(1+T)^N := by
    have hfun : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun p : HeightSpace=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((r:ℂ)+p.1.2*I)*G p) := by
      funext p
      exact continuedRowOnLines_eq_amplitude ..
    rw [hfun]
    exact ht
  apply le_trans _ ((ht'.2 H hH).trans_eq (by dsimp [A];ring))
  apply setIntegral_mono_set ht'.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
  apply Filter.Eventually.of_forall
  intro p hp
  have hx : H < |p.1.1| := by simpa using hp
  exact Or.inl hx

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2636

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.UniformError
Source SHA256: c6a122676ac1e822b0effc5d3f8fa68cf2c13bf0b014e86c65e9a08cd155b5bc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2637




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_original_row_central_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨Cj,hCj,hjoin0⟩ := uniform_buffered_horizontal_join_decay (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  obtain ⟨Ct,hCt,htail0⟩ := uniform_original_x_height_tail K S hS hmax (hfirst.mono_parameter (by linarith))
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*(2*Cj+Ct),by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have hjoin := hjoin0 η u hu P hP hPS ψ
  have htail := htail0 η u hu P hP hPS
  have hcost := contourArithmeticCost_nonneg η u P
  have hZ0 : 0<Z := by linarith
  let k := fun σ p=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) (17/50) p
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let J := fun tx : ℝ=>∫q : ℝ×ℝ,(∫v : ℝ in (a+16*e)..2,k v ((tx,q.1),q.2)) ∂volume.prod volume
  let tail := ∫p : HeightSpace in Eᶜ,k 2 p ∂heightMeasure
  let A : ℝ := contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (by positivity) (pow_nonneg (height_pos _).le _)
  have hj (tx : ℝ) (htx : |tx|=H) : ‖J tx‖≤Cj*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := (hjoin X Y Z hX hY hZ0 a B H i ha haTop hB hH hbin tx htx).2
    rw [scaleBound_eq_rpow_of_one_le hZ (by norm_num)] at hb
    convert hb using 1 ; dsimp [J,k,A] ; ring
  have ht : ‖tail‖≤Ct*A := by
    apply (norm_integral_le_integral_norm _).trans
    have hb := htail (1-a-6*e) ⟨by linarith,by linarith⟩ X Y Z hX hY hZ0 H hH0
    convert hb using 1 ; dsimp [tail,k,E,A,height] ; rw [abs_of_nonneg hH0] ; ring
  have hdec := (rowIntegral_central_decomposition e a B H i he he' ha haTop hB hH0 hH S hS hmax hfirst
    P hP hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ0).2
  have heq : rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
      centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=n*(I*(J (-H)-J H)+tail) := by
    rw [hdec]
    dsimp [centralRowIntegral,n,J,tail,k,E]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(‖J (-H)‖+‖J H‖+‖tail‖) := by
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg n)
      apply (norm_add_le (I*(J (-H)-J H)) tail).trans
      rw [norm_mul,norm_I,one_mul]
      exact add_le_add (norm_sub_le (J (-H)) (J H)) (le_refl ‖tail‖)
    _ ≤ ‖n‖*(Cj*A+Cj*A+Ct*A) := by
      gcongr
      · exact hj (-H) (by rw [abs_neg,abs_of_nonneg hH0])
      · exact hj H (abs_of_nonneg hH0)
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2637

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralWTail
Source SHA256: 80fb876b474ca4d8bb79ca3c4611f7846698475312d7338e05791f9e14941bd0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2638


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_central_w_height_tail (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H ∧ H < |t.2|},
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin σ hσ
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let R : Set HeightSpace := {t | |t.1.1|≤H ∧ H < |t.2|}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hR : MeasurableSet R := hE.inter (measurableSet_lt measurable_const (show Measurable (fun t : HeightSpace => |t.2|) by fun_prop))
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  let G := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  have hb (t : HeightSpace) : ‖G t‖≤(9*A*(3+|H|)^2)*jointHeight t.1.1 t.1.2 t.2^2 := by
    by_cases ht : t∈E
    · rw [show G t=rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t by exact Set.indicator_of_mem ht _]
      have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
        unfold jointHeight
        linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
      apply (hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r ⟨hr,hr1⟩ t ht).trans
      calc
        _ ≤ (A*(3+|H|)^2)*(3*jointHeight t.1.1 t.1.2 t.2)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
        _ = _ := by ring
    · simp only [G,Set.indicator_of_notMem ht,norm_zero]
      positivity
  let F := fun t : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*G t
  have hp := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have hFR (t : HeightSpace) (ht : t∈R) : F t=continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t := by
    dsimp only [F,G]
    rw [Set.indicator_of_mem (show t∈E from ht.1),continuedRowOnLines_eq_amplitude]
  have hb' : (∫t in R,‖F t‖ ∂heightMeasure)≤
      (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/(1+H)^(N+2) := by
    apply le_trans _ (hp.2 H hH0)
    apply setIntegral_mono_set hp.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=>Or.inr (Or.inr ht.2))
  have heq : (∫t in R,‖F t‖ ∂heightMeasure)=
      ∫t in R,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t‖ ∂heightMeasure :=
    setIntegral_congr_fun hR (fun t ht=>congrArg norm (hFR t ht))
  rw [heq] at hb'
  apply hb'.trans
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hheight : 1+H=height H := by simp [height,abs_of_nonneg hH0]
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*height H^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2638

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralRectangle
Source SHA256: 6bd8daa53432dc2d09bfe912b60f6b3065f2b01f250bf52b289cf1f8c4f3ae6d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2639


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def centralRectangleIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H ∧ |t.2|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

theorem central_row_w_cutoff_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_w_height_tail (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let T : Set HeightSpace := {t | |t.1.1|≤H ∧ |t.2|≤H}
  let R : Set HeightSpace := {t | |t.1.1|≤H ∧ H < |t.2|}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hT : MeasurableSet T := hE.inter (measurableSet_le (show Measurable (fun t : HeightSpace => |t.2|) by fun_prop) measurable_const)
  have hi : IntegrableOn f E heightMeasure := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hdiff : E\T=R := by
    ext t
    change (|t.1.1|≤H ∧ ¬(|t.1.1|≤H ∧ |t.2|≤H)) ↔ (|t.1.1|≤H ∧ H < |t.2|)
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,lt_of_not_ge (fun h=>hw ⟨hx,h⟩)⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,fun h=>not_le_of_gt hw h.2⟩
  have heq : centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=
      n*(∫t in R,f t ∂heightMeasure) := by
    rw [← hdiff,setIntegral_sdiff hT hi (fun t ht=>ht.1)]
    dsimp [centralRowIntegral,centralRectangleIntegral,n,E,T,f]
    ring
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in R,‖f t‖ ∂heightMeasure) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left (hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
        (a+16*e) ⟨le_rfl,by linarith⟩) (norm_nonneg _)
    _ = _ := by ring

theorem uniform_original_row_rectangle_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_central_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨C1,hC1,h1⟩ := central_row_w_cutoff_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY (by linarith) a B H i ha haTop hB hH0 hH hbin
  have hcost := contourArithmeticCost_nonneg η u P
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
      centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply h1'.trans
    gcongr
    exact pow_nonneg (height_pos _).le _
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralRowIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2639

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralErrorSaving
Source SHA256: 7cc7837f8e3c9635c0c90e189c2457c2c81c5267781dc2c03b225a84562de81f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2640


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_source_crude_scale {Z a e : ℝ} (hZ : 1≤Z) (ha : 0≤a) (he : 0≤e) :
    (Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*
      (Z^(23/48:ℝ))^((1-a-6*e)-1)≤Z^(2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  simp_rw [←Real.rpow_mul hZ0.le]
  rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
  exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma central_prime_product_bound {K : ℕ} (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (_hb : 0≤b) (length : Fin K→ℝ)
    (hlength : ∑j,length j=(1/6:ℝ)) (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    (∏j,((P j).val.absNorm:ℝ))≤b^K*Z^(1/6:ℝ) := by
  calc
    _ ≤ ∏j,b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hP j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hlength]

lemma central_arithmetic_cost_bound {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b ζ : ℝ) (hZ : 1≤Z) (hb : 0≤b) (hζ : ζ≤1/48)
    (hu : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ))
    (length : Fin K→ℝ) (hlength : ∑j,length j=(1/6:ℝ))
    (hP : ∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) :
    contourArithmeticCost η u P≤(η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hu' : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z :=
    hu.trans (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (13/16:ℝ)+ζ≤1 by linarith))
  have hp := central_prime_product_bound P Z b hZ0 hb length hlength hP
  have hp0 : 0≤∏j,((P j).val.absNorm:ℝ) := Finset.prod_nonneg (fun j _=>Nat.cast_nonneg _)
  unfold contourArithmeticCost
  calc
    _ ≤ (η.modulus.absNorm:ℝ)^2*Z^6*(b^K*Z^(1/6:ℝ))^3 := by
      exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg _) hu' 6) (sq_nonneg _))
        (pow_le_pow_left₀ hp0 hp 3) (pow_nonneg hp0 3) (mul_nonneg (sq_nonneg _) (pow_nonneg hZ0.le 6))
    _ = _ := by
      rw [mul_pow,←Real.rpow_mul_natCast hZ0.le,←Real.rpow_natCast Z 6]
      have heq : Z^(6:ℝ)*Z^((1/6:ℝ)*(3:ℕ))=Z^(13/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←heq]
      norm_num only [Nat.cast_ofNat]
      ring

theorem original_row_rectangle_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralRectangleIntegral S hS hmax P hPS η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((17/2:ℝ)+saving)/τ)
  have hN' : (17/2:ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_rectangle_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(17/2:ℝ)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/height H^N) := by
      have hh : Z^(13/2:ℝ)*Z^(2:ℝ)=Z^(17/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2640

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralFiniteError
Source SHA256: e14dd8e9187084ec44086ab27bc91624150eca422998488570f27ae3489cbda7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2641



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma central_prime_tuple_count {K : ℕ} (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (Z b : ℝ) (hZ : 0<Z) (hb : 0≤b) (length : Fin K→ℝ)
    (hl : ∑j,length j=(1/6:ℝ))
    (hT : ∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) :
    (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z^(1/6:ℝ) := by
  have hc (j : Fin K) : ((T j).card:ℝ)≤128*b*Z^(length j) := by
    have hh := ProbeSelectedPrimeSums.finite_ideal_count ((T j).image Subtype.val) (b*Z^(length j)) (by positivity)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact p.property.ne_zero)
      (by intro I hI;obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hI;exact hT j p hp)
    simpa only [Finset.card_image_of_injective _ Subtype.val_injective,mul_assoc] using hh
  rw [Fintype.card_pi,Nat.cast_prod]
  simp only [Fintype.card_coe]
  calc
    _ ≤ ∏j,128*b*Z^(length j) := Finset.prod_le_prod₀ (fun j _=>Nat.cast_nonneg _) (fun j _=>hc j)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,←Real.rpow_sum_of_pos hZ,hl]

def finiteCentralRectangleRows {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e : ℝ) (a H : FreeRow→ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    centralRectangleIntegral S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
      η u W0 W1 X Y Z (a u) e (H u)

theorem finite_rectangle_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralRectangleRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_rectangle_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((13/16:ℝ)+ζ)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (13/16:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (1/6:ℝ)≤1 by norm_num)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralRectangleIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralRectangleRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralRectangleIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2641

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralZTail
Source SHA256: a7234d729a8fe8edc33f0beff0099206b41ccff8743cbf6ab01f41ac0251f027
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2642


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem uniform_central_z_height_tail (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) (hr1 : r≤1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,
      (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H ∧ H < |t.1.2|},
        ‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r p‖ ∂heightMeasure)≤
        C*contourArithmeticCost η u P*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A0,hA0,hrow0⟩ := rowAmplitudeOnLines_buffered_polynomial (ι:=ι) K e he he' S hS hfirst hmax
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A0*D,by positivity,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin σ hσ
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  let R : Set HeightSpace := {t | |t.1.1|≤H ∧ H < |t.1.2|}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hR : MeasurableSet R := hE.inter (measurableSet_lt measurable_const (show Measurable (fun t : HeightSpace => |t.1.2|) by fun_prop))
  let A := A0*contourArithmeticCost η u P
  have hA : 0≤A := mul_nonneg hA0 (contourArithmeticCost_nonneg η u P)
  let G := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  have hb (t : HeightSpace) : ‖G t‖≤(9*A*(3+|H|)^2)*jointHeight t.1.1 t.1.2 t.2^2 := by
    by_cases ht : t∈E
    · rw [show G t=rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t by exact Set.indicator_of_mem ht _]
      have hh : 3+|t.2|≤3*jointHeight t.1.1 t.1.2 t.2 := by
        unfold jointHeight
        linarith [abs_nonneg t.1.1,abs_nonneg t.1.2,abs_nonneg t.2]
      apply (hrow0 η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r ⟨hr,hr1⟩ t ht).trans
      calc
        _ ≤ (A*(3+|H|)^2)*(3*jointHeight t.1.1 t.1.2 t.2)^2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
        _ = _ := by ring
    · simp only [G,Set.indicator_of_notMem ht,norm_zero]
      positivity
  let F := fun t : HeightSpace=>sourceMellinWeight W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*G t
  have hp := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have hFR (t : HeightSpace) (ht : t∈R) : F t=continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t := by
    dsimp only [F,G]
    rw [Set.indicator_of_mem (show t∈E from ht.1),continuedRowOnLines_eq_amplitude]
  have hb' : (∫t in R,‖F t‖ ∂heightMeasure)≤
      (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/(1+H)^(N+2) := by
    apply le_trans _ (hp.2 H hH0)
    apply setIntegral_mono_set hp.1.norm.integrableOn (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=>Or.inr (Or.inl ht.2))
  have heq : (∫t in R,‖F t‖ ∂heightMeasure)=
      ∫t in R,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r t‖ ∂heightMeasure :=
    setIntegral_congr_fun hR (fun t ht=>congrArg norm (hFR t ht))
  rw [heq] at hb'
  apply hb'.trans
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hheight : 1+H=height H := by simp [height,abs_of_nonneg hH0]
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*height H^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by dsimp [A];rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2642

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralCube
Source SHA256: f1c6a680b1031ed11c22462430e909cb0ecf9f90c1af768cf0af421f53f2fb84
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2643



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def centralCubeIntegral {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)^3*
    ∫p : HeightSpace in {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H},
      continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) p ∂heightMeasure

theorem central_rectangle_z_cutoff_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := uniform_central_z_height_tail (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N (17/50) le_rfl (by norm_num)
  let n : ℂ := ((1/(2*Real.pi):ℝ):ℂ)^3
  refine ⟨‖n‖*C,mul_nonneg (norm_nonneg _) hC,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  let E : Set HeightSpace := {t | |t.1.1|≤H ∧ |t.2|≤H}
  let T : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  let R : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ H < |t.1.2|}
  let f := continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)
  have hE : MeasurableSet E := (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)
  have hT : MeasurableSet T := hE.inter (measurableSet_le (show Measurable (fun t : HeightSpace => |t.1.2|) by fun_prop) measurable_const)
  have hi0 : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  have hi : IntegrableOn f E heightMeasure := hi0.mono_set (fun t ht=>ht.1)
  have hdiff : E\T=R := by
    ext t
    change ((|t.1.1|≤H ∧ |t.2|≤H) ∧ ¬((|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H)) ↔ ((|t.1.1|≤H ∧ |t.2|≤H) ∧ H < |t.1.2|)
    constructor
    · rintro ⟨hx,hw⟩
      exact ⟨hx,lt_of_not_ge (fun h=>hw ⟨hx,h⟩)⟩
    · rintro ⟨hx,hw⟩
      exact ⟨hx,fun h=>not_le_of_gt hw h.2⟩
  have heq : centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H=
      n*(∫t in R,f t ∂heightMeasure) := by
    rw [← hdiff,setIntegral_sdiff hT hi (fun t ht=>ht.1)]
    dsimp [centralRectangleIntegral,centralCubeIntegral,n,E,T,f]
    ring
  have htail : (∫t in R,‖f t‖ ∂heightMeasure)≤
      C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply le_trans _ (hbound η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
      (a+16*e) ⟨le_rfl,by linarith⟩)
    apply setIntegral_mono_set ((show IntegrableOn (fun t=>‖f t‖) {t : HeightSpace | |t.1.1|≤H} heightMeasure from hi0.norm).mono_set (fun t ht=>ht.1)) (Filter.Eventually.of_forall (fun _=>norm_nonneg _))
    exact Filter.Eventually.of_forall (fun t ht=>⟨ht.1.1,ht.2⟩)
  rw [heq,norm_mul]
  calc
    _ ≤ ‖n‖*(∫t in R,‖f t‖ ∂heightMeasure) := mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ ≤ ‖n‖*(C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(a+16*e+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N) :=
      mul_le_mul_of_nonneg_left htail (norm_nonneg _)
    _ = _ := by ring

theorem uniform_original_row_cube_error (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀X Y Z : ℝ,0<X → 0<Y → 1≤Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → 0≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
        C*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C0,hC0,h0⟩ := uniform_original_row_rectangle_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  obtain ⟨C1,hC1,h1⟩ := central_rectangle_z_cutoff_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C0+C1,add_nonneg hC0 hC1,?_⟩
  intro η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h0' := h0 η u hu P hP hPS ψ X Y Z hX hY hZ a B H i ha haTop hB hH0 hH hbin
  have h1' := h1 η u hu P hP hPS ψ X Y Z hX hY (by linarith) a B H i ha haTop hB hH0 hH hbin
  have hcost := contourArithmeticCost_nonneg η u P
  have hz : Z^(a+16*e+(17/50:ℝ)-1)≤Z^(2+(17/50:ℝ)-1) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h1'' : ‖centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H-
      centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H‖≤
      C1*contourArithmeticCost η u P*(X^(1/2-(17/50:ℝ))*Z^(2+(17/50:ℝ)-1)*Y^((1-a-6*e)-1))/height H^N := by
    apply h1'.trans
    gcongr
    exact pow_nonneg (height_pos _).le _
  apply (norm_sub_le_norm_sub_add_norm_sub _ (centralRectangleIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H) _).trans
  exact (add_le_add h0' h1'').trans_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2643

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeErrorSaving
Source SHA256: fbf54f48998aea90df619f0e3e6757439d279c9def05a03af79cdd55587a390d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2644



namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem original_row_cube_arbitrary_saving (K : ℕ) (τ saving b ζ : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀Z : ℝ,1≤Z →
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j,((P j).val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → Z^τ≤H → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralCubeIntegral S hS hmax P hPS η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z a e H‖≤
        C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨N,hN⟩ := exists_nat_gt (((17/2:ℝ)+saving)/τ)
  have hN' : (17/2:ℝ)+saving<τ*N := by exact (div_lt_iff₀ hτ).mp hN |>.trans_eq (mul_comm _ _)
  obtain ⟨C,hC,hbound⟩ := uniform_original_row_cube_error (ι:=ι) K e he he' S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N
  refine ⟨C*(b^K)^3,mul_nonneg hC (pow_nonneg (pow_nonneg hb.le _) _),?_⟩
  intro η u hu P hP hPS ψ Z hZ huZ length hl hp a B H i ha haTop hB hHlo hH hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hH0 : 0≤H := (Real.rpow_nonneg hZ0.le τ).trans hHlo
  have hmain := hbound η u hu P hP hPS ψ (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ a B H i ha haTop hB hH0 hH hbin
  have hcost := central_arithmetic_cost_bound η u P Z b ζ hZ hb.le hζ huZ length hl hp
  have hscale := central_source_crude_scale hZ (by linarith : 0≤a) he.le
  have hden : Z^(τ*N)≤height H^N := by
    rw [Real.rpow_mul_natCast hZ0.le]
    apply pow_le_pow_left₀ (Real.rpow_nonneg hZ0.le _) (hHlo.trans _) N
    simp only [height,abs_of_nonneg hH0]
    linarith
  have hsave : Z^(17/2:ℝ)/Z^(τ*N)≤Z^(-saving) := by
    rw [←Real.rpow_sub hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  apply hmain.trans
  calc
    _ ≤ C*((η.modulus.absNorm:ℝ)^2*(b^K)^3*Z^(13/2:ℝ))*Z^(2:ℝ)/height H^N := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg (height_pos _).le _)
      exact mul_le_mul (mul_le_mul_of_nonneg_left hcost hC) hscale (by positivity) (by positivity)
    _ = (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/height H^N) := by
      have hh : Z^(13/2:ℝ)*Z^(2:ℝ)=Z^(17/2:ℝ) := by rw [←Real.rpow_add hZ0];norm_num
      rw [←hh]
      ring
    _ ≤ (C*(b^K)^3*(η.modulus.absNorm:ℝ)^2)*(Z^(17/2:ℝ)/Z^(τ*N)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact div_le_div_of_nonneg_left (Real.rpow_nonneg hZ0.le _) (Real.rpow_pos_of_pos hZ0 _) hden
    _ ≤ _ := mul_le_mul_of_nonneg_left hsave (by positivity)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2644

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteError
Source SHA256: f054fe24d580e1f27412dba0087a1e7fd81ab481cd8ddba776540e45c1759065
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2645



namespace OAI
noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def finiteCentralCubeRows {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z e : ℝ) (a H : FreeRow→ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    centralCubeIntegral S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
      η u W0 W1 X Y Z (a u) e (H u)

theorem finite_cube_arbitrary_saving (K : ℕ) (τ saving b ζ A : ℝ)
    (hτ : 0<τ) (hb : 0<b) (hζ : ζ≤1/48) (hA : 0≤A)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∑j,length j)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀j y,‖W j y‖≤A) →
      ∀(a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e) →
      ‖finitePhysicalRows S hmax η R T W (fun j=>Z^(length j)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η R T hT W (fun j=>Z^(length j)) W0 W1
          (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H‖≤C*(η.modulus.absNorm:ℝ)^2*Z^(-saving) := by
  obtain ⟨C,hC,hrow⟩ := original_row_cube_arbitrary_saving (ι:=ι) K τ (saving+2) b ζ hτ hb hζ e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨128*(128*b)^K*A^K*C,by positivity,?_⟩
  intro η Z hZ R hR T hT hdis length hl hp W hW a B H idx ψ hbin
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrange : Z^((13/16:ℝ)+ζ)≤Z := by
    simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (13/16:ℝ)+ζ≤1 by linarith)
  have hcR : (R.card:ℝ)≤128*Z := freeRow_count R Z hZ (by
    intro u hu
    exact (hR u hu).2.trans hrange)
  have hcT : (Fintype.card (∀j,T j):ℝ)≤(128*b)^K*Z :=
    (central_prime_tuple_count T Z b hZ0 hb.le length hl hp).trans
      (mul_le_mul_of_nonneg_left (by simpa using Real.rpow_le_rpow_of_exponent_le hZ (show (1/6:ℝ)≤1 by norm_num)) (by positivity))
  let E := C*(η.modulus.absNorm:ℝ)^2*Z^(-(saving+2))
  have hE : 0≤E := by dsimp [E];positivity
  have herr (u : FreeRow) (hu : u∈R) (P : ∀j,T j) :
      ‖rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val)
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u-
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖≤E := by
    rcases hbin u hu with ⟨ha,ha',hB,hHlo,hH,hzero⟩
    exact hrow η u (hR u hu).1 (fun j=>(P j).val) (hdis P) (fun j=>hT j _ (P j).property)
      (ψ u) Z hZ (hR u hu).2 length hl (fun j=>hp j _ (P j).property)
      (a u) (B u) (H u) (idx u) ha ha' hB hHlo hH hzero
  have hw (P : ∀j,T j) : ‖∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j))‖≤A^K := by
    rw [norm_prod]
    calc
      _ ≤ ∏j : Fin K,A := Finset.prod_le_prod₀ (fun j _=>norm_nonneg _) (fun j _=>hW j _)
      _ = _ := by simp
  unfold finitePhysicalRows finiteCentralCubeRows
  rw [←Finset.sum_sub_distrib]
  calc
    _ ≤ ∑u∈R,‖(∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        rowIntegral η S (calibrationForSet S hmax) (fun j=>CompletedGauss.primaryGenerator (P j).val.val) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z u)-
      ∑P:(∀j,T j),(∏j,W j (((P j).val.val.absNorm:ℝ)/Z^(length j)))*
        centralCubeIntegral S hS hmax (fun j=>(P j).val) (fun j=>hT j _ (P j).property)
          η u W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (a u) e (H u)‖ := norm_sum_le _ _
    _ ≤ ∑_u∈R,∑_P:(∀j,T j),A^K*E := by
      apply Finset.sum_le_sum
      intro u hu
      rw [←Finset.sum_sub_distrib]
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro P hP
      rw [←mul_sub,norm_mul]
      exact mul_le_mul (hw P) (herr u hu P) (norm_nonneg _) (pow_nonneg hA _)
    _ = (R.card:ℝ)*(Fintype.card (∀j,T j):ℝ)*(A^K*E) := by simp;ring
    _ ≤ (128*Z)*((128*b)^K*Z)*(A^K*E) := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul hcR hcT (Nat.cast_nonneg _) (by positivity)) (mul_nonneg (pow_nonneg hA _) hE)
    _ = _ := by
      have hz : Z^2*Z^(-(saving+2))=Z^(-saving) := by
        rw [←Real.rpow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      dsimp [E]
      calc
        _ = (128*(128*b)^K*A^K*C*(η.modulus.absNorm:ℝ)^2)*(Z^2*Z^(-(saving+2))) := by ring
        _ = _ := by rw [hz]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2645

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeFiniteIntegral
Source SHA256: 7b3b8c08c3986d98fc40102ed0e623b335cc1b5908683aba0f62584911d25ef8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2646


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

def cubeWeightedRow {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) : HeightSpace→ℂ :=
  {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}.indicator
    (weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50))

theorem cubeWeightedRow_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H) heightMeasure := by
  have hi := continuedPhysicalRowKernel_buffered_integrable e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    (a+16*e) (17/50) le_rfl (by linarith) le_rfl
  let E : Set HeightSpace := {t | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H}
  have hE : MeasurableSet E := ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
    (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  apply (integrable_indicator_iff hE).mpr
  have heq : weightedRowOnLines S hS hmax P hPS η u W Yp W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50)=
      fun t=>(∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z (a+16*e) (1-a-6*e) (17/50) t := by
    funext t
    exact weightedRowOnLines_eq ..
  rw [heq]
  exact (hi.mono_set (fun t ht=>ht.1.1)).const_mul _

lemma cubeWeightedRow_integral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a e H : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,cubeWeightedRow S hS hmax P hPS η u W Yp W0 W1 X Y Z a e H t ∂heightMeasure)=
      (∏j,W j (((P j).val.absNorm:ℝ)/Yp j))*centralCubeIntegral S hS hmax P hPS η u W0 W1 X Y Z a e H := by
  have hE : MeasurableSet {t : HeightSpace | (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H} :=
    ((measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.1|) by fun_prop) measurable_const).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.2|) by fun_prop) measurable_const)).inter
      (measurableSet_le (show Measurable (fun t : HeightSpace=>|t.1.2|) by fun_prop) measurable_const)
  unfold cubeWeightedRow
  rw [integral_indicator hE]
  simp_rw [weightedRowOnLines_eq]
  rw [integral_const_mul]
  unfold centralCubeIntegral
  ring

theorem finiteCentralCubeRows_eq_integral {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (η : Character) (R : Finset FreeRow) (hR : ∀u∈R,u.val≠1)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i → P.val∉S)
    (a B H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character)
    (hbin : ∀u∈R,(51/100:ℝ)≤a u ∧ a u≤1 ∧ 2<B u ∧ H u≤(3*idx u+2:ℕ)*B u ∧
      detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*B u)<a u+2*e)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun t : HeightSpace=>∑u∈R,∑P:(∀i,T i),
      cubeWeightedRow S hS hmax (fun i=>(P i).val) (fun i=>hT i _ (P i).property)
        η u W Yp W0 W1 X Y Z (a u) e (H u) t
    Integrable F heightMeasure ∧
      finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=
        ((1/(2*Real.pi):ℝ):ℂ)^3*(∫t,F t ∂heightMeasure) := by
  let f (u : FreeRow) (P : ∀i,T i) := cubeWeightedRow S hS hmax
    (fun i=>(P i).val) (fun i=>hT i _ (P i).property) η u W Yp W0 W1 X Y Z (a u) e (H u)
  have hi (u : FreeRow) (hu : u∈R) (P : ∀i,T i) : Integrable (f u P) heightMeasure := by
    rcases hbin u hu with ⟨ha,ha',hB,hH,hzero⟩
    exact cubeWeightedRow_integrable e (a u) (B u) (H u) (idx u) he he' ha ha' hB hH
      S hS hmax hfirst _ _ η u (hR u hu) (ψ u) hzero W Yp W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z hX hY hZ
  have hiu (u : FreeRow) (hu : u∈R) : Integrable (fun t=>∑P:(∀i,T i),f u P t) heightMeasure :=
    integrable_finsetSum _ (fun P _=>hi u hu P)
  refine ⟨integrable_finsetSum _ hiu,?_⟩
  change finiteCentralCubeRows S hS hmax η R T hT W Yp W0 W1 X Y Z e a H=_*(∫t,∑u∈R,∑P:(∀i,T i),f u P t ∂heightMeasure)
  rw [integral_finsetSum R hiu,Finset.mul_sum]
  unfold finiteCentralCubeRows
  apply Finset.sum_congr rfl
  intro u hu
  rw [integral_finsetSum Finset.univ (fun P _=>hi u hu P),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  exact (cubeWeightedRow_integral S hS hmax _ _ η u W Yp W0 W1 X Y Z (a u) e (H u)).symm

lemma cube_buffered_heights (t : HeightSpace) (H B : ℝ) (i : ℕ)
    (ht : (|t.1.1|≤H ∧ |t.2|≤H) ∧ |t.1.2|≤H) (hB : 0≤B)
    (hbuffer : H+B/2≤(3*i+2:ℕ)*B) :
    |t.1.1|≤(3*i+2:ℕ)*B ∧ |t.2|≤(3*i+2:ℕ)*B ∧
      |t.1.2|+B/2≤(3*i+2:ℕ)*B := by
  constructor
  · linarith [ht.1.1]
  constructor
  · linarith [ht.1.2]
  · linarith [ht.2]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2646

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeReduction
Source SHA256: 28641905675b292399b202f22de7d8baae3e9d6f3e3fe0654652e9eb8e34313b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2647



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_minus_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(alpha base H : FreeRow→ℝ) (idx : FreeRow→ℕ) (ψ : FreeRow→ι→Character),
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (51/100:ℝ)≤alpha u ∧ alpha u≤1 ∧ 2<base u ∧ Z^τ≤H u ∧ H u≤(3*idx u+2:ℕ)*base u ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*base u)<alpha u+2*e) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C0,hC0,h0⟩ := canonical_probe_minus_central K e δ a b B ζ saving he he' hδ hδ' hζ ha hb hB hβ
    S hS hmax (hfirst.mono_parameter (by linarith)) W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨C1,hC1,h1⟩ := finite_cube_arbitrary_saving (ι:=ι) K τ saving b ζ B hτ hb hζ' hB e he he'
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C0+C1,add_pos_of_pos_of_nonneg hC0 hC1,?_⟩
  intro η Z hZ T hT hdis length hl0 hl hpool W hWS hWB alpha base H idx ψ hbin
  have h0' := h0 η Z hZ T hT hdis length hl0 hl W hWS hWB
  let R := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))
  have hR (u : FreeRow) (hu : u∈R) : u.val≠1 ∧ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤Z^((13/16:ℝ)+ζ) :=
    ⟨(mem_rowBand.mp hu).1,(mem_rowBand.mp hu).2.2.le⟩
  have h1' := h1 η Z hZ R hR T hT hdis length hl hpool W hWB alpha base H idx ψ hbin
  have hQ := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hQδ : (η.modulus.absNorm:ℝ)^δ≤(η.modulus.absNorm:ℝ)^2 := by
    rw [←Real.rpow_two]
    exact Real.rpow_le_rpow_of_exponent_le hQ (by linarith)
  let E := Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)
  have hE : 0≤E := by dsimp [E];positivity
  have hsave : Z^(-saving)≤E := by dsimp [E];have : 0≤Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := Real.rpow_nonneg (by linarith) _;linarith
  have h0'' : ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z‖≤
      C0*(η.modulus.absNorm:ℝ)^2*E :=
    h0'.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQδ hC0.le) hE)
  have h1'' := h1'.trans (mul_le_mul_of_nonneg_left hsave (mul_nonneg hC1 (sq_nonneg (η.modulus.absNorm:ℝ))))
  apply (norm_sub_le_norm_sub_add_norm_sub _
    (finitePhysicalRows S hmax η R T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z) _).trans
  exact (add_le_add h0'' h1'').trans_eq (by dsimp [E];ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2647

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeBins
Source SHA256: 978aa0b65987eea024a97b5b5b9f7ece0408fa259842600ebdb45669af044ad1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2648


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem exists_source_cube_bins (e B : ℝ) (he : 0<e) (hB : 2<B)
    (n : ℕ) (hn : 0<n) (hwidth : (49/100:ℝ)≤n*e)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) (η : Character) (ψ : FreeRow→ι→Character) :
    ∃idx grid : FreeRow→ℕ,∀u : FreeRow,
      1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
      let a : ℝ := 51/100+e*grid u
      let H : ℝ := (3*idx u+1:ℕ)*B
      (51/100:ℝ)≤a ∧ a≤1 ∧ B≤H ∧ H+B/2≤(3*idx u+2:ℕ)*B ∧
      a≤detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*idx u*B) ∧
      detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*idx u*B)<a+e ∧
      detectorMaximum (sourceDetectorFamily S hS η u (ψ u)) (3*(idx u+1:ℕ)*B)<a+2*e ∧
      (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS η u (ψ u) j) s=0 ∧
        ¬((sourceDetectorFamily S hS η u (ψ u) j).residue=1 ∧ s=1) ∧
        a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*B) := by
  have hex (u : FreeRow) := exists_detector_buffered_bin (sourceDetectorFamily S hS η u (ψ u)) B e hB he n hn hwidth
  choose idx grid hspec using hex
  refine ⟨idx,grid,?_⟩
  intro u
  rcases hspec u with ⟨hi,hin,ha,hlo,hhi,hnext,hzero,hdisk⟩
  refine ⟨hi,hin,?_,?_,ha,?_,?_,hlo,hhi,hnext,hzero⟩
  · apply Nat.le_floor
    apply (le_div_iff₀ he).mpr
    nlinarith
  · nlinarith [Nat.cast_nonneg (α:=ℝ) (grid u)]
  · push_cast
    nlinarith [Nat.cast_nonneg (α:=ℝ) (idx u)]
  · push_cast
    linarith

theorem exists_source_cube_bin_number (e : ℝ) (he : 0<e) :
    ∃n : ℕ,0<n ∧ (49/100:ℝ)≤n*e := by
  refine ⟨⌈(49/100:ℝ)/e⌉₊+1,by omega,?_⟩
  have hh := Nat.le_ceil ((49/100:ℝ)/e)
  have hmul := (div_le_iff₀ he).mp hh
  push_cast
  nlinarith

theorem source_cube_height_eventually (τ : ℝ) (hτ : 0<τ) :
    ∀ᶠ Z : ℝ in atTop,1≤Z ∧ 2<Z^τ := by
  filter_upwards [eventually_ge_atTop (1:ℝ),
    (tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2648

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CanonicalCubeChoice
Source SHA256: d4bf1ea049dcd36b241c4f1c20b6e3c5e66c5a0ea38e9c805ae9b945fbeee14c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2649


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem canonical_probe_exists_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀(η : Character) (Z : ℝ),1≤Z → 2<Z^τ →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀ψ : FreeRow→ι→Character,∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (ψ u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (ψ u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (ψ u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let H : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun i=>canonicalSlotSupport (T i)) W (fun i=>Z^(length i)) (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        principalPhysicalPool η S T W (fun i=>Z^(length i)) W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT W (fun i=>Z^(length i))
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha H‖≤
        C*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)) := by
  obtain ⟨C,hC,hbound⟩ := canonical_probe_minus_cube (ι:=ι) K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha hb hB hβ S hS hmax hfirst
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨n,hn,hwidth⟩ := exists_source_cube_bin_number e he
  refine ⟨C,hC,n,hn,?_⟩
  intro η Z hZ hZT T hT hdis length hl0 hl hpool W hWS hWB ψ
  obtain ⟨idx,grid,hbins⟩ := exists_source_cube_bins e (Z^τ) he hZT n hn hwidth S hS.prime η ψ
  refine ⟨idx,grid,?_,?_,?_⟩
  · intro u
    exact ⟨(hbins u).1,(hbins u).2.1,(hbins u).2.2.1,(hbins u).2.2.2.2.2.2.1⟩
  · intro u
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    exact ⟨ha0,ha1,hlo,hhi,hnext,hzero⟩
  · apply hbound η Z hZ T hT hdis length hl0 hl hpool W hWS hWB
      (fun u=>51/100+e*grid u) (fun _=>Z^τ) (fun u=>(3*idx u+1:ℕ)*Z^τ) idx ψ
    intro u hu
    rcases hbins u with ⟨hi,hin,hgrid,ha0,ha1,hBH,hbuffer,hlo,hhi,hnext,hzero⟩
    refine ⟨ha0,ha1,hZT,hBH,?_,hnext⟩
    have : 0≤Z^τ := Real.rpow_nonneg (by linarith) _
    linarith

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2649

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CanonicalRayCube
Source SHA256: c42ec3bf993ce27fe4950ad028b724b42b1a405922670c03dbbcea30e12b0958
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2650



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def rayCubeFamily (u : FreeRow) : RayQuotient.Characters M H→Character :=
  HeckePrimeRay.twistedFamily M H hH (rawRow u).inverse

theorem canonical_probe_exists_ray_cube (K : ℕ) (e δ a b B ζ saving τ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∃n : ℕ,0<n ∧ ∀ᶠ Z : ℝ in atTop,∀η : Character,
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      (∀j P,P∈T j → (P.val.absNorm:ℝ)≤b*Z^(length j)) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
