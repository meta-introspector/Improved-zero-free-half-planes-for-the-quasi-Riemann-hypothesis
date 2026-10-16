        (Real.log ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))) t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ (elementCharacter χ)
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) (fun i=>poolList F (L i))
            (fun i P=>coeff i P.val*logPhase (-t) (Real.log (slotRatio Z z i P.val))))
            (childLogTest W t) Z D) u):=by
    have hh:=InverseInitialExcludedFourier.original_tuples_excluded_fourier
      (childLogTest Woriginal θ) W ao bo hao
      ((InverseInitialOriginalHeight.child_support Woriginal θ).trans hso)
      (InverseInitialOriginalHeight.child_smooth Woriginal ao bo hao hso hWo θ)
      (reflectionExcludedPrimes q) (reflectionExcludedPrimes_prime q)
      (all\assigned) L hL coeff j hj.1 hP hcopTuple hPE χ hout u Z r
      (assignedCenter all z) (assignedCenter assigned z) hZp z lo hi hsum jlo jhi hjratio hcoeff
      (fun v yj yc hv hyj hyc hn=>hFresh v yj yc hv hyj hyc
        (InverseInitialOriginalHeight.child_support Woriginal θ hn))
      F hFa (fun I hI=>(Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2) hsub
    rw [hh,InverseInitialOriginalHeight.logSchwartz_child]
    simp only [←hDeq]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rw [InverseInitialInputReindex.input_puncture_span p hg Finset.univ (elementCharacter χ)
      (primaryGenerator j) (assignedElement assigned qelem) hgj]
  simpa only [hid] using he

end SevenEighths.InverseInitialResidualTupleEnergy

end

end OAI
end OAIOriginalModule2146

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialResidualUniformEnergy
Source SHA256: f320fadc23cf79019777f5aa3b6a9e1576e5fccab40aec9e5c28337ca21e2ceb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2147




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialResidualUniformEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
open InverseInitialCommonLists InverseInitialCommonRatios InverseInitialCommonTuples
open InverseInitialOverlap InverseInitialPoissonBridge InverseInitialExcludedPool
open InverseInitialCommonProfile InverseInitialEnergyCallerWindow
theorem original_residual_uniform_energy
    (Woriginal:ℝ→ℂ)(ao bo:ℝ)(hao:0<ao)(hab:ao≤bo)
    (hso:Function.support Woriginal⊆Set.Icc ao bo)(hWo:ContDiff ℝ ∞ Woriginal)
    (Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(L:σ→Finset (Ideal O))(Hslot:σ→ℝ)(coeff:σ→Ideal O→ℂ),
      (all:Set σ).PairwiseDisjoint L→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,(P.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈L i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀χ:Ideal O→*ℂ,(∀u,‖elementCharacter χ u‖≤1)→
      FactorsModulo (fixedBaseConductor q) (elementCharacter χ)→
      (∀c,¬outside (reflectionExcludedPrimes q) c→χ c=0)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(j:Ideal O),Admissible j→Ideal.span {assignedElement assigned qelem}=j→
      ((j.absNorm:ℝ)/Z^(assignedCenter assigned z))∈Set.Icc (1:ℝ) ((2:ℝ)^K)→
      (∀i∈all\assigned,∀P∈L i,Prime P)→
      (∀i∈all\assigned,∀P∈L i,coeff i P≠0→slotRatio Z z i P∈Set.Icc (1:ℝ) 2)→
      (∀t∈(all\assigned).pi L,Admissible (j*survivingProduct (all\assigned) t))→
      (∀t∈(all\assigned).pi L,Pairwise (Function.onFun IsCoprime
        (fun i:↥(all\assigned)=>t i.val i.property)))→
      (∀t∈(all\assigned).pi L,outside (reflectionExcludedPrimes q)
        (j*survivingProduct (all\assigned) t))→
    ∀θ:ℝ,
      (∑u∈rows,‖∑t∈(all\assigned).pi L,
        (∏i∈(all\assigned).attach,coeff i.val (t i.val i.property))*
        residualNormalizedPolynomial (originalSource Z r bo)
          (j*survivingProduct (all\assigned) t) j χ (fun _=>1)
          (childLogTest Woriginal θ) Z r (assignedCenter all z) (assignedCenter assigned z) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨W,A,B,Bnorm,hA,hAB,hBn,hWc,hWs,hWb,hFresh⟩:=
    InverseInitialUniformFresh.exists_uniform_fresh K ao bo hao hab
  have hs:Function.support (W:ℝ→ℂ)⊆Set.Icc A B:=(subset_tsupport (W:ℝ→ℂ)).trans hWs
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialResidualTupleEnergy.original_residual_tuple_energy
    Woriginal W ao bo hao hso hWo A B 1 hA le_rfl hs (W.smooth ⊤) Φ hΦ hone Bnorm hBn hWb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨J,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ σ dec all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan hjratio hL hcoeff hP hcopTuple hPE θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  obtain ⟨Dpool,hfloor,hcover⟩:=InverseInitialResidualPool.exists_original_complete_pool
    q Z r bo cap Btree hZp (zero_le_one.trans hBtree) ((all\assigned).pi L)
    (fun t=>j*survivingProduct (all\assigned) t) j hP (fun t _=>dvd_mul_right j _) hPE
  exact henergy Z hZ Dpool hfloor all assigned hassigned hK L Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive χ hχ hperiod hout
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows
    j hj hspan (fun _=>1) (fun _=>2) 1 ((2:ℝ)^K) hjratio hL hcoeff
    (hFresh (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK) Woriginal hso)
    hP hcopTuple hPE hcover θ

end SevenEighths.InverseInitialResidualUniformEnergy

end

end OAI
end OAIOriginalModule2147

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationEligibility
Source SHA256: f9ea020aadfe572d7d5e02a7f1c85aa6f12930e62e83672c448efe80cd9ea322
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2148




namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentAmplificationEligibility
open CenteredMomentPrimePool CenteredMomentPrimeElements CenteredMomentAmplificationEnergy
open CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def exclusionIdeal (R s : Ideal O) (h : O) : Ideal O := R*s*Ideal.span {h}

def eligible (R s : Ideal O) (h p : O) : Prop := ¬Ideal.span {p}∣exclusionIdeal R s h

theorem exclusionIdeal_ne_zero (R s : Ideal O) (h : O)
    (hR : R ≠ 0) (hs : s ≠ 0) (hh : h ≠ 0) : exclusionIdeal R s h ≠ 0 :=
  mul_ne_zero (mul_ne_zero hR hs) (Ideal.span_singleton_eq_bot.not.mpr hh)

theorem exclusionIdeal_norm (R s : Ideal O) (h : O) (Z B b M : ℝ) (hZ : 0 < Z)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (Ideal.absNorm (exclusionIdeal R s h):ℝ) ≤ Z^(B+b+M) := by
  simp only [exclusionIdeal,map_mul,Nat.cast_mul]
  calc
    _ ≤ (Z^B*Z^b)*Z^M := mul_le_mul
      (mul_le_mul hR hs (Nat.cast_nonneg _) (Real.rpow_nonneg hZ.le _)) hh
      (Nat.cast_nonneg _) (by positivity)
    _ = _ := by rw [← Real.rpow_add hZ,← Real.rpow_add hZ]

theorem eligible_not_dvd_row (R s : Ideal O) (h p : O) (he : eligible R s h p) : ¬p∣h := by
  intro hd
  apply he
  exact (Ideal.dvd_iff_le.mpr (Ideal.span_singleton_le_span_singleton.mpr hd)).trans
    (dvd_mul_left (Ideal.span {h}) (R*s))

theorem eligible_coprime_divisor (R s : Ideal O) (h p : O)
    (hp : Prime (Ideal.span {p})) (he : eligible R s h p) : IsCoprime s (Ideal.span {p}) := by
  apply (HeckeInverseAmplification.prime_coprime_iff ⟨Ideal.span {p},hp⟩ s).mpr
  intro hd
  exact he (hd.trans ((dvd_mul_left s R).mul_right (Ideal.span {h})))

theorem uniform_eligible_pool (P : Finset (Ideal O))
    (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (h : O) (hh0 : h ≠ 0) (hh : (Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (P.card:ℝ)/2 ≤ ((elementPool P).filter (eligible R s h)).card := by
  unfold eligible
  convert eligible_element_card_half P hp hbad (exclusionIdeal R s h)
    (exclusionIdeal_ne_zero R s h hR0 hs0 hh0) Z ell (B+b+M) hZ hell hlower
    (exclusionIdeal_norm R s h Z B b M (zero_lt_one.trans hZ) hR hs hh) hsize

theorem actual_eligible_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (rows : Finset O) (hrows : ∀ h ∈ rows,h ≠ 0)
    (P : Finset (Ideal O)) (hp : ∀ Q ∈ P, Prime Q) (hbad : ∀ Q ∈ P,Q ∉ fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R ≠ 0) (hs0 : s ≠ 0)
    (Z ell B b M L : ℝ) (hZ : 1 < Z) (hell : 0 < ell)
    (hlower : ∀ Q ∈ P,Z^ell ≤ (Ideal.absNorm Q:ℝ))
    (hupper : ∀ Q ∈ P,(Ideal.absNorm Q:ℝ) ≤ Z^L)
    (hR : (Ideal.absNorm R:ℝ) ≤ Z^B) (hs : (Ideal.absNorm s:ℝ) ≤ Z^b)
    (hsize : 2*((B+b+M)/ell) ≤ P.card)
    (hrowNorm : ∀ h ∈ rows,(Ideal.absNorm (Ideal.span {h}):ℝ) ≤ Z^M) :
    (∑ h ∈ rows, ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c h‖^2) ≤
      (8/(P.card:ℝ))*
        (((M+6*L)/ell)*(∑ y ∈ (eligiblePairs rows (elementPool P) (eligible R s)).image outputRow,
          ‖CenteredMomentGaussEnergy.gaussPolynomial S a ha c y‖^2)+
          ∑ x ∈ eligiblePairs rows (elementPool P) (eligible R s),errorEnergy S a ha c x.1 x.2) := by
  have hpos : (0:ℝ)<P.card := by exact_mod_cast Finset.card_pos.mpr hP
  have hb := gauss_energy_amplification S a ha c rows (elementPool P) (eligible R s) hrows
    (fun p hpP => (elementPool_data P hp hbad p hpP).1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.1)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.2.2.2)
    (fun p hpP => (elementPool_data P hp hbad p hpP).2.2.1)
    (fun h hh p hpP he => eligible_not_dvd_row R s h p he)
    ((P.card:ℝ)/2) (by positivity)
    (fun h hh => uniform_eligible_pool P hp hbad R s hR0 hs0 Z ell B b M hZ hell hlower hR hs hsize h (hrows h hh) (hrowNorm h hh))
    Z ell M L hZ hell
    (fun p hpP => hlower (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    (fun p hpP => hupper (Ideal.span {p}) (elementPool_data P hp hbad p hpP).2.1)
    hrowNorm
  convert hb using 1 ; ring

end SevenEighths.CenteredMomentAmplificationEligibility

end

end OAI
end OAIOriginalModule2148

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationSlotGap
Source SHA256: 7aac61e5450a041016403affecf4acc96c533c3b0c87f08ed7b18c559220707d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2149


namespace OAI

noncomputable section
open scoped BigOperators Classical
open Filter
namespace SevenEighths.CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

theorem eventually_scale_gap (b η ell : ℝ) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop, 1 ≤ Z ∧ b*Z^η < Z^ell := by
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hgap)).eventually (eventually_gt_atTop b)
  filter_upwards [hg,eventually_ge_atTop (1:ℝ)] with Z hz hZ
  refine ⟨hZ,?_⟩
  have hZ0 : 0 < Z := zero_lt_one.trans_le hZ
  have hh := mul_lt_mul_of_pos_right hz (Real.rpow_pos_of_pos hZ0 η)
  rwa [← Real.rpow_add hZ0,sub_add_cancel] at hh

theorem amplifier_not_dvd_slot (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q)
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell)
    (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ)) (hQN : (Ideal.absNorm Q:ℝ) ≤ b*Z^η) :
    ¬P∣Q := by
  intro hd
  have he := (prime_dvd_prime_iff_eq hP hQ).mp hd
  subst Q
  linarith

theorem amplifier_not_dvd_slot_product {ι : Type*} (S : Finset ι) (v : ι → Ideal O)
    (P : Ideal O) (hP : Prime P) (hv : ∀ i ∈ S,Prime (v i))
    (Z ell η b : ℝ) (hgap : b*Z^η < Z^ell) (hPN : Z^ell ≤ (Ideal.absNorm P:ℝ))
    (hN : ∀ i ∈ S,(Ideal.absNorm (v i):ℝ) ≤ b*Z^η) :
    ¬P∣∏ i ∈ S,v i := by
  apply hP.not_dvd_finsetProd
  intro i hi
  exact amplifier_not_dvd_slot P (v i) hP (hv i hi) Z ell η b hgap hPN (hN i hi)

theorem live_profile_norm_bound (W : ℝ → ℂ) (b Z z η : ℝ) (I : Ideal O)
    (hb : 0 ≤ b) (hZ : 1 ≤ Z) (hz : z ≤ η)
    (hs : Function.support W ⊆ Set.Iic b)
    (hW : W ((Ideal.absNorm I:ℝ)/Z^z) ≠ 0) :
    (Ideal.absNorm I:ℝ) ≤ b*Z^η := by
  have hpow : 0 < Z^z := Real.rpow_pos_of_pos (zero_lt_one.trans_le hZ) _
  have h := (div_le_iff₀ hpow).mp (hs hW)
  exact h.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hz) hb)

theorem eventually_live_slot_exclusion (b η ell : ℝ) (hb : 0 ≤ b) (hgap : η < ell) :
    ∀ᶠ Z : ℝ in atTop,
      ∀ {ι : Type*} (S : Finset ι) (v : ι → Ideal O) (W : ι → ℝ → ℂ) (z : ι → ℝ),
      (∀ i ∈ S,Prime (v i)) → (∀ i ∈ S,z i ≤ η) →
      (∀ i ∈ S,Function.support (W i) ⊆ Set.Iic b) →
      (∀ i ∈ S,W i ((Ideal.absNorm (v i):ℝ)/Z^(z i)) ≠ 0) →
      ∀ P : Ideal O,Prime P → Z^ell ≤ (Ideal.absNorm P:ℝ) → ¬P∣∏ i ∈ S,v i := by
  filter_upwards [eventually_scale_gap b η ell hgap] with Z hZ
  intro ι S v W z hv hz hs hW P hP hPN
  exact amplifier_not_dvd_slot_product S v P hP hv Z ell η b hZ.2 hPN
    (fun i hi => live_profile_norm_bound (W i) b Z (z i) η (v i) hb hZ.1 (hz i hi) (hs i hi) (hW i hi))

end SevenEighths.CenteredMomentAmplificationSlotGap

end

end OAI
end OAIOriginalModule2149

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplificationChoice
Source SHA256: 9676fcf5ed9200b782ce1565ed9a3dddcba7779743ef55d081d6457d69018f5f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2150








namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open Filter

namespace SevenEighths.CenteredMomentFirstAmplificationChoice
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentSectorLocalization CenteredMomentPrimePool
open CenteredMomentPrimeElements CenteredMomentAmplificationEligibility
open CenteredMomentAmplificationEnergy CenteredMomentGaussEnergy
open CenteredMomentSourceRow CenteredMomentGaussNormalization
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationSlotGap
local notation "O" => ActualEisensteinCubic.O

abbrev ballProfile : 𝓢(ℝ,ℂ) := QuadraticInitialBound.sieveCutoff

theorem ballProfile_nonneg (x : ℝ) : 0 ≤ (ballProfile x).re := by
  simpa only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,Complex.ofReal_re]
    using (QuadraticInitialBound.sieveBump.nonneg (x:=x))

theorem ballProfile_le_one (x : ℝ) : (ballProfile x).re ≤ 1 := by
  simpa only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,Complex.ofReal_re]
    using (QuadraticInitialBound.sieveBump.le_one (x:=x))

theorem ballProfile_one (x : ℝ) (hx : 0≤x) (hx1 : x≤1) : ballProfile x=1 := by
  simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,
    QuadraticInitialBound.sieveBump_eq_one hx hx1,Complex.ofReal_one]

theorem ballProfile_majorizes (Y : ℝ) (hY : 0<Y) (z : O)
    (hz : normValue z≤Y) : 1≤(ballProfile (‖eisEmbedding z‖^2/Y)).re := by
  rw [←normValue_eq_embedding]
  have he := ballProfile_one (normValue z/Y)
    (div_nonneg (by unfold normValue; positivity) hY.le) ((div_le_one hY).mpr hz)
  rw [he]
  norm_num

def primeTest : ContDiffBump (3/4 : ℝ) where
  rIn := 1/16
  rOut := 1/8
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

theorem primeTest_support : Function.support primeTest ⊆ Set.Ioo (1/2) 1 := by
  intro x hx
  rw [primeTest.support_eq,Metric.mem_ball,Real.dist_eq] at hx
  change |x-3/4|<1/8 at hx
  have hh := abs_lt.mp hx
  constructor <;> linarith

theorem primeTest_tsupport : tsupport primeTest ⊆ Set.Ioi 0 := by
  intro x hx
  rw [primeTest.tsupport_eq,Metric.mem_closedBall,Real.dist_eq] at hx
  change |x-3/4|≤1/8 at hx
  have hh := abs_le.mp hx
  change 0<x
  linarith

theorem primeTest_ne_zero : (primeTest : ℝ→ℝ)≠0 := by
  have h : primeTest (3/4)=1 := primeTest.one_of_mem_closedBall
    (by simp [primeTest,Metric.mem_closedBall])
  intro hz
  have he := congrFun hz (3/4)
  change primeTest (3/4)=0 at he
  linarith

theorem eventually_log_card_power (c ell loss : ℝ)
    (hc : 0<c) (hell : 0<ell) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤c*Z^ell/Real.log (Z^ell) := by
  have hb := (isLittleO_log_rpow_atTop hloss).bound (div_pos hc hell)
  filter_upwards [hb,eventually_gt_atTop (1:ℝ)] with Z hbound hZ
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlog : 0<Real.log Z := Real.log_pos hZ
  have hpow : 0<Z^loss := Real.rpow_pos_of_pos hz _
  have hh : ell*Real.log Z≤c*Z^loss := by
    have hh' : Real.log Z≤(c/ell)*Z^loss := by
      simpa only [Real.norm_eq_abs,abs_of_pos hlog,abs_of_pos hpow] using hbound
    calc
      _ ≤ ell*((c/ell)*Z^loss) := mul_le_mul_of_nonneg_left hh' hell.le
      _ = _ := by field_simp
  rw [Real.log_rpow hz]
  apply (le_div_iff₀ (mul_pos hell hlog)).mpr
  calc
    _ ≤ Z^(ell-loss)*(c*Z^loss) :=
      mul_le_mul_of_nonneg_left hh (Real.rpow_nonneg hz.le _)
    _ = _ := by rw [mul_left_comm,←Real.rpow_add hz,sub_add_cancel]

section Pool
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

include hH

theorem eventually_actual_pool_card (Sbad : Finset (Ideal O))
    (ell loss : ℝ) (hell : 0<ell) (hloss : 0<loss) :
    ∀ᶠ Z : ℝ in atTop,
      Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
  obtain ⟨c,hc,hcard⟩ := eventually_primePool_card M H hH Sbad primeTest
    primeTest.contDiff primeTest.hasCompactSupport primeTest_tsupport
    (fun _ => primeTest.nonneg) primeTest_ne_zero (1/2) 1 1
    (by norm_num) (by norm_num) (by norm_num) primeTest_support (fun _ => primeTest.le_one)
  filter_upwards [(tendsto_rpow_atTop hell).eventually hcard,
    eventually_log_card_power c ell loss hc hell hloss] with Z hcard hpower
  exact hpower.trans hcard

theorem eventually_actual_pool (Sbad : Finset (Ideal O))
    (hbad : fixedBadPrimes⊆Sbad) (ell loss cap b eta : ℝ)
    (hell : 0<ell) (hloss : 0<loss) (hgap : eta<ell/2) :
    ∀ᶠ Z : ℝ in atTop,
      1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^ell)
      P.Nonempty ∧ Z^(ell-loss)≤(P.card:ℝ) ∧
      2*(cap/(ell/2))≤(P.card:ℝ) ∧ b*Z^eta<Z^(ell/2) ∧
      ∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(ell/2)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤Z^ell := by
  have he : 0<ell/2 := by linarith
  filter_upwards [eventually_actual_pool_card M H hH Sbad ell loss hell hloss,
    eventually_actual_pool_card M H hH Sbad ell (ell/2) hell he,
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop he).eventually (eventually_ge_atTop (2*(cap/(ell/2)))),
    eventually_scale_gap b eta (ell/2) hgap,eventually_gt_atTop (1:ℝ)]
    with Z hcard hlarge htwo hcap hslot hZ
  have hz : 0<Z := zero_lt_one.trans hZ
  have hlarge' : Z^(ell/2)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card := by
    simpa only [show ell-ell/2=ell/2 by ring] using hlarge
  have hp : (primePool M H Sbad (1/2) 1 (Z^ell)).Nonempty := by
    apply Finset.card_pos.mp
    exact_mod_cast (Real.rpow_pos_of_pos hz (ell/2)).trans_le hlarge'
  refine ⟨hZ,hp,hcard,hcap.trans hlarge',hslot.2,?_⟩
  intro Q hQ
  have hdata := primePool_data M H Sbad hbad (1/2) 1 (Z^ell) Q hQ
  have hn := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos hz ell) (Finset.mem_sdiff.mp hQ).1
  have hs : Z^ell=(Z^(ell/2))^2 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  refine ⟨hdata.1,hdata.2,?_,?_⟩
  · rw [hs] at hn
    nlinarith [sq_nonneg (Z^(ell/2)-2)]
  · simpa only [mul_one] using hn.2

omit hH in
theorem reciprocal_pool_bound (Sbad : Finset (Ideal O)) (ell loss Z : ℝ)
    (hZ : 0<Z)
    (hc : Z^(ell-loss)≤(primePool M H Sbad (1/2) 1 (Z^ell)).card) :
    ((primePool M H Sbad (1/2) 1 (Z^ell)).card:ℝ)⁻¹≤Z^(-ell+loss) := by
  have hp := Real.rpow_pos_of_pos hZ (ell-loss)
  have he := (inv_le_inv₀ (hp.trans_le hc) hp).mpr hc
  simpa only [←Real.rpow_neg hZ.le,show -(ell-loss)=-ell+loss by ring] using he

end Pool

def dyadRows (n : ℤ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈dyadicScale n⌉₊).filter
    (fun h => dyadicWeight n (normValue h)≠0)

@[simp] theorem mem_dyadRows (n : ℤ) (h : O) :
    h∈dyadRows n ↔ dyadicWeight n (normValue h)≠0 := by
  constructor
  · exact fun hh => (Finset.mem_filter.mp hh).2
  · intro hh
    refine Finset.mem_filter.mpr ⟨?_,hh⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    have hn := (dyadicWeight_support n hh).2.le.trans (Nat.le_ceil (dyadicScale n))
    unfold normValue at hn
    exact_mod_cast hn

theorem dyadRows_ne_zero (n : ℤ) (h : O) (hh : h∈dyadRows n) : h≠0 := by
  intro he
  have hn := (mem_dyadRows n h).mp hh
  subst h
  exact hn (by simpa [normValue] using dyadicWeight_zero_nonpos n 0 le_rfl)

theorem dyadRows_norm_lt (n : ℤ) (h : O) (hh : h∈dyadRows n) :
    normValue h<dyadicScale n :=
  (dyadicWeight_support n ((mem_dyadRows n h).mp hh)).2

theorem dyadRows_log_nonneg (Z : ℝ) (hZ : 1<Z) (n : ℤ)
    (hne : (dyadRows n).Nonempty) : 0≤Real.logb Z (dyadicScale n) := by
  obtain ⟨h,hh⟩ := hne
  exact Real.logb_nonneg hZ
    ((normValue_ge_one h (dyadRows_ne_zero n h hh)).trans (dyadRows_norm_lt n h hh).le)

theorem dyadic_energy_eq_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)=
      ∑ h∈dyadRows n,dyadicWeight n (normValue h)*‖f h‖^2 := by
  apply tsum_eq_sum
  intro h hh
  have hz : dyadicWeight n (normValue h)=0 := by
    by_contra hn
    exact hh ((mem_dyadRows n h).mpr hn)
  rw [hz,zero_mul]

theorem dyadic_energy_le_sum (n : ℤ) (f : O→ℂ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖f h‖^2)≤
      ∑ h∈dyadRows n,‖f h‖^2 := by
  rw [dyadic_energy_eq_sum]
  exact Finset.sum_le_sum (fun h _ =>
    mul_le_of_le_one_left (sq_nonneg _) (dyadicWeight_bounds n (normValue h)).2)

theorem dyadic_energy_empty (n : ℤ) (f : O→ℂ) (h : dyadRows n=∅) :
    (∑' z : O,dyadicWeight n (normValue z)*‖f z‖^2)=0 := by
  rw [dyadic_energy_eq_sum,h,Finset.sum_empty]

def mainGain (D0 c sigma : ℝ) : ℝ := max (D0-c) 0+2*sigma

def errorRemoval (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  (k:ℝ)*Real.logb Z (normValue p)

def errorMoving (p : O) (Z : ℝ) (k : ℕ) : ℝ :=
  if k=6 then 0 else Real.logb Z (normValue p)

def errorGain (D0 c sigma Z : ℝ) (p : O) (k : ℕ) : ℝ :=
  max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma

theorem mainGain_bounds (D0 c sigma : ℝ) (hs : 0≤sigma) :
    2*sigma≤mainGain D0 c sigma ∧ D0-c+sigma≤mainGain D0 c sigma := by
  have h0 := le_max_right (D0-c) (0:ℝ)
  have h1 := le_max_left (D0-c) (0:ℝ)
  unfold mainGain
  constructor <;> linarith

theorem errorGain_bounds (D0 c sigma Z : ℝ) (p : O) (k : ℕ) (hs : 0≤sigma) :
    sigma≤errorGain D0 c sigma Z p k ∧
    D0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤errorGain D0 c sigma Z p k ∧
    errorGain D0 c sigma Z p k≤
      max (D0-c-2*errorRemoval p Z k+errorMoving p Z k) 0+2*sigma := by
  have h0 := le_max_right (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  have h1 := le_max_left (D0-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)
  unfold errorGain
  constructor
  · linarith
  constructor <;> linarith

theorem error_lengths (p : O) (Z sigma : ℝ) (hs : 0≤sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7)
    (hl : 0≤Real.logb Z (normValue p))
    (hu : Real.logb Z (normValue p)≤sigma/3) :
    0≤errorMoving p Z k ∧ errorMoving p Z k≤errorRemoval p Z k ∧
      errorRemoval p Z k≤7*sigma/3 := by
  have hk1 : (1:ℝ)≤k := by rcases hk with rfl|rfl|rfl <;> norm_num
  have hk7 : (k:ℝ)≤7 := by rcases hk with rfl|rfl|rfl <;> norm_num
  unfold errorMoving errorRemoval
  split_ifs <;> refine ⟨?_,?_,?_⟩ <;> nlinarith

theorem dyadRows_norm_power (Z : ℝ) (hZ : 1<Z) (n : ℤ)
    (h : O) (hh : h∈dyadRows n) :
    normValue h≤Z^(Real.logb Z (dyadicScale n)) := by
  rw [Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (dyadicScale_pos n)]
  exact (dyadRows_norm_lt n h hh).le

theorem dyad_ball_majorant (Z : ℝ) (hZ : 1<Z) (n : ℤ) (g : ℝ) (hg : 0≤g)
    (h : O) (hh : h∈dyadRows n) :
    1≤(ballProfile (‖eisEmbedding h‖^2/Z^(Real.logb Z (dyadicScale n)+g))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact (dyadRows_norm_power Z hZ n h hh).trans
    (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

theorem amplified_ball_majorant (Z sigma D0 c : ℝ) (hZ : 1<Z) (hs : 0≤sigma)
    (n : ℤ) (h p : O) (hh : h∈dyadRows n)
    (hp : normValue p≤Z^(sigma/3)) :
    1≤(ballProfile (‖eisEmbedding (p^6*h)‖^2/
      Z^(Real.logb Z (dyadicScale n)+mainGain D0 c sigma))).re := by
  apply ballProfile_majorizes _ (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  have hb := outputRow_norm (h,p) Z (Real.logb Z (dyadicScale n)) (sigma/3)
    (zero_lt_one.trans hZ) (dyadRows_norm_power Z hZ n h hh) hp
  change normValue (p^6*h)≤Z^(Real.logb Z (dyadicScale n)+6*(sigma/3)) at hb
  exact hb.trans (Real.rpow_le_rpow_of_exponent_le hZ.le
    (by linarith [(mainGain_bounds D0 c sigma hs).1]))

theorem gaussEnergy_ball_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (Y : ℝ) (hY : 0<Y) :
    0≤(gaussEnergy S a ha c ballProfile Y).re := by
  have hs := CenteredMomentSmoothedWindowEnergy.gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  rw [←hs.tsum_eq]
  exact tsum_nonneg (fun h => mul_nonneg (sq_nonneg _) (ballProfile_nonneg _))

theorem errorEnergy_nonneg {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ) (h p : O) :
    0≤errorEnergy S a ha c h p := by
  unfold errorEnergy
  positivity

theorem eligible_error_sum {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (rows P : Finset O) (allow : O→O→Prop) :
    (∑x∈eligiblePairs rows P allow,errorEnergy S a ha c x.1 x.2)=
      ∑p∈P,∑h∈rows.filter (fun h => allow h p),errorEnergy S a ha c h p := by
  rw [←sum_eligiblePairs]
  simp only [Finset.sum_filter]
  exact Finset.sum_comm

theorem dyadic_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Z sigma D0 cLog : ℝ) (hZ : 1<Z) (hsigma : 0≤sigma) (n : ℤ) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (gaussEnergy S a ha c ballProfile
        (Z^(Real.logb Z (dyadicScale n)+(max (D0-cLog) 0+sigma)))).re := by
  apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans
  apply finite_energy_le_gaussEnergy S a ha c ballProfile _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _) (dyadRows n)
    (fun _ => ballProfile_nonneg _)
  exact dyad_ball_majorant Z hZ n _ (by positivity)

theorem dyadic_amplification_to_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (P : Finset (Ideal O)) (hp : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (hP : P.Nonempty) (R s : Ideal O) (hR0 : R≠0) (hs0 : s≠0)
    (Z sigma BR Bs Mmax D0 cLog : ℝ) (hZ : 1<Z) (hsigma : 0<sigma) (hM : 0≤Mmax)
    (hlower : ∀Q∈P,Z^(sigma/6)≤(Ideal.absNorm Q:ℝ))
    (hupper : ∀Q∈P,(Ideal.absNorm Q:ℝ)≤Z^(sigma/3))
    (hR : (Ideal.absNorm R:ℝ)≤Z^BR) (hs : (Ideal.absNorm s:ℝ)≤Z^Bs)
    (hsize : 2*((BR+Bs+Mmax)/(sigma/6))≤(P.card:ℝ))
    (n : ℤ) (hK : Real.logb Z (dyadicScale n)≤Mmax) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
      (8/(P.card:ℝ))*
        (((Mmax+2*sigma)/(sigma/6))*
          (gaussEnergy S a ha c ballProfile
            (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
          ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
            errorEnergy S a ha c h p) := by
  let K := Real.logb Z (dyadicScale n)
  have hY : 0<Z^(K+mainGain D0 cLog sigma) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  have henergy := gaussEnergy_ball_nonneg S a ha c _ hY
  by_cases hn : (dyadRows n).Nonempty
  · have hK0 := dyadRows_log_nonneg Z hZ n hn
    have hsize' : 2*((BR+Bs+K)/(sigma/6))≤(P.card:ℝ) := by
      apply le_trans _ hsize
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)
    have he := actual_eligible_amplification S a ha c (dyadRows n)
      (dyadRows_ne_zero n) P hp hbad hP R s hR0 hs0 Z (sigma/6) BR Bs K (sigma/3)
      hZ (by linarith) hlower hupper hR hs hsize' (dyadRows_norm_power Z hZ n)
    have hmajor : (∑y∈(eligiblePairs (dyadRows n) (elementPool P) (eligible R s)).image outputRow,
        ‖gaussPolynomial S a ha c y‖^2)≤
        (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re := by
      apply finite_energy_le_gaussEnergy S a ha c ballProfile _ hY _
        (fun _ => ballProfile_nonneg _) _
      intro y hy
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
      have hx' := Finset.mem_product.mp (Finset.mem_filter.mp hx).1
      have hpx := elementPool_data P hp hbad x.2 hx'.2
      exact amplified_ball_majorant Z sigma D0 cLog hZ hsigma.le n x.1 x.2 hx'.1
        (hupper _ hpx.2.1)
    apply (dyadic_energy_le_sum n (gaussPolynomial S a ha c)).trans (he.trans ?_)
    rw [eligible_error_sum]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply add_le_add _ le_rfl
    calc
      _ ≤ ((K+6*(sigma/3))/(sigma/6))*
          (gaussEnergy S a ha c ballProfile (Z^(K+mainGain D0 cLog sigma))).re :=
        mul_le_mul_of_nonneg_left hmajor (by dsimp [K];positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by dsimp [K];linarith) (by linarith)) henergy
  · rw [dyadic_energy_empty n _ (Finset.not_nonempty_iff_eq_empty.mp hn)]
    apply mul_nonneg (by positivity)
    apply add_nonneg
    · exact mul_nonneg (by positivity) henergy
    · exact Finset.sum_nonneg (fun p _ => Finset.sum_nonneg
        (fun h _ => errorEnergy_nonneg S a ha c h p))

theorem eventually_dyadic_amplification (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧ b*Z^eta<Z^(sigma/6) ∧
      (∀ Q∈P,Prime Q ∧ Q∉fixedBadPrimes ∧
        Z^(sigma/6)≤(Ideal.absNorm Q:ℝ) ∧ (Ideal.absNorm Q:ℝ)≤Z^(sigma/3)) ∧
      ∀ {α : Type*} (S : Finset α) (a : α→O) (ha : ∀i,Supported (Ideal.span {a i}))
        (c : α→ℂ) (R s : Ideal O), R≠0 → s≠0 →
        (Ideal.absNorm R:ℝ)≤Z^BR → (Ideal.absNorm s:ℝ)≤Z^Bs →
        ∀ (n : ℤ),Real.logb Z (dyadicScale n)≤Mmax → ∀ (D0 cLog : ℝ),
        (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha c h‖^2)≤
          (8/(P.card:ℝ))*
            (((Mmax+2*sigma)/(sigma/6))*
              (gaussEnergy S a ha c ballProfile
                (Z^(Real.logb Z (dyadicScale n)+mainGain D0 cLog sigma))).re+
              ∑p∈elementPool P,∑h∈(dyadRows n).filter (fun h => eligible R s h p),
                errorEnergy S a ha c h p) := by
  have he := eventually_actual_pool M H hH Sbad hbad (sigma/3) loss
    (BR+Bs+Mmax) b eta (by linarith) hloss (by linarith)
  simp only [show sigma/3/2=sigma/6 by ring] at he
  filter_upwards [he] with Z hz
  obtain ⟨hZ,hP,hcard,hsize,hslot,hdata⟩ := hz
  refine ⟨hZ,hP,hcard,hslot,hdata,?_⟩
  intro α S a ha c R s hR0 hs0 hR hs n hK D0 cLog
  exact dyadic_amplification_to_ball S a ha c _ (fun Q hQ => (hdata Q hQ).1)
    (fun Q hQ => (hdata Q hQ).2.1) hP R s hR0 hs0 Z sigma BR Bs Mmax D0 cLog
    hZ hsigma hM (fun Q hQ => (hdata Q hQ).2.2.1)
    (fun Q hQ => (hdata Q hQ).2.2.2) hR hs hsize n hK

open CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentOriginalChildEnergy
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentAmplificationLiveMask CenteredMomentHeckeExpansion
open ConcretePrimeRowBridge CanonicalRowCompletion RayFourExpansion
open HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeColumnWindow
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor

local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

structure OriginalData (ι : Type*) [Fintype ι] where
  S : (ι ⊕ Fin 2) → Finset (Ideal O)
  R : Ideal O
  s : Ideal O
  nu : ι → Ideal O → ℂ
  slot : ι → ℝ → ℂ
  lengths : ι → ℝ
  W₁ : ℝ → ℂ
  W₂ : ℝ → ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  B₁ : Ideal O
  B₂ : Ideal O

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def profile (D : OriginalData ι) : Tuple ι → ℂ :=
  profileCoefficient D.R D.nu D.slot D.lengths D.W₁ D.W₂
    D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ D.s

def columns (D : OriginalData ι) : Finset (Ideal O) :=
  finiteColumns (Fintype.piFinset D.S)

def beta (D : OriginalData ι) : Ideal O → ℂ :=
  finiteColumnCoefficient (Fintype.piFinset D.S) D.profile

def coefficient (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ)
    : supportedColumns D.columns → ℂ :=
  fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)

theorem coefficient_eq (D : OriginalData ι) (η : Character) (m : O) (t T : ℝ) :
    D.coefficient η m t T = fun I : supportedColumns D.columns =>
      (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I) := rfl

def childEnergy (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) : ℝ :=
  let C := (Ideal.span {p})^(n+1)
  (16*(n+2:ℝ)*localErrorCost p n) *
    ((∑ χ : RayCharacter,∑ B : actualAllocations D.S C,
      (sourceGaussEnergy
        (finiteColumns (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1))
        (finiteColumnCoefficient
          (liveBox D.S B (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
          (maskedLiveProfile B C D.R D.s D.nu D.slot D.lengths D.W₁ D.W₂
            D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂))
        (heightCoeff (τ χ) t) ballProfile K).re) /
      (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)))

theorem childEnergy_nonneg (D : OriginalData ι) (τ : RayCharacter → Character)
    (p : O) (n : ℕ) (t T K : ℝ) (hT : 0≤T) (hK : 0<K) :
    0≤D.childEnergy τ p n t T K := by
  apply mul_nonneg (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_nonneg _ (div_nonneg hT (by positivity))
  exact Finset.sum_nonneg (fun χ _ => Finset.sum_nonneg (fun B _ =>
    sourceGaussEnergy_nonneg _ _ _ ballProfile K hK (fun _ => ballProfile_nonneg _)))

end OriginalData

theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0<Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

def errorIndex (i : Fin 3) : ℕ := ![0,5,6] i

theorem errorIndex_cases (i : Fin 3) : errorIndex i=0 ∨ errorIndex i=5 ∨ errorIndex i=6 := by
  fin_cases i <;> simp [errorIndex]

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : Character) (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (D.coefficient η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6

theorem original_slot_coprime {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (Z sigma b eta : ℝ) (hZ : 1≤Z) (hb : 0≤b)
    (hgap : b*Z^eta<Z^(sigma/6))
    (z : ι → ℝ) (hz : ∀i,z i≤eta) (hlen : ∀i,D.lengths i=Z^(z i))
    (hsupp : ∀i,Function.support (D.slot i)⊆Set.Iic b)
    (hslot : ∀i,∀I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0)
    (hprime : ∀i,∀I∈D.S (Sum.inl i),Prime I)
    (Q : Ideal O) (hQ : Prime Q) (hQN : Z^(sigma/6)≤(Ideal.absNorm Q:ℝ)) :
    ∀i,∀I∈D.S (Sum.inl i),IsCoprime Q I := by
  intro i I hI
  have hW := hslot i I hI
  rw [hlen] at hW
  have hN := live_profile_norm_bound (D.slot i) b Z (z i) eta I hb hZ (hz i) (hsupp i) hW
  exact ((HeckeInverseAmplification.prime_coprime_iff ⟨Q,hQ⟩ I).mpr
    (amplifier_not_dvd_slot Q I hQ (hprime i I hI) Z (sigma/6) eta b hgap hQN hN)).symm

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)

namespace OriginalData
variable {ι : Type*} [Fintype ι]

def active (D : OriginalData ι) : OriginalData ι :=
  { D with S := fun i => match i with
    | Sum.inl j => (D.S i).filter (fun I => D.slot j ((Ideal.absNorm I:ℝ)/D.lengths j)≠0)
    | Sum.inr _ => D.S i }

theorem active_subset (D : OriginalData ι) (i : ι ⊕ Fin 2) : D.active.S i⊆D.S i := by
  cases i <;> simp only [active]
  · exact Finset.filter_subset _ _
  · exact fun _ h => h

theorem active_profile (D : OriginalData ι) : D.active.profile=D.profile := rfl

theorem active_slot (D : OriginalData ι) (i : ι) (I : Ideal O) (hI : I∈D.active.S (Sum.inl i)) :
    D.active.slot i ((Ideal.absNorm I:ℝ)/D.active.lengths i)≠0 :=
  (Finset.mem_filter.mp hI).2

theorem active_profile_zero (D : OriginalData ι) (v : Tuple ι)
    (hv : v∈Fintype.piFinset D.S) (hn : v∉Fintype.piFinset D.active.S) : D.profile v=0 := by
  have hn' : ¬∀i,v i∈D.active.S i := by simpa only [Fintype.mem_piFinset] using hn
  obtain ⟨i,hi⟩ := not_forall.mp hn'
  have hvi := Fintype.mem_piFinset.mp hv i
  cases i with
  | inr j => exact False.elim (hi hvi)
  | inl j =>
    have hz : D.slot j ((Ideal.absNorm (v (Sum.inl j)):ℝ)/D.lengths j)=0 := by
      by_contra hne
      exact hi (Finset.mem_filter.mpr ⟨hvi,hne⟩)
    have hp : (∏k,D.nu k (v (Sum.inl k))*D.slot k
        ((Ideal.absNorm (v (Sum.inl k)):ℝ)/D.lengths k))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      rw [hz,mul_zero]
    simp only [profile,profileCoefficient,hp,zero_mul]

theorem active_beta (D : OriginalData ι) : D.active.beta=D.beta := by
  funext I
  unfold beta finiteColumnCoefficient
  rw [active_profile]
  apply Finset.sum_subset (Finset.filter_subset_filter _
    (Fintype.piFinset_subset _ _ (D.active_subset)))
  intro v hv hn
  have hv' := Finset.mem_filter.mp hv
  apply D.active_profile_zero v hv'.1
  intro hm
  exact hn (Finset.mem_filter.mpr ⟨hm,hv'.2⟩)

theorem active_columns_subset (D : OriginalData ι) : D.active.columns⊆D.columns :=
  Finset.image_subset_image (Fintype.piFinset_subset _ _ D.active_subset)

theorem active_gaussPolynomial (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (h : O) :
    gaussPolynomial Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) h=
    gaussPolynomial Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) h := by
  unfold coefficient
  rw [D.active_beta]
  rw [CenteredMomentLiveDomain.source_gaussPolynomial D.active.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h,
    CenteredMomentLiveDomain.source_gaussPolynomial D.columns
    (fun I => (Real.sqrt T:ℂ)⁻¹*(D.beta I*rowWeight η m 1 1 t I)) h]
  apply Finset.sum_subset (Finset.filter_subset_filter _ D.active_columns_subset)
  intro I hI hn
  have hz : D.beta I=0 := by
    by_contra hne
    have hm := CenteredMomentLiveDomain.finite_column_mem
      (Fintype.piFinset D.active.S) D.active.profile I
      (by change D.active.beta I≠0;rw [D.active_beta];exact hne)
    exact hn (Finset.mem_filter.mpr ⟨hm,(Finset.mem_filter.mp hI).2⟩)
  rw [hz,zero_mul,mul_zero,zero_mul]

theorem active_gaussEnergy (D : OriginalData ι) (η : Character) (m : O)
    (t T : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    gaussEnergy Finset.univ (sourceGenerator D.active.columns)
      (sourceGenerator_supported D.active.columns) (D.active.coefficient η m t T) W K=
    gaussEnergy Finset.univ (sourceGenerator D.columns)
      (sourceGenerator_supported D.columns) (D.coefficient η m t T) W K := by
  unfold gaussEnergy
  simp_rw [D.active_gaussPolynomial]

end OriginalData

theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          rowConductorBound (childCharacter η χ) m 1 (p.val^(2*errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [D.active_gaussPolynomial,D.active_gaussEnergy] using he

open CenteredMomentFirstScale CenteredMomentCanonicalFirst CenteredMomentCompleteCommon
open CenteredMomentFirstCanonicalFamily CenteredMomentFirstExtractedLedger
open CenteredMomentDescentLedger CenteredMomentCommonSupport
open CenteredMomentFirstColumns CenteredMomentRankinRadical ActualEisensteinCubic

def nominalLog (I J E : Ideal O) (K X Z : ℝ) : ℝ :=
  Real.logb Z (firstNominalScale I J E K X)

theorem retained_nominal_choice (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n)
    (hne : (dyadRows n).Nonempty) :
    0≤Real.logb Z (dyadicScale n) ∧
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi ∧
    Real.logb Z ((commonPart J I).absNorm:ℝ)-frequencyLoss Z Csec xi≤
      Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
        Real.logb Z (dyadicScale n) := by
  have hs : Tsec≤Csec*Z^(nominalLog I J E K X Z) := by
    rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)]
    exact hsec
  have he := retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC hs n hn
  exact ⟨dyadRows_log_nonneg Z hZ n hne,he,by linarith⟩

theorem canonical_active_log_le (η τ : Character) (m : O) (I J : Ideal O)
    (E : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) E*activeConductor I J}) :
    0≤Real.logb Z (τ.modulus.absNorm:ℝ) ∧
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)≤
      Real.logb Z (τ.modulus.absNorm:ℝ) := by
  have hpos : 0<τ.modulus.absNorm := Nat.pos_of_ne_zero
    (Ideal.absNorm_eq_zero_iff.not.mpr τ.modulus_ne_bot)
  have hd : Ideal.span {activeConductor I J}∣τ.modulus := by
    rw [hmod,←Ideal.span_singleton_mul_span_singleton]
    exact (dvd_mul_left (Ideal.span {activeConductor I J}) _).trans (dvd_mul_left _ _)
  have hN : (Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)≤(τ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.le_of_dvd hpos (map_dvd Ideal.absNorm hd)
  refine ⟨Real.logb_nonneg hZ (by exact_mod_cast hpos),?_⟩
  exact Real.logb_le_logb_of_le hZ (active_norm_pos I J) hN

theorem retained_main_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi) (hsigma : 0≤sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hne : (dyadRows n).Nonempty) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale n)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*c/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R) (mainGain D0 c sigma) (sigma/3) := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn hne).2.2
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale n)
  have he := actual_extracted_first_saving I J hI hJ Z hZ
    D0 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0 (mainGain D0 c sigma) (sigma/3) sigma (frequencyLoss Z Csec xi)
    (by norm_num) hq.1 (by norm_num) hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD (by simp only [mainGain,c,mul_zero,sub_zero,add_zero];exact le_rfl)
    (by positivity) (by positivity)
  simpa only [add_zero] using he

theorem pool_prime_log_range (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (Z sigma : ℝ) (hZ : 1<Z) (p : O)
    (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
    0≤Real.logb Z (normValue p) ∧ Real.logb Z (normValue p)≤sigma/3 := by
  have hd := elementPool_data _
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).1)
    (fun Q hQ => (primePool_data M H Sbad hbad (1/2) 1 (Z^(sigma/3)) Q hQ).2) p hp
  have hb := PNT.AnnularPrimeMass.norm_bounds_of_mem_annularPrimeIdeals
    (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)≤1)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) (sigma/3)) (Finset.mem_sdiff.mp hd.2.1).1
  have hu : normValue p≤Z^(sigma/3) := by simpa only [normValue,mul_one] using hb.2
  refine ⟨Real.logb_nonneg hZ (normValue_ge_one p hd.1.ne_zero),?_⟩
  have hh := Real.logb_le_logb_of_le hZ (normValue_pos p hd.1.ne_zero) hu
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hh

theorem errorRemoval_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z) (k : ℕ) :
    Z^(errorRemoval p Z k)=(normValue p)^k := by
  unfold errorRemoval
  rw [mul_comm,Real.rpow_mul_natCast (zero_lt_one.trans hZ).le,
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)]

theorem errorMoving_power (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    Z^(2*errorMoving p Z (n+1))=normValue (p^(2*errorMovingExponent n)) := by
  have he := errorRemoval_power p hp Z hZ 2
  have hn2 : normValue (p^2)=(normValue p)^2 := by
    unfold normValue
    rw [←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]
  rcases hn with rfl|rfl|rfl
  · simpa only [errorMoving,errorMovingExponent,show ¬(0:ℕ)=5 by decide,
      show ¬(1:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he
  · norm_num [errorMoving,errorMovingExponent,normValue]
  · simpa only [errorMoving,errorMovingExponent,show ¬(6:ℕ)=5 by decide,
      show ¬(7:ℕ)=6 by decide,ite_false,Nat.reduceAdd,mul_one,hn2,errorRemoval,Nat.cast_ofNat] using he

theorem shortened_raw_exact (p : O) (hp : p≠0) (Z : ℝ) (hZ : 1<Z) (T : ℝ) (k : ℕ) :
    T/(Ideal.absNorm (Ideal.span {p}):ℝ)^k=T/Z^(errorRemoval p Z k) := by
  rw [errorRemoval_power p hp Z hZ]
  rfl

theorem eventually_frequency_loss (Csec xi : ℝ) (hC : 1≤Csec) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧ 0≤frequencyLoss Z Csec xi ∧ frequencyLoss Z Csec xi<xi := by
  filter_upwards [Real.tendsto_log_atTop.eventually
    (eventually_gt_atTop (2*Real.log (4*Csec)/xi)),eventually_gt_atTop (1:ℝ)] with Z hlog hZ
  have hh := (div_lt_iff₀ hxi).mp hlog
  have hr : Real.log (4*Csec)/Real.log Z<xi/2 := by
    apply (div_lt_iff₀ (Real.log_pos hZ)).mpr
    nlinarith
  refine ⟨hZ,frequencyLoss_nonneg Z Csec xi hZ hC hxi.le,?_⟩
  unfold frequencyLoss Real.logb
  linarith

theorem retained_error_first_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J) (hE : E≠0)
    (A : Finset (CommonIndex I J)) (K X Z Csec Tsec xi sigma : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi) (hsigma : 0≤sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (j : ℤ) (hj : Retained (frequencyRadius Tsec Z xi) j) (hne : (dyadRows j).Nonempty)
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let D0 := d+nominalLog I J E K X Z-Real.logb Z (dyadicScale j)
    let u := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    2*(c+errorRemoval p Z k)/3-3*sigma-5*frequencyLoss Z Csec xi/6≤
      firstSaving c D0 (errorRemoval p Z k) (Real.logb Z (τ.modulus.absNorm:ℝ))
        (errorMoving p Z k) (c+d-2*u-R) (errorGain D0 c sigma Z p k) 0 := by
  dsimp only
  let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
  let D0 := Real.logb Z ((commonPart J I).absNorm:ℝ)+nominalLog I J E K X Z-
    Real.logb Z (dyadicScale j)
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hD := (retained_nominal_choice I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec j hj hne).2.2
  have hl := pool_prime_log_range M H Sbad hbad Z sigma hZ p hp
  have hw := error_lengths p Z sigma hsigma k hk hl.1 hl.2
  have hg := (errorGain_bounds D0 c sigma Z p k hsigma).2.2
  exact actual_extracted_first_saving I J hI hJ Z hZ D0 (errorRemoval p Z k)
    (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p Z k)
    (errorGain D0 c sigma Z p k) 0 sigma (frequencyLoss Z Csec xi)
    (hw.1.trans hw.2.1) hq.1 hw.1 hsigma (frequencyLoss_nonneg Z Csec xi hZ hC hxi)
    hq.2 hD hg (by norm_num) hw.2.2

end SevenEighths.CenteredMomentFirstAmplificationChoice

end

end OAI
end OAIOriginalModule2150

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationChildInput
Source SHA256: edd8f01b93411c5fe9e91c3abbe63b190f884c7c4123cf200b4b29f552a64c8a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2151



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAmplificationChildInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRectangle CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform CenteredMomentRemainingBox
open CenteredMomentAmplificationAllocationCost CenteredMomentAmplificationAllocationScale
open CenteredMomentHeckeColumnWindow CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationShortening
open CenteredMomentAmplificationLiveMask CenteredMomentFirstAmplificationChoice
open CenteredMomentOriginalChildEnergy CenteredMomentSecondHeightFamily
open CenteredMomentFirstSectors CenteredMomentRectangle CenteredMomentExtraction
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

def original (s : Input ι) (R seed : Ideal O) : OriginalData ι where
  S := s.pools
  R := R
  s := seed
  nu := s.ν
  slot := s.W
  lengths := s.P
  W₁ := s.W₁
  W₂ := s.W₂
  X₁ := s.X₁
  X₂ := s.X₂
  Y₁ := s.Y₁
  Y₂ := s.Y₂
  B₁ := 1
  B₂ := 1

def volume (s : Input ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

theorem volume_pos (s : Input ι) : 0<volume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

theorem residual_ne (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (B : Ideal O) (hB : B≠0) : ∀I∈residualPool B hB S,I≠0 := by
  intro I hI
  exact right_ne_zero_of_mul (hS (B*I) ((mem_residualPool B hB S I).mp hI))

theorem residual_one (S : Finset (Ideal O)) (h : (1:Ideal O)≠0) :
    residualPool 1 h S=S := by
  ext I
  simp only [mem_residualPool,one_mul]

theorem residual_coverage (S : Finset (Ideal O)) (W : ℝ→ℂ)
    (B : Ideal O) (hB : B≠0) (X Y : ℝ) (h : PlainCoverage S W 1 X Y) :
    PlainCoverage (residualPool B hB S) W 1 (X/B.absNorm) (Y/B.absNorm) := by
  have he := plainCoverage_residualPool S W 1 B hB X Y h
  intro I hi
  apply he I
  simpa only [one_mul,map_mul,map_one,Nat.cast_mul,Nat.cast_one,mul_one,div_div_eq_mul_div,mul_comm] using hi

def child (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : Input (liveIndices B.val) where
  toData := {commonData s C R B with η:=τ,t:=t}
  plain₁ := residualPool (B.val (Sum.inr 0)) (alloc_ne s C B _) s.plain₁
  plain₂ := residualPool (B.val (Sum.inr 1)) (alloc_ne s C B _) s.plain₂
  plain₁_ne := residual_ne s.plain₁ s.plain₁_ne _ _
  plain₂_ne := residual_ne s.plain₂ s.plain₂_ne _ _
  coverage₁ := residual_coverage s.plain₁ s.W₁ _ _ _ _ s.coverage₁
  coverage₂ := residual_coverage s.plain₂ s.W₂ _ _ _ _ s.coverage₂
  ν_bound := fun i=>s.ν_bound i.val
  W_bound := fun i=>s.W_bound i.val
  lower := s.lower
  upper := s.upper
  lower_pos := s.lower_pos
  lower_le := fun i=>s.lower_le i.val
  upper_ge := fun i=>s.upper_ge i.val

@[simp] theorem child_modulus (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).m=fixedBadMask*idealGenerator (R*C) := rfl

@[simp] theorem child_character (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).η=τ := rfl

@[simp] theorem child_height (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) : (child s C R B τ t).t=t := rfl

theorem live_slot_one (B : Tuple ι) (i : liveIndices B) : B (Sum.inl i.val)=1 :=
  (Finset.mem_filter.mp i.property).2

theorem child_tuplePool (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1 =
      Fintype.piFinset (child s C R B τ t).pools := by
  ext v
  simp only [liveBox,Fintype.mem_piFinset]
  constructor <;> intro h j
  all_goals
    cases j with
    | inl i =>
      have hi:=h (Sum.inl i)
      simpa only [remainingSets,child,commonData,Input.pools,Sum.elim_inl,live_slot_one B.val i,
        residual_one] using hi
    | inr j =>
      fin_cases j
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 0)
      · simpa [remainingSets,child,commonData,Input.pools] using h (Sum.inr 1)

theorem child_profile (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂
      s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1 = (original (child s C R B τ t) (R*C) seed).profile := by
  funext v
  simp only [maskedLiveProfile,OriginalData.profile,original,child,commonData,
    profileCoefficient,one_mul,idealRectangle_extract]
  rfl

theorem prime_slot_one (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) (i : ι) : B.val (Sum.inl i)=1 :=
  allocation_slot_one s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B i

theorem prime_slots_live (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : liveIndices B.val=Finset.univ :=
  all_slots_live s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem prime_plain_norm_product (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) :
    (B.val (Sum.inr 0)).absNorm*(B.val (Sum.inr 1)).absNorm=Q.absNorm^k := by
  rw [←map_mul,allocation_plain_product s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B,map_pow]

theorem child_products (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    (child s (Q^k) R B τ t).X₁*(child s (Q^k) R B τ t).X₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k ∧
    (child s (Q^k) R B τ t).Y₁*(child s (Q^k) R B τ t).Y₂=
      (s.X₁*s.X₂)/(Q.absNorm:ℝ)^k := by
  have hnorm : ((B.val (Sum.inr 0)).absNorm:ℝ)*(B.val (Sum.inr 1)).absNorm=(Q.absNorm:ℝ)^k := by
    exact_mod_cast prime_plain_norm_product s Q hQ k hslot B
  change (s.X₁/_)*(s.X₂/_)=_ ∧ (s.Y₁/_)*(s.Y₂/_)=_
  rw [div_mul_div_comm,div_mul_div_comm,hnorm,s.same_product]
  exact ⟨rfl,rfl⟩

theorem child_volume (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I) (R : Ideal O)
    (B : actualAllocations s.pools (Q^k)) (τ : Character) (t : ℝ) :
    volume (child s (Q^k) R B τ t)=volume s/(Q.absNorm:ℝ)^k := by
  change (s.X₁/(B.val (Sum.inr 0)).absNorm)*(s.X₂/(B.val (Sum.inr 1)).absNorm)*
    (∏i:liveIndices B.val,s.P i.val)=_
  rw [div_mul_div_comm]
  exact remainingRaw_exact s.pools Q hQ k
    (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B s.P (s.X₁*s.X₂)

theorem child_slot_card (s : Input ι) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime Q I)
    (B : actualAllocations s.pools (Q^k)) : Fintype.card (liveIndices B.val)=Fintype.card ι :=
  live_slot_card s.pools Q hQ k (fun i I hI=>⟨(s.prime i I hI).ne_zero,hslot i I hI⟩) B

theorem child_slot_scale_ge_one (s : Input ι) (hs : ∀i,1≤s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    ∀i,1≤(child s C R B τ t).P i := fun i=>hs i.val

theorem child_plain_annuli (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t a₁ a₂ b₁ b₂ : ℝ)
    (h₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (h₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) :
    Function.support (child s C R B τ t).W₁⊆Set.Icc a₁ b₁ ∧
    Function.support (child s C R B τ t).W₂⊆Set.Icc a₂ b₂ := ⟨h₁,h₂⟩

theorem child_columns (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)=
      (original (child s C R B τ t) (R*C) seed).columns ∧
    finiteColumnCoefficient
      (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
      (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1)=
      (original (child s C R B τ t) (R*C) seed).beta := by
  dsimp only [OriginalData.columns, OriginalData.beta, original]
  rw [child_tuplePool s C R B τ t,child_profile s C R seed B τ t]
  dsimp only [original]
  constructor
  · apply congrArg finiteColumns
    ext v
    simp only [Fintype.mem_piFinset]
  · apply congrArg (fun S => finiteColumnCoefficient S _)
    ext v
    simp only [Fintype.mem_piFinset]

theorem child_gauss_source (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy
      (finiteColumns (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1))
      (finiteColumnCoefficient
        (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
        (maskedLiveProfile B C R seed s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1))
      (heightCoeff τ t) W K=
    sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta
      (heightCoeff (child s C R B τ t).η (child s C R B τ t).t) W K := by
  obtain ⟨hcols,hcoeff⟩ := child_columns s C R seed B τ t
  rw [hcols,hcoeff]
  rfl

def normalizedGaussSource (s : Input ι) (R seed : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (original s R seed).columns (original s R seed).beta
    (heightCoeff s.η s.t) W K).re / volume s

def childNormalizedGaussSource (s : Input ι) (C R seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  normalizedGaussSource (child s C R B τ t) (R*C) seed W K

theorem original_childEnergy_eq_inputs (s : Input ι) (R seed : Ideal O)
    (τ : RayCharacter→Character) (p : O) (hp : p≠0)
    (hslot : ∀i,∀I∈s.slots i,IsCoprime (Ideal.span {p}) I)
    (n : ℕ) (t K : ℝ) :
    (original s R seed).childEnergy τ p n t (volume s) K=
      (16*(n+2:ℝ)*localErrorCost p n)*
        ∑χ:RayCharacter,∑B:actualAllocations s.pools ((Ideal.span {p})^(n+1)),
          childNormalizedGaussSource s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K := by
  have hQ : (Ideal.span {p}:Ideal O)≠0 := Ideal.span_singleton_eq_bot.not.mpr hp
  unfold OriginalData.childEnergy
  simp only [original,Finset.sum_div]
  apply congrArg (fun x : ℝ => (16*(n+2:ℝ)*localErrorCost p n)*x)
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro B hB
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_volume s (Ideal.span {p}) hQ (n+1) hslot R B (τ χ) t,
    child_gauss_source s ((Ideal.span {p})^(n+1)) R seed B (τ χ) t ballProfile K]

end SevenEighths.CenteredMomentAmplificationChildInput

end

end OAI
end OAIOriginalModule2151

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationChildSourceCaps
Source SHA256: bb931376cdfe356e5cbb7d604dc9d85ae2943faa5cbca5b635b13ab3a22dc308
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2152




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplificationChildSourceCaps
open ConcretePrimeRowBridge HeckeFamily CanonicalQuadraticSieve CenteredMomentCommonRadialData
open CenteredMomentFirstAmplificationChoice CenteredMomentHeckeColumnWindow
open CenteredMomentCommonAllocationSum CenteredMomentCommonRawScale
open CenteredMomentCommonProfile CenteredMomentSourceLiveColumn CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationChildInput CenteredMomentOriginalCommonHarmonic
open CenteredMomentSourceMass CenteredMomentSecondHeightFamily CenteredMomentSectorLocalization
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _

def geometry (N : ℕ) (b b₁ b₂ : ℝ) : ℝ := b^(2*N)*b₁*b₂

lemma geometry_ge_one (N : ℕ) (b b₁ b₂ : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) : 1≤geometry N b b₁ b₂ := by
  unfold geometry
  have hp : 1≤b^(2*N):=one_le_pow₀ hb
  have hp1 : 1≤b^(2*N)*b₁ := by nlinarith
  nlinarith

lemma norm_ge_one (I : Ideal O) (hI : I≠0) : (1:ℝ)≤I.absNorm := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)

lemma allocation_product (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) :
    finiteTupleProduct B.val=C := (Finset.mem_filter.mp B.property).2

lemma allocation_ne (s : Input ι) (C : Ideal O) (B : actualAllocations s.pools C) : C≠0 := by
  rw [←allocation_product s C B]
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>alloc_ne s C B i)

theorem common_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)=
      CenteredMomentAmplificationChildInput.volume s/rawReduction B.val s.P := by
  have hh:=raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  change _ = CenteredMomentAmplificationChildInput.volume s at hh
  rw [←hh]
  congr 1
  unfold CenteredMomentAmplificationChildInput.volume child commonData remainingRaw plainNorm
  dsimp only
  ring

lemma live_card_le (B : Tuple ι) : Fintype.card (liveIndices B)≤Fintype.card ι := by
  simpa only [Fintype.card_coe] using (Finset.card_le_univ (liveIndices B))

theorem common_volume_le (N : ℕ) (b : ℝ) (hb : 1≤b) (s : Input ι)
    (hcard : Fintype.card ι≤N) (hs : s.upper≤b)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0) :
    CenteredMomentAmplificationChildInput.volume (child s C R B τ t)≤
      b^N*CenteredMomentAmplificationChildInput.volume s/(C.absNorm:ℝ) := by
  have hc:=norm_ge_one C (allocation_ne s C B)
  have hr:=rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  have hn:=(actual_reduction_norm B.val (alloc_ne s C B) C R (allocation_product s C B)
    s.ν s.W s.P s.P_pos s.lower b s.lower_pos
    (fun i x hx=>⟨(s.slot_support i hx).1,((s.slot_support i hx).2).trans hs⟩) hne).2
  rw [max_eq_right hb] at hn
  have hn':(C.absNorm:ℝ)≤b^N*rawReduction B.val s.P := hn.trans
    (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb hcard) hr.le)
  rw [common_volume]
  apply (div_le_div_iff₀ hr (zero_lt_one.trans_le hc)).mpr
  nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]

theorem frozen_zero (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (hz : frozenCoefficient B.val C R s.ν s.W s.P=0) (f : O→ℂ) (z : O) :
    frozenCoefficient B.val C R s.ν s.W s.P*f z=0 := by rw [hz,zero_mul]

theorem radius_le (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 0≤b₁) (_h₂ : 0≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (hhi : ∀i,0≤s.hi i) (hhib : ∀i,s.hi i≤b)
    (hs₁ : 0≤s.b₁) (hs₂ : 0≤s.b₂) (hb₁ : s.b₁≤b₁) (hb₂ : s.b₂≤b₂) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧ CenteredMomentOriginalCommonHarmonic.sourceRadius s≤(b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s := by
  have hp:0≤∏i,s.hi i:=Finset.prod_nonneg (fun i _=>hhi i)
  have hp':(∏i,s.hi i)≤b^N := by
    calc
      _ ≤ ∏i:ι,b := Finset.prod_le_prod₀ (fun i _=>hhi i) (fun i _=>hhib i)
      _ = b^Fintype.card ι := by simp
      _ ≤ b^N := pow_le_pow_right₀ hb hc
  have hpp:=mul_le_mul (mul_le_mul hp' hb₁ hs₁ (pow_nonneg (zero_le_one.trans hb) _)) hb₂ hs₂
    (mul_nonneg (pow_nonneg (zero_le_one.trans hb) _) h₁)
  change 0≤_ ∧ _≤_
  have he:CenteredMomentOriginalCommonHarmonic.sourceRadius s=((∏i,s.hi i)*s.b₁*s.b₂)*CenteredMomentAmplificationChildInput.volume s := by
    unfold CenteredMomentOriginalCommonHarmonic.sourceRadius CenteredMomentAmplificationChildInput.volume; ring
  rw [he]
  exact ⟨mul_nonneg (mul_nonneg (mul_nonneg hp hs₁) hs₂)
    (CenteredMomentAmplificationChildInput.volume_pos s).le,
    mul_le_mul_of_nonneg_right hpp (CenteredMomentAmplificationChildInput.volume_pos s).le⟩

theorem original_beta (s : Input ι) (R seed : Ideal O) :
    (original s R seed).beta=coefficient s R seed := rfl

theorem child_column_norm (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hne : (original (child s C R B τ t) (R*C) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤CenteredMomentOriginalCommonHarmonic.sourceRadius (child s C R B τ t) := by
  rw [original_beta] at hne
  have hn:=original_column_norm (child s C R B τ t) (R*C) seed I hz₁ hz₂ hne
  exact ⟨hn.1,original_column_mask _ _ _ I hne,hn.2⟩

def nominal (s : Input ι) (K : ℝ) : ℝ := CenteredMomentAmplificationChildInput.volume s^2/K

lemma nominal_pos (s : Input ι) (K : ℝ) (hK : 0<K) : 0<nominal s K :=
  div_pos (sq_pos_of_pos (CenteredMomentAmplificationChildInput.volume_pos s)) hK

lemma nominal_lower (s : Input ι) (K : ℝ) :
    (CenteredMomentAmplificationChildInput.volume s)^2/K≤nominal s K := le_rfl

lemma nominal_upper (s : Input ι) (K G H : ℝ) (hK : 0<K) (_hG : 0≤G) (_hH : 0≤H)
    (h : CenteredMomentAmplificationChildInput.volume s≤G*H) :
    nominal s K≤G^2*H^2/K := by
  unfold nominal
  exact div_le_div_of_nonneg_right (by nlinarith [CenteredMomentAmplificationChildInput.volume_pos s]) hK.le

def Endpoints (b b₁ b₂ : ℝ) (s : Input ι) : Prop :=
  s.upper≤b ∧ (∀i,0≤s.hi i) ∧ 0≤s.b₁ ∧ s.b₁≤b₁ ∧ 0≤s.b₂ ∧ s.b₂≤b₂

lemma endpoints_child (b b₁ b₂ : ℝ) (s : Input ι) (h : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    Endpoints b b₁ b₂ (child s C R B τ t) :=
  ⟨h.1,fun i=>h.2.1 i.val,h.2.2⟩

lemma radius_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s) :
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius s ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius s≤
      (b^N*b₁*b₂)*CenteredMomentAmplificationChildInput.volume s :=
  radius_le N b b₁ b₂ hb (zero_le_one.trans h₁) (zero_le_one.trans h₂) s hc he.2.1
    (fun i=>(s.upper_ge i).trans he.1) he.2.2.1 he.2.2.2.2.1 he.2.2.2.1 he.2.2.2.2.2

def twiceChild (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :=
  child (child s C R B τ t) (Q^k) (R*C) Bp υ v

theorem twiceChild_data (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (k : ℕ)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    (twiceChild s C R B τ t Q k Bp υ v).η=υ ∧
    (twiceChild s C R B τ t Q k Bp υ v).t=v ∧
    (twiceChild s C R B τ t Q k Bp υ v).m=
      fixedBadMask*idealGenerator ((R*C)*(Q^k)) := ⟨rfl,rfl,rfl⟩

theorem twice_volume (s : Input ι) (C R : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    CenteredMomentAmplificationChildInput.volume (twiceChild s C R B τ t Q k Bp υ v)=
      CenteredMomentAmplificationChildInput.volume s/(rawReduction B.val s.P*(Q.absNorm:ℝ)^k) := by
  rw [twiceChild,child_volume _ Q hQ k hslot,common_volume,div_div]

theorem twice_caps (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    let H:=CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k);
    0<H ∧ 0≤CenteredMomentOriginalCommonHarmonic.sourceRadius d ∧
    CenteredMomentAmplificationChildInput.volume d≤geometry N b b₁ b₂*H ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius d≤geometry N b b₁ b₂*H := by
  dsimp only
  have hC:=norm_ge_one C (allocation_ne s C B)
  have hNp:0<(Q.absNorm:ℝ)^k:=pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k
  have hH:0<CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k):=
    div_pos (CenteredMomentAmplificationChildInput.volume_pos s)
      (mul_pos (zero_lt_one.trans_le hC) hNp)
  have hv:CenteredMomentAmplificationChildInput.volume (twiceChild s C R B τ t Q k Bp υ v)≤
      b^N*(CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
    rw [twiceChild,child_volume _ Q hQ k hslot]
    exact (div_le_div_of_nonneg_right (common_volume_le N b hb s hc he.1 C R B τ t hne) hNp.le).trans_eq (by ring)
  have hc1:= (live_card_le B.val).trans hc
  have hc2:= (live_card_le Bp.val).trans hc1
  have hep:=endpoints_child b b₁ b₂ _ (endpoints_child b b₁ b₂ s he C R B τ t) (Q^k) (R*C) Bp υ v
  have hr:=radius_bound N b b₁ b₂ hb h₁ h₂ _ hc2 hep
  have hbf:0≤b^N*b₁*b₂:=by positivity
  have hpow: b^N≤geometry N b b₁ b₂ := by
    have hp:1≤b^N:=one_le_pow₀ hb
    unfold geometry
    rw [show 2*N=N+N by omega,pow_add]
    have hh:1≤b₁*b₂:=by nlinarith
    nlinarith
  refine ⟨hH,hr.1,hv.trans (mul_le_mul_of_nonneg_right hpow hH.le),?_⟩
  exact hr.2.trans ((mul_le_mul_of_nonneg_left hv hbf).trans_eq (by
    unfold geometry; rw [show 2*N=N+N by omega,pow_add];ring))

theorem twice_column (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    I≠0 ∧ seed∣I ∧ (I.absNorm:ℝ)≤geometry N b b₁ b₂*
      (CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)) := by
  have hi:=child_column_norm (child s C R B τ t) (Q^k) (R*C) seed Bp υ v hz₁ hz₂ I hI
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨hi.1,hi.2.1,hi.2.2.trans hcap.2.2.2⟩

theorem twice_nominal (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v K : ℝ) (hK : 0<K) :
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    0<nominal d K ∧ CenteredMomentAmplificationChildInput.volume d^2/K=nominal d K ∧
    nominal d K≤(geometry N b b₁ b₂)^2*
      (CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k))^2/K := by
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  exact ⟨nominal_pos _ K hK,rfl,nominal_upper _ K _ _ hK
    (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂)) hcap.1.le hcap.2.2.1⟩

theorem puncture_norm (R C Q : Ideal O) (k : ℕ) :
    (((R*C)*(Q^k)).absNorm:ℝ)=(R.absNorm:ℝ)*(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
  simp only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]

theorem live_puncture_bound (N : ℕ) (b b₁ b₂ : ℝ) (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂)
    (s : Input ι) (hc : Fintype.card ι≤N) (he : Endpoints b b₁ b₂ s)
    (C R seed : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (hne : frozenCoefficient B.val C R s.ν s.W s.P≠0)
    (Q : Ideal O) (hQ : Q≠0) (k : ℕ)
    (hslot : ∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I)
    (Bp : actualAllocations (child s C R B τ t).pools (Q^k)) (υ : Character) (v : ℝ)
    (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0) (I : Ideal O)
    (hI : (original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) :
    (C.absNorm:ℝ)*(Q.absNorm:ℝ)^k≤geometry N b b₁ b₂*CenteredMomentAmplificationChildInput.volume s ∧
    (((R*C)*(Q^k)).absNorm:ℝ)≤(R.absNorm:ℝ)*geometry N b b₁ b₂*CenteredMomentAmplificationChildInput.volume s := by
  have hi:=twice_column N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI
  have hh:1≤geometry N b b₁ b₂*(CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)):=
    (norm_ge_one I hi.1).trans hi.2.2
  have hd:0<(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k:=mul_pos
    (zero_lt_one.trans_le (norm_ge_one C (allocation_ne s C B)))
    (pow_pos (zero_lt_one.trans_le (norm_ge_one Q hQ)) k)
  rw [←mul_div_assoc] at hh
  have hn:=(le_div_iff₀ hd).mp hh
  simp only [one_mul] at hn
  refine ⟨hn,?_⟩
  rw [puncture_norm]
  nlinarith [mul_le_mul_of_nonneg_left hn (show (0:ℝ)≤R.absNorm by positivity)]

theorem eventual_geometry (G ε : ℝ) (hG : 1≤G) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ G≤Z^ε ∧ G^2≤Z^ε := by
  have hh:=(Filter.tendsto_atTop.1 (tendsto_rpow_atTop hε)) (G^2)
  filter_upwards [eventually_gt_atTop (1:ℝ),hh] with Z hZ hpow
  exact ⟨hZ,(by nlinarith : G≤G^2).trans hpow,hpow⟩

theorem polynomial_caps (G V X H K Z A D ε ξ : ℝ)
    (hG : 1≤G) (hZ : 1<Z) (hGp : G^2≤Z^ε)
    (hV : 0<V) (hX : 0<X) (_hH : 0≤H) (hK : 0<K)
    (hXV : X≤G*V) (hHV : H≤G*V) (hVp : V≤Z^A) (hKp : K⁻¹≤Z^D) :
    X≤Z^(A+ε) ∧ H≤Z^(A+ε) ∧ X^2/K≤Z^(2*A+D+ε) ∧
    0<frequencyRadius (X^2/K) Z ξ ∧
    frequencyRadius (X^2/K) Z ξ≤Z^(2*A+D+ε+ξ/2) := by
  have hz:=hZ.trans' zero_lt_one
  have hgp:G≤Z^ε := (by nlinarith : G≤G^2).trans hGp
  have hvpow:0<Z^A:=Real.rpow_pos_of_pos hz A
  have hrpow:0<Z^ε:=Real.rpow_pos_of_pos hz ε
  have hcap:G*V≤Z^(A+ε) := by
    rw [Real.rpow_add hz]
    nlinarith [mul_le_mul hgp hVp hV.le hrpow.le]
  have hsq:X^2≤G^2*(Z^A)^2 := by nlinarith [mul_le_mul_of_nonneg_left hVp (by linarith : 0≤G)]
  have ht:X^2/K≤Z^(2*A+D+ε) := by
    have hm:=mul_le_mul hsq hKp (inv_nonneg.mpr hK.le)
      (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    have hg:=mul_le_mul_of_nonneg_right hGp (mul_nonneg (sq_nonneg (Z^A)) (Real.rpow_nonneg hz.le D))
    calc
      _ ≤ (G^2*(Z^A)^2)*Z^D := by simpa only [div_eq_mul_inv] using hm
      _ ≤ (Z^ε*(Z^A)^2)*Z^D := by nlinarith [hg]
      _ = _ := by rw [pow_two,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz];congr 1;ring
  refine ⟨hXV.trans hcap,hHV.trans hcap,ht,?_,?_⟩
  · exact mul_pos (div_pos (sq_pos_of_pos hX) hK) (Real.rpow_pos_of_pos hz _)
  · unfold frequencyRadius
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hz.le _)

theorem eventual_twice_caps (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v K A D ξ:ℝ),
    0<K → CenteredMomentAmplificationChildInput.volume s≤Z^A → K⁻¹≤Z^D →
    let d:=twiceChild s C R B τ t Q k Bp υ v;
    CenteredMomentAmplificationChildInput.volume d≤Z^(A+ε) ∧
    0≤CenteredMomentOriginalCommonHarmonic.sourceRadius d ∧
    CenteredMomentOriginalCommonHarmonic.sourceRadius d≤Z^(A+ε) ∧
    0<nominal d K ∧ nominal d K≤Z^(2*A+D+ε) ∧
    0<frequencyRadius (nominal d K) Z ξ ∧
    frequencyRadius (nominal d K) Z ξ≤Z^(2*A+D+ε+ξ/2) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R B τ t hne Q hQ k hslot Bp υ v K A D ξ hK hVp hKp
  have hcap:=twice_caps N b b₁ b₂ hb h₁ h₂ s hc he C R B τ t hne Q hQ k hslot Bp υ v
  have hd:1≤(C.absNorm:ℝ)*(Q.absNorm:ℝ)^k := by
    have hc:=norm_ge_one C (allocation_ne s C B)
    have hq:1≤(Q.absNorm:ℝ)^k:=one_le_pow₀ (norm_ge_one Q hQ)
    nlinarith
  have hH:CenteredMomentAmplificationChildInput.volume s/((C.absNorm:ℝ)*(Q.absNorm:ℝ)^k)≤
      CenteredMomentAmplificationChildInput.volume s :=
    div_le_self (CenteredMomentAmplificationChildInput.volume_pos s).le hd
  have hm:=mul_le_mul_of_nonneg_left hH (zero_le_one.trans (geometry_ge_one N b b₁ b₂ hb h₁ h₂))
  have hh:=polynomial_caps (geometry N b b₁ b₂) _ _ _ K Z A D ε ξ
    (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hZ.1 hZ.2.2
    (CenteredMomentAmplificationChildInput.volume_pos s)
    (CenteredMomentAmplificationChildInput.volume_pos _) hcap.2.1 hK
    (hcap.2.2.1.trans hm) (hcap.2.2.2.trans hm) hVp hKp
  exact ⟨hh.1,hcap.2.1,hh.2.1,nominal_pos _ K hK,hh.2.2⟩

theorem plain_zero (s : Input ι) (a₁ a₂ b₁ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support s.W₁⊆Set.Icc a₁ b₁)
    (hs₂ : Function.support s.W₂⊆Set.Icc a₂ b₂) : s.W₁ 0=0 ∧ s.W₂ 0=0 := by
  constructor
  · by_contra hn; exact (not_le_of_gt ha₁) (hs₁ hn).1
  · by_contra hn; exact (not_le_of_gt ha₂) (hs₂ hn).1

theorem twice_slots_ge_one (s : Input ι) (hs : ∀i,1≤s.P i)
    (C R : Ideal O) (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (Q : Ideal O) (k : ℕ) (Bp : actualAllocations (child s C R B τ t).pools (Q^k))
    (υ : Character) (v : ℝ) : ∀i,1≤(twiceChild s C R B τ t Q k Bp υ v).P i :=
  fun i=>hs i.val.val

theorem child_localized (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K Z ξ : ℝ) (hK : 0<K) :
    let d:=child s C R B τ t;
    let S:=(original d (R*C) seed).columns;
    let β:=(original d (R*C) seed).beta;
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy S β (heightCoeff τ t) W K/
      (CenteredMomentAmplificationChildInput.volume d:ℂ)=
      (((K:ℂ)*EisensteinSchwartzPoisson.paperRadialFourier W 0)*
          CenteredMomentSourceSecondZeroEnergy.sourceSecondZero S β τ t+
        CenteredMomentSecondLocalization.secondRetainedEnergy τ t S β W K (nominal d K) Z ξ+
        CenteredMomentSupportedTailAggregate.secondDiscardedEnergy τ t S β W K (nominal d K) Z ξ)/
      (CenteredMomentAmplificationChildInput.volume d:ℂ) := by
  dsimp only
  rw [CenteredMomentSecondLocalization.sourceGaussEnergy_localized τ t _ _ W K _ Z ξ hK]

theorem child_source_zero (s : Input ι) (C R seed : Ideal O) (B : actualAllocations s.pools C)
    (τ : Character) (t : ℝ) (hz₁ : s.W₁ 0=0) (hz₂ : s.W₂ 0=0)
    (hsmall : CenteredMomentOriginalCommonHarmonic.sourceRadius (child s C R B τ t)<1)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    CenteredMomentOriginalChildEnergy.sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (original (child s C R B τ t) (R*C) seed).beta (heightCoeff τ t) W K=0 := by
  have hz (I:Ideal O):(original (child s C R B τ t) (R*C) seed).beta I=0 := by
    by_contra hn
    have hh:=child_column_norm s C R seed B τ t hz₁ hz₂ I hn
    exact (not_le_of_gt hsmall) ((norm_ge_one I hh.1).trans hh.2.2)
  simp [CenteredMomentOriginalChildEnergy.sourceGaussEnergy,CenteredMomentGaussEnergy.gaussEnergy,
    CenteredMomentGaussEnergy.gaussPolynomial,hz]

theorem eventual_live_puncture (N : ℕ) (b b₁ b₂ ε : ℝ)
    (hb : 1≤b) (h₁ : 1≤b₁) (h₂ : 1≤b₂) (hε : 0<ε) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀{ι:Type*}[Fintype ι],∀(s:Input ι),
    Fintype.card ι≤N → Endpoints b b₁ b₂ s →
    ∀(C R seed:Ideal O)(B:actualAllocations s.pools C)(τ:Character)(t:ℝ),
    frozenCoefficient B.val C R s.ν s.W s.P≠0 →
    ∀(Q:Ideal O),Q≠0 → ∀k:ℕ,
    (∀i,∀I∈(child s C R B τ t).slots i,IsCoprime Q I) →
    ∀(Bp:actualAllocations (child s C R B τ t).pools (Q^k))(υ:Character)(v A P:ℝ),
    s.W₁ 0=0 → s.W₂ 0=0 → CenteredMomentAmplificationChildInput.volume s≤Z^A →
    (R.absNorm:ℝ)≤Z^P →
    (∃I:Ideal O,(original (twiceChild s C R B τ t Q k Bp υ v) ((R*C)*(Q^k)) seed).beta I≠0) →
    (((R*C)*(Q^k)).absNorm:ℝ)≤Z^(A+P+ε) := by
  filter_upwards [eventual_geometry (geometry N b b₁ b₂) ε (geometry_ge_one N b b₁ b₂ hb h₁ h₂) hε] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v A P hz₁ hz₂ hVp hRp ⟨I,hI⟩
  have hn:=(live_puncture_bound N b b₁ b₂ hb h₁ h₂ s hc he C R seed B τ t hne Q hQ k hslot Bp υ v hz₁ hz₂ I hI).2
  have hg:=geometry_ge_one N b b₁ b₂ hb h₁ h₂
  have hm:=mul_le_mul (mul_le_mul hRp hZ.2.1 (zero_le_one.trans hg)
    (Real.rpow_nonneg (by linarith : 0≤Z) P)) hVp
    (CenteredMomentAmplificationChildInput.volume_pos s).le
    (mul_nonneg (Real.rpow_nonneg (by linarith : 0≤Z) P) (Real.rpow_nonneg (by linarith : 0≤Z) ε))
  apply hn.trans (hm.trans_eq ?_)
  rw [←Real.rpow_add (by linarith : 0<Z),←Real.rpow_add (by linarith : 0<Z)]
  congr 1;ring

end SevenEighths.CenteredMomentAmplificationChildSourceCaps

end

end OAI
end OAIOriginalModule2152

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalFamily
Source SHA256: d1eadab311cdb0dd6cef819b2ded87caf316f4656a388d273ffeefd146868000
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2153



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.CenteredMomentAmplificationRadicalFamily
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentRadicalFamily CenteredMomentFirstFamily
open CenteredMomentAmplificationFamily CenteredMomentAmplificationFamilyEnergy
open CenteredMomentAmplificationActiveFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentOriginalChildEnergy CenteredMomentGaussEnergy
open CenteredMomentSecondChildProfile
open CenteredMomentAmplificationGlobal CenteredMomentAmplificationErrorEnergy
open CenteredMomentAmplificationChildEnergy CenteredMomentAmplificationErrorPool
open CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
open CenteredMomentFirstAmplificationChoice
open CenteredMomentSectorLocalization CenteredMomentAmplificationEligibility
local notation "O"=>ActualEisensteinCubic.O
local instance {ι : Type*} : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def radicalBound (η:Character)(m p:O)(k:ℕ):ℕ :=
  η.modulus.absNorm*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm*
    (if k=0 then 1 else (Ideal.span {p}).absNorm)

theorem radicalBound_error_power (η:Character)(m p:O)(hp:p≠0)(Z:ℝ)(hZ:1<Z)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    (radicalBound η m p (errorMovingExponent n):ℝ)=
      ((η.modulus.absNorm:ℝ)*(Ideal.span {m}).absNorm*(Ideal.span {(72:O)}).absNorm)*
        Z^(errorMoving p Z (n+1)):=by
  have hpow:=Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normValue_pos p hp)
  rcases hn with rfl|rfl|rfl <;>
    norm_num only [radicalBound,errorMovingExponent,errorMoving,Nat.cast_mul,
      Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals simp only [ite_false,ite_true,Nat.one_ne_zero,eq_self,
    Nat.cast_one,Real.rpow_zero,mul_one]
  all_goals rw [hpow]; rfl

theorem exists_radical_row (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤radicalBound η m p k ∧
      ∀n:O,elementCoeff τ n=rowTwist (elementHom η) m 1 (p^(2*k)) n:=by
  by_cases hk:k=0
  · obtain ⟨τ,hN,hτ⟩:=exists_supported_row_presentation η m 1 hm
      CenteredMomentAddedZero.supported_one_element hmLam hm2
    refine ⟨τ,?_,?_⟩
    · simp [radicalBound,hk,hN]
    · simpa [hk] using hτ
  · obtain ⟨τ,hM,hN,hτ⟩:=exists_radical_row_presentation η m hm hmLam hm2
      (fun _:Fin 1=>p) (fun _=>hs) (fun _=>2*k)
      (fun _=>Nat.mul_pos (by omega) (Nat.pos_of_ne_zero hk))
    refine ⟨τ,?_,?_⟩
    · simpa [radicalBound,hk] using hN
    · simpa using hτ

theorem exists_radical_height (η:Character)(χ:RayCharacter)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:Character,τ.modulus.absNorm≤radicalBound (childCharacter η χ) m p k ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom (p^(2*k)) I*
          rayCharacter χ (primaryGenerator I):=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_row (childCharacter η χ) m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he:=idealCoeff_eq_row (childCharacter η χ) τ m 1 (p^(2*k)) hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom (p^(2*k)) I*rayCharacter χ (primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem exists_radical_family (η:Character)(m p:O)(hm:m≠0)
    (hs:Supported (Ideal.span {p}))(hpp:goodLambda^2∣p-1)
    (hmLam:goodLambda∣m)(hm2:(2:O)∣m)(k:ℕ):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p k) ∧
      ∀I:Ideal O,Supported I→∀t:ℝ,
        rowWeight η m 1 1 t I*residualCharacter p k (primaryGenerator I)=
          ∑χ:RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I:=by
  choose τ hN hτ using fun χ:RayCharacter=>exists_radical_height η χ m p hm hs hmLam hm2 k
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have hn:=supported_primaryGenerator_ne_zero I hI
  have hgen:Supported (Ideal.span {primaryGenerator I}):=by
    rw [primary_span_supported I hI];exact hI
  rw [residualCharacter_moving p _ k hs hgen hpp (primaryGenerator_spec I hn).2,
    primary_span_supported I hI,amplificationPhase_expansion p _ k hgen]
  simp only [Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [hτ χ I hI t]
  ring

theorem exists_actual_error_family (η:Character)(m p:O)
    (hm:m≠0)(hp:Prime p)(hs:Supported (Ideal.span {p}))
    (hpp:goodLambda^2∣p-1)(hmLam:goodLambda∣m)(hm2:(2:O)∣m)
    (n:ℕ)(hn:n=0∨n=5∨n=6):
    ∃τ:RayCharacter→Character,
      (∀χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀(S:Finset (Ideal O))(C:Ideal O),C≠0→∀(β:Ideal O→ℂ)(t:ℝ)
        (W:𝓢(ℝ,ℂ))(K:ℝ),0<K→
      (∀z:O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)→
      (sourceGaussEnergy (residualColumns S p hp (n+1))
        (fun I=>β (C*I)*rowWeight η m 1 1 t (C*I))
        (fun I=>residualCharacter p (n+1) (primaryGenerator I)) W K).re≤
        16*∑χ:RayCharacter,
          (sourceGaussEnergy (residualColumns S p hp (n+1))
            (fun I=>β (C*I)) (heightCoeff (τ χ) t) W K).re:=by
  obtain ⟨τ,hN,hτ⟩:=exists_radical_family η m p hm hs hpp hmLam hm2 (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S C hC β t W K hK hW
  rw [actual_error_energy_active S p hp hs n hn]
  exact amplification_family_energy η m p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) C hC β t W K hK hW

theorem original_errors_to_children {ι : Type*} [Fintype ι] (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (S : (ι ⊕ Fin 2) → Finset (Ideal O)),
      (∀ i,∀ I∈S i,I≠0) → (∀ i,∀ I∈S (Sum.inl i),Prime I) →
      (∀ i,∀ I∈S (Sum.inl i),I≠0 ∧ IsCoprime (Ideal.span {p}) I) →
      ∀ (R s : Ideal O),IsCoprime s ((Ideal.span {p})^(n+1)) →
      ∀ (ν : ι → Ideal O → ℂ) (Wslot : ι → ℝ → ℂ) (P : ι → ℝ)
        (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (t T : ℝ),0<T →
      ∀ (rows : Finset O),(∀ h∈rows,¬p∣h) →
      ∀ (W : 𝓢(ℝ,ℂ)) (K : ℝ),0<K →
      (∀ z : O,0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z∈rows,1≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      let β := finiteColumnCoefficient (Fintype.piFinset S)
        (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
      let C := (Ideal.span {p})^(n+1)
      (∑ h∈rows,‖amplificationError Finset.univ
        (sourceGenerator (finiteColumns (Fintype.piFinset S)))
        (sourceGenerator_supported (finiteColumns (Fintype.piFinset S)))
        (fun I : supportedColumns (finiteColumns (Fintype.piFinset S)) =>
          (Real.sqrt T:ℂ)⁻¹*(β I*rowWeight η m 1 1 t I))
        (fun I => multiplicity p (sourceGenerator (finiteColumns (Fintype.piFinset S)) I)) p (n+1) h‖^2)≤
        (16*(n+2:ℝ)*localErrorCost p n) *
          ((∑ χ : RayCharacter,∑ B : actualAllocations S C,
            (sourceGaussEnergy
              (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
              (finiteColumnCoefficient
                (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
                (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
              (heightCoeff (τ χ) t) W K).re) /
            (T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := exists_actual_error_family η m p hm hp hs hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro S hS hprime hslot R s hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ t T hT rows hrows W K hK hW hmajor
  dsimp only
  let β := finiteColumnCoefficient (Fintype.piFinset S)
    (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ s)
  let S₀ := finiteColumns (Fintype.piFinset S)
  let C := (Ideal.span {p})^(n+1)
  let Q := residualColumns S₀ p hp (n+1)
  let T' := T/(Ideal.absNorm (Ideal.span {p}):ℝ)^(n+1)
  have hC : C≠0 := pow_ne_zero _ hs.1
  have ht : 0<T' := by
    apply div_pos hT
    apply pow_pos
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  have he := finite_original_error_energy S₀ (fun I => β I*rowWeight η m 1 1 t I)
    p hp hs hg hc hpp n hn T hT rows hrows W K hK hW hmajor
  have hf := hτ S₀ C hC β t W K hK hW
  have hb (χ : RayCharacter) :
      (sourceGaussEnergy Q (fun I => β (C*I)) (heightCoeff (τ χ) t) W K).re≤
        (n+2:ℝ)*∑ B : actualAllocations S C,
          (sourceGaussEnergy
            (finiteColumns (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1))
            (finiteColumnCoefficient
              (liveBox S B (allocation_data S C B (Finset.mem_filter.mp B.property).1).1)
              (maskedLiveProfile B C R s ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂))
            (heightCoeff (τ χ) t) W K).re := by
    have hpool := residual_energy_eq_punctured S₀ β (heightCoeff (τ χ) t) p hp hs hpp (n+1) (by omega) W K
    change _≤_
    rw [hpool]
    simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using
      actual_amplification_child_energy S hS hprime (Ideal.span {p}) R s hPid hs (n+1)
        hslot hsc ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ (heightCoeff (τ χ) t) W K hK hW
  apply he.trans
  apply (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right
    (hf.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun χ _ => hb χ)) (by norm_num))) ht.le)
    (localErrorCost_nonneg p n)).trans_eq
  rw [←Finset.mul_sum]
  ring

theorem exists_original_error_ball_family {ι : Type*} [Fintype ι]
    (η : Character) (m p : O) (hm : m≠0) (hp : Prime p)
    [(Ideal.span {p}).IsMaximal] (hPid : Prime (Ideal.span {p}))
    (hs : Supported (Ideal.span {p})) (hg : goodLambda∉Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p})≠2) (hpp : goodLambda^2∣p-1)
    (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) m p (errorMovingExponent n)) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑ h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          ‖amplificationError Finset.univ (sourceGenerator D.columns)
            (sourceGenerator_supported D.columns) (D.coefficient η m t T)
            (fun I => multiplicity p (sourceGenerator D.columns I)) p (n+1) h‖^2)≤
          D.childEnergy τ p n t T
            (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1))) := by
  obtain ⟨τ,hN,hτ⟩ := original_errors_to_children (ι:=ι) η m p hm hp hPid hs hg hc hpp hmLam hm2 n hn
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  have hK : 0<Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (n+1)) :=
    Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _
  by_cases he : ((dyadRows j).filter (fun h => eligible D.R D.s h p)).Nonempty
  · obtain ⟨h,hh⟩ := he
    have hsc := (eligible_coprime_divisor D.R D.s h p hPid (Finset.mem_filter.mp hh).2).pow_right (n:=n+1)
    have hfull := hτ D.S hS hprime (fun i I hI => ⟨hS _ _ hI,hslot i I hI⟩) D.R D.s hsc
      D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂ t T hT
      ((dyadRows j).filter (fun h => eligible D.R D.s h p))
      (fun h hh => eligible_not_dvd_row D.R D.s h p (Finset.mem_filter.mp hh).2)
      ballProfile _ hK (fun _ => ballProfile_nonneg _)
      (fun h hh => dyad_ball_majorant Z hZ j _
        (hsigma.trans (errorGain_bounds D0 cLog sigma Z p (n+1) hsigma).1)
        h (Finset.mem_filter.mp hh).1)
    rw [OriginalData.coefficient_eq]
    dsimp only at hfull
    dsimp only [OriginalData.childEnergy,OriginalData.coefficient,OriginalData.beta,
      OriginalData.columns,OriginalData.profile]
    exact hfull
  · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
    exact D.childEnergy_nonneg τ p n t T _ hT.le hK

end SevenEighths.CenteredMomentAmplificationRadicalFamily

end

end OAI
end OAIOriginalModule2153

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplifiedRetainedRadius
Source SHA256: 8ab0f7421c9355a43124887413fa7080494929064ab5ac04b67cdf97c36aece1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2154



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.CenteredMomentAmplifiedRetainedRadius
open HeckeFamily CanonicalQuadraticSieve ConcreteTraceCRT
open CenteredMomentFirstAmplificationChoice CenteredMomentGaussEnergy
open CenteredMomentSmoothedWindowEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentAmplificationErrorEnergy CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentGaussNormalization
local notation "O" => ActualEisensteinCubic.O

theorem ballProfile_support_upper (x : ℝ) (hx : 0≤x) (h : ballProfile x≠0) : x<2 := by
  have hb : x∈Function.support QuadraticInitialBound.sieveBump := by
    intro hz
    exact h (by simp only [ballProfile,QuadraticInitialBound.sieveCutoff_apply,hz,Complex.ofReal_zero])
  rw [QuadraticInitialBound.sieveBump.support_eq] at hb
  simpa only [Metric.mem_ball,dist_zero_right,Real.norm_eq_abs,abs_of_nonneg hx,
    QuadraticInitialBound.sieveBump] using hb

theorem ballProfile_radius_le (x Y V : ℝ) (hx : 0≤x) (hY : 0<Y) (hV : 0<V)
    (hscale : 2*Y≤V) : (ballProfile (x/Y)).re≤(ballProfile (x/V)).re := by
  by_cases hz : ballProfile (x/Y)=0
  · simpa only [hz,Complex.zero_re] using ballProfile_nonneg (x/V)
  have hs := ballProfile_support_upper (x/Y) (div_nonneg hx hY.le) hz
  have hxy : x≤V := ((div_lt_iff₀ hY).mp hs).le.trans hscale
  rw [ballProfile_one (x/V) (div_nonneg hx hV.le) ((div_le_one hV).mpr hxy)]
  exact ballProfile_le_one _

theorem gaussEnergy_radius_le {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (c : α→ℂ)
    (Y V : ℝ) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    (gaussEnergy S a ha c ballProfile Y).re≤(gaussEnergy S a ha c ballProfile V).re := by
  have h1 := gaussEnergy_hasSum_re S a ha c ballProfile Y hY
  have h2 := gaussEnergy_hasSum_re S a ha c ballProfile V hV
  rw [←h1.tsum_eq,←h2.tsum_eq]
  apply Summable.tsum_le_tsum _ h1.summable h2.summable
  intro z
  exact mul_le_mul_of_nonneg_left
    (ballProfile_radius_le _ Y V (sq_nonneg _) hY hV hscale) (sq_nonneg _)

theorem sourceGaussEnergy_radius_le (Q : Finset (Ideal O)) (c f : Ideal O→ℂ)
    (Y V : ℝ) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    (sourceGaussEnergy Q c f ballProfile Y).re≤(sourceGaussEnergy Q c f ballProfile V).re :=
  gaussEnergy_radius_le _ _ _ _ Y V hY hV hscale

theorem childEnergy_radius_le {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Y V : ℝ) (hT : 0≤T) (hY : 0<Y) (hV : 0<V) (hscale : 2*Y≤V) :
    D.childEnergy τ p n t T Y≤D.childEnergy τ p n t T V := by
  unfold OriginalData.childEnergy
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (by positivity) (localErrorCost_nonneg p n))
  apply div_le_div_of_nonneg_right _ (div_nonneg hT (by positivity))
  apply Finset.sum_le_sum
  intro χ _
  apply Finset.sum_le_sum
  intro B _
  exact sourceGaussEnergy_radius_le _ _ _ Y V hY hV hscale

lemma exponent_max (d K0 j c g : ℝ) :
    j+(max (d+K0-j-c) 0+g)=max (j+g) (d+K0-c+g) := by
  by_cases h : d+K0-j-c≤0
  · rw [max_eq_right h,max_eq_left (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h),max_eq_right (by linarith)]
    ring

lemma rpow_exponent_max (Z a b : ℝ) (hZ : 1≤Z) :
    Z^(max a b)=max (Z^a) (Z^b) := by
  rcases le_total a b with h|h
  · rw [max_eq_right h,max_eq_right (Real.rpow_le_rpow_of_exponent_le hZ h)]
  · rw [max_eq_left h,max_eq_left (Real.rpow_le_rpow_of_exponent_le hZ h)]

theorem main_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤Z) :
    Z^(j+mainGain (d+K0-j) c sigma)=
      max (Z^(j+2*sigma)) (Z^(d+K0-c+2*sigma)) := by
  rw [mainGain,exponent_max,rpow_exponent_max Z _ _ hZ]

theorem error_radius_identity (Z d K0 j c sigma : ℝ) (p : O) (k : ℕ) (hZ : 1≤Z) :
    Z^(j+errorGain (d+K0-j) c sigma Z p k)=
      max (Z^(j+sigma))
        (Z^(d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma)) := by
  have he := exponent_max d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma
  have hbase : j+errorGain (d+K0-j) c sigma Z p k=
      max (j+sigma) (d+K0-c-2*errorRemoval p Z k+errorMoving p Z k+sigma) := by
    unfold errorGain
    convert he using 1 <;> ring_nf
  rw [hbase,rpow_exponent_max Z _ _ hZ]

lemma envelope_exponent (d K0 j c g δ : ℝ) (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+(max (d+K0-j-c) 0+g)≤K0+max (d-c) 0+g+δ := by
  rw [exponent_max]
  apply max_le
  · linarith [le_max_right (d-c) (0:ℝ)]
  · linarith [le_max_left (d-c) (0:ℝ)]

theorem main_exponent_envelope (d K0 j c sigma δ : ℝ) (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+mainGain (d+K0-j) c sigma≤K0+max (d-c) 0+2*sigma+δ :=
  envelope_exponent d K0 j c (2*sigma) δ hδ hj

theorem error_exponent_envelope (d K0 j c sigma δ Z : ℝ) (p : O) (k : ℕ)
    (hδ : 0≤δ) (hj : j≤K0+δ) :
    j+errorGain (d+K0-j) c sigma Z p k≤
      K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ := by
  have he := envelope_exponent d K0 j (c+2*errorRemoval p Z k-errorMoving p Z k) sigma δ hδ hj
  unfold errorGain
  convert he using 1 <;> ring_nf

theorem eventually_support_reserve (reserve : ℝ) (hreserve : 0<reserve) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ 2≤Z^reserve := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop hreserve).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hpow
  exact ⟨hZ,hpow⟩

lemma doubled_radius_le (Z a b reserve : ℝ) (hZ : 1<Z) (hab : a≤b)
    (hreserve : 2≤Z^reserve) : 2*Z^a≤Z^(b+reserve) := by
  rw [Real.rpow_add (zero_lt_one.trans hZ)]
  calc
    _≤2*Z^b := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.le hab) (by norm_num)
    _≤Z^b*Z^reserve := by
      rw [mul_comm (Z^b)]
      exact mul_le_mul_of_nonneg_right hreserve (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)

theorem unamplified_radius_identity (Z d K0 j c sigma : ℝ) (hZ : 1≤Z) :
    Z^(j+(max (d+K0-j-c) 0+sigma))=
      max (Z^(j+sigma)) (Z^(d+K0-c+sigma)) := by
  rw [exponent_max,rpow_exponent_max Z _ _ hZ]

theorem dyadic_to_common_ball {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 c sigma δ reserve : ℝ) (hZ : 1<Z) (hsigma : 0≤sigma) (hδ : 0≤δ)
    (n : ℤ) (hn : Real.logb Z (dyadicScale n)≤K0+δ) (hreserve : 2≤Z^reserve) :
    (∑' h : O,dyadicWeight n (normValue h)*‖gaussPolynomial S a ha coeff h‖^2)≤
      (gaussEnergy S a ha coeff ballProfile (Z^(K0+max (d-c) 0+sigma+δ+reserve))).re := by
  apply (dyadic_to_ball S a ha coeff Z sigma
    (d+K0-Real.logb Z (dyadicScale n)) c hZ hsigma n).trans
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (envelope_exponent d K0 _ c sigma δ hδ hn) hreserve

def mainCommonRadius (Z d K0 c sigma δ reserve : ℝ) : ℝ :=
  Z^(K0+max (d-c) 0+2*sigma+δ+reserve)

def errorCommonRadius (Z d K0 c sigma δ reserve : ℝ) (p : O) (k : ℕ) : ℝ :=
  Z^(K0+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+sigma+δ+reserve)

theorem main_energy_common {α : Type*} (S : Finset α) (a : α→O)
    (ha : ∀i,Supported (Ideal.span {a i})) (coeff : α→ℂ)
    (Z d K0 j c sigma δ reserve : ℝ) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    (gaussEnergy S a ha coeff ballProfile (Z^(j+mainGain (d+K0-j) c sigma))).re≤
      (gaussEnergy S a ha coeff ballProfile (mainCommonRadius Z d K0 c sigma δ reserve)).re := by
  apply gaussEnergy_radius_le _ _ _ _ _ _
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (main_exponent_envelope d K0 j c sigma δ hδ hj) hreserve

theorem child_energy_common {ι : Type*} [Fintype ι]
    (D : OriginalData ι) (τ : RayFourExpansion.RayCharacter→Character) (p : O) (n : ℕ)
    (t T Z d K0 j c sigma δ reserve : ℝ) (hT : 0≤T) (hZ : 1<Z) (hδ : 0≤δ)
    (hj : j≤K0+δ) (hreserve : 2≤Z^reserve) :
    D.childEnergy τ p n t T (Z^(j+errorGain (d+K0-j) c sigma Z p (n+1)))≤
      D.childEnergy τ p n t T (errorCommonRadius Z d K0 c sigma δ reserve p (n+1)) := by
  apply childEnergy_radius_le D τ p n t T _ _ hT
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
  exact doubled_radius_le Z _ _ reserve hZ
    (error_exponent_envelope d K0 j c sigma δ Z p (n+1) hδ hj) hreserve

theorem errorCommonRadius_six (Z d K0 c sigma δ reserve : ℝ) (p : O) :
    errorCommonRadius Z d K0 c sigma δ reserve p 6=
      Z^(K0+max (d-c-2*errorRemoval p Z 6) 0+sigma+δ+reserve) := by
  simp only [errorCommonRadius,errorMoving,ite_true,add_zero]

open CenteredMomentFirstScale

theorem retained_nominal_upper (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi : ℝ) (hK : 0<K) (hX : 0<X) (hZ : 1<Z)
    (hC : 0<Csec) (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    Real.logb Z (dyadicScale n)≤nominalLog I J E K X Z+frequencyLoss Z Csec xi := by
  apply retained_first_dyad_enclosure Tsec Z Csec (nominalLog I J E K X Z) xi hZ hC _ n hn
  rw [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (firstNominalScale_pos I J E hE K X hK hX)]
  exact hsec

theorem actual_retained_radii (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec) (hxi : 0≤xi)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (hreserve : 2≤Z^reserve) :
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let δ := frequencyLoss Z Csec xi
    2*Z^(j+mainGain (d+K0-j) c sigma)≤mainCommonRadius Z d K0 c sigma δ reserve ∧
      ∀(p:O)(k:ℕ),2*Z^(j+errorGain (d+K0-j) c sigma Z p k)≤
        errorCommonRadius Z d K0 c sigma δ reserve p k := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  constructor
  · exact doubled_radius_le Z _ _ reserve hZ (main_exponent_envelope _ _ _ _ _ _ hδ hj) hreserve
  · intro p k
    exact doubled_radius_le Z _ _ reserve hZ (error_exponent_envelope _ _ _ _ _ _ Z p k hδ hj) hreserve

open CenteredMomentPrimePool CenteredMomentPrimeElements
open CenteredMomentAmplificationOriginalErrors CenteredMomentAmplificationGlobal

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
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
          HeckeRowClosure.rowConductorBound (CenteredMomentChildRows.childCharacter η χ) m 1 (p.val^(2*CenteredMomentAmplificationActiveFactor.errorMovingExponent (errorIndex i)))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T d cLog : ℝ),0<T →
          ∀ (I J E : Ideal O),E≠0 → ∀ (K X Tsec : ℝ),0<K → 0<X →
          Tsec≤Csec*firstNominalScale I J E K X →
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2

end SevenEighths.CenteredMomentAmplifiedRetainedRadius

end

end OAI
end OAIOriginalModule2154

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationRadicalChoice
Source SHA256: b75c75eb3654b95c3b1eb3a92908a9669ab754d311a5ddc0c7bbf5c7bb597127
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2155



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentAmplificationRadicalChoice
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

theorem exists_pool_error_families {ι : Type*} [Fintype ι]
    (P : Finset (Ideal O)) (hP : ∀Q∈P,Prime Q) (hbad : ∀Q∈P,Q∉fixedBadPrimes)
    (η : Character) (m : O) (hm : m≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
      (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
      ∀ (D : OriginalData ι),
        (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
        (∀ p∈elementPool P,∀ i,∀ I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I) →
        ∀ (t T Z sigma D0 cLog : ℝ),0<T → 1<Z → 0≤sigma → ∀ (j : ℤ),
        (∑p∈elementPool P,∑h∈(dyadRows j).filter (fun h => eligible D.R D.s h p),
          errorEnergy Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
            (D.coefficient η m t T) h p)≤
        ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
          (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1))) := by
  have hf (p : elementPool P) (i : Fin 3) := by
    have hd := elementPool_data P hP hbad p p.property
    have hPid := hP _ hd.2.1
    letI : (Ideal.span {p.val}).IsMaximal :=
      (Ideal.isPrime_of_prime hPid).isMaximal hPid.ne_zero
    exact CenteredMomentAmplificationRadicalFamily.exists_original_error_ball_family (ι:=ι) η m p hm hd.1 hPid hd.2.2.2.1
      hd.2.2.2.2.1 hd.2.2.2.2.2 hd.2.2.1 hmLam hm2 (errorIndex i) (errorIndex_cases i)
  choose τ hτ using hf
  refine ⟨τ,fun p i => (hτ p i).1,?_⟩
  intro D hS hprime hslot t T Z sigma D0 cLog hT hZ hsigma j
  rw [←Finset.sum_coe_sort (elementPool P)]
  apply Finset.sum_le_sum
  intro p hp
  have h0 := (hτ p 0).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h5 := (hτ p 1).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  have h6 := (hτ p 2).2 D hS hprime (hslot p p.property) t T Z sigma D0 cLog hT hZ hsigma j
  simpa only [errorEnergy,Finset.sum_add_distrib,Fin.sum_univ_three,
    show errorIndex 0=0 from rfl,show errorIndex 1=5 from rfl,show errorIndex 2=6 from rfl,Nat.reduceAdd] using
    add_le_add (add_le_add h0 h5) h6

theorem eventually_original_source_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,∀ I∈D.S (Sum.inl i),D.slot i ((Ideal.absNorm I:ℝ)/D.lengths i)≠0) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_dyadic_amplification M H hH Sbad hbad sigma loss BR Bs Mmax b eta
    hsigma hloss hM hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hsep,hdata,hamp⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,herr⟩ := exists_pool_error_families (ι:=ι) _
    (fun Q hQ => (hdata Q hQ).1) (fun Q hQ => (hdata Q hQ).2.1) η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hslot hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have hcop (p : O) (hp : p∈elementPool (primePool M H Sbad (1/2) 1 (Z^(sigma/3)))) :
      ∀i,∀I∈D.S (Sum.inl i),IsCoprime (Ideal.span {p}) I := by
    have hd := elementPool_data _ (fun Q hQ => (hdata Q hQ).1)
      (fun Q hQ => (hdata Q hQ).2.1) p hp
    exact original_slot_coprime D Z sigma b eta hZ.le hb hsep z hz hlen hsupp hslot hprime
      (Ideal.span {p}) (hdata _ hd.2.1).1 (hdata _ hd.2.1).2.2.1
  have he := herr D hS hprime hcop t T Z sigma D0 cLog hT hZ hsigma.le j
  apply (hamp Finset.univ (sourceGenerator D.columns) (sourceGenerator_supported D.columns)
    (D.coefficient η m t T) D.R D.s hR0 hs0 hR hs j hK D0 cLog).trans
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl he) (by positivity)

theorem eventually_original_amplification {ι : Type*} [Fintype ι]
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (sigma loss BR Bs Mmax b eta : ℝ)
    (hsigma : 0<sigma) (hloss : 0<loss) (hM : 0≤Mmax) (hb : 0≤b) (hgap : eta<sigma/6) :
    ∀ᶠ Z : ℝ in atTop, 1<Z ∧
      let P := primePool M H Sbad (1/2) 1 (Z^(sigma/3))
      P.Nonempty ∧ Z^(sigma/3-loss)≤(P.card:ℝ) ∧
      ∀ (η : Character) (m : O),m≠0 → goodLambda∣m → (2:O)∣m →
      ∃ τ : (elementPool P) → Fin 3 → RayCharacter → Character,
        (∀ (p : elementPool P) i χ,(τ p i χ).modulus.absNorm≤
          radicalBound (childCharacter η χ) m p.val (errorMovingExponent (errorIndex i))) ∧
        ∀ (D : OriginalData ι),
          (∀ i,∀ I∈D.S i,I≠0) → (∀ i,∀ I∈D.S (Sum.inl i),Prime I) →
          (∀ i,Function.support (D.slot i)⊆Set.Iic b) →
          ∀ (z : ι→ℝ),(∀i,z i≤eta) → (∀i,D.lengths i=Z^(z i)) →
          D.R≠0 → D.s≠0 → (Ideal.absNorm D.R:ℝ)≤Z^BR → (Ideal.absNorm D.s:ℝ)≤Z^Bs →
          ∀ (t T D0 cLog : ℝ),0<T → ∀ (j : ℤ),Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (Z^(Real.logb Z (dyadicScale j)+mainGain D0 cLog sigma))).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (Z^(Real.logb Z (dyadicScale j)+errorGain D0 cLog sigma Z p (errorIndex i+1)))) := by
  filter_upwards [eventually_original_source_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap] with Z hz
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T D0 cLog hT j hK
  have he := henergy D.active (fun i I hI => hS i I (D.active_subset i hI))
    (fun i I hI => hprime i I (D.active_subset _ hI)) D.active_slot hsupp z hz hlen
    hR0 hs0 hR hs t T D0 cLog hT j hK
  simpa only [D.active_gaussPolynomial,D.active_gaussEnergy] using he

theorem eventually_original_amplification_common {ι : Type*} [Fintype ι]
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
          ∀ (j : ℤ),Retained (frequencyRadius Tsec Z xi) j →
          Real.logb Z (dyadicScale j)≤Mmax →
          (∑' h : O,dyadicWeight j (normValue h)*
            ‖gaussPolynomial Finset.univ (sourceGenerator D.columns)
              (sourceGenerator_supported D.columns) (D.coefficient η m t T) h‖^2)≤
            (8/(P.card:ℝ))*
              (((Mmax+2*sigma)/(sigma/6))*
                (gaussEnergy Finset.univ (sourceGenerator D.columns)
                  (sourceGenerator_supported D.columns) (D.coefficient η m t T) ballProfile
                  (mainCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve)).re+
                ∑p : elementPool P,∑i : Fin 3,D.active.childEnergy (τ p i) p (errorIndex i) t T
                  (errorCommonRadius Z d (nominalLog I J E K X Z) cLog sigma
                    (frequencyLoss Z Csec xi) reserve p (errorIndex i+1))) := by
  filter_upwards [eventually_original_amplification (ι:=ι) M H hH Sbad hbad
    sigma loss BR Bs Mmax b eta hsigma hloss hM hb hgap,
    eventually_support_reserve reserve hreserve] with Z hz hsupport
  obtain ⟨hZ,hP,hcard,hfam⟩ := hz
  refine ⟨hZ,hP,hcard,?_⟩
  intro η m hm hmLam hm2
  obtain ⟨τ,hN,henergy⟩ := hfam η m hm hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T d cLog hT
    I J E hE K X Tsec hK hX hsec j hj hMdyad
  let K0 := nominalLog I J E K X Z
  let kdyad := Real.logb Z (dyadicScale j)
  have henclose : kdyad≤K0+frequencyLoss Z Csec xi :=
    retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
      (zero_lt_one.trans_le hC) hsec j hj
  have hδ := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have he := henergy D hS hprime hsupp z hz hlen hR0 hs0 hR hs t T
    (d+K0-kdyad) cLog hT j hMdyad
  apply he.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact main_energy_common _ _ _ _ Z d K0 kdyad cLog sigma _ reserve hZ hδ henclose hsupport.2
  · apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro i _
    exact child_energy_common D.active (τ p i) p (errorIndex i) t T Z d K0 kdyad cLog sigma
      _ reserve hT.le hZ hδ henclose hsupport.2

end SevenEighths.CenteredMomentAmplificationRadicalChoice

end

end OAI
end OAIOriginalModule2155

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonRadiusSaving
Source SHA256: ee625794b23b08fd5094d628d59c167d10cea9a00f2651db76a513d957e6e239
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2156


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentCommonRadiusSaving
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

theorem common_saving_identity (c d x w q wo B sigma branch delta reserve ell : ℝ) :
    firstSaving c (d+x) w q wo B
      (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell =
      c/6+5*d/6+w/3+q/6+wo+B-5*max (d-c-2*w+wo) 0/6-
        5*branch*sigma/6-5*(delta+reserve)/6+ell := by
  unfold firstSaving
  ring

theorem common_saving_lower (c d x w q wo B sigma branch delta reserve ell : ℝ)
    (hc : 0≤c) (hw : 0≤w) (hq : 0≤q) (hwo : 0≤wo) (hB : 0≤B)
    (hallow : 3*c-5*d≤6*B+q) :
    2*(c+w)/3-max (w/3-wo) 0-5*branch*sigma/6-5*(delta+reserve)/6+ell≤
      firstSaving c (d+x) w q wo B
        (x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve) ell := by
  rw [common_saving_identity]
  have hm0 := le_max_right (w/3-wo) (0:ℝ)
  have hm1 := le_max_left (w/3-wo) (0:ℝ)
  by_cases h : 0≤d-c-2*w+wo
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem main_saving_lower (c d x q B sigma delta reserve : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q) :
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+x) 0 q 0 B
        (x+max (d-c) 0+2*sigma+delta+reserve) (sigma/3) := by
  have hh := common_saving_lower c d x 0 q 0 B sigma 2 delta reserve (sigma/3)
    hc (by norm_num) hq (by norm_num) hB hallow
  norm_num only [zero_div,sub_zero,add_zero,mul_zero,max_self] at hh
  linarith

theorem error_penalty_le (l sigma : ℝ) (hl : 0≤l) (hu : l≤sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0≤2*sigma/3 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [Nat.cast_ofNat,ite_false,ite_true,
    one_mul,sub_zero] <;> apply max_le <;> linarith

def errorLoss (sigma : ℝ) (k : ℕ) : ℝ :=
  if k=1 then 5*sigma/6 else if k=6 then 3*sigma/2 else 23*sigma/18

theorem error_penalty_refined (l sigma : ℝ) (hl : 0≤l) (hu : l≤sigma/3)
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    max (((k:ℝ)*l)/3-(if k=6 then 0 else l)) 0+5*sigma/6≤errorLoss sigma k := by
  have hs : 0≤sigma := by linarith
  rcases hk with rfl|rfl|rfl
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_one,one_mul]
    have hm : max (l/3-l) 0=0 := max_eq_right (by linarith)
    rw [hm,zero_add]
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat,sub_zero]
    have hm : max (6*l/3) 0≤2*sigma/3 := max_le (by linarith) (by linarith)
    linarith
  · norm_num only [errorLoss,ite_true,ite_false,Nat.cast_ofNat]
    have hm : max (7*l/3-l) 0≤4*sigma/9 := max_le (by linarith) (by linarith)
    linarith

theorem errorLoss_le (sigma : ℝ) (hs : 0≤sigma) (k : ℕ)
    (hk : k=1 ∨ k=6 ∨ k=7) : errorLoss sigma k≤3*sigma/2 := by
  rcases hk with rfl|rfl|rfl <;> norm_num only [errorLoss,ite_true,ite_false] <;> linarith

theorem error_saving_refined (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_refined l sigma hl hu k hk]

theorem error_saving_lower (c d x q B sigma delta reserve l : ℝ)
    (hc : 0≤c) (hq : 0≤q) (hB : 0≤B) (hallow : 3*c-5*d≤6*B+q)
    (hl : 0≤l) (hu : l≤sigma/3) (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    2*(c+(k:ℝ)*l)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+x) ((k:ℝ)*l) q (if k=6 then 0 else l) B
        (x+max (d-c-2*((k:ℝ)*l)+(if k=6 then 0 else l)) 0+
          sigma+delta+reserve) 0 := by
  have hw : 0≤(k:ℝ)*l := mul_nonneg (Nat.cast_nonneg k) hl
  have hwo : 0≤(if k=6 then (0:ℝ) else l) := by split_ifs <;> linarith
  have hh := common_saving_lower c d x ((k:ℝ)*l) q (if k=6 then 0 else l)
    B sigma 1 delta reserve 0 hc hw hq hwo hB hallow
  simp only [one_mul,add_zero] at hh
  linarith [error_penalty_le l sigma hl hu k hk]

theorem common_gain_width (d x c w wo sigma delta reserve branch : ℝ)
    (hs : 0≤sigma) (hd : 0≤delta) (hr : 0≤reserve) (hb : 1≤branch)
    (hx : -delta≤x) :
    0≤x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve ∧
    (d+x)-c-2*w+wo+sigma≤
      x+max (d-c-2*w+wo) 0+branch*sigma+delta+reserve := by
  have h0 := le_max_right (d-c-2*w+wo) (0:ℝ)
  have h1 := le_max_left (d-c-2*w+wo) (0:ℝ)
  constructor <;> nlinarith

theorem saving_power_factor (Z F c w sigma delta reserve : ℝ) (hZ : 1≤Z)
    (hF : 2*(c+w)/3-3*sigma/2-5*(delta+reserve)/6≤F) :
    Z^(-F)≤Z^(-2*(c+w)/3+3*sigma/2+5*(delta+reserve)/6) := by
  apply Real.rpow_le_rpow_of_exponent_le hZ
  linarith

theorem main_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z) :
    Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j=
      (K0-j)+max (d-c) 0+2*sigma+delta+reserve := by
  rw [mainCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem error_radius_gain (Z d K0 c sigma delta reserve j : ℝ) (hZ : 1<Z)
    (p : O) (k : ℕ) :
    Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j=
      (K0-j)+max (d-c-2*errorRemoval p Z k+errorMoving p Z k) 0+
        sigma+delta+reserve := by
  rw [errorCommonRadius,Real.logb_rpow (zero_lt_one.trans hZ) hZ.ne']
  ring

theorem canonical_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    let B := c+d-2*p-R
    0≤c ∧ 0≤q ∧ 0≤B ∧ 3*c-5*d≤6*B+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hh := actual_extracted_common_support_allowance I J hI hJ Z hZ
  dsimp only at hh
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have h0 := le_max_right (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h1 := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  have h2 := le_max_right (3*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    5*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  exact ⟨hc,hq.1,by linarith,by linarith [hq.2]⟩

theorem actual_main_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_common_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_common_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := canonical_saving_gates η τ m I J hI hJ A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_main_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z) (hs : 0≤sigma)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (c+d-2*p-R)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3))≤
      Z^(-2*c/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_main_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve hZ hmod
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

theorem actual_error_common_factor (η τ : Character) (m : O)
    (I J E : Ideal O) (hI : Supported I) (hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    Z^(-firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (c+d-2*p-R)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0)≤
      Z^(-2*(c+errorRemoval p0 Z k)/3+3*sigma/2+5*(delta+reserve)/6) := by
  dsimp only
  have hh := actual_error_common_saving η τ m I J E hI hJ A K X Z j sigma delta reserve
    hZ hmod M H Sbad hbad p0 hp0 k hk
  dsimp only at hh
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith

open CenteredMomentFirstScale

theorem actual_common_radius_widths (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 1≤Csec)
    (hxi : 0≤xi) (hs : 0≤sigma) (hr : 0≤reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    let j := Real.logb Z (dyadicScale n)
    let delta := frequencyLoss Z Csec xi
    let gm := Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j
    (0≤gm ∧ d+K0-j-c+sigma≤gm) ∧
    ∀p : O,∀k : ℕ,
      let ge := Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p k)-j
      0≤ge ∧ d+K0-j-c-2*errorRemoval p Z k+errorMoving p Z k+sigma≤ge := by
  dsimp only
  have hj := retained_nominal_upper I J E hE K X Z Csec Tsec xi hK hX hZ
    (zero_lt_one.trans_le hC) hsec n hn
  have hd := frequencyLoss_nonneg Z Csec xi hZ hC hxi
  have hx : -frequencyLoss Z Csec xi≤nominalLog I J E K X Z-Real.logb Z (dyadicScale n) := by
    linarith
  constructor
  · rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) 0 0 sigma
      (frequencyLoss Z Csec xi) reserve 2 hs hd hr (by norm_num) hx
    simp only [mul_zero,sub_zero,add_zero] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩
  · intro p k
    rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
    have hg := common_gain_width
      (Real.logb Z ((commonPart J I).absNorm:ℝ))
      (nominalLog I J E K X Z-Real.logb Z (dyadicScale n))
      (Real.logb Z ((commonPart I J).absNorm:ℝ)) (errorRemoval p Z k) (errorMoving p Z k)
      sigma (frequencyLoss Z Csec xi) reserve 1 hs hd hr (by norm_num) hx
    simp only [one_mul] at hg
    exact ⟨hg.1,by linarith [hg.2]⟩

end SevenEighths.CenteredMomentCommonRadiusSaving

end

end OAI
end OAIOriginalModule2156

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMaskedFamily
Source SHA256: cdf0dabe49d94768b25e4265511a5178c06fd26db2fc724e8d036bf6a3e1d2da
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2157




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedFamily
open HeckeFamily HeckeRowClosure CanonicalRowCompletion CanonicalQuadraticSieve
open ConcretePrimeRowBridge CompletedGauss RayFourExpansion
open CenteredMomentFixedRowMask
open CenteredMomentFirstFamily CenteredMomentFirstIdealFamily CenteredMomentFirstCanonicalFamily
open CenteredMomentFirstColumns CenteredMomentCanonicalFirst CenteredMomentCommonSupport
open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentSourceRow
open CenteredMomentAmplificationRadicalFamily CenteredMomentAmplificationActiveFactor
open CenteredMomentAmplificationShortening CenteredMomentAmplificationSourceDomain
open CenteredMomentAmplificationFamily CenteredMomentSourceAllocationEnergy
open CenteredMomentAmplificationFamilyEnergy CenteredMomentOriginalChildEnergy
open CenteredMomentGaussEnergy CenteredMomentLiveDomain CenteredMomentPrimaryCharacter
open ActualEisensteinCubic ConcreteTraceCRT CenteredMomentChildAssembly CenteredMomentChildRows
local notation "O" => HeckeFamily.O
local notation "fixedBadMask" => (goodLambda*(2:O))

lemma fixed_mask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)

def idealMask (u : O) (I : Ideal O) : ℂ := if IsCoprime I (Ideal.span {u}) then 1 else 0

def maskedSource (u : O) (β : Ideal O → ℂ) (I : Ideal O) : ℂ := β I * idealMask u I

lemma idealMask_span (u n : O) : idealMask u (Ideal.span {n}) =
    if IsCoprime n u then 1 else 0 := by
  simp only [idealMask, Ideal.isCoprime_span_singleton_iff]

lemma idealMask_primary (u : O) (I : Ideal O) (hI : Supported I) :
    idealMask u I = if IsCoprime (primaryGenerator I) u then 1 else 0 := by
  conv_lhs => rw [←primary_span_supported I hI, idealMask_span]

lemma row_mask_factor (η : Character) (u z n : O) :
    rowTwist (elementHom η) (fixedBadMask*u) 1 z n =
      (if IsCoprime n u then (1:ℂ) else 0)*
        rowTwist (elementHom η) fixedBadMask 1 z n := by
  have h := row_mask_mul η fixedBadMask u 1 z n
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda)
  simp only [one_mul] at h
  rw [h]
  split_ifs <;> simp

lemma rowWeight_mask_factor (η : Character) (u : O) (I : Ideal O)
    (hI : Supported I) (t : ℝ) :
    rowWeight η (fixedBadMask*u) 1 1 t I =
      idealMask u I * rowWeight η fixedBadMask 1 1 t I := by
  rw [rowWeight_one_primary η (fixedBadMask*u) t I hI,
    rowWeight_one_primary η fixedBadMask t I hI, idealMask_primary u I hI]
  change elementCoeff η (primaryGenerator I) *
      (if IsCoprime (fixedBadMask*u) (primaryGenerator I) then (1:ℂ) else 0) *
      (Ideal.absNorm I:ℂ)^(Complex.I*t) =
    (if IsCoprime (primaryGenerator I) u then (1:ℂ) else 0) *
      (elementCoeff η (primaryGenerator I) *
        (if IsCoprime fixedBadMask (primaryGenerator I) then (1:ℂ) else 0) *
        (Ideal.absNorm I:ℂ)^(Complex.I*t))
  rw [IsCoprime.mul_left_iff]
  by_cases hm : IsCoprime fixedBadMask (primaryGenerator I)
  <;> by_cases hu : IsCoprime (primaryGenerator I) u
  <;> simp [hm, hu, show IsCoprime u (primaryGenerator I) ↔
      IsCoprime (primaryGenerator I) u from isCoprime_comm]

theorem exists_first_masked_character (η : Character) (e r : O)
    (he : Supported (Ideal.span {e})) (hr : Supported (Ideal.span {r}))
    (χ : MulChar (Residue r) ℂ) (ξ : RayCharacter) :
    ∃ τ : Character,
      τ.modulus = η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r} ∧
      (∀ n : O, elementCoeff τ n =
        rowTwist (elementHom η) fixedBadMask 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n) ∧
      ∀ u n : O,
        rowTwist (elementHom η) (fixedBadMask*u) 1 (e*r) n * maskedPrimaryHom r χ n *
          elementCoeff (CenteredMomentFixedRay.primaryRayCharacter ξ) n =
        (if IsCoprime n u then (1:ℂ) else 0)*elementCoeff τ n := by
  obtain ⟨τ,hM,hτ,_⟩ := exists_first_character η fixedBadMask e r fixed_mask_ne_zero
    he hr (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) χ ξ
  refine ⟨τ,hM,hτ,?_⟩
  intro u n
  rw [row_mask_factor,hτ]
  ring

theorem exists_canonical_masked_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₁ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I)) =
          idealMask u I*heightCoeff τ₂ t I) := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂⟩ := exists_first_ideal_pair η fixedBadMask fixed_mask_ne_zero
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₁ I hI t]
    ring
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,heightCoeff,h₂ I hI t]
    ring

lemma divisor_column_masked (η τ : Character) (F : O → ℂ) (ξ : RayCharacter)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*
        (F (primaryGenerator I)*rayCharacter ξ (primaryGenerator I)))
    (u : O) (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (fun J => β J*rowWeight η (fixedBadMask*u) 1 1 t J*F (primaryGenerator J)) ξ I =
      (if L∣I then maskedSource u β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,primary_span_supported I hI,rowWeight_mask_factor η u I hI t,hτ I hI t]
  split_ifs
  · simp only [maskedSource]; ring
  · ring

lemma sourceGaussEnergy_congr (Q : Finset (Ideal O)) (c f c' f' : Ideal O → ℂ)
    (h : ∀ I ∈ Q, Supported I → c I*f I=c' I*f' I)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : sourceGaussEnergy Q c f W K=sourceGaussEnergy Q c' f' W K := by
  unfold sourceGaussEnergy
  congr 1
  funext I
  exact h I (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2

lemma first_source_energy (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    sourceGaussEnergy Q β
      (fun I => rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryGenerator I)) W K =
    sourceGaussEnergy Q (maskedSource u β) (heightCoeff τ t) W K := by
  apply sourceGaussEnergy_congr
  intro I _ hI
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  simp only [maskedSource]
  ring

lemma maskedSource_eq_of_live (u : O) (β : Ideal O → ℂ)
    (h : ∀ I, β I≠0 → IsCoprime I (Ideal.span {u})) : maskedSource u β=β := by
  funext I
  by_cases hi : β I=0
  · simp [maskedSource,hi]
  · simp [maskedSource,idealMask,h I hi]

lemma extracted_masked_coefficient (η : Character) (u : O) (C I : Ideal O)
    (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) (f : ℂ) :
    β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I)*f =
      (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I)*
        (rowWeight η fixedBadMask 1 1 t I*f) := by
  rw [map_mul,rowWeight_mask_factor η u I hI t]
  ring

lemma idealMask_generator (R I : Ideal O) :
    idealMask (idealGenerator R) I = if IsCoprime I R then 1 else 0 := by
  rw [idealMask,span_idealGenerator]

lemma maskedSource_punctured (u : O) (R : Ideal O) (β : Ideal O → ℂ) (I : Ideal O) :
    maskedSource u (fun J => if IsCoprime J R then β J else 0) I =
      if IsCoprime I R ∧ IsCoprime I (Ideal.span {u}) then β I else 0 := by
  unfold maskedSource idealMask
  split_ifs <;> simp_all

lemma first_gauss_row (η τ : Character) (F : O → ℂ)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η fixedBadMask 1 1 t I*F (primaryGenerator I))
    (Q : Finset (Ideal O)) (β : Ideal O → ℂ) (u : O) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => β I*
        (rowWeight η (fixedBadMask*u) 1 1 t I*F (primaryGenerator I))) z =
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q => maskedSource u β I*heightCoeff τ t I) z := by
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [rowWeight_mask_factor η u I hI t,hτ I hI t]
  dsimp only [maskedSource]
  ring

theorem exists_canonical_source_pair (η : Character) (C D : Ideal O)
    (hC : Supported C) (E : Finset (CommonIndex C D)) (ξ₁ ξ₂ : RayCharacter) :
    let e := primeSubsetGenerator (fun P : CommonIndex C D => P.val) E
    let r := activeConductor C D
    let ρ := finiteSexticRow (activePrime C D) (activeGood C D hC) (activeExponent C D)
    let M := η.modulus*Ideal.span {fixedBadMask}*Ideal.span {(72:O)}*Ideal.span {e*r}
    ∃ τ₁ τ₂ : Character, τ₁.modulus=M ∧ τ₂.modulus=M ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*
          (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*
          (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) ∧
      ∀ (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
      sourceGaussEnergy Q₁ β₁ (fun I => rowWeight η (fixedBadMask*u₁) 1 1 t I*
        (leftCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₁ (primaryGenerator I))) W K =
        sourceGaussEnergy Q₁ (maskedSource u₁ β₁) (heightCoeff τ₁ t) W K ∧
      sourceGaussEnergy Q₂ β₂ (fun I => rowWeight η (fixedBadMask*u₂) 1 1 t I*
        (rightCoefficient e r ρ (primaryGenerator I)*rayCharacter ξ₂ (primaryGenerator I))) W K =
        sourceGaussEnergy Q₂ (maskedSource u₂ β₂) (heightCoeff τ₂ t) W K := by
  obtain ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,_,_⟩ := exists_canonical_masked_pair η C D hC E ξ₁ ξ₂
  refine ⟨τ₁,τ₂,hM₁,hM₂,h₁,h₂,?_⟩
  intro Q₁ Q₂ β₁ β₂ u₁ u₂ t W K
  constructor
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₁ I hI t,h₁ I hI t]
    dsimp only [maskedSource]
    ring
  · apply sourceGaussEnergy_congr
    intro I _ hI
    rw [rowWeight_mask_factor η u₂ I hI t,h₂ I hI t]
    dsimp only [maskedSource]
    ring

def rayHeight (p : O) (k : ℕ) (τ : RayCharacter → Character) (t : ℝ) (I : Ideal O) : ℂ :=
  ∑ χ : RayCharacter,phaseCoeff (amplificationPhase p k) χ*heightCoeff (τ χ) t I

def extractedSource (η : Character) (u : O) (C : Ideal O)
    (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t C*idealMask u I

theorem exists_masked_radical_family (η : Character) (p : O)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1) (k : ℕ) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤radicalBound (childCharacter η χ) fixedBadMask p k) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryGenerator I)=
          rayHeight p k τ t I) ∧
      (∀ u : O, ∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η (fixedBadMask*u) 1 1 t I*residualCharacter p k (primaryGenerator I)=
          idealMask u I*rayHeight p k τ t I) ∧
      ∀ (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy Q (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p k (primaryGenerator I)) W K =
        sourceGaussEnergy Q (extractedSource η u C β t) (rayHeight p k τ t) W K := by
  obtain ⟨τ,hN,hτ⟩ := exists_radical_family η fixedBadMask p fixed_mask_ne_zero hs hpp
    (dvd_mul_right goodLambda (2:O)) (dvd_mul_left (2:O) goodLambda) k
  refine ⟨τ,hN,hτ,?_,?_⟩
  · intro u I hI t
    rw [rowWeight_mask_factor η u I hI t,mul_assoc,hτ I hI t]
    rfl
  · intro Q u C β t W K
    apply sourceGaussEnergy_congr
    intro I _ hI
    rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
    rfl

theorem exists_masked_error_source (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      (∀ I : Ideal O, Supported I → ∀ t : ℝ,
        rowWeight η fixedBadMask 1 1 t I*
          residualCharacter p (errorMovingExponent n) (primaryGenerator I)=
            rayHeight p (errorMovingExponent n) τ t I) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ)
        (t : ℝ) (W : 𝓢(ℝ,ℂ)) (K : ℝ),
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (fun I => β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))
          (fun I => residualCharacter p (n+1) (primaryGenerator I)) W K =
        sourceGaussEnergy (residualColumns S p hp (n+1))
          (extractedSource η u C β t) (rayHeight p (errorMovingExponent n) τ t) W K := by
  obtain ⟨τ,hN,hτ,_,henergy⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,hτ,?_⟩
  intro S u C β t W K
  rw [←henergy (residualColumns S p hp (n+1)) u C β t W K]
  apply sourceGaussEnergy_congr
  intro I hI _
  rw [residual_column_active S p hp hs n hn I hI]

lemma idealMask_mul (u : O) (C I : Ideal O) :
    idealMask u (C*I)=idealMask u C*idealMask u I := by
  simp only [idealMask,IsCoprime.mul_left_iff]
  split_ifs <;> simp_all

lemma extractedSource_whole_mask (η : Character) (u : O) (C : Ideal O)
    (hC : Supported C) (β : Ideal O → ℂ) (t : ℝ) (I : Ideal O) :
    extractedSource η u C β t I =
      maskedSource u β (C*I)*rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource,rowWeight_mask_factor η u C hC t,maskedSource,idealMask_mul]
  ring

lemma extracted_gauss_row (η : Character) (p : O) (k : ℕ) (τ : RayCharacter → Character)
    (hτ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      rowWeight η fixedBadMask 1 1 t I*residualCharacter p k (primaryGenerator I)=
        rayHeight p k τ t I)
    (Q : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
      (fun I : supportedColumns Q =>
        (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
          residualCharacter p k (primaryGenerator I)) z =
    ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p k) χ *
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  rw [←gaussPolynomial_allocation]
  apply congrArg (fun c => gaussPolynomial Finset.univ (sourceGenerator Q)
    (sourceGenerator_supported Q) c z)
  funext I
  have hI := (Finset.mem_filter.mp I.property).2
  rw [extracted_masked_coefficient η u C I hI β t,hτ I hI t]
  simp only [rayHeight,Finset.mul_sum,extractedSource]
  apply Finset.sum_congr rfl
  intro χ _
  ring

theorem exists_masked_error_rows (η : Character) (p : O) (hp : Prime p)
    (hs : Supported (Ideal.span {p})) (hpp : goodLambda^2∣p-1)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤
        radicalBound (childCharacter η χ) fixedBadMask p (errorMovingExponent n)) ∧
      ∀ (S : Finset (Ideal O)) (u : O) (C : Ideal O) (β : Ideal O → ℂ) (t : ℝ) (z : O),
      let Q := residualColumns S p hp (n+1)
      gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
        (fun I : supportedColumns Q =>
          (β (C*I)*rowWeight η (fixedBadMask*u) 1 1 t (C*I))*
            residualCharacter p (n+1) (primaryGenerator I)) z =
      ∑ χ : RayCharacter, phaseCoeff (amplificationPhase p (errorMovingExponent n)) χ *
        gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
          (fun I : supportedColumns Q => extractedSource η u C β t I*heightCoeff (τ χ) t I) z := by
  obtain ⟨τ,hN,hτ,_,_⟩ := exists_masked_radical_family η p hs hpp (errorMovingExponent n)
  refine ⟨τ,hN,?_⟩
  intro S u C β t z
  dsimp only
  rw [←extracted_gauss_row η p (errorMovingExponent n) τ hτ
    (residualColumns S p hp (n+1)) u C β t z]
  apply congrArg (fun c => gaussPolynomial Finset.univ
    (sourceGenerator (residualColumns S p hp (n+1)))
    (sourceGenerator_supported (residualColumns S p hp (n+1))) c z)
  funext I
  rw [residual_column_active S p hp hs n hn I (Finset.mem_filter.mp I.property).1]

lemma paired_gauss_rows (η τ₁ τ₂ : Character) (F₁ F₂ : O → ℂ)
    (h₁ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₁ t I=rowWeight η fixedBadMask 1 1 t I*F₁ (primaryGenerator I))
    (h₂ : ∀ I : Ideal O, Supported I → ∀ t : ℝ,
      heightCoeff τ₂ t I=rowWeight η fixedBadMask 1 1 t I*F₂ (primaryGenerator I))
    (Q₁ Q₂ : Finset (Ideal O)) (β₁ β₂ : Ideal O → ℂ) (u₁ u₂ : O) (t : ℝ) (z₁ z₂ : O) :
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => β₁ I*
        (rowWeight η (fixedBadMask*u₁) 1 1 t I*F₁ (primaryGenerator I))) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => β₂ I*
        (rowWeight η (fixedBadMask*u₂) 1 1 t I*F₂ (primaryGenerator I))) z₂) =
    gaussPolynomial Finset.univ (sourceGenerator Q₁) (sourceGenerator_supported Q₁)
      (fun I : supportedColumns Q₁ => maskedSource u₁ β₁ I*heightCoeff τ₁ t I) z₁ *
    star (gaussPolynomial Finset.univ (sourceGenerator Q₂) (sourceGenerator_supported Q₂)
      (fun I : supportedColumns Q₂ => maskedSource u₂ β₂ I*heightCoeff τ₂ t I) z₂) := by
  rw [first_gauss_row η τ₁ F₁ h₁ Q₁ β₁ u₁ t z₁,
    first_gauss_row η τ₂ F₂ h₂ Q₂ β₂ u₂ t z₂]

end SevenEighths.CenteredMomentFirstMaskedFamily

end

end OAI
end OAIOriginalModule2157

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMaskedInput
Source SHA256: 6ab20ce52e05c5917935dbc4bdded2b86930fb86392c8e2324cc6ea1ad36fbcb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2158




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstMaskedInput
open HeckeFamily CanonicalQuadraticSieve ConcretePrimeRowBridge
open CenteredMomentFirstMaskedFamily CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentAddedZeroUniform CenteredMomentAmplificationLiveMask
open CenteredMomentAmplificationChildInput CenteredMomentFirstAmplificationChoice
open CenteredMomentCommonRadialData CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentRemainingBox
open CenteredMomentSourceLiveColumn CenteredMomentSecondHeightFamily
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]
local instance {κ : Type*} : DecidableEq κ := Classical.decEq _
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

lemma profile_combined_mask (R T seed : Ideal O) (ν : ι→Ideal O→ℂ)
    (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) (v : Tuple ι) :
    profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v *
      idealMask (idealGenerator T) (finiteTupleProduct v) =
    profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed v := by
  rw [idealMask_generator]
  simp only [profileCoefficient, IsCoprime.mul_right_iff]
  split_ifs <;> simp_all

lemma column_combined_mask (S : Finset (Tuple ι)) (R T seed : Ideal O)
    (ν : ι→Ideal O→ℂ) (Wslot : ι→ℝ→ℂ) (P : ι→ℝ) (W₁ W₂ : ℝ→ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ : Ideal O) :
    maskedSource (idealGenerator T)
      (finiteColumnCoefficient S (profileCoefficient R ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed)) =
    finiteColumnCoefficient S (profileCoefficient (R*T) ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ seed) := by
  funext I
  unfold maskedSource finiteColumnCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro v hv
  rw [←(Finset.mem_filter.mp hv).2]
  exact profile_combined_mask R T seed ν Wslot P W₁ W₂ X₁ X₂ Y₁ Y₂ B₁ B₂ v

lemma input_combined_mask (s : Input ι) (R T seed : Ideal O) :
    maskedSource (idealGenerator T) (original s R seed).beta =
      (original s (R*T) seed).beta := by
  simpa only [OriginalData.beta, OriginalData.profile, original] using
    column_combined_mask (Fintype.piFinset s.pools) R T seed s.ν s.W s.P
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1

lemma extracted_input (s : Input ι) (η : Character) (R T seed C : Ideal O)
    (hC : Supported C) (t : ℝ) (I : Ideal O) :
    extractedSource η (idealGenerator T) C (original s R seed).beta t I =
      (original s (R*T) seed).beta (C*I) * rowWeight η fixedBadMask 1 1 t C := by
  rw [extractedSource_whole_mask η (idealGenerator T) C hC, input_combined_mask]
  rfl

theorem extracted_input_allocations (s : Input ι) (η τ : Character)
    (R T seed C I : Ideal O) (hC : Supported C) (hI : I≠0)
    (hseed : IsCoprime seed C) (t : ℝ) :
    (if IsCoprime C I then
      extractedSource η (idealGenerator T) C (original s R seed).beta t I else 0) =
    rowWeight η fixedBadMask 1 1 t C *
      ∑ B : actualAllocations s.pools C,
        frozenCoefficient B C (R*T) s.ν s.W s.P *
          (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta I := by
  have hh := original_masked_live_column s.pools s.pools_ne
    (fun i J hJ => s.prime i J hJ) C (R*T) seed I hC.1 hI hseed
    s.ν s.W s.P s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1
  rw [extracted_input s η R T seed C hC t I]
  calc
    _ = rowWeight η fixedBadMask 1 1 t C *
        (if IsCoprime C I then (original s (R*T) seed).beta (C*I) else 0) := by
      split_ifs <;> ring
    _ = rowWeight η fixedBadMask 1 1 t C *
        ∑ B : actualAllocations s.pools C, frozenCoefficient B C (R*T) s.ν s.W s.P *
          finiteColumnCoefficient
            (liveBox s.pools B (allocation_data s.pools C B (Finset.mem_filter.mp B.property).1).1)
            (maskedLiveProfile B C (R*T) seed s.ν s.W s.P s.W₁ s.W₂
              s.X₁ s.X₂ s.Y₁ s.Y₂ 1 1) I := by
      exact congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z) hh
    _ = _ := by
      apply congrArg (fun z : ℂ => rowWeight η fixedBadMask 1 1 t C * z)
      apply Finset.sum_congr rfl
      intro B _
      exact congrArg (fun z : ℂ => frozenCoefficient B C (R*T) s.ν s.W s.P * z)
        (congrFun (child_columns s C (R*T) seed B τ t).2 I)

lemma normalized_input_mask (s : Input ι) (R T seed : Ideal O)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original s R seed).columns
      (maskedSource (idealGenerator T) (original s R seed).beta)
      (heightCoeff s.η s.t) W K).re / volume s =
      normalizedGaussSource s (R*T) seed W K := by
  rw [input_combined_mask]
  rfl

lemma child_input_combined_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ) :
    maskedSource (idealGenerator T)
      (original (child s C R B τ t) (R*C) seed).beta =
      (original (child s C (R*T) B τ t) ((R*T)*C) seed).beta := by
  rw [input_combined_mask]
  simp only [OriginalData.beta, OriginalData.profile, original, child, commonData, Input.pools,
    mul_assoc, mul_comm C T]

lemma normalized_child_mask (s : Input ι) (C R T seed : Ideal O)
    (B : actualAllocations s.pools C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    (sourceGaussEnergy (original (child s C R B τ t) (R*C) seed).columns
      (maskedSource (idealGenerator T)
        (original (child s C R B τ t) (R*C) seed).beta)
      (heightCoeff τ t) W K).re / volume (child s C R B τ t) =
      childNormalizedGaussSource s C (R*T) seed B τ t W K := by
  have hcolumns :
      (original (child s C R B τ t) (R*C) seed).columns =
        (original (child s C (R*T) B τ t) ((R*T)*C) seed).columns :=
    (child_columns s C R seed B τ t).1.symm.trans (child_columns s C (R*T) seed B τ t).1
  have hvolume : volume (child s C R B τ t) = volume (child s C (R*T) B τ t) := by
    simp only [volume, child, commonData]
  unfold childNormalizedGaussSource normalizedGaussSource
  rw [child_input_combined_mask, hcolumns, hvolume, child_character, child_height]

end SevenEighths.CenteredMomentFirstMaskedInput

end

end OAI
end OAIOriginalModule2158

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalDyadicRows
Source SHA256: bb293402f045ee53be0c4eef0bf33b0867f5e81decb392928e664b728313b913
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2159



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstPhysicalDyadicRows
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge
open HeckeFamily CanonicalQuadraticSieve
open CenteredMomentFirstPhysicalSource CenteredMomentCanonicalFirst
open CenteredMomentFirstWholeKernel CenteredMomentLogDyadic CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm
local notation "O" => HeckeFamily.O

def activeRows (rows : Finset O) (n : Fin 4→ℤ) : Finset O :=
  rows.filter (fun h => h∈dyadRows (n 1))

lemma mem_activeRows (rows : Finset O) (n : Fin 4→ℤ) (h : O) :
    h∈activeRows rows n ↔ h∈rows ∧ dyadicWeight (n 1) (normValue h)≠0 := by
  simp only [activeRows,Finset.mem_filter,mem_dyadRows]

lemma activeRows_subset (rows : Finset O) (n : Fin 4→ℤ) : activeRows rows n⊆rows :=
  Finset.filter_subset _ _

lemma activeRows_nonzero (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) : h≠0 :=
  dyadRows_ne_zero (n 1) h (Finset.mem_filter.mp hh).2

lemma activeRows_norm (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤normValue h ∧ dyadicScale (n 1)/4<normValue h ∧ normValue h<dyadicScale (n 1) :=
  ⟨normValue_ge_one h (activeRows_nonzero rows n h hh),
    dyadicWeight_support (n 1) ((mem_activeRows rows n h).mp hh).2⟩

lemma activeRows_scale_gt_one (rows : Finset O) (n : Fin 4→ℤ)
    (hne : (activeRows rows n).Nonempty) : 1<dyadicScale (n 1) := by
  obtain ⟨h,hh⟩:=hne
  exact (activeRows_norm rows n h hh).1.trans_lt (activeRows_norm rows n h hh).2.2

lemma activeRows_ball_majorant (rows : Finset O) (n : Fin 4→ℤ) (h : O)
    (hh : h∈activeRows rows n) :
    1≤(ballProfile (‖eisEmbedding h‖^2/dyadicScale (n 1))).re :=
  ballProfile_majorizes _ (dyadicScale_pos (n 1)) h (activeRows_norm rows n h hh).2.2.le

lemma row_log_window (n : ℤ) (h : O) :
    logAnnulus (Real.log (‖eisEmbedding h‖^2/dyadicScale n)) =
      (dyadicWeight n (normValue h):ℂ) := by
  by_cases hh : h=0
  · subst h
    simp only [map_zero,norm_zero,zero_pow (by decide : 2≠0),zero_div,Real.log_zero,
      logAnnulus,Real.exp_zero]
    rw [annulus_zero_high 1 le_rfl]
    rw [show normValue (0:O)=0 by simp [normValue_eq_embedding],
      dyadicWeight_zero_nonpos n 0 le_rfl,Complex.ofReal_zero]
  · rw [←normValue_eq_embedding]
    exact (actual_dyadic_log_window n (normValue h)
      (zero_lt_one.trans_le (normValue_ge_one h hh))).symm

theorem block_activeRows (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O→ℂ) (C D : Ideal O)
    (hC : Supported C) (hD : Supported D) (E : Finset (CommonIndex C D))
    (rows : Finset O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (n : Fin 4→ℤ) :
    block η m A t S c C D hC hD E rows W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) =
    block η m A t S c C D hC hD E (activeRows rows n) W (fun _=>logAnnulus) K
      (dyadicScale (n 0)) (dyadicScale (n 1)) (dyadicScale (n 2)) (dyadicScale (n 3)) := by
  unfold block activeRows
  dsimp only
  rw [Finset.sum_filter]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  by_cases hd : h∈dyadRows (n 1)
  · simp only [hd,ite_true]
  · have hw : dyadicWeight (n 1) (normValue h)=0 := by
      simpa only [mem_dyadRows,not_not] using hd
    simp only [hd,windows,row_log_window,hw,Complex.ofReal_zero,
      mul_zero,zero_mul,ite_self,Finset.sum_const_zero]

end SevenEighths.CenteredMomentFirstPhysicalDyadicRows

end

end OAI
end OAIOriginalModule2159

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAmplifiedRadiusLower
Source SHA256: 4a088d33d2386ad17e18ecd8252b76cd1d0ae116b09616915bc0f82ef8da6175
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2160



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstAmplifiedRadiusLower
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstScale
open CenteredMomentFirstPhysicalDyadicRows
local notation "O" => ActualEisensteinCubic.O

lemma base_radius_identity (Z K0 Csec xi : ℝ) (hZ : 1<Z) (hC : 0<Csec) :
    Z^(K0+frequencyLoss Z (32*Csec) xi)=128*Csec*Z^K0*Z^(xi/2) := by
  have h := source_enclosure_power Z (32*Csec) K0 xi 1 hZ (by positivity) zero_lt_one
  simpa only [Real.logb_one,sub_zero,div_one] using h.symm.trans (by ring)

lemma retained_base_le (Z K0 Csec Tsec xi H0 : ℝ) (hZ : 1<Z) (hC : 0<Csec)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi) :
    H0≤Z^(K0+frequencyLoss Z (32*Csec) xi) := by
  rw [base_radius_identity Z K0 Csec xi hZ hC]
  have hp : 0≤Z^(xi/2) := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  have hq : 0≤Z^K0 := Real.rpow_nonneg (zero_lt_one.trans hZ).le _
  calc
    H0≤4*(Tsec*Z^(xi/2)) := hrow
    _≤4*((Csec*Z^K0)*Z^(xi/2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsec hp) (by norm_num)
    _≤128*Csec*Z^K0*Z^(xi/2) := by nlinarith [mul_nonneg (mul_nonneg hC.le hq) hp]

theorem common_radii_lower (Z d K0 c sigma reserve Csec Tsec xi H0 : ℝ)
    (hZ : 1<Z) (hC : 0<Csec) (hsigma : 0≤sigma) (hreserve : 0≤reserve)
    (hsec : Tsec≤Csec*Z^K0) (hrow : H0≤4*frequencyRadius Tsec Z xi)
    (p : O) (k : ℕ) :
    H0≤mainCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve ∧
    H0≤errorCommonRadius Z d K0 c sigma (frequencyLoss Z (32*Csec) xi) reserve p k := by
  have hb := retained_base_le Z K0 Csec Tsec xi H0 hZ hC hsec hrow
  constructor
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c) (0:ℝ)]
  · apply hb.trans
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith [le_max_right (d-c-2*errorRemoval p Z k+errorMoving p Z k) (0:ℝ)]

theorem actual_retained_radii_lower (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤sigma) (hreserve : 0≤reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z xi) n) (p : O) (k : ℕ) :
    dyadicScale n≤mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve ∧
    dyadicScale n≤errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k := by
  apply common_radii_lower Z d _ c sigma reserve Csec Tsec xi _ hZ hC hsigma hreserve
  · simpa only [nominalLog,Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
      (firstNominalScale_pos I J E hE K X hK hX)] using hsec
  · exact retained_scale_le _ n hn

theorem active_row_reciprocals (I J E : Ideal O) (hE : E≠0)
    (K X Z Csec Tsec xi d c sigma reserve : ℝ)
    (hK : 0<K) (hX : 0<X) (hZ : 1<Z) (hC : 0<Csec)
    (hsigma : 0≤sigma) (hreserve : 0≤reserve)
    (hsec : Tsec≤Csec*firstNominalScale I J E K X)
    (rows : Finset O) (n : Fin 4→ℤ)
    (hn : Retained (frequencyRadius Tsec Z xi) (n 1))
    (hne : (activeRows rows n).Nonempty) (p : O) (k : ℕ) :
    (mainCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve)⁻¹≤1 ∧
    (errorCommonRadius Z d (nominalLog I J E K X Z) c sigma
      (frequencyLoss Z (32*Csec) xi) reserve p k)⁻¹≤1 := by
  have hb := actual_retained_radii_lower I J E hE K X Z Csec Tsec xi d c sigma reserve
    hK hX hZ hC hsigma hreserve hsec (n 1) hn p k
  have ho := (activeRows_scale_gt_one rows n hne).le
  exact ⟨inv_le_one_of_one_le₀ (ho.trans hb.1),inv_le_one_of_one_le₀ (ho.trans hb.2)⟩

end SevenEighths.CenteredMomentFirstAmplifiedRadiusLower

end

end OAI
end OAIOriginalModule2160

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstPhysicalSourceOriginalData
Source SHA256: 6033e5a0b5e9fb5bac6c274164d1ab05f77b528fc2a802d55d414ea5762532a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2161







namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstPhysicalSource
open HeckeFamily CanonicalQuadraticSieve CenteredMomentSourceRow
open CenteredMomentFirstAmplificationChoice CenteredMomentFirstSectors
open CenteredMomentSourceLiveColumn CenteredMomentCommonAllocationSum CenteredMomentCommonProfile
open CenteredMomentSourceMass CenteredMomentSourceProfileMass CenteredMomentAddedZeroUniform
open CenteredMomentAmplificationLiveMask CenteredMomentLiveDomain CenteredMomentRemainingBox
open CenteredMomentGaussEnergy CenteredMomentSourceAllocationEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentSecondHeightFamily CenteredMomentCommonPuncture CenteredMomentOriginalChildEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι]
local instance : DecidableEq (ι⊕Fin 2):=Classical.decEq _

def allocatedData (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    OriginalData (liveIndices B.val) where
  S:=remainingSets B.val (fun i=>residualPool (B.val i)
    ((allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 i) (D.S i))
  R:=D.R*C
  s:=L
  nu:=fun i=>D.nu i.val
  slot:=fun i=>D.slot i.val
  lengths:=fun i=>D.lengths i.val
  W₁:=D.W₁
  W₂:=D.W₂
  X₁:=D.X₁
  X₂:=D.X₂
  Y₁:=D.Y₁
  Y₂:=D.Y₂
  B₁:=D.B₁*B.val (Sum.inr 0)
  B₂:=D.B₂*B.val (Sum.inr 1)

lemma allocated_pools (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    Fintype.piFinset (allocatedData D C L B).S=
      liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1:=rfl

lemma allocated_profile (D:OriginalData ι)(C L:Ideal O)(B:actualAllocations D.S C):
    (allocatedData D C L B).profile=maskedLiveProfile B.val C D.R L D.nu D.slot D.lengths
      D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂:=rfl

def commonGauss (D:OriginalData ι)(C:Ideal O)(hC:Supported C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):ℂ:=
  let Q:=residualPool C hC.1 D.columns
  gaussPolynomial Finset.univ (sourceGenerator Q) (sourceGenerator_supported Q)
    (fun I:supportedColumns Q=>(if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O)
      then D.beta (C*I) else 0)*heightCoeff τ t I) z

theorem common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t:ℝ)(L:Ideal O)(z:O):
    commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          (fun I=>((allocatedData D C L B).beta I)*heightCoeff τ t I) z:=by
  let Q:=residualPool C hC.1 D.columns
  let b:=fun B:actualAllocations D.S C=>frozenCoefficient B.val C D.R D.nu D.slot D.lengths
  let d:=fun (B:actualAllocations D.S C)(I:supportedColumns Q)=>
    finiteColumnCoefficient (liveBox D.S B.val (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1)
      (liveProfile B.val C D.R D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂) I*
        ((if L∣(I:Ideal O) then 1 else 0)*heightCoeff τ t I)
  have he (I:supportedColumns Q):
      (if IsCoprime C (I:Ideal O) ∧ L∣(I:Ideal O) then D.beta (C*I) else 0)*heightCoeff τ t I=
        ∑B,b B*d B I:=by
    have hc:=original_source_punctured_column D.S hS hp C D.R D.s I hC.1
      (Finset.mem_filter.mp I.property).2.1 hseed D.nu D.slot D.lengths D.W₁ D.W₂
      D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    change (if IsCoprime C (I:Ideal O) then D.beta (C*I) else 0)=_ at hc
    by_cases hl:L∣(I:Ideal O)
    · simp only [hl,and_true]
      change (if IsCoprime C (I:Ideal O) then _ else 0)*heightCoeff τ t I=_
      rw [hc,Finset.sum_mul]
      simp only [b,d,hl,ite_true,one_mul,mul_assoc]
    · simp only [hl,and_false,ite_false,zero_mul,b,d,mul_zero,Finset.sum_const_zero]
  unfold commonGauss
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ _ z=_
  rw [funext he,gaussPolynomial_allocation]
  apply Finset.sum_congr rfl
  intro B hB
  apply congrArg (fun w:ℂ=>b B*w)
  have hh:=live_gaussPolynomial D.S hS hp B.val
    (allocation_data D.S C B (Finset.mem_filter.mp B.property).1).1 C D.R hC
    (Finset.mem_filter.mp B.property).1 (Finset.mem_filter.mp B.property).2
    D.nu D.slot D.lengths D.W₁ D.W₂ D.X₁ D.X₂ D.Y₁ D.Y₂ D.B₁ D.B₂
    (fun I=>(if L∣I then 1 else 0)*heightCoeff τ t I) z
  change gaussPolynomial Finset.univ (sourceGenerator Q) _ (d B) z=_ at hh
  rw [hh]
  congr 1
  funext I
  change _=finiteColumnCoefficient _ (allocatedData D C L B).profile I*heightCoeff τ t I
  rw [allocated_profile,maskedLiveProfile,column_mask]
  dsimp only [liveProfile]
  rw [allocated_pools]
  ring

theorem normalized_common_gauss_allocation (D:OriginalData ι)
    (hS:∀i,∀I∈D.S i,I≠0)(hp:∀i,∀I∈D.S (Sum.inl i),Prime I)
    (C:Ideal O)(hC:Supported C)(hseed:D.s∣C)(τ:Character)(t T:ℝ)(L:Ideal O)(z:O):
    (Real.sqrt T:ℂ)⁻¹*commonGauss D C hC τ t L z=
      ∑B:actualAllocations D.S C,frozenCoefficient B.val C D.R D.nu D.slot D.lengths*
        gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
          (sourceGenerator_supported (allocatedData D C L B).columns)
          ((allocatedData D C L B).coefficient τ fixedBadMask t T) z:=by
  rw [common_gauss_allocation D hS hp C hC hseed τ t L z,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro B hB
  simp only [OriginalData.coefficient,gaussPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [heightCoeff_eq_fixed_rowWeight τ t I (Finset.mem_filter.mp I.property).2]
  ring

end SevenEighths.CenteredMomentFirstPhysicalSource

end

end OAI
end OAIOriginalModule2161

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstAllocationGaussEnergy
Source SHA256: 2576d7d093bc613f2913be7fe0bfa7a9e6e09d713576656f1b9a80318a57e613
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2162



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentFirstAllocationGaussEnergy
open HeckeFamily CanonicalQuadraticSieve CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalSource CenteredMomentSourceRow
open CenteredMomentCommonAllocationSum CenteredMomentSourceLiveColumn
open CenteredMomentCommonRawScale CenteredMomentAddedZeroUniform
open CenteredMomentGaussEnergy CenteredMomentSmoothedWindowEnergy
open CenteredMomentOriginalChildEnergy CenteredMomentHeckeColumnWindow
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

def commonEnergy (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑' z : O, ‖commonGauss D C hC τ t L z‖^2 *
    (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re

def allocatedEnergy (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  (sourceGaussEnergy (allocatedData D C L B).columns
    (allocatedData D C L B).beta (heightCoeff τ t) W K).re

lemma common_summable (D : OriginalData ι) (C : Ideal O) (hC : Supported C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    Summable (fun z : O => ‖commonGauss D C hC τ t L z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
  exact (gaussEnergy_hasSum_re Finset.univ
    (sourceGenerator (CenteredMomentFirstSectors.residualPool C hC.1 D.columns))
    (sourceGenerator_supported _) _ W K hK).summable

lemma allocated_hasSum (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O =>
      ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
        (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
      (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
      (allocatedEnergy D C L B τ t W K) :=
  gaussEnergy_hasSum_re _ _ _ _ W K hK

lemma allocated_nonneg (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (τ : Character) (t : ℝ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    0≤allocatedEnergy D C L B τ t W K := by
  rw [← (allocated_hasSum D C L B τ t W K hK).tsum_eq]
  exact tsum_nonneg (fun z => mul_nonneg (sq_nonneg _) (hW z))

theorem common_energy_allocation (D : OriginalData ι)
    (hS : ∀ i, ∀ I∈D.S i, I≠0) (hp : ∀ i, ∀ I∈D.S (Sum.inl i), Prime I)
    (C : Ideal O) (hC : Supported C) (hseed : D.s∣C)
    (τ : Character) (t : ℝ) (L : Ideal O) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hW : ∀ z : O, 0≤(W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) :
    commonEnergy D C hC τ t L W K ≤
      ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 * allocatedEnergy D C L B τ t W K := by
  unfold commonEnergy
  apply Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hW z))
  intro rows
  calc
    _ ≤ ∑ z∈rows, ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          (‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
          (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) := by
      apply Finset.sum_le_sum
      intro z hz
      rw [common_gauss_allocation D hS hp C hC hseed τ t L z]
      have hc := mul_le_mul_of_nonneg_right
        (CubicEisenstein.norm_sum_sq_le_card Finset.univ
          (fun B : actualAllocations D.S C =>
            frozenCoefficient B.val C D.R D.nu D.slot D.lengths *
              gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
                (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z))
        (hW z)
      simpa only [Finset.card_univ,Fintype.card_coe,norm_mul,mul_pow,Finset.sum_mul,mul_assoc] using hc
    _ = ((actualAllocations D.S C).card:ℝ) * ∑ B : actualAllocations D.S C,
        ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖^2 *
          ∑ z∈rows, ‖gaussPolynomial Finset.univ (sourceGenerator (allocatedData D C L B).columns)
            (sourceGenerator_supported _) (fun I => (allocatedData D C L B).beta I * heightCoeff τ t I) z‖^2 *
            (W (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Finset.sum_le_sum
      intro B hB
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
      exact sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z))
        (allocated_hasSum D C L B τ t W K hK)

def rawVolume (D : OriginalData ι) : ℝ :=
  (D.X₁*D.X₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂)) * ∏ i,D.lengths i

lemma rawVolume_pos (D : OriginalData ι) (hX₁ : 0<D.X₁) (hX₂ : 0<D.X₂)
    (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) (hP : ∀ i,0<D.lengths i) : 0<rawVolume D := by
  apply mul_pos (div_pos (mul_pos hX₁ hX₂) _)
    (Finset.prod_pos (fun i _ => hP i))
  exact mul_pos (CenteredMomentFirstScale.norm_pos _ hB₁) (CenteredMomentFirstScale.norm_pos _ hB₂)

lemma allocated_rawVolume_mul (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0) :
    rawVolume (allocatedData D C L B) * rawReduction B.val D.lengths = rawVolume D := by
  have hB := (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1
  have hv := remainingRaw_source B.val hB D.B₁ D.B₂ hB₁ hB₂ (D.X₁*D.X₂) D.lengths
  change _ = rawVolume (allocatedData D C L B) at hv
  rw [← hv]
  exact raw_scale_identity B.val hB _ D.lengths

lemma allocated_rawVolume (D : OriginalData ι) (C L : Ideal O)
    (B : actualAllocations D.S C) (hB₁ : D.B₁≠0) (hB₂ : D.B₂≠0)
    (hP : ∀ i,0<D.lengths i) :
    rawVolume (allocatedData D C L B) = rawVolume D / rawReduction B.val D.lengths := by
  have hr := rawReduction_pos B.val
    (allocation_data D.S C B.val (Finset.mem_filter.mp B.property).1).1 D.lengths hP
  exact (eq_div_iff hr.ne').mpr (allocated_rawVolume_mul D C L B hB₁ hB₂)

lemma rawVolume_both (D : OriginalData ι) (T : ℝ)
    (hX : D.X₁*D.X₂=T) (hY : D.Y₁*D.Y₂=T) :
    rawVolume D=(T/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i ∧
    rawVolume D=(D.Y₁*D.Y₂/((Ideal.absNorm D.B₁:ℝ)*Ideal.absNorm D.B₂))*∏ i,D.lengths i := by
  simp only [rawVolume,hX,hY,and_self]

def frozenControl (B : Tuple ι) (M : ι → ℝ) : ℝ :=
  ∏ i∈Finset.univ.filter (fun i => B (Sum.inl i)≠1),M i

lemma frozenControl_nonneg (B : Tuple ι) (M : ι → ℝ)
    (hM : ∀ i,0≤M i) : 0≤frozenControl B M :=
  Finset.prod_nonneg (fun i _ => hM i)

lemma frozen_norm_bound (D : OriginalData ι) (C : Ideal O)
    (B : actualAllocations D.S C) (M : ι → ℝ) (_hM : ∀ i,0≤M i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hW : ∀ i x,‖D.slot i x‖≤M i) :
    ‖frozenCoefficient B.val C D.R D.nu D.slot D.lengths‖≤frozenControl B.val M := by
  unfold frozenCoefficient frozenControl
  rw [norm_mul]
  have hc : ‖(if IsCoprime C D.R then (1:ℂ) else 0)‖≤1 := by split_ifs <;> simp
  apply (mul_le_of_le_one_right (norm_nonneg _) hc).trans
  rw [norm_prod]
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
  intro i hi
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hν i _)).trans (hW i _)

theorem frozen_normalized_bound (N : ℕ) (a b : ℝ) (ha : 0<a)
    (D : OriginalData ι) (hcard : Fintype.card ι≤N)
    (C : Ideal O) (hC : C≠0) (B : actualAllocations D.S C)
    (M : ι → ℝ) (hM : ∀ i,0≤M i) (hP : ∀ i,0<D.lengths i)
    (hν : ∀ i I,‖D.nu i I‖≤1) (hWnorm : ∀ i x,‖D.slot i x‖≤M i)
    (hW : ∀ i,Function.support (D.slot i)⊆Set.Icc a b) :
