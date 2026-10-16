        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (K : Finset ι → Finset ι → Finset O) (Z H M : ℝ) (j : SecondLogIndex)
        (s : Finset (SecondExpansionData ι)),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        s ⊆ secondLogSector p ∅ F K R Z M j →
        let X := initialLogColumn Z (primeProductNorm p R) j
        let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
        ∃ B : Frequency → ℝ,
          (∀ q, 0 ≤ B q) ∧
          (∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray s
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) W H‖ ≤
          (C*H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
            (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
              sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
                (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_sector_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F R Ψ m ray K Z H M j s hZ hH hΨ hsub
  dsimp only
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let X := initialLogColumn Z (primeProductNorm p R) j
  have hR : 0 < primeProductNorm p R := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hs : ∀ x ∈ s, InSecondQuotientSector p r x := by
    intro x hx
    exact secondExpansionSector_valid p F (fun G E => (K G E).erase 0) R x
      (secondLogSector_subset p ∅ F K R Z M j (hsub hx))
  have hk : ∀ x ∈ s, x.frequency ≠ 0 := by
    intro x hx
    exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp (hsub hx)).1).2.2.2.1
  have hcoords := initial_sector_coordinates p hp F R K Z M hZ j
  obtain ⟨B,hB,hdec,hbound⟩ := ht p hp hcop hg hinj hc hpr F Ψ m r ray s Z H
    (secondLogE j) (secondLogV j) X (secondLogK j) hZ hH
    (normLogScale_pos _) (normLogScale_pos _) hX (normLogScale_pos _) hΨ hs hk
    (fun x hx => (hcoords x (hsub hx)).1) (fun x hx => (hcoords x (hsub hx)).2.1)
    (fun x hx => (hcoords x (hsub hx)).2.2.1) (fun x hx => (hcoords x (hsub hx)).2.2.2)
  refine ⟨B,hB,?_,?_⟩
  · simpa only [X, initial_log_radial Z H (primeProductNorm p R) hZ.ne' hR.ne'] using hdec
  · simpa only [r, elementNorm, primeSubsetGenerator_norm_eq_productNorm] using hbound

end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialBinCost_of_canonical_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := secondLogSector p ∅ F K R Z M j
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j)^2)*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := secondLogSector p ∅ F K R Z M j
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X
  let E := Cchild*(X*initialLogLabel j)^2
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hpR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hpR)
  have hlabel : 0 < initialLogLabel j := by
    unfold initialLogLabel secondLogE secondLogV
    exact mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) (Real.exp_pos _)
  have hE : 0 ≤ E := mul_nonneg hCc (sq_nonneg _)
  have hS : 0 < S := by
    dsimp [S]
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  have hG : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    intro q
    exact (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X q).trans (hchild q)
  have hb := polynomial_density_cost B G J S Cₛ E hS hCₛ hE hB hG hdec henergy
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3) := mul_le_mul_of_nonneg_left hb hpref
    _ = _ := by
      dsimp only [E,X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hpR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by
        rw [pow_two,←Real.exp_add]
        norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hpR.ne'
      field_simp

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0211

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.DiagonalDensity
Source SHA256: fe5c40e52effbe06e56ca897b86b56ff3e69513df6259e1ce2f366bb3da0f045
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0212


namespace OAI

noncomputable section

namespace InitialMeanSquare

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical SchwartzMap ContDiff

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open EisensteinSchwartzPoisson (paperRadialFourier)

theorem initial_diagonal_fixed_profile (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ m c d
        (fun S => star (normalizedColumn p (fun T => g (columnLog p Z T)) S)) W Y K‖≤C*Y := by
  obtain ⟨C₀,hC₀,h₀⟩ := full_uniform_normalized_second_mass (conjugateProfile g) M
    (conjugateProfile_support_bound g M hgM)
  refine ⟨‖paperRadialFourier W 0‖*C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ m c d Z Y hZ hY K hK
  simp_rw [star_normalizedColumn]
  apply (truncatedSecondZero_norm_le p hg hinj F Ψ m c d _ W Y K hK).trans
  rw [abs_of_pos hY]
  have hh := h₀ p hp hg hinj F Ψ hΨ m c d Z hZ
  calc
    _ ≤ Y*‖paperRadialFourier W 0‖*C₀ := mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ (‖paperRadialFourier W 0‖*C₀+1)*Y := by nlinarith

theorem initial_normalized_diagonal
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (_hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1)
      (Z Y : ℝ),0<Z → 0<Y →
      ∀K : Finset ι→Finset ι→Finset O,
      (∀G∈F.powerset,∀E∈G.powerset,(0:O)∈K G E) →
      ‖truncatedSecondZero p hg F Ψ 1 1 1
        (fun S => star (normalizedColumn p
          (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T)) S)) rowMajorant Y K‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_diagonal_fixed_profile (initialLogProfile W a b ha hs hW)
    rowMajorant (|Real.log a|+|Real.log b|+1) (initialLogProfile_support W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj F Ψ hΨ Z Y hZ hY K hK
  exact h p hp hg hinj F Ψ hΨ 1 1 1 Z Y hZ hY K hK

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

def initialFrequencyCutoff (Z Y M T : ℝ) : Finset O :=
  secondFrequencyCutoff (Y/(1+Z*Real.exp M)^3) T

theorem initialFrequencyCutoff_zero (Z Y M T : ℝ) :
    (0:O)∈initialFrequencyCutoff Z Y M T := secondFrequencyCutoff_zero _ _

theorem initialFrequencyCutoff_valid
    {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (Ψ : O→*ℂ) (m c d : O) (g : 𝓢(ℝ,ℂ)) (M Z Y T : ℝ)
    (hZ : 0<Z) (hY : 0<Y) (hgM : ∀t,g t≠0 → |t|≤M)
    (G E S R : Finset ι) (hEG : E⊆G) (hSR : Disjoint S R)
    (hw : residualPairWeight p hg Ψ Ψ m c d
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U))
      (fun U => normalizedColumn p (fun V => g (columnLog p Z V)) (G∪U)) S R≠0)
    (k : O) (hk : k∉initialFrequencyCutoff Z Y M T) :
    T≤(Y/(‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2))*‖eisEmbedding k‖^2 := by
  let lengthScale : ℝ := 1+Z*Real.exp M
  have hL : 0<lengthScale := by dsimp [lengthScale]; positivity
  obtain ⟨hG,hE,hS,hR⟩ := residualPairWeight_support_bounds p hp hg Ψ m c d g M Z hZ hgM G E S R hEG hw
  have hZL : Z*Real.exp M≤lengthScale := by dsimp [lengthScale]; linarith
  have hn : ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2=primeProductNorm p S*primeProductNorm p R :=
    active_norm_sq_disjoint p S R hSR
  have hden : ‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2≤lengthScale^3 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    have hSRn := mul_le_mul (hS.trans hZL) (hR.trans hZL)
      (FirstPassCubeLabels.primeProductNorm_pos p hp R).le hL.le
    have hESR := mul_le_mul (hE.trans hZL) hSRn
      (mul_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp S).le
        (FirstPassCubeLabels.primeProductNorm_pos p hp R).le) hL.le
    nlinarith
  have hden0 : 0<‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E)‖^2*
      ‖eisEmbedding (∏i : activeSupport R S,p i.val)‖^2 := by
    rw [primeSubsetGenerator_norm_eq_productNorm,hn]
    exact mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp E)
      (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp S) (FirstPassCubeLabels.primeProductNorm_pos p hp R))
  have hout := (outside_secondFrequencyCutoff (Y/lengthScale^3) T (by positivity) k hk).le
  exact hout.trans (mul_le_mul_of_nonneg_right
    (div_le_div_of_nonneg_left hY.le hden0 hden) (sq_nonneg _))

theorem initial_tail_polynomial (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) (A : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y T : ℝ),0<Z → 0<Y → 0≤T →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (normalizedColumn p (fun V => g (columnLog p Z V))) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M T)‖≤
        C*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by
  obtain ⟨s,C,hC,h⟩ := full_uniform_secondSourceTail_bound A
  let P : ℝ := C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let C₀ : ℝ := 128^4*(SchwartzMap.seminorm ℝ 0 0 g)^2*P
  have hP : 0≤P := by dsimp [P]; positivity
  have hC₀ : 0≤C₀ := by dsimp [C₀]; positivity
  refine ⟨C₀+1,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y T hZ hY hT
  have hb := h p hp hg hinj hc F Ψ m c d
    (normalizedColumn p (fun V => g (columnLog p Z V))) W Y T hY hT
    (fun _ _ => initialFrequencyCutoff Z Y M T)
    (fun G hG E S hS R hR hSR hw k hk => initialFrequencyCutoff_valid p hp hg Ψ m c d g M Z Y T
      hZ hY hgM G E.val S R (Finset.mem_powerset.mp E.property) hSR hw k hk)
  have hpoly := secondSourceTailCost_polynomial p hp hg hinj F Ψ hΨ m c d g M Z Y T
    (1+Z*Real.exp M) P A hZ hY hT hP (by linarith [mul_pos hZ (Real.exp_pos M)]) (by linarith) hgM
  apply (hb.trans hpoly).trans
  calc
    _ = C₀*(1+Z*Real.exp M)^4*Y*(1+(1+Z*Real.exp M)^3/Y)^2/(1+T)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

def initialTailHeight (Z Y M : ℝ) : ℝ :=
  (1+Z*Real.exp M)^2*(1+(1+Z*Real.exp M)^3/Y)

theorem initialTailHeight_pos (Z Y M : ℝ) (hZ : 0<Z) (hY : 0<Y) :
    0 < initialTailHeight Z Y M := by unfold initialTailHeight; positivity

theorem initial_tail_fixed_profile (g W : 𝓢(ℝ,ℂ)) (M : ℝ)
    (hgM : ∀t,g t≠0 → |t|≤M) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1) (m c d : O)
      (Z Y : ℝ),0<Z → 0<Y →
      ‖secondSourceTail p hp hg hinj F Ψ m c d
        (fun S => star (normalizedColumn p (fun V => g (columnLog p Z V)) S)) W Y
        (fun _ _ => initialFrequencyCutoff Z Y M (initialTailHeight Z Y M))‖≤C*Y := by
  obtain ⟨C,hC,h⟩ := initial_tail_polynomial (conjugateProfile g) W M
    (conjugateProfile_support_bound g M hgM) 2
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d Z Y hZ hY
  simp_rw [star_normalizedColumn]
  apply (h p hp hg hinj hc F Ψ hΨ m c d Z Y (initialTailHeight Z Y M) hZ hY
    (initialTailHeight_pos Z Y M hZ hY).le).trans
  have hth := initialTailHeight_pos Z Y M hZ hY
  apply (div_le_iff₀ (by positivity : 0<(1+initialTailHeight Z Y M)^2)).mpr
  have hh : (1+Z*Real.exp M)^4*(1+(1+Z*Real.exp M)^3/Y)^2≤(1+initialTailHeight Z Y M)^2 := by
    have hp := initialTailHeight_pos Z Y M hZ hY
    calc
      _ = (initialTailHeight Z Y M)^2 := by unfold initialTailHeight; ring
      _ ≤ _ := by nlinarith
  have hb := mul_le_mul_of_nonneg_left hh (show 0≤C*Y by positivity)
  nlinarith

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)
open ConcreteTraceCRT (eisEmbedding)

def initialErrorWindow (a b : ℝ) : ℝ := |Real.log a|+|Real.log b|+1

def initialErrorCutoff (a b Z Y : ℝ) : Finset O :=
  initialFrequencyCutoff Z Y (initialErrorWindow a b)
    (initialTailHeight Z Y (initialErrorWindow a b))

theorem initialErrorCutoff_zero (a b Z Y : ℝ) : (0:O)∈initialErrorCutoff a b Z Y :=
  initialFrequencyCutoff_zero _ _ _ _

def initialErrorFrequencyBound (a b Z Y : ℝ) : ℝ :=
  3*(initialTailHeight Z Y (initialErrorWindow a b)*
    (1+Z*Real.exp (initialErrorWindow a b))^3/Y+2)^2

theorem initialErrorCutoff_norm_bound (a b Z Y : ℝ) (hZ : 0<Z) (hY : 0<Y)
    (k : O) (hk : k∈initialErrorCutoff a b Z Y) :
    ‖eisEmbedding k‖^2≤ initialErrorFrequencyBound a b Z Y := by
  let M := initialErrorWindow a b
  let v : ℝ := initialTailHeight Z Y M/(Y/(1+Z*Real.exp M)^3)
  have hv : 0≤v := by
    dsimp [v]
    exact div_nonneg (initialTailHeight_pos Z Y M hZ hY).le (by positivity)
  have hb := secondFrequencyCutoff_norm_sq_le (Y/(1+Z*Real.exp M)^3)
    (initialTailHeight Z Y M) k hk
  have hc : (⌈v⌉₊:ℝ)+1≤v+2 := by
    have hh := (Nat.ceil_lt_add_one hv).le
    linarith
  apply hb.trans
  change 3*((⌈v⌉₊:ℝ)+1)^2≤_
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hc 2) (by norm_num : (0:ℝ)≤3)
  convert hsq using 1
  dsimp [initialErrorFrequencyBound,v,M]
  congr 2
  field_simp

theorem initial_normalized_errors
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ) (_hΨ : ∀z,‖Ψ z‖≤1)
      (Z Y : ℝ),0<Z → 0<Y →
      let G := normalizedColumn p
        (fun T => initialLogProfile W a b ha hs hW (columnLog p Z T))
      let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y
      ‖truncatedSecondZero p hg F Ψ 1 1 1 (fun T => star (G T)) rowMajorant Y K‖+
        ‖secondSourceTail p hp hg hinj F Ψ 1 1 1 (fun T => star (G T)) rowMajorant Y K‖≤C*Y := by
  obtain ⟨Cd,hCd,hd⟩ := initial_normalized_diagonal W a b ha hs hW
  obtain ⟨Ct,hCt,ht⟩ := initial_tail_fixed_profile (initialLogProfile W a b ha hs hW)
    rowMajorant (initialErrorWindow a b) (initialLogProfile_support W a b ha hs hW)
  refine ⟨Cd+Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ Z Y hZ hY
  dsimp only
  have h₁ := hd p hp hg hinj F Ψ hΨ Z Y hZ hY
    (fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y)
    (fun G hG E hE => initialErrorCutoff_zero a b Z Y)
  have h₂ := ht p hp hg hinj hc F Ψ hΨ 1 1 1 Z Y hZ hY
  change ‖secondSourceTail p hp hg hinj F Ψ 1 1 1
    (fun T => star (normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V)) T))
    rowMajorant Y (fun (_ _ : Finset ι) => initialErrorCutoff a b Z Y)‖≤Ct*Y at h₂
  linarith

end

open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_source_with_errors
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) :
    ∃C : ℝ,0<C ∧ ∀{q : ℕ} (χ : DirichletCharacter ℂ q)
      (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
      (hSp : ∀P∈S,Prime P) (Z Y : ℝ),0<Z → 0<Y → b*Z≤D →
    ∀T : Finset O,(∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Y) → (∀z∈T,z≠0) →
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    let hg := poolPrimary_good F hF
    letI : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
      intro i j hij
      apply Subtype.ext
      simpa only [p,poolPrimary_span F hF] using hij
    let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
    let Ψ := conjugateMonoid (normCharacter χ)
    (∑z∈T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)/Z≤
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant Y (fun _ _ => (initialErrorCutoff a b Z Y).erase 0)‖+
      C*Y-‖G ∅‖^2 := by
  obtain ⟨C,hC,h⟩ := initial_normalized_errors W a b ha hs hW
  refine ⟨C,hC,?_⟩
  intro q χ S D hbad hSp Z Y hZ hY hD T hT hT0
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let p := poolPrimary F
  let hp := poolPrimary_ne_zero F hF
  let hg := poolPrimary_good F hF
  let : ∀i : primePool F,(Ideal.span {p i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hinj : Function.Injective (fun i : primePool F => Ideal.span {p i}) := by
    intro i j hij
    apply Subtype.ext
    simpa only [p,poolPrimary_span F hF] using hij
  let G := normalizedColumn p (fun V => initialLogProfile W a b ha hs hW (columnLog p Z V))
  let Ψ := conjugateMonoid (normCharacter χ)
  let K : Finset (primePool F)→Finset (primePool F)→Finset O := fun _ _ => initialErrorCutoff a b Z Y
  have he := h p hp hg hinj (poolPrimary_odd F hF) Finset.univ Ψ
    (conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)) Z Y hZ hY
  have hm := outside_mean_square_source χ S D hbad hSp W a b Z Y ha hZ hY hs hW hD T hT hT0 K
  have hz := Complex.re_le_norm (truncatedSecondZero p hg Finset.univ Ψ 1 1 1
    (fun V => star (G V)) rowMajorant Y K)
  change ‖truncatedSecondZero p hg Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖+
    ‖secondSourceTail p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V)) rowMajorant Y K‖≤C*Y at he
  apply hm.trans
  linarith

end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem initial_nonzero_source_norm_le_squarefree_bins
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1) (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g W : 𝓢(ℝ,ℂ)) (Z H M Kmax : ℝ) (hZ : 0 < Z)
    (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (K : Finset ι → Finset ι → Finset O)
    (hK : ∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z M,
      elementNorm (sourceObservation p x).1 ≤ Kmax) :
    let G := fun S => normalizedColumn p (fun T => g (columnLog p Z T)) S
    ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1 G W H (fun C E => (K C E).erase 0)‖ ≤
      ∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)) G G W H‖ := by
  dsimp only
  apply (initial_nonzero_source_norm_le_bins p hp hcop hg hinj hc hpr
    F Ψ m g W Z H M Kmax hZ hgM K hK).trans_eq
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro R hR
  apply Finset.sum_congr rfl
  intro j hj
  apply congrArg norm
  apply initial_source_eq_squarefree p hp hcop hg Ψ m ray F _ _ _ _ W H
  intro x hx
  exact (secondSupportedSector_mem p F K R Z M x (Finset.mem_filter.mp hx).1).2.1

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)

def initialSquarefreeBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ, B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X (t₁,t₂,t₃))

theorem initial_nonzero_source_squarefree_transfer
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU : ∀ t, g t ≠ 0 → U t=1) (hgA : ∀ t, g t ≠ 0 → |t| ≤ A)
    (ε : ℝ) (hε : 0 < ε) (N J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Cₛ : ℝ), 0 ≤ C ∧ 0 ≤ Cₛ ∧
      (∀ i, HasCompactSupport (windows i)) ∧ (∀ i, ContDiff ℝ ∞ (windows i)) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
        [∀ i, (Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i, lambda ∉ Ideal.span {p i})
        (hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
        (_hpr : ∀ i, lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O)
        (K : Finset ι → Finset ι → Finset O) (Z H Kmax : ℝ),
        0 < Z → 0 < H → (∀ a, ‖Ψ a‖ ≤ 1) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R Z A,
          elementNorm (sourceObservation p x).1 ≤ Kmax) →
        ∃ B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ,
          (∀ ray R j q, 0 ≤ B ray R j q) ∧
          (∀ ray R j q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B ray R j q ≤
            Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) ∧
          ‖truncatedSecondSource p hp hg hinj F Ψ m 1 1
            (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
            W H (fun C E => (K C E).erase 0)‖ ≤
            C*(∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (Z*Real.exp A),
              ∑ j ∈ secondLogBinBox (Z*Real.exp A) Kmax,
                initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H A ε j windows (B ray R j)) := by
  obtain ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W A hA hU hgA ε hε N J
  refine ⟨windows,C,Cₛ,hC,hCₛ,hwc,hws,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m K Z H Kmax hZ hH hΨ hK
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j
        (initialSquarefreeSector p (secondLogSector p ∅ F K R Z A j)) hZ hH hΨ
        (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H A j
        (initialSquarefreeSector p (secondLogSector p ∅ F K R Z A j)) hZ hH hΨ
        (Finset.filter_subset _ _))
  refine ⟨B,fun ray R j => (hB ray R j).1,fun ray R j => (hB ray R j).2.1,?_⟩
  apply (initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj hc hpr F Ψ m
    g W Z H A Kmax hZ hgA K hK).trans
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro ray hray
  apply Finset.sum_le_sum
  intro R hR
  apply Finset.sum_le_sum
  intro j hj
  convert (hB ray R j).2.2 using 1 ; dsimp only [initialSquarefreeBinCost, B] ; ring

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialSquarefreeBinCost_of_canonical_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hchild : ∀ q,
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X q ≤
        (Cchild*(X*initialLogLabel j)^2)*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ*(∫ t : ℝ,firstLogDensity 0 t)^3)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X
  let E := Cchild*(X*initialLogLabel j)^2
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hpR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hX : 0 < X := div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hpR)
  have hlabel : 0 < initialLogLabel j := by
    unfold initialLogLabel secondLogE secondLogV
    exact mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) (Real.exp_pos _)
  have hE : 0 ≤ E := mul_nonneg hCc (sq_nonneg _)
  have hS : 0 < S := by
    dsimp [S]
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  have hG : ∀ q, 0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have henergy : ∀ q, G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    intro q
    exact (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6) X X q).trans (hchild q)
  have hb := polynomial_density_cost B G J S Cₛ E hS hCₛ hE hB hG hdec henergy
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by
    have hk : 0 < secondLogK j := normLogScale_pos _
    positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ*E/S)*(∫ t : ℝ,firstLogDensity 0 t)^3) := mul_le_mul_of_nonneg_left hb hpref
    _ = _ := by
      dsimp only [E,X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hpR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by
        rw [pow_two,←Real.exp_add]
        norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hpR.ne'
      field_simp

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem positive_nested_density_transfer (f G : Frequency → ℝ) (J : ℕ)
    (hG : Continuous G) (M : ℝ) (hGM : ∀ q, ‖G q‖ ≤ M)
    (C : ℝ) (hf : ∀ q, 0 ≤ f q)
    (hbound : ∀ q, f q ≤ C*tripleLogDensity J q*G q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,f (x,y,z)) ≤
      C*(∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,tripleLogDensity J (x,y,z)*G (x,y,z)) := by
  let u : Frequency → ℝ := fun q => C*(tripleLogDensity J q*G q)
  have hu : Integrable u := (tripleLogDensity_bounded_integrable J G hG M hGM).const_mul C
  have hux (x : ℝ) : Integrable (fun yz : ℝ × ℝ => u (x,yz)) :=
    (tripleLogDensity_slice_integrable J G hG M hGM x).const_mul C
  have huxy (x y : ℝ) : Integrable (fun z : ℝ => u (x,y,z)) := by
    have hd : Integrable (fun z : ℝ =>
        C*firstLogDensity J x*firstLogDensity J y*firstLogDensity J z) :=
      (firstLogDensity_integrable J).const_mul _
    have hgxy : Continuous (fun z : ℝ => G (x,y,z)) :=
      hG.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id))
    have hi := hd.mul_bdd hgxy.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun z : ℝ => hGM (x,y,z)))
    convert hi using 1
    funext z
    dsimp [u,tripleLogDensity]
    ring
  have hz (x y : ℝ) : (∫ z : ℝ,f (x,y,z)) ≤ ∫ z : ℝ,u (x,y,z) := by
    apply integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z : ℝ => hf (x,y,z))) (huxy x y)
    exact Filter.Eventually.of_forall (fun z : ℝ => by simpa only [u,mul_assoc] using hbound (x,y,z))
  have hy (x : ℝ) : (∫ y : ℝ,∫ z : ℝ,f (x,y,z)) ≤ ∫ y : ℝ,∫ z : ℝ,u (x,y,z) := by
    exact integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))
      (hux x).integral_prod_left (Filter.Eventually.of_forall (hz x))
  have hui : Integrable (fun x : ℝ => ∫ y : ℝ, ∫ z : ℝ,u (x,y,z)) := by
    apply hu.integral_prod_left.congr
    filter_upwards [] with x
    exact integral_prod _ (hux x)
  have hx := integral_mono_of_nonneg
    (Filter.Eventually.of_forall (fun x : ℝ => integral_nonneg
      (fun y : ℝ => integral_nonneg (fun z : ℝ => hf (x,y,z))))) hui
    (Filter.Eventually.of_forall hy)
  simpa only [u,integral_const_mul] using hx

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem initial_source_density_transfer (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m : O) (T : Finset (O × O)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ : ℝ)
    (B : Frequency → ℝ) (J : ℕ) (S C : ℝ) (hS : 0 < S) (hC : 0 ≤ C)
    (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,S*B q ≤ C*tripleLogDensity J q) :
    (∫ x : ℝ, ∫ y : ℝ, ∫ z : ℝ,B (x,y,z)*
      sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ (x,y,z)) ≤
    (C/S)*densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂ J := by
  let G := childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m (sourceIdealTarget T) V₁ V₂ X₁ X₂
  have hc₁ := childEnergy_continuous p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false
    (fun q : Frequency => q.1) (fun q : Frequency => q.2.2) continuous_fst continuous_snd.snd
  have hc₂ := childEnergy_continuous p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true
    (fun q : Frequency => q.2.1) (fun q : Frequency => q.2.2) continuous_snd.fst continuous_snd.snd
  have hG : Continuous G := (Real.continuous_sqrt.comp hc₁).mul (Real.continuous_sqrt.comp hc₂)
  have hG0 : ∀ q,0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  let M := Real.sqrt (energyMagnitude p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false)*
    Real.sqrt (energyMagnitude p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true)
  have hGM : ∀ q,‖G q‖ ≤ M := by
    intro q
    rw [Real.norm_of_nonneg (hG0 q)]
    exact mul_le_mul
      (Real.sqrt_le_sqrt (childEnergy_le p hp hcop hg F Ψ₁ m (sourceIdealTarget T) V₁ X₁ true false q.1 q.2.2))
      (Real.sqrt_le_sqrt (childEnergy_le p hp hcop hg F Ψ₂ m (sourceIdealTarget T) V₂ X₂ false true q.2.1 q.2.2))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  change _ ≤ (C/S)*(∫ x : ℝ,∫ y : ℝ,∫ z : ℝ,tripleLogDensity J (x,y,z)*G (x,y,z))
  apply positive_nested_density_transfer
    (fun q => B q*sourceGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q)
    G J hG M hGM (C/S)
  · intro q
    exact mul_nonneg (hB q) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · intro q
    have hb : B q ≤ (C/S)*tripleLogDensity J q := by
      have hd : B q ≤ (C*tripleLogDensity J q)/S :=
        (le_div_iff₀ hS).mpr (by simpa only [mul_comm] using hdec q)
      convert hd using 1 ; ring
    exact mul_le_mul hb (sourceGeometricMean_le_ideal p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X₁ X₂ q)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg (div_nonneg hC hS.le) (tripleLogDensity_nonneg _ _))

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0212

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.HarmonicAggregation
Source SHA256: 7c9ad1bd2f44c4de6567080753e9afb64252392366337cb628db4e02f9696c58
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0213



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstPassCubeLabels (primeProductNorm)

def initialRayMass : ℝ := ∑ ray : SecondRayIndex,‖secondRayCoefficient ray‖

lemma initialRayMass_nonneg : 0 ≤ initialRayMass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj in

theorem initial_complementary_harmonic (F : Finset ι) (U : ℝ) :
    (∑ R ∈ boundedPrimeSupports p F U,1/primeProductNorm p R) ≤
      128*Real.exp 1*(normLogBin U+1 : ℝ) := by
  let f : Finset ι → Ideal O := fun R => ∏ i ∈ R,Ideal.span {p i}
  have hf : Function.Injective f := FirstCauchyArithmetic.family_product_injective _ hinj
  let T := (boundedPrimeSupports p F U).image f
  have hT : ∀ I ∈ T,I ≠ (0 : Ideal O) := by
    intro I hI
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hI
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (Ideal.span {p i}))
  have hU : ∀ I ∈ T,(Ideal.absNorm I : ℝ) ≤ U := by
    intro I hI
    obtain ⟨R,hR,rfl⟩ := Finset.mem_image.mp hI
    rw [←primeProductNorm_eq_ideal_norm p R]
    exact (Finset.mem_filter.mp hR).2
  have hb := descent_ideal_inverse_sum T U hT hU
  rw [Finset.sum_image (fun R _ S _ h => hf h)] at hb
  simpa only [f,←primeProductNorm_eq_ideal_norm p] using hb

include hinj in

theorem initial_harmonic_aggregation (F : Finset ι) (U K D : ℝ) (hD : 0 ≤ D)
    (a : SecondRayIndex → Finset ι → SecondLogIndex → ℝ)
    (ha : ∀ ray, ∀ R ∈ boundedPrimeSupports p F U, ∀ j ∈ secondLogBinBox U K,
      a ray R j ≤ D/primeProductNorm p R*‖secondRayCoefficient ray‖) :
    (∑ ray : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F U,
      ∑ j ∈ secondLogBinBox U K,a ray R j) ≤
    D*initialRayMass*((secondLogBinBox U K).card : ℝ)*
      (128*Real.exp 1*(normLogBin U+1 : ℝ)) := by
  let B := secondLogBinBox U K
  let C := 128*Real.exp 1*(normLogBin U+1 : ℝ)
  have hinner (ray : SecondRayIndex) :
      (∑ R ∈ boundedPrimeSupports p F U,∑ j ∈ B,a ray R j) ≤
      (D*‖secondRayCoefficient ray‖*(B.card : ℝ))*C := by
    calc
      _ ≤ ∑ R ∈ boundedPrimeSupports p F U,∑ _j ∈ B,
          D/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
        apply Finset.sum_le_sum
        intro R hR
        exact Finset.sum_le_sum (fun j hj => ha ray R hR j hj)
      _ = (D*‖secondRayCoefficient ray‖*(B.card : ℝ))*
          ∑ R ∈ boundedPrimeSupports p F U,1/primeProductNorm p R := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro R hR
        simp only [Finset.sum_const,nsmul_eq_mul]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (initial_complementary_harmonic p hinj F U)
        (by positivity)
  calc
    _ ≤ ∑ ray : SecondRayIndex,(D*‖secondRayCoefficient ray‖*(B.card : ℝ))*C :=
      Finset.sum_le_sum (fun ray _ => hinner ray)
    _ = _ := by
      unfold initialRayMass
      simp only [Finset.sum_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hray
      ring

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def sourceGlobalBlock (b:CubeCoordinates ι) (C D:Finset ι) : GlobalCubeBlock ι :=
  ⟨b.swap,C,D⟩

lemma cube_swap_support (b:CubeCoordinates ι) : b.swap.support=b.support := by
  simp only [CubeCoordinates.swap,CubeCoordinates.support,Finset.union_comm]

omit [DecidableEq ι] in
lemma cube_swap_sum (b:CubeCoordinates ι) :
    (fun i=>b.swap.leftExponent i+b.swap.rightExponent i)=
      (fun i=>b.leftExponent i+b.rightExponent i) := by
  funext i
  exact Nat.add_comm _ _

lemma orientedCubeFirstBlock_single_source
    (pool:Finset ι) (b:CubeCoordinates ι) (C D:Finset ι) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D) {(I,h)} (fun _=>1)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell =
    (primeProductNorm p D:ℂ)⁻¹ *
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (originalLabelColumn p hg b.support b.leftBit b.rightBit true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
            (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        (originalLabelColumn p hg b.support b.leftBit b.rightBit false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
            (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S)))
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) C) (idealGenerator I))
        W V₁ V₂ (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  have hl : b.swap.leftBit=b.rightBit := rfl
  have hr : b.swap.rightBit=b.leftBit := rfl
  have hst : b.swap.sideDivisor true=b.rightDivisor := rfl
  have hsf : b.swap.sideDivisor false=b.leftDivisor := rfl
  simp only [orientedCubeFirstBlock,sourceGlobalBlock,globalCubePool,globalCubeColumnScale,
    globalFirstBlockColumnScale,GlobalCubeBlock.withCommon,cube_swap_support,cube_swap_sum,
    hl,hr,hst,hsf,Finset.sum_singleton,one_mul]

lemma canonical_log_kernel
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C:Finset ι)
    (hCB:Disjoint C b.support) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f d h:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell) :
    actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K d h =
    actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
      (originalLabelColumn p hg b.support b.leftBit b.rightBit true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p
          (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      (originalLabelColumn p hg b.support b.leftBit b.rightBit false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p
          (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) S))) (∏i∈C,p i) f)
      W (fun _=>1) (fun _=>1) (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
        (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) K d h := by
  unfold actualFirstKernel
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  have hdis (S:Finset ι) (hS:S∈(pool\(b.support∪C)).powerset) :
      Disjoint S C ∧ Disjoint S b.support := by
    constructor <;> apply Finset.disjoint_left.mpr
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_right _ hx)
    · intro i hi hx
      exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hS) hi)).2 (Finset.mem_union_left _ hx)
  have h₁:=canonicalCubeResidual_log p hp hg b hb C N hCB (hdis N hN).1 (hdis N hN).2 true Ψ₁ m₁ f g₁ ell hell
  have h₂:=canonicalCubeResidual_log p hp hg b hb C P hCB (hdis P hP).1 (hdis P hP).2 false Ψ₂ m₂ f g₂ ell hell
  simp only [CubeCoordinates.sideDivisor,Bool.not_true,Bool.not_false,Bool.false_eq_true,ite_false,ite_true] at h₁ h₂
  simp only [threeGaussRowFactor,h₁,h₂]

def commonProductUnit (C:Finset ι) : Oˣ :=
  Classical.choose (exists_label_unit (∏i∈C,p i) (∏i∈C,Ideal.span {p i})
    (FiniteGaussPhase.span_finset_prod C p))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma commonProductUnit_spec (C:Finset ι) :
    (∏i∈C,p i)=(commonProductUnit p C:O)*primeSubsetGenerator (fun i=>Ideal.span {p i}) C :=
  Classical.choose_spec (exists_label_unit (∏i∈C,p i) (∏i∈C,Ideal.span {p i})
    (FiniteGaussPhase.span_finset_prod C p))

def commonCubePhase (b:CubeCoordinates ι) (C:Finset ι) : ℂ :=
  blockRow p hg (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    (fun i=>(conductorExponent (parity (b.leftExponent i+b.rightExponent i)) (b.leftBit i) (b.rightBit i)).val)
    ((commonProductUnit p C:O)^2)

lemma commonCubePhase_norm (b:CubeCoordinates ι) (C:Finset ι) :
    ‖commonCubePhase p hg b C‖=1 :=
  commonUnitPhase_norm p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
    b.leftBit b.rightBit (commonProductUnit p C)

theorem canonicalSource_mode_attachment
    (pool:Finset ι) (b:CubeCoordinates ι) (hb:b.Admissible) (C D:Finset ι)
    (hCB:Disjoint C b.support) (I:Ideal O) (h:O)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    ((UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ))*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ (idealGenerator I) (fun U=>g₁ (columnLog p ell U)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ (idealGenerator I) (fun U=>g₂ (columnLog p ell U)))
        W (fun _=>1) (fun _=>1) 1 1 K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h =
    (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*commonCubePhase p hg b C*
      orientedCubeFirstBlock p hp hcop hg pool (sourceGlobalBlock b C D)
        {(I,(commonProductUnit p C:O)^2*h)} (fun _=>1) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hFB:Disjoint (pool\(b.support∪C)) b.support :=
    Finset.disjoint_left.mpr (fun i hi hiB=>(Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB))
  rw [canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ (idealGenerator I) _ h g₁ g₂ W K ell hell]
  rw [actualFirstKernel_insert_windows p hp hcop hg _ _ _ _ _ Ψ₁ Ψ₂ m₁ m₂ _ _
    g₁ g₂ W V₁ V₂ _ _ K _ h hV₁ hV₂]
  rw [commonProductUnit_spec p C]
  rw [actualFirstKernel_common_unit p hp hcop hg _ _ hFB _ _ _ _ _ W V₁ V₂ _ _ K
    (commonProductUnit p C) _ (idealGenerator I) _ h]
  rw [orientedCubeFirstBlock_single_source]
  unfold commonCubePhase
  ring

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcretePrimeRowBridge (idealGenerator)
open ConcreteTraceCRT (eisEmbedding)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

lemma orientedCubeFirstBlock_eq_sum_single (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) :
    orientedCubeFirstBlock p hp hcop hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell=
      ∑x∈s,a x*orientedCubeFirstBlock p hp hcop hg pool b {x} (fun _=>1)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  unfold orientedCubeFirstBlock
  simp only [Finset.sum_singleton,one_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def rawCanonicalBlock (pool:Finset ι) (b:GlobalCubeBlock ι)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (K ell:ℝ) : ℂ :=
  let q:=b.cube.swap
  ∑x∈s,a x*((UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)/
    (primeProductNorm p b.firstDivisor:ℂ))*
    actualFirstKernel p hp hcop hg (pool\(q.support∪b.common)) q.support
      (fun i=>q.leftExponent i+q.rightExponent i) q.leftBit q.rightBit
      (canonicalCubeResidual p hg q b.common true Ψ₁ m₁ (idealGenerator x.1)
        (fun U=>g₁ (columnLog p ell U)))
      (canonicalCubeResidual p hg q b.common false Ψ₂ m₂ (idealGenerator x.1)
        (fun U=>g₂ (columnLog p ell U)))
      W (fun _=>1) (fun _=>1) 1 1 K
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) b.firstDivisor) x.2

def sourceFrequencyEquiv (C:Finset ι) : (Ideal O×O)≃(Ideal O×O) :=
  Equiv.prodCongr (Equiv.refl _) (unitSquareRowEquiv (commonProductUnit p C))

def sourceRotatedCoefficient (b:GlobalCubeBlock ι) (a:Ideal O×O→ℂ) (x:Ideal O×O) : ℂ :=
  (UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)*
    commonCubePhase p hg b.cube.swap b.common*a ((sourceFrequencyEquiv p b.common).symm x)

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_label (C:Finset ι) (x:Ideal O×O) :
    (sourceFrequencyEquiv p C x).1=x.1 := rfl

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_row_norm (C:Finset ι) (x:Ideal O×O) :
    ‖eisEmbedding (sourceFrequencyEquiv p C x).2‖=‖eisEmbedding x.2‖ := by
  have hr : (sourceFrequencyEquiv p C x).2=(commonProductUnit p C:O)^2*x.2 := rfl
  rw [hr,map_mul,norm_mul,map_pow,norm_pow,GaussGeneratorTransport.norm_eisEmbedding_unit,one_pow,one_mul]

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceFrequencyEquiv_row_ne_zero (C:Finset ι) (x:Ideal O×O) (hx:x.2≠0) :
    (sourceFrequencyEquiv p C x).2≠0 := by
  change (commonProductUnit p C:O)^2*x.2≠0
  exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hx

lemma sourceRotatedCoefficient_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:GlobalCubeBlock ι) (a:Ideal O×O→ℂ) (x:Ideal O×O) :
    ‖sourceRotatedCoefficient p hg b a x‖=‖a ((sourceFrequencyEquiv p b.common).symm x)‖ := by
  have hprime (i:ι):Prime (Ideal.span {p i}):=
    Ideal.prime_of_isPrime (NeZero.ne _) inferInstance
  have hμ : ‖(UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)‖=1 := by
    have hh:=congrArg norm (FirstCauchyArithmetic.supportMobius_sq _ hprime hinj b.firstDivisor)
    simp only [norm_mul,norm_one] at hh
    change ‖FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) b.firstDivisor‖=1
    nlinarith [norm_nonneg (FirstCauchyArithmetic.supportMobius (fun i=>Ideal.span {p i}) b.firstDivisor)]
  simp only [sourceRotatedCoefficient,norm_mul,hμ,commonCubePhase_norm,one_mul]

theorem rawCanonicalBlock_eq_oriented
    (pool:Finset ι) (b:GlobalCubeBlock ι) (hb:GlobalCubeAdmissible b)
    (s:Finset (Ideal O×O)) (a:Ideal O×O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W V₁ V₂:𝓢(ℝ,ℂ)) (K ell:ℝ) (hell:0<ell)
    (hV₁:∀t,g₁ t≠0→V₁ t=1) (hV₂:∀t,g₂ t≠0→V₂ t=1) :
    rawCanonicalBlock p hp hcop hg pool b s a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell =
    orientedCubeFirstBlock p hp hcop hg pool b (s.image (sourceFrequencyEquiv p b.common))
      (sourceRotatedCoefficient p hg b a) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
  have hq:b.cube.swap.Admissible := by
    constructor
    · change b.cube.rightDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.2
    · change b.cube.leftDivisor⊆b.cube.swap.support
      rw [cube_swap_support]
      exact hb.1.1
  have hc:Disjoint b.common b.cube.swap.support := by
    rw [cube_swap_support]
    exact hb.2.1
  have hback:sourceGlobalBlock b.cube.swap b.common b.firstDivisor=b := by
    cases b
    simp only [sourceGlobalBlock,CubeCoordinates.swap_swap]
  rw [orientedCubeFirstBlock_eq_sum_single,Finset.sum_image]
  · unfold rawCanonicalBlock
    dsimp only
    apply Finset.sum_congr rfl
    intro x hx
    have hmode:=canonicalSource_mode_attachment p hp hcop hg pool b.cube.swap hq b.common b.firstDivisor hc
      x.1 x.2 Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell hell hV₁ hV₂
    rw [hback] at hmode
    have hidx : (x.1,(commonProductUnit p b.common:O)^2*x.2)=sourceFrequencyEquiv p b.common x := rfl
    rw [hidx] at hmode
    simp only [sourceRotatedCoefficient,Equiv.symm_apply_apply]
    calc
      _ = a x*((UniqueFactorizationMonoid.moebius (∏i∈b.firstDivisor,Ideal.span {p i}):ℂ)/
          (primeProductNorm p b.firstDivisor:ℂ)*
          actualFirstKernel p hp hcop hg (pool\(b.cube.swap.support∪b.common)) b.cube.swap.support
            (fun i=>b.cube.swap.leftExponent i+b.cube.swap.rightExponent i) b.cube.swap.leftBit b.cube.swap.rightBit
            (canonicalCubeResidual p hg b.cube.swap b.common true Ψ₁ m₁ (idealGenerator x.1) (fun U=>g₁ (columnLog p ell U)))
            (canonicalCubeResidual p hg b.cube.swap b.common false Ψ₂ m₂ (idealGenerator x.1) (fun U=>g₂ (columnLog p ell U)))
            W (fun _=>1) (fun _=>1) 1 1 K (primeSubsetGenerator (fun i=>Ideal.span {p i}) b.firstDivisor) x.2) := by ring
      _ = _ := by rw [hmode];ring
  · exact fun x hx y hy hxy=>(sourceFrequencyEquiv p b.common).injective hxy

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem rawCanonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (hWin₁ : ∀ t,g₁ t≠0 → V₁ t=1) (hWin₂ : ∀ t,g₂ t≠0 → V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H U : ℝ),
      0≤Γ → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell‖ ≤
      Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,htransfer⟩ :=
    orientedTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  let s' := fun b:GlobalCubeBlock ι=>(s b).image (sourceFrequencyEquiv p b.common)
  let a' := fun b:GlobalCubeBlock ι=>sourceRotatedCoefficient p hg b (a b)
  have heq : (∑b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell)=
      ∑b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s' b) (a' b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell := by
    apply Finset.sum_congr rfl
    intro b hb
    exact rawCanonicalBlock_eq_oriented p hp hcop hg pool b (hadm b hb) (s b) (a b)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell hell hWin₁ hWin₂
  rw [heq]
  apply htransfer p hp hinj hcop hg hc hpr pool blocks s' a' w Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H U
    hΓ hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    dsimp only [a']
    rw [sourceRotatedCoefficient_norm p hg hinj,Equiv.symm_apply_apply]
    exact ha b hb y hy
  · exact hadm
  · exact hb₁
  · exact hb₂
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hsf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact sourceFrequencyEquiv_row_ne_zero p b.common y (hs0 b hb y hy)
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_row_norm]
    exact hh b hb y hy

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

theorem padded_orientedCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (Ksrc K ell B F Ymax : ℝ),
      0<Ksrc → 0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      (Ksrc/K)*C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ Ksrc K ell B F Ymax hKsrc hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤(Ksrc/K)*C*Ymax^deltaLoss := mul_nonneg (mul_nonneg (div_nonneg hKsrc.le hK.le) hC) (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      ((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hswapD := FirstPassCubeLabels.dilationLabel_swap p b.cube.support
      (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ Ksrc hKsrc (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (by simpa only [hswapD] using hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    rw [firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit true,
      firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit false,
      FirstPassCubeLabels.cubeActiveSupport_swap b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit] at hh
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hscl' : (ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
        ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
          (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤
        (Ksrc/K)*globalCubeCoefficient p K ell B F true b := by
      have hKratio : Ksrc=(Ksrc/K)*K := by field_simp
      calc
        _ = (Ksrc/K)*((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)) := by
          conv_lhs => rw [hKratio]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscl (div_nonneg hKsrc.le hK.le)
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ ((Ksrc/K)*globalCubeCoefficient p K ell B F true b)*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl'
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (mul_nonneg (div_nonneg hKsrc.le hK.le) (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _))
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = ((Ksrc/K)*C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0213

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.PaddedPassage
Source SHA256: 324b2bf1a21040a9994dbd94853f14d8bca1aa297a78be699bc11e9ab95e50d8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0214



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem padded_orientedTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ Ksrc K ell B F H U : ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := padded_orientedCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Cd₁,Ct₁,hC₁,hCd₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Cd₂,Ct₂,hC₂,hCd₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ :=
    globalCubeInputFamilyEnergy_quantitative ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCfirst,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  have hB0 : 0<B := by linarith
  let T := fun b => globalCubeFirstTargets p b (s b)
  have hT0 (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) : z≠0 :=
    globalCubeFirstTargets_ne_zero p hp b (s b) (hsf b hb) (hs0 b hb) z hz
  have hT (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) :=
    globalCubeFirstTargets_norm_bound p hp b (s b) K ell B F hK hell hB0 hF
      (hb₁ b hb) (hb₂ b hb) (hf b hb) (hh b hb) z hz
  have hTc (b : GlobalCubeBlock ι) (hb : b∈blocks) (z : O) (hz : z∈T b) :
      (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    rw [globalFirstPooledRow_side]
    exact hT b hb z hz
  have hblock := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ Ksrc K ell B F
    (globalFirstRowCap K ell B F) hKsrc hK hell hB0 hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha
    (fun b hb => globalFirstPooledRow_le_cap p hp K ell B F hK hell hB0 hF b (hadm b hb) (hb₁ b hb) (hb₂ b hb))
    hsf hs0 (fun b _ x hx => globalCubeFirstTargets_mem p b (s b) x hx) hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₁ m₁ T
    hΓ hw hK hell hB hF hH hU hellU1 hadm hΨ₁ hb₁ hb₂ hT hT0
  have hr := hright p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H U Ψ₂ m₂ T
    hΓ hw hK hell hB hF hH hU hellU2 hadm hΨ₂ hb₁ hb₂ hTc hT0
  have hprefix : 0≤(Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss :=
    mul_nonneg (mul_nonneg (div_nonneg hKsrc.le hK.le) hCfirst) (Real.rpow_nonneg (globalFirstRowCap_pos K ell B F hK hell hB0 hF).le _)
  exact hblock.trans (mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hl) hprefix)
    (Real.sqrt_le_sqrt hr) (Real.sqrt_nonneg _) (mul_nonneg hprefix (Real.sqrt_nonneg _)))

theorem padded_rawCanonicalTwoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (hWin₁ : ∀ t,g₁ t≠0 → V₁ t=1) (hWin₂ : ∀ t,g₂ t≠0 → V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀ i,HasCompactSupport (windows₁ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀ i t,windows₁ i t≠0 → |t|≤M₁+6+1) ∧
      (∀ i,HasCompactSupport (windows₂ i)) ∧ (∀ i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀ i t,windows₂ i t≠0 → |t|≤M₂+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ Ksrc K ell B F H U : ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U → ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,(Ideal.absNorm x.1 : ℝ)≤F) →
      (∀ b∈blocks,∀ x∈s b,‖eisEmbedding x.2‖^2≤globalFirstFrequencyScale p K ell b) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell‖ ≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true) *
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool blocks Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,htransfer⟩ :=
    padded_orientedTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂ hg₁ hg₂ hV₁ hV₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hc₁,hs₁,hb₁,hc₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hsf hs0 hf hh
  let s' := fun b:GlobalCubeBlock ι=>(s b).image (sourceFrequencyEquiv p b.common)
  let a' := fun b:GlobalCubeBlock ι=>sourceRotatedCoefficient p hg b (a b)
  have heq : (∑b∈blocks,rawCanonicalBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell)=
      ∑b∈blocks,orientedCubeFirstBlock p hp hcop hg pool b (s' b) (a' b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell := by
    apply Finset.sum_congr rfl
    intro b hb
    exact rawCanonicalBlock_eq_oriented p hp hcop hg pool b (hadm b hb) (s b) (a b)
      Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell hell hWin₁ hWin₂
  rw [heq]
  apply htransfer p hp hinj hcop hg hc hpr pool blocks s' a' w Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hellU1 hellU2 hΨ₁ hΨ₂ hw
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    dsimp only [a']
    rw [sourceRotatedCoefficient_norm p hg hinj,Equiv.symm_apply_apply]
    exact ha b hb y hy
  · exact hadm
  · exact hb₁
  · exact hb₂
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hsf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    exact sourceFrequencyEquiv_row_ne_zero p b.common y (hs0 b hb y hy)
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_label]
    exact hf b hb y hy
  · intro b hb x hx
    obtain ⟨y,hy,rfl⟩:=Finset.mem_image.mp hx
    rw [sourceFrequencyEquiv_row_norm]
    exact hh b hb y hy

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)

def firstFrequencyDisk (R:ℝ) : Finset O :=
  (ShortDraftLatticeCount.rowNormBall ⌈R⌉₊).filter (fun h=>‖eisEmbedding h‖^2≤R)

lemma mem_firstFrequencyDisk (R:ℝ) (h:O) :
    h∈firstFrequencyDisk R ↔ ‖eisEmbedding h‖^2≤R := by
  constructor
  · exact fun hh=>(Finset.mem_filter.mp hh).2
  · intro hh
    apply Finset.mem_filter.mpr
    refine ⟨?_,hh⟩
    apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
    rw [eisEmbedding_norm_sq_eq_absNorm_span] at hh
    exact_mod_cast hh.trans (Nat.le_ceil R)

lemma firstFrequencyDisk_zero (R:ℝ) (hR:0≤R) : (0:O)∈firstFrequencyDisk R := by
  rw [mem_firstFrequencyDisk]
  simpa using hR

lemma outside_firstFrequencyDisk (R:ℝ) (h:O) (hh:h∉firstFrequencyDisk R) :
    R<‖eisEmbedding h‖^2 := lt_of_not_ge (fun hb=>hh ((mem_firstFrequencyDisk R h).mpr hb))

lemma firstFrequencyDisk_unit_invariant (R:ℝ) (u:Oˣ) (h:O) :
    (u:O)*h∈firstFrequencyDisk R ↔ h∈firstFrequencyDisk R := by
  simp only [mem_firstFrequencyDisk,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

lemma euclideanCoordinateVector_eq_basis (j : Fin 3) :
    euclideanCoordinateVector j=EuclideanSpace.basisFun (Fin 3) ℝ j := by
  rw [EuclideanSpace.basisFun_apply]
  rfl

lemma schwartz_toL2_norm_sq (g : 𝓢(EuclideanSpatial,ℂ)) :
    ‖g.toLp 2 volume‖^2=∫p,‖g p‖^2 := by
  calc
    ‖g.toLp 2 volume‖^2=inner ℝ (g.toLp 2 volume) (g.toLp 2 volume) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (g.toLp 2 volume p) (g.toLp 2 volume p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [g.coeFn_toLp 2 volume] with p hp
      rw [hp,real_inner_self_eq_norm_sq]

def kernelLocalizedDensity (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : ℝ :=
  ‖kernelLocalizedField χ f p‖^2+∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
    (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2

lemma kernelLocalizedDensity_eq_schwartz (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) :
    kernelLocalizedDensity χ f p=‖kernelLocalizedSchwartz χ f p‖^2+
      ∑j : Fin 3,‖(∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)) p‖^2 := by
  simp only [SchwartzMap.lineDerivOp_apply_eq_fderiv,euclideanCoordinateVector_eq_basis,
    kernelLocalizedSchwartz_coe]
  rfl

lemma kernelLocalizedDensity_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (kernelLocalizedDensity χ f) volume := by
  change Integrable (fun p => kernelLocalizedDensity χ f p) volume
  simp_rw [kernelLocalizedDensity_eq_schwartz]
  exact ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq.add
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq))

lemma kernelLocalizedH1_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2=∫p,kernelLocalizedDensity χ f p := by
  rw [euclideanH1_norm_sq,kernelLocalizedH1_embedding,PiLp.norm_sq_eq_of_L2]
  simp_rw [kernelLocalizedH1_gradient,schwartz_toL2_norm_sq,kernelLocalizedDensity_eq_schwartz]
  rw [integral_add (((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq)
    (integrable_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)),
    integral_finsetSum _ (fun j _ =>
      ((∂_{euclideanCoordinateVector j} (kernelLocalizedSchwartz χ f)).memLp 2 volume).norm.integrable_sq)]

lemma kernelLocalizedDensity_zero (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : p∉tsupport χ.func) : kernelLocalizedDensity χ f p=0 := by
  have hz : kernelLocalizedField χ f=ᶠ[𝓝 p]0 := by
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hp] with q hq
    simp only [kernelLocalizedField,hq,Pi.zero_apply,zero_smul]
  simp only [kernelLocalizedDensity,hz.self_of_nhds,hz.fderiv_eq,fderiv_zero,
    Pi.zero_apply,_root_.zero_apply,norm_zero,zero_pow (by decide : 2≠0),Finset.sum_const_zero,add_zero]

lemma kernelLocalizedDensity_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) (M D A : ℝ)
    (hM : (χ.func p)^2≤M)
    (hD : (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : (χ.func p)^2≤A*(p 2)^2) :
    kernelLocalizedDensity χ f p≤
      (M+2*D)*‖kernelTestField f p‖^2+
        2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
  have he := kernelLocalizedField_energy_bound χ f p hp
  have he' : (p 2)^2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      (p 2)^2*(2*A*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
        2*D*‖kernelTestField f p‖^2) := by
    refine he.trans ?_
    calc
      _ ≤ 2*(A*(p 2)^2)*kernelTestEnergyDensity f (euclideanToHyperbolic p)+
          2*(p 2)^2*D*‖kernelTestField f p‖^2 := by
        gcongr
        · exact kernelTestEnergyDensity_nonneg _ _
      _ = _ := by ring
  have hs := le_of_mul_le_mul_left he' (sq_pos_of_pos hp)
  have hm : ‖kernelLocalizedField χ f p‖^2≤M*‖kernelTestField f p‖^2 := by
    simp only [kernelLocalizedField,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
    exact mul_le_mul_of_nonneg_right hM (sq_nonneg _)
  unfold kernelLocalizedDensity
  nlinarith

lemma kernelEuclideanProjection_volume_integrable (S : Set EuclideanSpatial)
    (hS : MeasurableSet S) (hpos : S⊆euclideanUpperHalf)
    (hinj : Set.InjOn kernelEuclideanProjection S) (b : ℝ) (hb : 0≤b)
    (hheight : ∀p∈S,p 2≤b) (g : KernelQuotient→ℝ)
    (hg : Integrable g (integralQuotientVolume globalKubotaKernel)) :
    IntegrableOn (fun p => g (kernelEuclideanProjection p)) S volume := by
  have hm := kernelEuclideanProjection_measurePreserving_on S hS hpos hinj
  have hh := (hm.integrable_comp_of_integrable hg.integrableOn).smul_measure
    (c := ENNReal.ofReal (b^3)) ENNReal.ofReal_ne_top
  exact hh.mono_measure (euclideanVolume_le_heightCube_hyperbolic S hS hpos b hb hheight)

theorem kernelLocalizedH1_norm_sq_le (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (M D A b : ℝ) (hM0 : 0≤M) (hD0 : 0≤D) (hA0 : 0≤A) (hb : 0≤b)
    (hheight : ∀p∈tsupport χ.func,p 2≤b)
    (hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M)
    (hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2)
    (f : kernelSmoothTests) :
    ‖kernelLocalizedH1 χ f‖^2≤b^3*((M+2*D)*‖kernelSmoothTestsToL2 f‖^2+
      2*A*kernelDirichletEnergy f) := by
  let G : KernelQuotient→ℝ := fun q =>
    (M+2*D)*‖f.1 q‖^2+2*A*kernelQuotientEnergyDensity f q
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _).add
      ((kernelQuotientEnergyDensity_integrable f).const_mul _)
  have hGn : ∀q,0≤G q := by
    intro q
    dsimp only [G]
    positivity [kernelQuotientEnergyDensity_nonneg f q]
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj b hb hheight G hG
  rw [kernelLocalizedH1_norm_sq]
  calc
    (∫p,kernelLocalizedDensity χ f p) =
        ∫p in tsupport χ.func,kernelLocalizedDensity χ f p :=
      (setIntegral_eq_integral_of_forall_compl_eq_zero (kernelLocalizedDensity_zero χ f)).symm
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on (kernelLocalizedDensity_integrable χ f).integrableOn hGI hS
      intro p hp
      exact kernelLocalizedDensity_le χ f p (χ.positive hp) M D A (hM p hp) (hD p hp) (hA p hp)
    _ ≤ b^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        b hb hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_add (((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul _)
        ((kernelQuotientEnergyDensity_integrable f).const_mul _),integral_const_mul,integral_const_mul,
        ←kernelSmoothTestsToL2_norm_sq]
      rfl

theorem kernelLocalizedH1_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedH1 χ f‖^2≤C*(‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hratio : ContinuousOn (fun p : EuclideanSpatial => (χ.func p)^2/(p 2)^2) (tsupport χ.func) :=
    (χ.smooth.continuous.pow 2).continuousOn.div (by fun_prop)
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨a,ha⟩ := χ.compact.bddAbove_image hratio
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let D := max 0 d
  let A := max 0 a
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hD0 : 0≤D := le_max_left _ _
  have hA0 : 0≤A := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hD : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hA : ∀p∈tsupport χ.func,(χ.func p)^2≤A*(p 2)^2 := fun p hp =>
    (div_le_iff₀ (sq_pos_of_pos (χ.positive hp))).mp
      ((ha ⟨p,hp,rfl⟩).trans (le_max_right _ _))
  refine ⟨B^3*(M+2*D+2*A),by positivity,fun f => ?_⟩
  refine (kernelLocalizedH1_norm_sq_le χ hinj M D A B hM0 hD0 hA0 hB0 hheight hM hD hA f).trans ?_
  rw [mul_assoc (B^3) (M+2*D+2*A)]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg hB0 3)
  have hm0 := sq_nonneg ‖kernelSmoothTestsToL2 f‖
  have he0 := kernelDirichletEnergy_nonneg f
  nlinarith [mul_nonneg (by positivity : 0≤M+2*D) he0,mul_nonneg hA0 hm0]

def kernelLocalizedSchwartzLinear (χ : PositiveChartCutoff) :
    kernelSmoothTests →ₗ[ℂ] 𝓢(EuclideanSpatial,ℂ) where
  toFun := kernelLocalizedSchwartz χ
  map_add' f g := by
    ext p
    change χ.func p • (kernelTestField f p+kernelTestField g p)=_
    exact smul_add _ _ _
  map_smul' c f := by
    ext p
    change χ.func p • (c • kernelTestField f p)=c • (χ.func p • kernelTestField f p)
    exact smul_comm _ _ _

def kernelLocalizedH1Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanH1 where
  toFun := kernelLocalizedH1 χ
  map_add' f g := by
    apply euclideanH1Embedding_injective
    simp only [map_add,kernelLocalizedH1_embedding]
    rw [show kernelLocalizedSchwartz χ (f+g)=kernelLocalizedSchwartz χ f+kernelLocalizedSchwartz χ g
      from (kernelLocalizedSchwartzLinear χ).map_add f g]
    rfl
  map_smul' c f := by
    apply euclideanH1Embedding_injective
    simp only [map_smul,kernelLocalizedH1_embedding,RingHom.id_apply]
    rw [show kernelLocalizedSchwartz χ (c•f)=c•kernelLocalizedSchwartz χ f
      from (kernelLocalizedSchwartzLinear χ).map_smul c f]
    rfl

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

namespace CubicEisenstein

abbrev KernelEnergyAmbient := WithLp 2 (KernelQuotientL2 × KernelGradientL2)

def kernelEnergyCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyAmbient :=
  (WithLp.linearEquiv 2 ℂ (KernelQuotientL2 × KernelGradientL2)).symm.toLinearMap.comp
    (kernelSmoothTestsToL2.prod kernelGradientLinear)

def kernelEnergyGraphSubmodule : Submodule ℂ KernelEnergyAmbient :=
  (LinearMap.range kernelEnergyCore).topologicalClosure

abbrev KernelEnergyGraph := kernelEnergyGraphSubmodule

instance kernelEnergyGraph_complete : CompleteSpace KernelEnergyGraph :=
  (LinearMap.range kernelEnergyCore).isClosed_topologicalClosure.completeSpace_coe

example : InnerProductSpace ℂ KernelEnergyGraph := inferInstance

def kernelEnergyGraphCore : kernelSmoothTests →ₗ[ℂ] KernelEnergyGraph :=
  kernelEnergyCore.codRestrict kernelEnergyGraphSubmodule
    (fun f => (LinearMap.range kernelEnergyCore).le_topologicalClosure ⟨f,rfl⟩)

lemma kernelEnergyGraphCore_dense : DenseRange kernelEnergyGraphCore := by
  rw [DenseRange,Subtype.dense_iff,←Set.range_comp]
  change closure (Set.range kernelEnergyCore)⊆closure (Set.range kernelEnergyCore)
  rfl

def kernelEnergyMass : KernelEnergyGraph →L[ℂ] KernelQuotientL2 :=
  (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

def kernelEnergyGradient : KernelEnergyGraph →L[ℂ] KernelGradientL2 :=
  (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelGradientL2).comp
    ((WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).toContinuousLinearMap.comp
      kernelEnergyGraphSubmodule.subtypeL)

lemma kernelEnergyMass_core (f : kernelSmoothTests) :
    kernelEnergyMass (kernelEnergyGraphCore f)=kernelSmoothTestsToL2 f := rfl

lemma kernelEnergyGradient_core (f : kernelSmoothTests) :
    kernelEnergyGradient (kernelEnergyGraphCore f)=kernelGradientToL2 f := rfl

lemma kernelEnergyGraph_norm_sq (u : KernelEnergyGraph) :
    ‖u‖^2=‖kernelEnergyMass u‖^2+‖kernelEnergyGradient u‖^2 :=
  WithLp.prod_norm_sq_eq_of_L2 u.1

lemma kernelEnergyGraphCore_norm_sq (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore f‖^2=‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f := by
  rw [kernelEnergyGraph_norm_sq,kernelEnergyMass_core,kernelEnergyGradient_core,
    kernelGradientToL2_norm_sq]

lemma kernelEnergyMass_dense : DenseRange kernelEnergyMass := by
  apply kernelSmoothTestsToL2_dense.mono
  rintro _ ⟨f,rfl⟩
  exact ⟨kernelEnergyGraphCore f,rfl⟩

lemma kernelLocalizedH1_graph_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedH1Linear χ f‖≤C*‖kernelEnergyGraphCore f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  have hh := hbound f
  rw [←kernelEnergyGraphCore_norm_sq] at hh
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  change ‖kernelLocalizedH1 χ f‖^2≤(Real.sqrt C*‖kernelEnergyGraphCore f‖)^2
  rw [mul_pow,Real.sq_sqrt hC]
  exact hh

def kernelEnergyLocalize (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanH1 :=
  (kernelLocalizedH1Linear χ).extendOfNorm kernelEnergyGraphCore

lemma kernelEnergyLocalize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelEnergyLocalize χ (kernelEnergyGraphCore f)=kernelLocalizedH1 χ f :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense (kernelLocalizedH1_graph_bound χ hinj) f

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap LineDeriv

namespace CubicEisenstein

def kernelLocalizedL2Linear (χ : PositiveChartCutoff) : kernelSmoothTests →ₗ[ℂ] EuclideanL2 :=
  euclideanH1Embedding.toLinearMap.comp (kernelLocalizedH1Linear χ)

lemma kernelLocalizedL2Linear_apply (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelLocalizedL2Linear χ f=(kernelLocalizedSchwartz χ f).toLp 2 volume := rfl

lemma kernelLocalizedL2_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖^2≤C*‖kernelSmoothTestsToL2 f‖^2 := by
  obtain ⟨m,hm⟩ := χ.compact.bddAbove_image (χ.smooth.continuous.pow 2).continuousOn
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let M := max 0 m
  let B := max 0 b
  have hM0 : 0≤M := le_max_left _ _
  have hB0 : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hM : ∀p∈tsupport χ.func,(χ.func p)^2≤M := fun p hp =>
    (hm ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨B^3*M,by positivity,fun f => ?_⟩
  let G : KernelQuotient→ℝ := fun q => M*‖f.1 q‖^2
  have hG : Integrable G (integralQuotientVolume globalKubotaKernel) :=
    ((kernelSmoothTests_memLp f).norm.integrable_sq).const_mul M
  have hGn : ∀q,0≤G q := fun q => mul_nonneg hM0 (sq_nonneg _)
  have hS := χ.compact.measurableSet
  have hGI := kernelEuclideanProjection_volume_integrable (tsupport χ.func) hS χ.positive
    hinj B hB0 hheight G hG
  have hfi := ((kernelLocalizedSchwartz χ f).memLp 2 volume).norm.integrable_sq
  rw [kernelLocalizedL2Linear_apply,schwartz_toL2_norm_sq]
  calc
    (∫p,‖kernelLocalizedSchwartz χ f p‖^2) =
        ∫p in tsupport χ.func,‖kernelLocalizedSchwartz χ f p‖^2 := by
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      change ‖χ.func p • kernelTestField f p‖^2=0
      simp only [hz,Pi.zero_apply,zero_smul,norm_zero,zero_pow (by decide : 2≠0)]
    _ ≤ ∫p in tsupport χ.func,G (kernelEuclideanProjection p) := by
      apply setIntegral_mono_on hfi.integrableOn hGI hS
      intro p hp
      change ‖χ.func p • kernelTestField f p‖^2≤M*‖kernelTestField f p‖^2
      simp only [norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]
      exact mul_le_mul_of_nonneg_right (hM p hp) (sq_nonneg _)
    _ ≤ B^3*∫q,G q∂integralQuotientVolume globalKubotaKernel :=
      kernelEuclideanProjection_volume_integral_le (tsupport χ.func) hS χ.positive hinj
        B hB0 hheight G hG hGn
    _ = _ := by
      dsimp only [G]
      rw [integral_const_mul,←kernelSmoothTestsToL2_norm_sq,mul_assoc]

lemma kernelLocalizedL2_bound (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,∀f : kernelSmoothTests,
      ‖kernelLocalizedL2Linear χ f‖≤C*‖kernelSmoothTestsToL2 f‖ := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedL2_bounded χ hinj
  refine ⟨Real.sqrt C,fun f => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg C) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC]
  exact hbound f

def kernelL2Localize (χ : PositiveChartCutoff) : KernelQuotientL2 →L[ℂ] EuclideanL2 :=
  (kernelLocalizedL2Linear χ).extendOfNorm kernelSmoothTestsToL2

lemma kernelL2Localize_core (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (f : kernelSmoothTests) :
    kernelL2Localize χ (kernelSmoothTestsToL2 f)=(kernelLocalizedSchwartz χ f).toLp 2 volume :=
  LinearMap.extendOfNorm_eq kernelSmoothTestsToL2_dense (kernelLocalizedL2_bound χ hinj) f

lemma kernelEnergyLocalize_mass (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph) :
    euclideanH1Embedding (kernelEnergyLocalize χ u)=kernelL2Localize χ (kernelEnergyMass u) := by
  have heq : (fun v => euclideanH1Embedding (kernelEnergyLocalize χ v))=
      fun v => kernelL2Localize χ (kernelEnergyMass v) :=
    kernelEnergyGraphCore_dense.equalizer (by fun_prop) (by fun_prop) (by
      funext f
      simp only [Function.comp_apply,kernelEnergyLocalize_core χ hinj,
        kernelLocalizedH1_embedding,kernelEnergyMass_core,kernelL2Localize_core χ hinj])
  exact congrFun heq u

lemma kernelEnergyLocalize_eq_zero_of_mass_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelEnergyLocalize χ u=0 := by
  apply euclideanH1Embedding_eq_zero
  rw [kernelEnergyLocalize_mass χ hinj u,hu,map_zero]

end CubicEisenstein

end

end OAI
end OAIOriginalModule0214

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.VariationalLaplacian
Source SHA256: 056490af1a915e434289b57c9ed6943ca6c522b427512f78bba9f31346d827da
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0215


namespace OAI

noncomputable section

namespace CubicEisenstein

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff

def kernelLiftedCutoff (χ : PositiveChartCutoff) (w : HyperbolicSpace) : ℝ :=
  χ.func (hyperbolicEuclideanCoordinates w)

lemma kernelLiftedCutoff_continuous (χ : PositiveChartCutoff) : Continuous (kernelLiftedCutoff χ) :=
  χ.smooth.continuous.comp hyperbolicEuclideanCoordinates_continuous

lemma kernelLiftedCutoff_compact (χ : PositiveChartCutoff) : HasCompactSupport (kernelLiftedCutoff χ) := by
  apply HasCompactSupport.of_support_subset_isCompact
    (χ.compact.image_of_continuousOn (fun p hp =>
      (euclideanToHyperbolic_contMDiffAt p (χ.positive hp)).continuousAt.continuousWithinAt))
  intro w hw
  refine ⟨hyperbolicEuclideanCoordinates w,?_,euclideanToHyperbolic_coordinates w⟩
  exact subset_tsupport χ.func hw

lemma kernelLiftedCutoff_bounded (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀w,‖kernelLiftedCutoff χ w‖≤C := by
  obtain ⟨w,hw⟩ := (kernelLiftedCutoff_continuous χ).norm.exists_forall_ge_of_hasCompactSupport
    (kernelLiftedCutoff_compact χ).norm
  exact ⟨_,hw⟩

lemma kernelCutoffGradient_memLp (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    MemLp (fun w => kernelLiftedCutoff χ w • g w) 2 KernelFundamentalVolume := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  have hm : AEStronglyMeasurable (fun w => kernelLiftedCutoff χ w • g w) KernelFundamentalVolume :=
    (kernelLiftedCutoff_continuous χ).aestronglyMeasurable.smul (Lp.aestronglyMeasurable g)
  refine (Lp.memLp g).of_le_mul (c := C) hm (Eventually.of_forall (fun w => ?_))
  change ‖kernelLiftedCutoff χ w • g w‖≤C*‖g w‖
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg (g w))

def kernelCutoffGradient (χ : PositiveChartCutoff) (g : KernelGradientL2) : KernelGradientL2 :=
  (kernelCutoffGradient_memLp χ g).toLp (fun w => kernelLiftedCutoff χ w • g w)

lemma kernelCutoffGradient_coe (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    (kernelCutoffGradient χ g : HyperbolicSpace→EuclideanSpace ℂ (Fin 3))=ᵐ[KernelFundamentalVolume]
      fun w => kernelLiftedCutoff χ w • g w := (kernelCutoffGradient_memLp χ g).coeFn_toLp

def kernelCutoffGradientLinear (χ : PositiveChartCutoff) : KernelGradientL2 →ₗ[ℂ] KernelGradientL2 where
  toFun := kernelCutoffGradient χ
  map_add' g h := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (g+h),kernelCutoffGradient_coe χ g,
      kernelCutoffGradient_coe χ h,Lp.coeFn_add g h,
      Lp.coeFn_add (kernelCutoffGradient χ g) (kernelCutoffGradient χ h)] with w hgh hg hh ha ha'
    simp only [hgh,ha',ha,Pi.add_apply,hg,hh,smul_add]
  map_smul' c g := by
    apply Lp.ext
    filter_upwards [kernelCutoffGradient_coe χ (c•g),kernelCutoffGradient_coe χ g,
      Lp.coeFn_smul c g,Lp.coeFn_smul c (kernelCutoffGradient χ g)] with w hcg hg ha ha'
    simp only [RingHom.id_apply,hcg,ha',ha,Pi.smul_apply,hg]
    exact smul_comm _ _ _

lemma kernelCutoffGradient_bound (χ : PositiveChartCutoff) :
    ∃C : ℝ,∀g : KernelGradientL2,‖kernelCutoffGradientLinear χ g‖≤C*‖g‖ := by
  obtain ⟨C,hC⟩ := kernelLiftedCutoff_bounded χ
  refine ⟨C,fun g => ?_⟩
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [kernelCutoffGradient_coe χ g] with w hw
  change ‖kernelCutoffGradient χ g w‖≤_
  rw [hw,norm_smul]
  exact mul_le_mul_of_nonneg_right (hC w) (norm_nonneg _)

def kernelCutoffGradientCLM (χ : PositiveChartCutoff) : KernelGradientL2 →L[ℂ] KernelGradientL2 :=
  (kernelCutoffGradientLinear χ).mkContinuousOfExistsBound (kernelCutoffGradient_bound χ)

lemma kernelCutoffGradient_norm_sq (χ : PositiveChartCutoff) (g : KernelGradientL2) :
    ‖kernelCutoffGradientCLM χ g‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*‖g w‖^2∂KernelFundamentalVolume := by
  calc
    ‖kernelCutoffGradientCLM χ g‖^2=inner ℝ (kernelCutoffGradientCLM χ g) (kernelCutoffGradientCLM χ g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫w,inner ℝ (kernelCutoffGradient χ g w) (kernelCutoffGradient χ g w)∂KernelFundamentalVolume := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [kernelCutoffGradient_coe χ g] with w hw
      rw [hw,real_inner_self_eq_norm_sq,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

lemma kernelCutoffGradient_core_norm_sq (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2=
      ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂KernelFundamentalVolume := by
  rw [kernelCutoffGradient_norm_sq]
  apply integral_congr_ae
  filter_upwards [kernelGradientToL2_coe f] with w hw
  rw [hw,kernelGradientAt_norm_sq]

lemma kernelLocalizedField_reverse_energy (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) (hp : 0<p 2) :
    (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)≤
      2*(p 2)^2*kernelLocalizedDensity χ f p+
      2*(p 2)^2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
  have hsum : (χ.func p)^2*(∑j : Fin 3,‖fderiv ℝ (kernelTestField f) p
      (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤
      2*(∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)+
      2*(∑j : Fin 3,‖fderiv ℝ χ.func p
        (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)*‖kernelTestField f p‖^2 := by
    simp only [Finset.mul_sum,Finset.sum_mul,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j hj
    have he := kernelLocalizedField_fderiv χ f p hp (EuclideanSpace.basisFun (Fin 3) ℝ j)
    have he' : χ.func p • fderiv ℝ (kernelTestField f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)=
        fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)-
        fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p := by rw [he]; abel
    have hb := complex_norm_add_sq_le
      (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
      (- (fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j) • kernelTestField f p))
    rw [←sub_eq_add_neg,←he'] at hb
    simpa only [norm_smul,norm_neg,mul_pow,Real.norm_eq_abs,sq_abs,mul_assoc] using hb
  have hc := hyperbolicEuclideanCoordinates_toHyperbolic p hp
  have hv : hyperbolicHeight (euclideanToHyperbolic p)=p 2 := congrArg (fun q : EuclideanSpatial => q 2) hc
  rw [kernelTestEnergyDensity_eq_partials,hv]
  simp only [kernelTestPartial,hc]
  have hh := mul_le_mul_of_nonneg_left hsum (sq_nonneg (p 2))
  unfold kernelLocalizedDensity
  nlinarith [mul_nonneg (sq_nonneg (p 2)) (sq_nonneg ‖kernelLocalizedField χ f p‖)]

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff ENNReal

lemma kernelLocalizedDensity_nonneg (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (p : EuclideanSpatial) : 0≤kernelLocalizedDensity χ f p := by
  unfold kernelLocalizedDensity
  positivity

lemma hyperbolicVolume_le_densityBound (S : Set EuclideanSpatial) (hS : MeasurableSet S)
    (hpos : S⊆euclideanUpperHalf) (H : ℝ)
    (hH : ∀p∈S,((p 2)^3)⁻¹≤H) :
    hyperbolicEuclideanVolume.restrict S≤ENNReal.ofReal H • volume.restrict S := by
  rw [hyperbolicEuclideanVolume,MeasureTheory.restrict_withDensity hS,
    Measure.restrict_restrict hS,Set.inter_eq_left.mpr hpos]
  have hh : hyperbolicDensity≤ᵐ[volume.restrict S] (fun _ => ENNReal.ofReal H) := by
    filter_upwards [ae_restrict_mem hS] with p hp
    exact ENNReal.ofReal_le_ofReal (hH p hp)
  simpa only [MeasureTheory.withDensity_const] using MeasureTheory.withDensity_mono hh

instance hyperbolicVolume_finiteOnCompacts : IsFiniteMeasureOnCompacts hyperbolicVolume where
  lt_top_of_isCompact K hK := by
    let S := hyperbolicEuclideanCoordinates '' K
    have hSK : IsCompact S := hK.image hyperbolicEuclideanCoordinates_continuous
    have hS : MeasurableSet S := hSK.measurableSet
    have hpos : S⊆euclideanUpperHalf := by
      rintro p ⟨w,hw,rfl⟩
      exact hyperbolicHeight_pos w
    have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) S :=
      (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
        (fun p hp => pow_ne_zero _ (ne_of_gt (hpos hp)))
    obtain ⟨H,hH⟩ := hSK.bddAbove_image hrho
    have hb := hyperbolicVolume_le_densityBound S hS hpos H (fun p hp => hH ⟨p,hp,rfl⟩)
    have hm : hyperbolicEuclideanVolume S< (∞ : ℝ≥0∞) := by
      have hbu := Measure.le_iff.mp hb Set.univ MeasurableSet.univ
      simp only [Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,Measure.smul_apply,
        smul_eq_mul] at hbu
      exact hbu.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hSK.measure_lt_top)
    have heq : euclideanToHyperbolic ⁻¹' K=ᵐ[hyperbolicEuclideanVolume]S := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      apply propext
      constructor
      · intro h
        exact ⟨euclideanToHyperbolic p,h,hyperbolicEuclideanCoordinates_toHyperbolic p hp⟩
      · rintro ⟨w,hw,rfl⟩
        simpa only [Set.mem_preimage,euclideanToHyperbolic_coordinates] using hw
    rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable hK.measurableSet,
      measure_congr heq]
    exact hm

private lemma integrable_sq_mul_of_compact (a b : HyperbolicSpace → ℝ)
    (ha : Continuous a) (hb : Continuous b) (hc : HasCompactSupport a) :
    Integrable (fun w => (a w)^2*b w) hyperbolicVolume := by
  have hs : HasCompactSupport (fun w => (a w)^2) :=
    hc.comp_left (g := fun x : ℝ => x^2) (by simp)
  exact ((ha.pow 2).mul hb).integrable_of_hasCompactSupport hs.mul_right

lemma kernelLiftedCutoffEnergy_integrable (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    Integrable (fun w => (kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w) hyperbolicVolume :=
  integrable_sq_mul_of_compact (kernelLiftedCutoff χ) (kernelTestEnergyDensity f)
    (kernelLiftedCutoff_continuous χ) (kernelTestEnergyDensity_continuous f)
    (kernelLiftedCutoff_compact χ)

lemma kernelLiftedCutoffEnergy_integral (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    (∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume)=
      ∫p,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
  rw [hyperbolicVolume,integral_map euclideanToHyperbolic_measurable.aemeasurable
    (kernelLiftedCutoffEnergy_integrable χ f).aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
  simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]

lemma kernelCutoffGradient_core_estimate (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (B D H : ℝ) (_hB : 0≤B) (hD : 0≤D) (hH : 0≤H)
    (hheight : ∀p∈tsupport χ.func,p 2≤B)
    (hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D)
    (hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H)
    (f : kernelSmoothTests) :
    ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
      2*B^2*(H*‖kernelLocalizedH1 χ f‖^2+D*‖kernelSmoothTestsToL2 f‖^2) := by
  let S := tsupport χ.func
  have hS : MeasurableSet S := χ.compact.measurableSet
  have hpos : S⊆euclideanUpperHalf := χ.positive
  have hmeasure := hyperbolicVolume_le_densityBound S hS hpos H hdensity
  have hloc : IntegrableOn (kernelLocalizedDensity χ f) S hyperbolicEuclideanVolume :=
    (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
      (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top).mono_measure hmeasure
  have hmass : IntegrableOn (fun p => ‖kernelTestField f p‖^2) S hyperbolicEuclideanVolume := by
    exact (kernelEuclideanProjection_measurePreserving_on S hS hpos hinj).integrable_comp_of_integrable
      ((kernelSmoothTests_memLp f).norm.integrable_sq.integrableOn)
  have hweight : IntegrableOn (fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p))
      S hyperbolicEuclideanVolume := by
    have hh := (kernelLiftedCutoffEnergy_integrable χ f).comp_measurable euclideanToHyperbolic_measurable
    have heq : (fun p => (kernelLiftedCutoff χ (euclideanToHyperbolic p))^2*
        kernelTestEnergyDensity f (euclideanToHyperbolic p))=ᵐ[hyperbolicEuclideanVolume]
        fun p => (χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p) := by
      filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp
      simp only [kernelLiftedCutoff,hyperbolicEuclideanCoordinates_toHyperbolic p hp]
    exact (hh.congr heq).integrableOn
  have hlocBound : (∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)≤
      H*‖kernelLocalizedH1 χ f‖^2 := by
    have hh := integral_mono_measure hmeasure
      (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))
      (((kernelLocalizedDensity_integrable χ f).integrableOn).smul_measure
        (c := ENNReal.ofReal H) ENNReal.ofReal_ne_top)
    rw [integral_smul_measure,ENNReal.toReal_ofReal hH] at hh
    rw [kernelLocalizedH1_norm_sq]
    exact hh.trans (mul_le_mul_of_nonneg_left
      (setIntegral_le_integral (kernelLocalizedDensity_integrable χ f)
        (Eventually.of_forall (kernelLocalizedDensity_nonneg χ f))) hH)
  rw [kernelCutoffGradient_core_norm_sq]
  calc
    _ ≤ ∫w,(kernelLiftedCutoff χ w)^2*kernelTestEnergyDensity f w∂hyperbolicVolume :=
      setIntegral_le_integral (kernelLiftedCutoffEnergy_integrable χ f)
        (Eventually.of_forall (fun w => mul_nonneg (sq_nonneg _) (kernelTestEnergyDensity_nonneg f w)))
    _ = ∫p in S,(χ.func p)^2*kernelTestEnergyDensity f (euclideanToHyperbolic p)∂hyperbolicEuclideanVolume := by
      rw [kernelLiftedCutoffEnergy_integral]
      apply (setIntegral_eq_integral_of_forall_compl_eq_zero _).symm
      intro p hp
      have hz := (notMem_tsupport_iff_eventuallyEq.mp hp).self_of_nhds
      simp only [hz,Pi.zero_apply,zero_pow (by decide : 2≠0),zero_mul]
    _ ≤ ∫p in S,(2*B^2*kernelLocalizedDensity χ f p+2*B^2*D*‖kernelTestField f p‖^2)
        ∂hyperbolicEuclideanVolume := by
      apply setIntegral_mono_on hweight ((hloc.const_mul _).add (hmass.const_mul _)) hS
      intro p hp
      refine (kernelLocalizedField_reverse_energy χ f p (hpos hp)).trans ?_
      simp only [Pi.add_apply]
      gcongr
      · exact kernelLocalizedDensity_nonneg _ _ _
      · exact (hpos hp).le
      · exact hheight p hp
      · exact (hpos hp).le
      · exact hheight p hp
      · exact hderiv p hp
    _ = 2*B^2*((∫p in S,kernelLocalizedDensity χ f p∂hyperbolicEuclideanVolume)+
        D*(∫p in S,‖kernelTestField f p‖^2∂hyperbolicEuclideanVolume)) := by
      rw [integral_add (hloc.const_mul _) (hmass.const_mul _),integral_const_mul,integral_const_mul]
      ring
    _ ≤ _ := by
      gcongr
      exact kernelLocalMass_le S hS hpos hinj f

lemma kernelCutoffGradient_core_bounded (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    ∃C : ℝ,0≤C ∧ ∀f : kernelSmoothTests,
      ‖kernelCutoffGradientCLM χ (kernelGradientToL2 f)‖^2≤
        C*(‖kernelLocalizedH1 χ f‖^2+‖kernelSmoothTestsToL2 f‖^2) := by
  have hgrad : Continuous (fun p : EuclideanSpatial =>
      ∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2) := by
    apply continuous_finsetSum
    intro j hj
    exact (((χ.smooth.continuous_fderiv (by simp)).clm_apply continuous_const).norm.pow 2)
  have hrho : ContinuousOn (fun p : EuclideanSpatial => ((p 2)^3)⁻¹) (tsupport χ.func) :=
    (by fun_prop : Continuous (fun p : EuclideanSpatial => (p 2)^3)).continuousOn.inv₀
      (fun p hp => pow_ne_zero _ (ne_of_gt (χ.positive hp)))
  obtain ⟨d,hd⟩ := χ.compact.bddAbove_image hgrad.continuousOn
  obtain ⟨r,hr⟩ := χ.compact.bddAbove_image hrho
  obtain ⟨b,hb⟩ := χ.compact.bddAbove_image (f := fun p : EuclideanSpatial => p 2) (by fun_prop)
  let D := max 0 d
  let H := max 0 r
  let B := max 0 b
  have hD : 0≤D := le_max_left _ _
  have hH : 0≤H := le_max_left _ _
  have hB : 0≤B := le_max_left _ _
  have hheight : ∀p∈tsupport χ.func,p 2≤B := fun p hp =>
    (hb ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hderiv : ∀p∈tsupport χ.func,
      (∑j : Fin 3,‖fderiv ℝ χ.func p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2)≤D := fun p hp =>
    (hd ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  have hdensity : ∀p∈tsupport χ.func,((p 2)^3)⁻¹≤H := fun p hp =>
    (hr ⟨p,hp,rfl⟩).trans (le_max_right _ _)
  refine ⟨2*B^2*(H+D),by positivity,fun f => ?_⟩
  refine (kernelCutoffGradient_core_estimate χ hinj B D H hB hD hH hheight hderiv hdensity f).trans ?_
  rw [mul_assoc (2*B^2)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg hH (sq_nonneg ‖kernelSmoothTestsToL2 f‖),
    mul_nonneg hD (sq_nonneg ‖kernelLocalizedH1 χ f‖)]

lemma kernelEnergyCutoffGradient_eq_zero (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) (u : KernelEnergyGraph)
    (hu : kernelEnergyMass u=0) : kernelCutoffGradientCLM χ (kernelEnergyGradient u)=0 := by
  obtain ⟨C,hC,hbound⟩ := kernelCutoffGradient_core_bounded χ hinj
  have hh : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖^2≤
      C*(‖kernelEnergyLocalize χ u‖^2+‖kernelEnergyMass u‖^2) :=
    kernelEnergyGraphCore_dense.induction_on u (isClosed_le (by fun_prop) (by fun_prop))
      (fun f => by simpa only [kernelEnergyGradient_core,kernelEnergyMass_core,
        kernelEnergyLocalize_core χ hinj] using hbound f)
  rw [kernelEnergyLocalize_eq_zero_of_mass_zero χ hinj u hu,hu] at hh
  have hz : ‖kernelCutoffGradientCLM χ (kernelEnergyGradient u)‖=0 := by simpa using hh
  exact norm_eq_zero.mp hz

lemma kernelCutoffGradient_faithful (g : KernelGradientL2)
    (hg : ∀χ : PositiveChartCutoff,
      Set.InjOn kernelEuclideanProjection (tsupport χ.func) → kernelCutoffGradientCLM χ g=0) : g=0 := by
  let Cutoff := {χ : PositiveChartCutoff // Set.InjOn kernelEuclideanProjection (tsupport χ.func)}
  let U : Cutoff→Set HyperbolicSpace := fun χ => {w | kernelLiftedCutoff χ.1 w≠0}
  have hU : ∀χ,IsOpen (U χ) := fun χ =>
    isOpen_ne.preimage (kernelLiftedCutoff_continuous χ.1)
  have hcover : (Set.univ : Set HyperbolicSpace)⊆⋃χ,U χ := by
    intro w hw
    obtain ⟨χ,hχ,hrange,hinj⟩ :=
      kernelChartCutoff_exists (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
    refine Set.mem_iUnion.mpr ⟨⟨χ,hinj⟩,?_⟩
    change χ.func (hyperbolicEuclideanCoordinates w)≠0
    rw [hχ]
    norm_num
  obtain ⟨r,hr,hcov⟩ := isLindelof_univ.elim_countable_subcover U hU hcover
  let : Countable r := hr.to_subtype
  have heach (χ : Cutoff) : ∀ᵐw∂KernelFundamentalVolume,kernelLiftedCutoff χ.1 w • g w=0 := by
    have hzero := hg χ.1 χ.2
    change kernelCutoffGradient χ.1 g=0 at hzero
    filter_upwards [kernelCutoffGradient_coe χ.1 g,
      (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
      with w hw hz
    rw [hzero] at hw
    exact hw.symm.trans hz
  have hall : ∀ᵐw∂KernelFundamentalVolume,∀χ : r,kernelLiftedCutoff χ.1.1 w • g w=0 :=
    ae_all_iff.mpr (fun χ => heach χ.1)
  apply Lp.ext
  filter_upwards [hall,
    (Lp.coeFn_zero (E := EuclideanSpace ℂ (Fin 3)) (p := (2:ℝ≥0∞)) («μ» := KernelFundamentalVolume))]
    with w hw hz
  obtain ⟨χ,hχ⟩ := Set.mem_iUnion.mp (hcov (Set.mem_univ w))
  obtain ⟨hχr,hχw⟩ := Set.mem_iUnion.mp hχ
  have hsm := hw ⟨χ,hχr⟩
  have hne : kernelLiftedCutoff χ.1 w≠0 := hχw
  exact ((smul_eq_zero.mp hsm).resolve_left hne).trans hz.symm

theorem kernelEnergyMass_eq_zero (u : KernelEnergyGraph) (hu : kernelEnergyMass u=0) : u=0 := by
  have hgrad : kernelEnergyGradient u=0 :=
    kernelCutoffGradient_faithful _ (fun χ hinj => kernelEnergyCutoffGradient_eq_zero χ hinj u hu)
  apply norm_eq_zero.mp
  have hn := kernelEnergyGraph_norm_sq u
  simp only [hu,hgrad,norm_zero,zero_pow (by decide : 2≠0),add_zero] at hn
  nlinarith [norm_nonneg u]

theorem kernelEnergyMass_injective : Function.Injective kernelEnergyMass := by
  intro u v huv
  apply sub_eq_zero.mp
  apply kernelEnergyMass_eq_zero
  rw [map_sub,huv,sub_self]

lemma kernelInitialGradient_closure_unique (x : KernelQuotientL2 × KernelGradientL2)
    (hx : x∈kernelInitialGradient.graph.topologicalClosure) (hz : x.1=0) : x.2=0 := by
  let J := (WithLp.prodContinuousLinearEquiv 2 ℂ KernelQuotientL2 KernelGradientL2).symm
  have hi : J '' (kernelInitialGradientGraph : Set (KernelQuotientL2 × KernelGradientL2))=
      Set.range kernelEnergyCore := by
    ext y
    constructor
    · rintro ⟨z,⟨f,rfl⟩,rfl⟩
      exact ⟨f,rfl⟩
    · rintro ⟨f,rfl⟩
      exact ⟨(kernelSmoothTestsToL2 f,kernelGradientLinear f),⟨f,rfl⟩,rfl⟩
  rw [kernelInitialGradient_graph] at hx
  change x∈closure (kernelInitialGradientGraph : Set (KernelQuotientL2 × KernelGradientL2)) at hx
  have hh := image_closure_subset_closure_image J.continuous ⟨x,hx,rfl⟩
  rw [hi] at hh
  let u : KernelEnergyGraph := ⟨J x,hh⟩
  have hu : kernelEnergyMass u=0 := hz
  have hu0 := kernelEnergyMass_eq_zero u hu
  have hv := congrArg kernelEnergyGradient hu0
  change x.2=kernelEnergyGradient 0 at hv
  simpa only [map_zero] using hv

theorem kernelInitialGradient_isClosable : kernelInitialGradient.IsClosable := by
  refine ⟨kernelInitialGradient.graph.topologicalClosure.toLinearPMap,?_⟩
  exact (Submodule.toLinearPMap_graph_eq _ kernelInitialGradient_closure_unique).symm

def kernelWeakGradient : KernelQuotientL2 →ₗ.[ℂ] KernelGradientL2 := kernelInitialGradient.closure

theorem kernelWeakGradient_closed : kernelWeakGradient.IsClosed :=
  kernelInitialGradient_isClosable.closure_isClosed

theorem kernelWeakGradient_dense_domain : Dense (kernelWeakGradient.domain : Set KernelQuotientL2) :=
  kernelInitialGradient_dense_domain.mono (LinearPMap.le_closure kernelInitialGradient).1

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff InnerProductSpace

lemma kernelEnergyGraph_inner (u v : KernelEnergyGraph) :
    inner ℂ u v=inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v) := rfl

lemma kernelEnergyMass_norm_le (u : KernelEnergyGraph) : ‖kernelEnergyMass u‖≤‖u‖ := by
  have hh := kernelEnergyGraph_norm_sq u
  nlinarith [sq_nonneg ‖kernelEnergyGradient u‖,norm_nonneg (kernelEnergyMass u),norm_nonneg u]

lemma kernelEnergyMass_opNorm_le : ‖kernelEnergyMass‖≤1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (by simpa using kernelEnergyMass_norm_le)

def kernelVariationalSolution : KernelQuotientL2 →L[ℂ] KernelEnergyGraph :=
  kernelEnergyMass.adjoint

lemma kernelVariationalSolution_equation (F : KernelQuotientL2) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyMass (kernelVariationalSolution F)) (kernelEnergyMass v)+
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution F)) (kernelEnergyGradient v)=
        inner ℂ F (kernelEnergyMass v) := by
  rw [←kernelEnergyGraph_inner]
  exact kernelEnergyMass.adjoint_inner_left v F

lemma kernelVariationalSolution_unique (F : KernelQuotientL2) (u : KernelEnergyGraph)
    (hu : ∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v)) :
    u=kernelVariationalSolution F := by
  apply ext_inner_right ℂ
  intro v
  rw [kernelEnergyGraph_inner,kernelEnergyGraph_inner]
  exact (hu v).trans (kernelVariationalSolution_equation F v).symm

theorem kernelVariationalSolution_existsUnique (F : KernelQuotientL2) :
    ∃!u : KernelEnergyGraph,∀v : KernelEnergyGraph,
      inner ℂ (kernelEnergyMass u) (kernelEnergyMass v)+
        inner ℂ (kernelEnergyGradient u) (kernelEnergyGradient v)=inner ℂ F (kernelEnergyMass v) :=
  ⟨kernelVariationalSolution F,kernelVariationalSolution_equation F,
    fun u hu => kernelVariationalSolution_unique F u hu⟩

lemma kernelVariationalSolution_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalSolution F‖≤‖F‖ := by
  have hnorm : ‖kernelVariationalSolution‖=‖kernelEnergyMass‖ :=
    ContinuousLinearMap.adjoint.norm_map _
  calc
    ‖kernelVariationalSolution F‖≤‖kernelVariationalSolution‖*‖F‖ :=
      kernelVariationalSolution.le_opNorm F
    _ ≤1*‖F‖ := mul_le_mul_of_nonneg_right (hnorm ▸ kernelEnergyMass_opNorm_le) (norm_nonneg F)
    _ = _ := one_mul _

def kernelVariationalResolvent : KernelQuotientL2 →L[ℂ] KernelQuotientL2 :=
  kernelEnergyMass.comp kernelVariationalSolution

lemma kernelVariationalResolvent_norm_le (F : KernelQuotientL2) :
    ‖kernelVariationalResolvent F‖≤‖F‖ :=
  (kernelEnergyMass_norm_le _).trans (kernelVariationalSolution_norm_le F)

private lemma selfAdjoint_comp_adjoint {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    (A : E →L[ℂ] F) : IsSelfAdjoint (A.comp A.adjoint) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_adjoint]

lemma kernelVariationalResolvent_selfAdjoint : IsSelfAdjoint kernelVariationalResolvent :=
  selfAdjoint_comp_adjoint kernelEnergyMass

lemma kernelVariationalResolvent_positive (F : KernelQuotientL2) :
    0≤(inner ℂ F (kernelVariationalResolvent F)).re := by
  change 0≤(inner ℂ F (kernelEnergyMass (kernelEnergyMass.adjoint F))).re
  rw [←kernelEnergyMass.adjoint_inner_left]
  exact inner_self_nonneg (𝕜 := ℂ) (x := kernelEnergyMass.adjoint F)

lemma kernelVariationalResolvent_injective : Function.Injective kernelVariationalResolvent := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro F hF
  change kernelEnergyMass (kernelVariationalSolution F)=0 at hF
  have hu : kernelVariationalSolution F=0 := kernelEnergyMass_injective (by
    rw [map_zero]
    exact hF)
  have he : (fun g : KernelQuotientL2 => inner ℂ F g)=(fun _ => (0 : ℂ)) :=
    kernelEnergyMass_dense.equalizer (by fun_prop) continuous_const (by
      funext v
      change inner ℂ F (kernelEnergyMass v)=0
      rw [←kernelEnergyMass.adjoint_inner_left]
      change inner ℂ (kernelVariationalSolution F) v=0
      rw [hu,inner_zero_left])
  exact inner_self_eq_zero.mp (congrFun he F)

lemma kernelVariationalResolvent_dense : DenseRange kernelVariationalResolvent := by
  change Dense (kernelVariationalResolvent.range : Set KernelQuotientL2)
  apply Submodule.dense_iff_topologicalClosure_eq_top.mpr
  have hh := kernelVariationalResolvent.orthogonal_ker
  rw [LinearMap.ker_eq_bot.mpr kernelVariationalResolvent_injective,Submodule.bot_orthogonal_eq_top,
    kernelVariationalResolvent_selfAdjoint.adjoint_eq] at hh
  exact hh.symm

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelLaplacianEquation : (KernelQuotientL2 × KernelQuotientL2) →L[ℂ] KernelQuotientL2 :=
  kernelVariationalResolvent.comp ((ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)+
    (ContinuousLinearMap.snd ℂ KernelQuotientL2 KernelQuotientL2))-
      (ContinuousLinearMap.fst ℂ KernelQuotientL2 KernelQuotientL2)

def kernelLaplacianGraph : Submodule ℂ (KernelQuotientL2 × KernelQuotientL2) :=
  kernelLaplacianEquation.ker

lemma mem_kernelLaplacianGraph (u f : KernelQuotientL2) :
    (u,f)∈kernelLaplacianGraph ↔ kernelVariationalResolvent (u+f)=u := by
  change kernelVariationalResolvent (u+f)-u=0 ↔ _
  exact sub_eq_zero

lemma kernelLaplacianGraph_unique (x : KernelQuotientL2 × KernelQuotientL2)
    (hx : x∈kernelLaplacianGraph) (hz : x.1=0) : x.2=0 := by
  have hh := (mem_kernelLaplacianGraph x.1 x.2).mp hx
  rw [hz,zero_add] at hh
  apply kernelVariationalResolvent_injective
  rw [map_zero]
  exact hh

def kernelEnergyLaplacian : KernelQuotientL2 →ₗ.[ℂ] KernelQuotientL2 :=
  kernelLaplacianGraph.toLinearPMap

lemma kernelEnergyLaplacian_graph : kernelEnergyLaplacian.graph=kernelLaplacianGraph :=
  Submodule.toLinearPMap_graph_eq _ kernelLaplacianGraph_unique

lemma kernelEnergyLaplacian_closed : kernelEnergyLaplacian.IsClosed := by
  rw [LinearPMap.IsClosed,kernelEnergyLaplacian_graph]
  exact kernelLaplacianEquation.isClosed_ker

lemma kernelEnergyLaplacian_resolvent_graph (F : KernelQuotientL2) :
    (kernelVariationalResolvent F,F-kernelVariationalResolvent F)∈kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
  congr 1
  abel

lemma kernelEnergyLaplacian_resolvent_domain (F : KernelQuotientL2) :
    kernelVariationalResolvent F∈kernelEnergyLaplacian.domain :=
  LinearPMap.mem_domain_of_mem_graph (kernelEnergyLaplacian_resolvent_graph F)

lemma kernelEnergyLaplacian_resolvent_apply (F : KernelQuotientL2) :
    kernelEnergyLaplacian ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩=
      F-kernelVariationalResolvent F :=
  kernelEnergyLaplacian.mem_graph_snd_inj (kernelEnergyLaplacian.mem_graph _)
    (kernelEnergyLaplacian_resolvent_graph F) rfl

lemma kernelEnergyLaplacian_dense_domain :
    Dense (kernelEnergyLaplacian.domain : Set KernelQuotientL2) := by
  apply kernelVariationalResolvent_dense.mono
  rintro _ ⟨F,rfl⟩
  exact kernelEnergyLaplacian_resolvent_domain F

lemma kernelEnergyLaplacian_resolvent_relation (u : kernelEnergyLaplacian.domain) :
    kernelVariationalResolvent (kernelEnergyLaplacian u+u)=u := by
  have hh := kernelEnergyLaplacian.mem_graph u
  rw [kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph] at hh
  simpa only [add_comm] using hh

lemma kernelEnergyLaplacian_isFormalAdjoint :
    kernelEnergyLaplacian.IsFormalAdjoint kernelEnergyLaplacian := by
  intro u v
  have hh := kernelVariationalResolvent_selfAdjoint.isSymmetric
    (kernelEnergyLaplacian u+u) (kernelEnergyLaplacian v+v)
  simp only [ContinuousLinearMap.coe_coe] at hh
  rw [kernelEnergyLaplacian_resolvent_relation,kernelEnergyLaplacian_resolvent_relation] at hh
  simp only [inner_add_left,inner_add_right] at hh
  exact add_right_cancel hh.symm

lemma kernelEnergyLaplacian_form (u : kernelEnergyLaplacian.domain) (v : KernelEnergyGraph) :
    inner ℂ (kernelEnergyLaplacian u) (kernelEnergyMass v)=
      inner ℂ (kernelEnergyGradient (kernelVariationalSolution (kernelEnergyLaplacian u+u)))
        (kernelEnergyGradient v) := by
  have hh := kernelVariationalSolution_equation (kernelEnergyLaplacian u+u) v
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he,inner_add_left] at hh
  exact (add_left_cancel (hh.trans (add_comm _ _))).symm

lemma kernelEnergyLaplacian_nonnegative (u : kernelEnergyLaplacian.domain) :
    0≤(inner ℂ (kernelEnergyLaplacian u) (u : KernelQuotientL2)).re := by
  have hh := kernelEnergyLaplacian_form u
    (kernelVariationalSolution (kernelEnergyLaplacian u+u))
  have he : kernelEnergyMass (kernelVariationalSolution (kernelEnergyLaplacian u+u))=u :=
    kernelEnergyLaplacian_resolvent_relation u
  rw [he] at hh
  rw [hh]
  exact inner_self_nonneg (𝕜 := ℂ)

theorem kernelEnergyLaplacian_selfAdjoint : IsSelfAdjoint kernelEnergyLaplacian := by
  rw [LinearPMap.isSelfAdjoint_def]
  apply le_antisymm
  · apply LinearPMap.le_of_le_graph
    intro x hx
    obtain ⟨u,hu,hv⟩ := (kernelEnergyLaplacian.adjoint.mem_graph_iff).mp hx
    change (x.1,x.2)∈kernelEnergyLaplacian.graph
    rw [←hu,←hv,kernelEnergyLaplacian_graph,mem_kernelLaplacianGraph]
    apply ext_inner_right ℂ
    intro F
    have ha := LinearPMap.adjoint_isFormalAdjoint kernelEnergyLaplacian_dense_domain u
      ⟨kernelVariationalResolvent F,kernelEnergyLaplacian_resolvent_domain F⟩
    rw [kernelEnergyLaplacian_resolvent_apply] at ha
    have hs := kernelVariationalResolvent_selfAdjoint.isSymmetric
      ((u : KernelQuotientL2)+kernelEnergyLaplacian.adjoint u) F
    simp only [ContinuousLinearMap.coe_coe] at hs
    rw [hs,inner_add_left,ha,inner_sub_right]
    abel
  · exact LinearPMap.IsFormalAdjoint.le_adjoint kernelEnergyLaplacian_dense_domain
      kernelEnergyLaplacian_isFormalAdjoint

end CubicEisenstein

end

end OAI
end OAIOriginalModule0215

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.HighRadialBounds
Source SHA256: 62e5ea716c68c1bae7449bceb3650220667fee2ee8d6f972b2e877efa8f09822
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0216


namespace OAI

noncomputable section

namespace InitialMeanSquare

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

section

open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open CanonicalQuadraticSieve (Admissible)

theorem initial_squarefree_target_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F R : Finset ι) (K : Finset ι → Finset ι → Finset O)
    (Z M : ℝ) (j : SecondLogIndex) :
    let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),
      Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 1 := by
  dsimp only
  intro z hz
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
  obtain ⟨hxs,hsq⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxp,hj⟩ := Finset.mem_filter.mp hxs
  have hk := (secondSupportedSector_mem p F K R Z M x hxp).2.2.2.1
  have hgeom := initial_log_target_bounds p hp x hk
  rw [initialLogIndex_eq_second,hj] at hgeom
  refine ⟨initial_squarefree_label_admissible p hp hg hc x hsq,?_,sourceRow_nonzero p x hk,hgeom.2⟩
  simpa only [sourceIdealPoint,elementNorm,eisEmbedding_norm_sq_eq_absNorm_span] using hgeom.1

end

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

theorem initialSquarefreeBinCost_of_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hCₛ : 0 ≤ Cₛ)
    (j : SecondLogIndex) (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ)
    (J N : ℕ) (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let E := densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J
  let S := (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N
  have hR : 0 < primeProductNorm p R := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hS : 0 < S := by dsimp [S]; positivity
  have hd := initial_source_density_transfer p hp hcop hg F (secondRayMinus Ψ ray)
    (secondRayPlus Ψ ray) (m*r) (s.image (sourceObservation p)) (windows 5) (windows 6)
    X X B J S Cₛ hS hCₛ hB (fun q => by
      simpa only [S,tripleLogDensity,mul_assoc] using hdec q)
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  calc
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*E) := mul_le_mul_of_nonneg_left hd hpref
    _ ≤ (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
        ((Cₛ/S)*(Cchild*(X*initialLogLabel j)^2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdensity (div_nonneg hCₛ hS.le)) hpref
    _ = _ := by
      dsimp only [X,S]
      rw [initial_log_mass Z (primeProductNorm p R) hR.ne',
        mul_pow (Z/primeProductNorm p R) (Real.exp 2) 2]
      have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
      rw [he]
      have hz := hZ.ne'
      have hr := hR.ne'
      field_simp

end

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels

lemma initial_bin_row_scale_le (U K : ℝ) (hK : 1 ≤ K) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U K) : secondLogK j ≤ K := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin K+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have hscale : secondLogK j ≤ normLogScale (normLogBin K) := by
    unfold secondLogK normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.2
  exact hscale.trans (normLogBin_scale_bounds K hK).1

theorem initial_bin_cost_uniform {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M Kmax ε Cₛ Cchild : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hKmax : 1 ≤ Kmax) (hε : 0 ≤ ε)
    (hCₛ : 0 ≤ Cₛ) (hCc : 0 ≤ Cchild)
    (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) (J N : ℕ)
    (hB : ∀ q, 0 ≤ B q)
    (hdec : ∀ q, (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cₛ*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2)
    (hdensity :
      let s := initialSquarefreeSector p (secondLogSector p ∅ F K R Z M j)
      let X := initialLogColumn Z (primeProductNorm p R) j
      let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
      densityChildEnergy p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (sourceIdealTarget (s.image (sourceObservation p))) (windows 5) (windows 6) X X J ≤
        Cchild*(X*initialLogLabel j)^2) :
    initialSquarefreeBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B ≤
      (H*Real.exp 4*Cchild*Cₛ*(Kmax*Real.exp 2)^ε)/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by
  have hb := initialSquarefreeBinCost_of_density_bound p hp hcop hg F R Ψ m ray K
    Z H M ε Cₛ Cchild hZ hH hCₛ j windows B J N hB hdec hdensity
  have hR := primeProductNorm_pos p hp R
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hden : 1 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
    apply one_le_pow₀
    have hnon : 0 ≤ H*secondLogK j*(primeProductNorm p R)^2/Z^2 := by positivity
    linarith
  have hnum : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
      ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε := by positivity
  have hrow : (secondLogK j*Real.exp 2)^ε ≤ (Kmax*Real.exp 2)^ε :=
    Real.rpow_le_rpow (mul_pos hk (Real.exp_pos 2)).le
    (mul_le_mul_of_nonneg_right (initial_bin_row_scale_le (Z*Real.exp M) Kmax hKmax j hj)
      (Real.exp_pos 2).le) hε
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε :=
      hb.trans (div_le_self hnum hden)
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*Cchild*Cₛ)*
        ‖secondRayCoefficient ray‖*(Kmax*Real.exp 2)^ε :=
      mul_le_mul_of_nonneg_left hrow (by positivity)
    _ = _ := by ring

end

open ActualEisensteinCubic ConcretePrimeRowBridge

theorem outside_prime_divisor_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I Q : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) (hQ : Prime Q)
    (hd : Q ∣ I) : Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  have hQpos : 1 ≤ Ideal.absNorm Q := Nat.one_le_iff_ne_zero.mpr
    (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  have hQI : Ideal.absNorm Q ≤ Ideal.absNorm I :=
    Nat.le_of_dvd (mem_outsideIdealsUpTo.mp hI).1 (map_dvd Ideal.absNorm hd)
  have hQo : Q ∈ outsideIdealsUpTo S D := mem_outsideIdealsUpTo.mpr
    ⟨hQpos, hQI.trans (mem_outsideIdealsUpTo.mp hI).2.1,
      fun P hP hPQ => (mem_outsideIdealsUpTo.mp hI).2.2 P hP (hPQ.trans hd)⟩
  apply mem_primePool_iff.mpr
  refine ⟨Q, Finset.mem_filter.mpr ⟨hQo,hQ.squarefree⟩,?_⟩
  exact (UniqueFactorizationMonoid.mem_normalizedFactors_iff hQ.ne_zero).mpr
    ⟨hQ,dvd_rfl⟩

theorem outside_factors_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I : Ideal O} (hI : I ∈ outsideIdealsUpTo S D) :
    ∀ Q ∈ UniqueFactorizationMonoid.normalizedFactors I,
      Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  intro Q hQ
  obtain ⟨hprime,hdiv⟩ :=
    (UniqueFactorizationMonoid.mem_normalizedFactors_iff
      (outsideIdealsUpTo_ne_bot S D I hI)).mp hQ
  exact outside_prime_divisor_mem_pool S D hI hprime hdiv

theorem outside_prime_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {Q : Ideal O} (hQ : Prime Q) (hQD : Ideal.absNorm Q ≤ D)
    (hQS : ∀ P ∈ S, ¬ P ∣ Q) :
    Q ∈ primePool (outsideSquarefreeIdeals S D) := by
  apply outside_prime_divisor_mem_pool S D (I := Q) _ hQ dvd_rfl
  exact mem_outsideIdealsUpTo.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr
      (fun hz => hQ.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz)),hQD,hQS⟩

end

section

open MeasureTheory
open scoped BigOperators Classical

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialElementaryConstant (A V : ℝ) : ℝ := 6*128^4*(Real.exp A*V)^2

lemma initialElementaryConstant_nonneg (A V : ℝ) : 0 ≤ initialElementaryConstant A V := by
  unfold initialElementaryConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_child_energy_elementary (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (T : Finset (Ideal O × O)) (V : ℝ → ℂ)
    (X lengthScale K A Vmax a b : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV : ∀ t,‖V t‖ ≤ Vmax) (hs : ∀ t,V t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (tn rn : Bool) :
    childEnergy p hp hcop hg F Ψ m T V X tn rn a b ≤
      initialElementaryConstant A Vmax*K*X^2*lengthScale := by
  by_cases hscale : 1 ≤ X*Real.exp A
  · have hb := childEnergy_elementary_normalized p hp hcop hg hc hinj F Ψ hΨ m T V
      X lengthScale K A Vmax a b hX hL hK hA hVmax hV hs hT tn rn
    have hXL : 0 < X*lengthScale := mul_pos hX (zero_lt_one.trans_le hL)
    have hb' := (div_le_iff₀ hXL).mp hb
    rw [max_eq_right hscale] at hb'
    convert hb' using 1
    unfold initialElementaryConstant
    field_simp

  · rw [childEnergy_subunit p hp hcop hg F Ψ m T V X A hX hs
      (lt_of_not_ge hscale) a b tn rn]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)

include hc hinj in

theorem initial_child_geometric_elementary (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) (q : Frequency) :
    childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤
      initialElementaryConstant A Vmax*K*(X*lengthScale)^2 := by
  let E := initialElementaryConstant A Vmax*K*X^2*lengthScale
  have hE : 0 ≤ E := by
    dsimp only [E]
    exact mul_nonneg (mul_nonneg (mul_nonneg (initialElementaryConstant_nonneg A Vmax)
      (zero_le_one.trans hK)) (sq_nonneg X)) (zero_le_one.trans hL)
  have he₁ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₁ hΨ₁ m T V₁
    X lengthScale K A Vmax q.1 q.2.2 hX hL hK hA hVmax hV₁ hs₁ hT true false
  have he₂ := initial_child_energy_elementary p hp hcop hg hc hinj F Ψ₂ hΨ₂ m T V₂
    X lengthScale K A Vmax q.2.1 q.2.2 hX hL hK hA hVmax hV₂ hs₂ hT false true
  have hb : childGeometricMean p hp hcop hg F Ψ₁ Ψ₂ m T V₁ V₂ X X q ≤ E := by
    calc
      _ ≤ Real.sqrt E*Real.sqrt E := mul_le_mul (Real.sqrt_le_sqrt he₁)
        (Real.sqrt_le_sqrt he₂) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = E := Real.mul_self_sqrt hE
  apply hb.trans
  calc
    E ≤ E*lengthScale := le_mul_of_one_le_right hE hL
    _ = _ := by dsimp only [E]; ring

include hp in

theorem initial_subbin_target_bounds (F R : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (Z M : ℝ) (j : SecondLogIndex)
    (s : Finset (SecondExpansionData ι)) (hs : s ⊆ secondLogSector p ∅ F K R Z M j) :
    ∀ z ∈ sourceIdealTarget (s.image (sourceObservation p)),z.1 ≠ ⊥ ∧
      (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
  apply sourceIdealTarget_bounds
  intro z hz
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  have hx' := hs hx
  obtain ⟨hxsec,hj⟩ := Finset.mem_filter.mp hx'
  have hk := (secondSupportedSector_mem p F K R Z M x hxsec).2.2.2.1
  have hji : initialLogIndex p x=j := (initialLogIndex_eq_second p x).trans hj
  have ht := initial_log_target_bounds p hp x hk
  rw [hji] at ht
  refine ⟨?_,ht.1,?_⟩
  · exact mul_ne_zero (primeSubsetGenerator_ne_zero _ _)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  · exact ht.2.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num))
      (normLogScale_pos _).le)

include hc hinj in

theorem initial_subbin_geometric_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z M A Vmax : ℝ)
    (hZ : 0 < Z) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (q : Frequency) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    childGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (sourceIdealTarget (s.image (sourceObservation p))) V₁ V₂ X X q ≤
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*(X*initialLogLabel j)^2 := by
  dsimp only
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hX : 0 < initialLogColumn Z (primeProductNorm p R) j :=
    div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hR)
  have hL : 1 ≤ initialLogLabel j := one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  exact initial_child_geometric_elementary p hp hcop hg hc hinj F
    (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (fun a => (secondRayMinus_norm_le Ψ ray a).trans (hΨ a))
    (fun a => (secondRayPlus_norm_le Ψ ray a).trans (hΨ a)) _ _ V₁ V₂
    _ _ _ A Vmax hX hL hrow hA hVmax hV₁ hV₂ hs₁ hs₂
    (initial_subbin_target_bounds p hp F R K Z M j s hs) q

end

open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRestrictedBinCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (Z H ε : ℝ) (j : SecondLogIndex)
    (V₁ V₂ : ℝ → ℂ) (B : Frequency → ℝ) : ℝ :=
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  (H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε)*
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃))

lemma initialRestrictedBinCost_full {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F R : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε : ℝ) (j : SecondLogIndex)
    (windows : Fin 7 → ℝ → ℂ) (B : Frequency → ℝ) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray
      (secondLogSector p ∅ F K R Z M j) Z H ε j (windows 5) (windows 6) B =
    initialBinCost p hp hcop hg F R Ψ m ray K Z H M ε j windows B := rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_density_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
    (∫ t₁ : ℝ,∫ t₂ : ℝ,∫ t₃ : ℝ,B (t₁,t₂,t₃)*
      sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (m*r) (s.image (sourceObservation p)) V₁ V₂ X X (t₁,t₂,t₃)) ≤
    (Cs*(initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2)/
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N)*(∫ t : ℝ,firstLogDensity 0 t)^3 := by
  dsimp only
  let X := initialLogColumn Z (primeProductNorm p R) j
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) R
  let G := sourceGeometricMean p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    (m*r) (s.image (sourceObservation p)) V₁ V₂ X X
  let E := initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2)*(X*initialLogLabel j)^2
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hE : 0 ≤ E := mul_nonneg
    (mul_nonneg (initialElementaryConstant_nonneg A Vmax) (mul_nonneg hk.le (Real.exp_pos _).le))
    (sq_nonneg _)
  have hG : ∀ q,0 ≤ G q := fun q => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hbound (q : Frequency) : G q ≤ E :=
    (sourceGeometricMean_le_ideal p hp hcop hg F (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      (m*r) (s.image (sourceObservation p)) V₁ V₂ X X q).trans
    (initial_subbin_geometric_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z M A Vmax
      hZ hA hVmax j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ q)
  have hweighted (q : Frequency) :
      G q ≤ E*(1+‖q.1‖)^J*(1+‖q.2.1‖)^J*(1+‖q.2.2‖)^J := by
    have h₁ := one_le_pow₀ (show 1 ≤ 1+‖q.1‖ by linarith [norm_nonneg q.1]) (n := J)
    have h₂ := one_le_pow₀ (show 1 ≤ 1+‖q.2.1‖ by linarith [norm_nonneg q.2.1]) (n := J)
    have h₃ := one_le_pow₀ (show 1 ≤ 1+‖q.2.2‖ by linarith [norm_nonneg q.2.2]) (n := J)
    exact (hbound q).trans ((le_mul_of_one_le_right hE h₁).trans
      ((le_mul_of_one_le_right (mul_nonneg hE (zero_le_one.trans h₁)) h₂).trans
        (le_mul_of_one_le_right (mul_nonneg (mul_nonneg hE (zero_le_one.trans h₁))
          (zero_le_one.trans h₂)) h₃)))
  exact polynomial_density_cost B G J _ Cs E (by positivity) hCs hE hB hG hdec hweighted

include hc hinj in

theorem initial_subbin_cost_elementary (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 0 < H) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
    ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*(secondLogK j*Real.exp 2)^ε /
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N := by
  have hb := initial_subbin_density_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    A Vmax Cs hZ hH hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hR := FirstPassCubeLabels.primeProductNorm_pos p hp R
  have hpref : 0 ≤ H*primeProductNorm p R/Z^2*‖secondRayCoefficient ray‖*
      (secondLogK j*Real.exp 2)^ε := by positivity
  have h := mul_le_mul_of_nonneg_left hb hpref
  apply h.trans_eq
  rw [initial_log_mass Z (primeProductNorm p R) hR.ne',mul_pow]
  have he : (Real.exp 2)^2=Real.exp 4 := by rw [pow_two,←Real.exp_add]; norm_num
  rw [he]
  have hz := hZ.ne'
  have hr := hR.ne'
  field_simp

end

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialRadial (Z H R : ℝ) (j : SecondLogIndex) : ℝ :=
  H*secondLogK j*R^2/Z^2

theorem initial_radial_absorbs_rows (Z H R k : ℝ) (N : ℕ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hR : 1 ≤ R) (hk : 0 ≤ k) :
    H*k^2/(1+H*k*R^2/Z^2)^(N+2) ≤ Z^4/(1+H*k*R^2/Z^2)^N := by
  let r := H*k*R^2/Z^2
  have hH0 : 0 ≤ H := zero_le_one.trans hH
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have h1 : 0 < 1+r := by linarith
  have hHR : 1 ≤ H*R^4 := one_le_mul_of_one_le_of_one_le hH (one_le_pow₀ hR)
  have he : Z^4*r^2=(H*k^2)*(H*R^4) := by
    dsimp [r]
    field_simp

  have hnum : H*k^2 ≤ Z^4*r^2 := by
    rw [he]
    exact le_mul_of_one_le_right (mul_nonneg hH0 (sq_nonneg k)) hHR
  change H*k^2/(1+r)^(N+2) ≤ Z^4/(1+r)^N
  calc
    _ ≤ Z^4*r^2/(1+r)^(N+2) := div_le_div_of_nonneg_right hnum (pow_nonneg h1.le _)
    _ ≤ Z^4*(1+r)^2/(1+r)^(N+2) := by
      apply div_le_div_of_nonneg_right _ (pow_nonneg h1.le _)
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr (by linarith) 2) (by positivity)
    _ = _ := by rw [pow_add]; field_simp

def initialHighRadialConstant (A Vmax Cs : ℝ) : ℝ :=
  Real.exp 8*initialElementaryConstant A Vmax*Cs*(∫ t : ℝ,firstLogDensity 0 t)^3

lemma initialHighRadialConstant_nonneg (A Vmax Cs : ℝ) (hCs : 0 ≤ Cs) :
    0 ≤ initialHighRadialConstant A Vmax Cs := by
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hc := initialElementaryConstant_nonneg A Vmax
  unfold initialHighRadialConstant
  positivity

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_subbin_cost_radial_decay (F R : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O) (ray : SecondRayIndex)
    (K : Finset ι → Finset ι → Finset O) (Z H M ε A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (j : SecondLogIndex) (s : Finset (SecondExpansionData ι))
    (hs : s ⊆ secondLogSector p ∅ F K R Z M j) (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : Frequency → ℝ) (J N : ℕ) (hB : ∀ q,0 ≤ B q)
    (hdec : ∀ q,(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialRestrictedBinCost p hp hcop hg F R Ψ m ray s Z H ε j V₁ V₂ B ≤
      initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖/(1+initialRadial Z H (primeProductNorm p R) j)^N := by
  have hH0 := zero_lt_one.trans_le hH
  have hb := initial_subbin_cost_elementary p hp hcop hg hc hinj F R Ψ hΨ m ray K Z H M
    ε A Vmax Cs hZ hH0 hA hVmax hCs j s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J (N+2) hB hdec
  have hR1 := primeProductNorm_ge_one p hp R
  have hR0 := zero_lt_one.trans_le hR1
  have hk : 0 < secondLogK j := normLogScale_pos _
  have hrow : 1 ≤ secondLogK j*Real.exp 2 :=
    one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hrowpow : (secondLogK j*Real.exp 2)^ε ≤ secondLogK j*Real.exp 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hrow hε
  have hcc := initialElementaryConstant_nonneg A Vmax
  have hi : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t := integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hpref : 0 ≤ ((H/primeProductNorm p R)*Real.exp 4*
      (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
      (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖ := by positivity
  have hden : 0 ≤ (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) := by positivity
  apply hb.trans
  calc
    _ ≤ ((H/primeProductNorm p R)*Real.exp 4*
        (initialElementaryConstant A Vmax*(secondLogK j*Real.exp 2))*Cs*
        (∫ t : ℝ,firstLogDensity 0 t)^3)*‖secondRayCoefficient ray‖*
        (secondLogK j*Real.exp 2)/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hrowpow hpref) hden
    _ = (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (H*(secondLogK j)^2/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)) := by
      unfold initialHighRadialConstant
      have he : Real.exp 4*(Real.exp 2)^2=Real.exp 8 := by
        rw [pow_two,←Real.exp_add,←Real.exp_add]; norm_num
      rw [←he]
      ring
    _ ≤ (initialHighRadialConstant A Vmax Cs/primeProductNorm p R*‖secondRayCoefficient ray‖)*
        (Z^4/(1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^N) :=
      mul_le_mul_of_nonneg_left (initial_radial_absorbs_rows Z H (primeProductNorm p R)
        (secondLogK j) N hZ hH hR1 hk.le) (by positivity)
    _ = _ := by unfold initialRadial; ring

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0216

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.SourceRemainders
Source SHA256: 17730eaa323879fc918194fddc78c1b95db74c949e85f6842dcf0049442f3141
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0217



namespace OAI

noncomputable section

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open Filter
open scoped Topology
open EisensteinEmbedding ConcreteTraceCRT ActualEisensteinCubic
open MulChar AddChar
open Filter Asymptotics
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter
open MulChar AddChar
open MulChar AddChar
open scoped LSeries.notation ArithmeticFunction.Moebius
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Ideal NumberField RingOfIntegers UniqueFactorizationMonoid
open Filter Asymptotics
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics Ideal NumberField
open Filter
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical SchwartzMap ContDiff
open scoped BigOperators Classical
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory Set
open scoped BigOperators
open scoped BigOperators Classical
open scoped BigOperators Classical
open ActualEisensteinCubic UniqueFactorizationMonoid
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical

namespace InitialMeanSquare

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

def initialHighRadialCost {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (F : Finset ι) (Ψ : O →* ℂ) (m : O)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ)
    (Z H U Kmax ε θ : ℝ) (V₁ V₂ : ℝ → ℂ) : ℝ :=
  ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F U,∑ j ∈ secondLogBinBox U Kmax,
    if Z^θ < initialRadial Z H (primeProductNorm p R) j then
      initialRestrictedBinCost p hp hcop hg F R Ψ m ray (s ray R j) Z H ε j V₁ V₂ (B ray R j)
    else 0

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
  [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})
  (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hc hinj in

theorem initial_high_radial_sum (F : Finset ι) (Ψ : O →* ℂ)
    (hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
    (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε θ A Vmax Cs : ℝ)
    (hZ : 0 < Z) (hH : 1 ≤ H) (hε : ε ≤ 1)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax) (hCs : 0 ≤ Cs)
    (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι))
    (hs : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
      s ray R j ⊆ secondLogSector p ∅ F K R Z M j)
    (V₁ V₂ : ℝ → ℂ)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J N : ℕ)
    (hB : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q)
    (hdec : ∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
      (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
      Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) :
    initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤
      (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := by
  have hconstant := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hzpow : 0 < Z^θ := Real.rpow_pos_of_pos hZ _
  unfold initialHighRadialCost
  apply initial_harmonic_aggregation p hinj F U Kmax _ (by positivity)
  intro ray R hR j hj
  split_ifs with hh
  · have hc' := initial_subbin_cost_radial_decay p hp hcop hg hc hinj F R Ψ hΨ m ray K
      Z H M ε A Vmax Cs hZ hH hε hA hVmax hCs j (s ray R j) (hs ray R hR j hj)
      V₁ V₂ hV₁ hV₂ hs₁ hs₂ (B ray R j) J N (hB ray R hR j hj) (hdec ray R hR j hj)
    have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    have hd : (Z^θ)^N ≤ (1+initialRadial Z H (primeProductNorm p R) j)^N :=
      pow_le_pow_left₀ hzpow.le (by linarith) N
    have hnum : 0 ≤ initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖ := by positivity
    apply hc'.trans
    calc
      _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/primeProductNorm p R*
        ‖secondRayCoefficient ray‖)/(Z^θ)^N :=
        div_le_div_of_nonneg_left hnum (pow_pos hzpow _) hd
      _ = _ := by ring
  · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
    positivity

end

theorem initial_log_harmonic_polynomial :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^2 := by
  obtain ⟨C,hC,hbound⟩ := initial_log_box_small_power 1 (by norm_num)
  refine ⟨C*(256*Real.exp 1),by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  have hc := hbound Y U Kmax hY hU hK hUY hKY
  rw [Real.rpow_one] at hc
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hl := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hY)
  have hlog : (normLogBin U : ℝ)+1 ≤ 2*Y := by linarith
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ (256*Real.exp 1)*Y := by
    have he := Real.exp_pos (1:ℝ)
    nlinarith
  have hnon : 0 ≤ 128*Real.exp 1*(normLogBin U+1 : ℝ) := by positivity
  calc
    _ ≤ (C*Y)*((256*Real.exp 1)*Y) := mul_le_mul hc hh hnon (by positivity)
    _ = _ := by ring

theorem initial_high_radial_order (θ τ : ℝ) (hθ : 0 < θ) :
    ∃ N : ℕ,38+τ ≤ θ*(N : ℝ) := by
  obtain ⟨N,hN⟩ := exists_nat_gt ((38+τ)/θ)
  refine ⟨N,?_⟩
  have hh := (div_lt_iff₀ hθ).mp hN
  linarith

theorem initial_high_radial_negligible (θ τ A Vmax Cs Ccap : ℝ) (N : ℕ)
    (hN : 38+τ ≤ θ*(N : ℝ)) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hCs : 0 ≤ Cs) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
      [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (F : Finset ι) (Ψ : O →* ℂ) (_hΨ : ∀ a,‖Ψ a‖ ≤ 1) (m : O)
      (K : Finset ι → Finset ι → Finset O) (Z H U Kmax M ε : ℝ),
      1 ≤ Z → 1 ≤ H → 0 < U → 0 < Kmax → ε ≤ 1 →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,
        s ray R j ⊆ secondLogSector p ∅ F K R Z M j) →
      ∀ (V₁ V₂ : ℝ → ℂ),
      (∀ t,‖V₁ t‖ ≤ Vmax) → (∀ t,‖V₂ t‖ ≤ Vmax) →
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) → (∀ t,V₂ t ≠ 0 → |t| ≤ A) →
      ∀ (B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ) (J : ℕ),
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,0 ≤ B ray R j q) →
      (∀ ray,∀ R ∈ boundedPrimeSupports p F U,∀ j ∈ secondLogBinBox U Kmax,∀ q,
        (1+H*secondLogK j*(primeProductNorm p R)^2/Z^2)^(N+2)*B ray R j q ≤
        Cs*firstLogDensity J q.1*firstLogDensity J q.2.1*firstLogDensity J q.2.2) →
      initialHighRadialCost p hp hcop hg F Ψ m s B Z H U Kmax ε θ V₁ V₂ ≤ C*Z^(-τ) := by
  obtain ⟨Clog,hClog,hlog⟩ := initial_log_harmonic_polynomial
  let Cbase := initialHighRadialConstant A Vmax Cs*initialRayMass*Clog*Ccap^2
  have hfixed := initialHighRadialConstant_nonneg A Vmax Cs hCs
  have hray := initialRayMass_nonneg
  have hbase : 0 ≤ Cbase := by
    dsimp [Cbase]
    exact mul_nonneg (mul_nonneg (mul_nonneg hfixed initialRayMass_nonneg) hClog.le) (sq_nonneg _)
  refine ⟨Cbase+1,by linarith,?_⟩
  intro ι _ p hp _ hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε hZ hH hU hK hε hUcap hKcap
    s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J hB hdec
  have hZ0 := zero_lt_one.trans_le hZ
  have hy : 1 ≤ Ccap*Z^17 := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog (Ccap*Z^17) U Kmax hy hU hK hUcap hKcap
  have hb := initial_high_radial_sum p hp hcop hg hc hinj F Ψ hΨ m K Z H U Kmax M ε θ
    A Vmax Cs hZ0 hH hε hA hVmax hCs s hs V₁ V₂ hV₁ hV₂ hs₁ hs₂ B J N hB hdec
  have hscalar : Z^(38 : ℕ)/(Z^θ)^N ≤ Z^(-τ) := by
    have he : Z^(38 : ℕ)/(Z^θ)^N=Z^((38 : ℝ)-θ*(N : ℝ)) := by
      rw [Real.rpow_sub hZ0,Real.rpow_mul_natCast hZ0.le]
      norm_cast
    rw [he]
    exact Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ (initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass*
        ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) := hb
    _ = ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ ((initialHighRadialConstant A Vmax Cs*Z^4/(Z^θ)^N)*initialRayMass)*
        (Clog*(Ccap*Z^17)^2) := mul_le_mul_of_nonneg_left hlogs (by positivity)
    _ = Cbase*(Z^(38 : ℕ)/(Z^θ)^N) := by dsimp [Cbase]; ring
    _ ≤ Cbase*Z^(-τ) := mul_le_mul_of_nonneg_left hscalar hbase
    _ ≤ (Cbase+1)*Z^(-τ) := mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ0.le _)

end

section
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

theorem initialErrorFrequencyBound_le (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    initialErrorFrequencyBound a b Z H ≤
      48*(1+Real.exp (initialErrorWindow a b))^16*Z^16 := by
  let Q := 1+Z*Real.exp (initialErrorWindow a b)
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  have hQ : 1 ≤ Q := by
    dsimp [Q]
    have hh : 0 ≤ Z*Real.exp (initialErrorWindow a b) := by positivity
    linarith
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have h3 : Q^3/H ≤ Q^3 := div_le_self (pow_nonneg hQ0 _) hH
  have hinner : 1+Q^3/H ≤ 2*Q^3 := by linarith [one_le_pow₀ hQ (n := 3)]
  have hT : initialTailHeight Z H (initialErrorWindow a b) ≤ 2*Q^5 := by
    change Q^2*(1+Q^3/H) ≤ 2*Q^5
    calc
      _ ≤ Q^2*(2*Q^3) := mul_le_mul_of_nonneg_left hinner (sq_nonneg Q)
      _ = _ := by ring
  have hT0 : 0 ≤ initialTailHeight Z H (initialErrorWindow a b) :=
    (initialTailHeight_pos Z H _ hZ0 hH0).le
  have hv : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H ≤ 2*Q^8 := by
    calc
      _ ≤ initialTailHeight Z H (initialErrorWindow a b)*Q^3 :=
        div_le_self (mul_nonneg hT0 (pow_nonneg hQ0 _)) hH
      _ ≤ (2*Q^5)*Q^3 := mul_le_mul_of_nonneg_right hT (pow_nonneg hQ0 _)
      _ = _ := by ring
  have hv2 : initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2 ≤ 4*Q^8 := by
    linarith [one_le_pow₀ hQ (n := 8)]
  have hb : initialErrorFrequencyBound a b Z H ≤ 48*Q^16 := by
    unfold initialErrorFrequencyBound
    change 3*(initialTailHeight Z H (initialErrorWindow a b)*Q^3/H+2)^2 ≤ _
    calc
      _ ≤ 3*(4*Q^8)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hv2 2) (by norm_num)
      _ = _ := by ring
  have hQZ : Q ≤ (1+Real.exp (initialErrorWindow a b))*Z := by
    dsimp [Q]
    nlinarith
  calc
    _ ≤ 48*Q^16 := hb
    _ ≤ 48*((1+Real.exp (initialErrorWindow a b))*Z)^16 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hQ0 hQZ 16) (by norm_num)
    _ = _ := by rw [mul_pow]; ring

def initialErrorRowBound (a b Z H : ℝ) : ℝ :=
  Z*Real.exp (initialErrorWindow a b)*initialErrorFrequencyBound a b Z H

lemma initialErrorRowBound_pos (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H) :
    0 < initialErrorRowBound a b Z H := by
  have ht := initialTailHeight_pos Z H (initialErrorWindow a b) hZ hH
  unfold initialErrorRowBound initialErrorFrequencyBound
  positivity

theorem initialErrorRowBound_valid {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H)
    (x : SecondExpansionData ι)
    (hx : x ∈ secondSupportedSector p F (fun _ _ => initialErrorCutoff a b Z H) R Z
      (initialErrorWindow a b)) :
    elementNorm (sourceObservation p x).1 ≤ initialErrorRowBound a b Z H := by
  obtain ⟨hG,hE,hV,hk,hkf,hR,hs⟩ := secondSupportedSector_mem p F
    (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) x hx
  have he := (secondSourceSupport_bounds p hp Z (initialErrorWindow a b) x hs hE).2.1
  have hf := initialErrorCutoff_norm_bound a b Z H hZ hH x.frequency hkf
  have hh := mul_le_mul he hf (sq_nonneg ‖eisEmbedding x.frequency‖) (by positivity)
  simpa only [initialErrorRowBound,sourceObservation,elementNorm,map_mul,norm_mul,mul_pow,
    primeSubsetGenerator_norm_eq_productNorm] using hh

def initialPolynomialCap (a b : ℝ) : ℝ :=
  1+Real.exp (initialErrorWindow a b)+
    48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16

lemma initialPolynomialCap_ge_one (a b : ℝ) : 1 ≤ initialPolynomialCap a b := by
  unfold initialPolynomialCap
  have he := Real.exp_pos (initialErrorWindow a b)
  have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
  linarith

theorem initial_actual_bin_polynomial_caps (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    Z*Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b*Z^17 ∧
    initialErrorRowBound a b Z H ≤ initialPolynomialCap a b*Z^17 := by
  have he := Real.exp_pos (initialErrorWindow a b)
  have hZ0 : 0 ≤ Z := zero_le_one.trans hZ
  have hz17 : Z ≤ Z^17 := by
    simpa only [pow_one] using pow_le_pow_right₀ hZ (by decide : 1 ≤ 17)
  have hC1 : Real.exp (initialErrorWindow a b) ≤ initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  have hC2 : 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 ≤
      initialPolynomialCap a b := by
    unfold initialPolynomialCap
    have hh : 0 ≤ 48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16 := by positivity
    linarith
  constructor
  · calc
      _ ≤ Real.exp (initialErrorWindow a b)*Z^17 := by
        rw [mul_comm Z]; exact mul_le_mul_of_nonneg_left hz17 he.le
      _ ≤ _ := mul_le_mul_of_nonneg_right hC1 (pow_nonneg hZ0 _)
  · have hb := mul_le_mul_of_nonneg_left (initialErrorFrequencyBound_le a b Z H hZ hH)
      (mul_nonneg hZ0 he.le)
    change initialErrorRowBound a b Z H ≤ _ at hb
    calc
      _ ≤ (Z*Real.exp (initialErrorWindow a b))*(48*(1+Real.exp (initialErrorWindow a b))^16*Z^16) := hb
      _ = (48*Real.exp (initialErrorWindow a b)*(1+Real.exp (initialErrorWindow a b))^16)*Z^17 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hC2 (pow_nonneg hZ0 _)

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem initial_two_windows_bounded (V₁ V₂ : ℝ → ℂ)
    (hc₁ : HasCompactSupport V₁) (hc₂ : HasCompactSupport V₂)
    (hs₁ : Continuous V₁) (hs₂ : Continuous V₂) :
    ∃ A Vmax : ℝ,0 ≤ A ∧ 0 ≤ Vmax ∧
      (∀ t,‖V₁ t‖ ≤ Vmax) ∧ (∀ t,‖V₂ t‖ ≤ Vmax) ∧
      (∀ t,V₁ t ≠ 0 → |t| ≤ A) ∧ (∀ t,V₂ t ≠ 0 → |t| ≤ A) := by
  obtain ⟨A₁,hA₁,hbound₁⟩ := hc₁.exists_pos_le_norm
  obtain ⟨A₂,hA₂,hbound₂⟩ := hc₂.exists_pos_le_norm
  obtain ⟨B₁,hB₁⟩ := hc₁.exists_bound_of_continuous hs₁
  obtain ⟨B₂,hB₂⟩ := hc₂.exists_bound_of_continuous hs₂
  refine ⟨max A₁ A₂,max 0 (max B₁ B₂),?_,le_max_left _ _,?_,?_,?_,?_⟩
  · exact hA₁.le.trans (le_max_left _ _)
  · intro t
    exact (hB₁ t).trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro t
    exact (hB₂ t).trans ((le_max_right _ _).trans (le_max_right _ _))
  · intro t ht
    have hh : ‖t‖ < A₁ := lt_of_not_ge (fun h => ht (hbound₁ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_left A₁ A₂)
  · intro t ht
    have hh : ‖t‖ < A₂ := lt_of_not_ge (fun h => ht (hbound₂ t h))
    simpa only [Real.norm_eq_abs] using hh.le.trans (le_max_right A₁ A₂)

theorem initial_high_radial_source
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b θ τ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hθ : 0 < θ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (F : Finset ι) (Ψ : O →* ℂ) (m : O) (Z H : ℝ),
      1 ≤ Z → 1 ≤ H → (∀ x,‖Ψ x‖ ≤ 1) →
      ∀ (s : SecondRayIndex → Finset ι → SecondLogIndex → Finset (SecondExpansionData ι)),
      (∀ ray R j,s ray R j ⊆ secondLogSector p ∅ F
        (fun _ _ => initialErrorCutoff a b Z H) R Z (initialErrorWindow a b) j) →
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      C*Z^(-τ) := by
  obtain ⟨N,hN⟩ := initial_high_radial_order θ τ hθ
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W (initialErrorWindow a b) hM hU hgs ε hε (N+2) 0
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded (windows 5) (windows 6) (hwc 5) (hwc 6)
      (hws 5).continuous (hws 6).continuous
  obtain ⟨Ch,hCh,hh⟩ := initial_high_radial_negligible θ τ A Vmax Cs (initialPolynomialCap a b)
    N hN hA hVmax hCs (initialPolynomialCap_ge_one a b)
  refine ⟨Ct*Ch+1,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr F Ψ m Z H hZ hH hΨ s hs
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hH0 := zero_lt_one.trans_le hH
  let K := fun (_ _ : Finset ι) => initialErrorCutoff a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let B : SecondRayIndex → Finset ι → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hB (ray : SecondRayIndex) (R : Finset ι) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg hinj hc hpr F R Ψ m ray K Z H (initialErrorWindow a b) j
        (s ray R j) hZ0 hH0 hΨ (hs ray R j))
  have hcost := hh p hp hcop hg hc hinj F Ψ hΨ m K Z H
    (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H)
    (initialErrorWindow a b) ε hZ hH (by positivity) (initialErrorRowBound_pos a b Z H hZ0 hH0)
    hε1 (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
    s (fun ray R _ j _ => hs ray R j) (windows 5) (windows 6) hV₁ hV₂ hs₁ hs₂ B 0
    (fun ray R _ j _ => (hB ray R j).1) (fun ray R _ j _ => (hB ray R j).2.1)
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if Z^θ < initialRadial Z H (primeProductNorm p R) j then
          ‖secondExpansionSource p hp hcop hg F Ψ m 1 1 ray (s ray R j) G G W H‖ else 0) ≤
      Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := by
    unfold initialHighRadialCost
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hjrad
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialRestrictedBinCost,G,B] ; ring
    · simp
  calc
    _ ≤ Ct*initialHighRadialCost p hp hcop hg F Ψ m s B Z H
        (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H) ε θ (windows 5) (windows 6) := hsum
    _ ≤ Ct*(Ch*Z^(-τ)) := mul_le_mul_of_nonneg_left hcost hCt
    _ ≤ (Ct*Ch+1)*Z^(-τ) := by
      have hz := Real.rpow_nonneg hZ0.le (-τ)
      nlinarith

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open MixedCrossSeparation (columnCoefficient columnPrimeCoprime)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeBlockExponent_ne_zero_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
  intro i hi
  by_cases hn:i∈N
  · simp [threeBlockExponent,hn]
  by_cases hp':i∈P
  · simp [threeBlockExponent,hn,hp']
  · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
    simp only [threeBlockExponent,ite_eq_right hn,ite_eq_right hp']
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2

lemma threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
  intro i hi
  unfold threeBlockExponent
  split_ifs <;> first | omega | exact ZMod.val_lt _

lemma threeGaussRowFactor_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O) :
    ‖threeGaussRowFactor p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ d h‖≤‖C₁ N‖*‖C₂ P‖ := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hG := FiniteGaussPhase.norm_canonicalProductGauss
    (fun i:S=>p i.val) (fun i=>hp i.val) (columnPrimeCoprime p hcop S)
    (fun i=>hg i.val) (fun i=>hc i.val) (fun i=>e i.val)
    (fun i=>threeBlockExponent_ne_zero_on N P B v ε₁ ε₂ i.val i.property)
    (fun i=>threeBlockExponent_lt_six_on N P B v ε₁ ε₂ i.val i.property)
  change ‖star (columnCoefficient p hp hcop hg N*C₁ N)*
    (columnCoefficient p hp hcop hg P*C₂ P)*
    FiniteGaussPhase.canonicalProductGauss (fun i:S=>p i.val) (fun i=>hp i.val)
      (columnPrimeCoprime p hcop S) (fun i=>hg i.val) (fun i=>e i.val)*
    (blockRow p hg S e d*star (blockRow p hg S e h))‖≤_
  simp only [norm_mul,norm_star,SecondPassArithmetic.columnCoefficient_norm_one p hp hcop hg hc,
    hG,one_mul,mul_one]
  apply mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg S e d)).trans (blockRow_norm_le_one p hg S e h)

lemma canonicalPairMode_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d h : O) :
    ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖)*
        (‖C₁ N‖*‖C₂ P‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖ := by
  have hn : 0<‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖ :=
    norm_pos_iff.mpr (eisEmbedding_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi=>hp i)))
  have ha : K*‖eisEmbedding h‖^2/(‖eisEmbedding d‖^2*
      primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) =
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by ring
  simp only [canonicalPairMode,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hK,abs_of_pos hn,ha]
  calc
    _ ≤ (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖))*
      ‖paperRadialFourier W ((K/(‖eisEmbedding d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖eisEmbedding h‖^2)‖*
      (‖C₁ N‖*‖C₂ P‖) := mul_le_mul_of_nonneg_left
        (threeGaussRowFactor_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ d h) (by positivity)
    _ = _ := by ring

end

theorem full_uniform_canonicalPairMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
