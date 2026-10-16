      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤scale*‖eisEmbedding h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤scale*‖eisEmbedding h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hcop hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hcop hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖eisEmbedding h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0

end

open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open SecondPassArithmetic (firstFrequencyDisk outside_firstFrequencyDisk columnLog_norm_upper)

def canonicalFirstFrequencyRadius {ι : Type*} [DecidableEq ι]
    (p : ι→O) (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (d : O) (X₁ X₂ K P : ℝ) : ℝ :=
  P*(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*X₁*X₂)/K

theorem firstFrequencyDisk_uniform {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0)
    (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hNQ : Disjoint N Q) (hNB : Disjoint N B) (hQB : Disjoint Q B)
    (d : O) (hd : d≠0) (X₁ X₂ K P M₁ M₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hK : 0<K)
    (hN : columnLog p X₁ N≤M₁) (hQ : columnLog p X₂ Q≤M₂)
    (h : O) (hh : h∉firstFrequencyDisk
      (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)) :
    P/Real.exp (M₁+M₂)≤
      (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖eisEmbedding h‖^2 := by
  let S := cubeActiveSupport B v ε₁ ε₂
  have hNS : Disjoint N S := hNB.mono_right (Finset.filter_subset _ _)
  have hQS : Disjoint Q S := hQB.mono_right (Finset.filter_subset _ _)
  have hNQS : Disjoint (N∪Q) S := Finset.disjoint_union_left.mpr ⟨hNS,hQS⟩
  have hnorm : primeProductNorm p ((N∪Q)∪S)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p S := by
    rw [primeProductNorm_union p _ _ hNQS,primeProductNorm_union p _ _ hNQ]
  have hNd : 0<‖eisEmbedding d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hU₁ : 0<X₁*Real.exp M₁ := mul_pos hX₁ (Real.exp_pos _)
  have hU₂ : 0<X₂*Real.exp M₂ := mul_pos hX₂ (Real.exp_pos _)
  let slow := K/(‖eisEmbedding d‖^2*(X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S)
  have hs : 0<slow := div_pos hK (mul_pos (mul_pos (mul_pos hNd hU₁) hU₂) (primeProductNorm_pos p hp S))
  have hn := columnLog_norm_upper p hp X₁ M₁ hX₁ N hN
  have hq := columnLog_norm_upper p hp X₂ M₂ hX₂ Q hQ
  have hprod : primeProductNorm p N*primeProductNorm p Q≤(X₁*Real.exp M₁)*(X₂*Real.exp M₂) :=
    mul_le_mul hn hq (primeProductNorm_pos p hp Q).le hU₁.le
  have hscale : slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪Q)∪S)) := by
    apply div_le_div_of_nonneg_left hK.le
      (mul_pos hNd (primeProductNorm_pos p hp _))
    rw [hnorm]
    calc
      _ ≤ ‖eisEmbedding d‖^2*((X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
      _ = _ := by ring
  have hr : (P/Real.exp (M₁+M₂))/slow=
      canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P := by
    dsimp [slow,canonicalFirstFrequencyRadius,S]
    rw [Real.exp_add]
    field_simp

  have ho := outside_firstFrequencyDisk _ h hh
  rw [←hr] at ho
  have hbase : P/Real.exp (M₁+M₂)≤slow*‖eisEmbedding h‖^2 := by
    have hz := (div_lt_iff₀ hs).mp ho
    simpa only [mul_comm] using hz.le
  exact hbase.trans (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))

theorem full_uniform_canonicalPairMode_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      Disjoint N Q → Disjoint N B → Disjoint Q B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K P M₁ M₂ : ℝ),0<X₁ → 0<X₂ → 0<K → 0≤P →
      columnLog p X₁ N≤M₁ → columnLog p X₂ Q≤M₂ → ∀(d : O),d≠0 →
      let S := (N∪Q)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖eisEmbedding d‖^2*primeProductNorm p S)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ Q)‖*
        (K/‖eisEmbedding (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ Q‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 scale)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hcop hg hc N Q B v ε₁ ε₂ hNQ hNB hQB C₁ C₂ W V₁ V₂ X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP hN hQ d hd
  apply hb p hp hcop hg hc N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K _ hK
    (div_nonneg hP (Real.exp_pos _).le) d hd
  intro h hh
  exact firstFrequencyDisk_uniform p hp N Q B v ε₁ ε₂ hNQ hNB hQB d hd
    X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hN hQ h hh

end FirstPassCubeLabels

end

end OAI
end OAIOriginalModule0217

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.DualZeroMode
Source SHA256: 432fcac889c9a486a39f7fb0ec4268756cd30f0f7b007a5a8f7b33a12436ccab
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0218


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

open scoped BigOperators Classical SchwartzMap
namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding)
open FiniteGaussPhase (canonicalProductGauss_cross_factors)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma threeGaussRowFactor_empty
    (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O)
    (hB : cubeActiveSupport B v ε₁ ε₂=∅) :
    threeGaussRowFactor p hp hcop hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d h=
      star (C₁ ∅)*C₂ ∅ := by
  let : IsEmpty {i:ι // i∈(((∅:Finset ι)∪∅)∪cubeActiveSupport B v ε₁ ε₂)} :=
    ⟨fun x=>by simpa [hB] using x.property⟩
  simp [MixedCrossSeparation.columnCoefficient,FiniteGaussPhase.canonicalProductCoefficient,
    threeGaussRowFactor,canonicalProductGauss_cross_factors,FiniteGaussPhase.angularFactor,
    blockRow,finiteSexticRow]

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma canonicalCubeResidual_empty (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) :
    canonicalCubeResidual p hg b C negative Ψ m f H ∅=
      H ((if negative then b.rightDivisor else b.leftDivisor)∪C) := by
  simp [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,
    finiteSquarefreeRow,rowCoprimeMask]

def canonicalCubeDualZero (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) 0

theorem canonicalCubeDualZero_eq_density
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
          (star (H₁ (b.rightDivisor∪C))*H₂ (b.leftDivisor∪C))*
          (K:ℂ)*paperRadialFourier W 0*
          ∏i∈C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit,
            (1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i}))
      else 0 := by
  unfold canonicalCubeDualZero
  simp_rw [actualFirstKernel_zero]
  split_ifs with hB
  · simp only [threeGaussRowFactor_empty p hp hcop hg _ _ _ _ _ _ _ _ hB,
      canonicalCubeResidual_empty,Bool.false_eq_true,ite_true,ite_false,one_mul]
    rw [←Finset.sum_mul]
    have hprime (i : ι) : Prime (Ideal.span {p i}) :=
      Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
    have hd (D : Finset ι) : (primeProductNorm p D:ℂ)=
        (Ideal.absNorm (∏i∈D,Ideal.span {p i}):ℂ) := by
      rw [primeProductNorm_eq_ideal_norm,Complex.ofReal_natCast]
    simp_rw [hd]
    rw [primeSubset_moebius_norm_sum _ hprime hinj]
    ring
  · simp only [mul_zero,Finset.sum_const_zero]

theorem canonicalCubeDualZero_norm_le
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖*|K| *‖paperRadialFourier W 0‖ else 0 := by
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs with hB
  · let M := C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
    have hprod : (∏i∈M,(1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i})))=
        ((∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i}))):ℝ) := by
      simp only [Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
        Complex.ofReal_div,Complex.ofReal_natCast]
    rw [show (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)=M from rfl,hprod]
    simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1]
    calc
      _ ≤ 1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖*
          ∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i})) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (abs_nonneg _)) (norm_nonneg _))
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).1
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_of_le_one_right
          (show 0≤(1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖) by positivity)
          (primeDensity_nonneg_le_one (fun i=>Ideal.span {p i}) M).2
  · simp

end

open ActualEisensteinCubic
open FirstPassCubeLabels

theorem boundedPrimeSupports_card_positive {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (X : ℝ) (hX : 0<X) :
    ((boundedPrimeSupports p F X).card:ℝ)≤128*X := by
  by_cases hx : 1≤X
  · exact boundedPrimeSupports_card p hinj F X hx
  · have he : boundedPrimeSupports p F X=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hx ((primeProductNorm_ge_one p hp S).trans (Finset.mem_filter.mp hS).2)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

end SecondPassArithmetic

namespace FirstPassCubeLabels
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open EisensteinSchwartzPoisson (paperRadialFourier)
open SecondPassArithmetic (boundedPrimeSupports boundedPrimeSupports_card_positive
  columnLog_norm_upper firstFrequencyDisk primeProductNorm_ge_one)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem actualFirstKernel_complement_eq_pairs
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) (T : Finset O) :
    (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val)=
      ∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
        ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val
        else 0 := by
  have hs (N Q : Finset ι) : Summable (fun h:{h:O // h∉T}=>if Disjoint N Q then
      canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0) := by
    by_cases hNQ : Disjoint N Q
    · simp only [hNQ,ite_true]
      exact (canonicalPairMode_summable p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).subtype _
    · simp only [hNQ,ite_false]
      exact summable_zero
  change (∑'h:{h:O // h∉T},∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
    canonicalPairMode p hp hcop hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN=>summable_sum (fun Q hQ=>hs N Q))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun Q hQ=>hs N Q)]
  apply Finset.sum_congr rfl
  intro Q hQ
  split_ifs <;> simp

end

theorem full_uniform_actualFirstKernel_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖eisEmbedding d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_disk_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let T:=firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
  let slow:=K/(‖eisEmbedding d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖eisEmbedding d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P/Real.exp (M₁+M₂):=div_nonneg hP (Real.exp_pos _).le
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hcop hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖eisEmbedding d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (eisEmbedding (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖eisEmbedding (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖eisEmbedding d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P/Real.exp (M₁+M₂))^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hcop hg hc N R B v ε₁ ε₂ hNR hNB hRB C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP (hS₁ N hNF hn) (hS₂ R hRF hr) d hd
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [ite_eq_left hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,ite_eq_right hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ (128*U₁)*(128*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end FirstPassCubeLabels

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i}))
  (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hinj

theorem canonicalCubeDualZero_support
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (ell K M : ℝ) (hell : 0<ell) (hgM : ∀t,g₁ t≠0→t≤M)
    (hC : ¬primeProductNorm p C≤ell*Real.exp M) :
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K=0 := by
  have hz : g₁ (columnLog p ell (b.rightDivisor∪C))=0 := by
    by_contra h
    exact hC ((primeProductNorm_mono p hp (Finset.subset_union_right)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj]
  split_ifs <;> simp [hz]

include hc

theorem canonicalCubeDualZero_fixed_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (G₁ G₂ ell K : ℝ) (hG₁ : 0≤G₁) (_hG₂ : 0≤G₂)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) :
    ‖canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        G₁*G₂*|K| *‖paperRadialFourier W 0‖ else 0 := by
  apply (canonicalCubeDualZero_norm_le p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hg₁ _) (hg₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

theorem canonicalCubeZero_common_sum_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ ell K M : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hell : 0<ell)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) (hgM : ∀t,g₁ t≠0→t≤M) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator I)
        (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        (128*(ell*Real.exp M))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (ConcretePrimeRowBridge.idealGenerator I)
    (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hL:0<ell*Real.exp M:=mul_pos hell (Real.exp_pos _)
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤ell*Real.exp M:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    rw [show z C I=0 from canonicalCubeDualZero_support p hp hcop hg hinj pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell K M hell hgM hbnd,mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [ite_eq_left hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_fixed_bound p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ ell K hG₁ hG₂ hg₁ hg₂
      rw [ite_eq_left hb] at hz
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [ite_eq_right hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hcop hg hinj,ite_eq_right hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end

theorem full_uniform_canonicalFirstZero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ ell K M B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<ell → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) → (∀t,g₁ t≠0→t≤M) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      C*B^(1+ε)*(ell*Real.exp M)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*128*128,by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M B F hΓ hG₁ hG₂ hell hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hg₁ hg₂ hgM
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:((bs.filter good).card:ℝ)≤C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then (128*(ell*Real.exp M))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact canonicalCubeZero_common_sum_bound p hp hcop hg hinj hc pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M hΓ hG₁ hG₂ hell (ha b hb) hg₁ hg₂ hgM
    _ = ((bs.filter good).card:ℝ)*((128*(ell*Real.exp M))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*((128*(ell*Real.exp M))*(128*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma originalLabelColumn_core_norm_le
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀u,‖Ψ u‖≤1) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H) c f S‖≤‖H S‖ := by
  have hm (z:O):‖rowCoprimeMask (fun i=>Ideal.span {p i}) S z‖≤1:=by
    unfold rowCoprimeMask;split_ifs <;> simp
  have hrow (z:O):‖finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S z‖^4≤1:=by
    simpa using pow_le_pow_left₀ (norm_nonneg _)
      (finiteSquarefreeRow_norm_le_one (fun i=>Ideal.span {p i}) hg S z) 4
  simp only [originalLabelColumn,multiplicativeCoreColumn,norm_mul,norm_pow]
  calc
    _ ≤ 1*‖H S‖*1*1*1 := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul (hΨ _) (hm m) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) (norm_nonneg _))
            (hm _) (norm_nonneg _) (by positivity))
          (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity))
        (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma originalLabelColumn_core_test_ne_zero
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι)
    (h : originalLabelColumn p hg B ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) c f S≠0) : H S≠0 := by
  intro hz
  apply h
  simp only [originalLabelColumn,multiplicativeCoreColumn,hz,mul_zero,zero_mul]

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem canonicalFirstFrequencyRadius_eq_global
    (b : CubeCoordinates ι) (hb : b.Admissible) (C D : Finset ι)
    (Ksrc K ell : ℝ) (hKsrc : 0<Ksrc) (hK : 0<K) :
    canonicalFirstFrequencyRadius p b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit (primeSubsetGenerator (fun i=>Ideal.span {p i}) D)
      (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
      (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) Ksrc (Ksrc/K)=
    globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D) := by
  have hl:b.swap.leftBit=b.rightBit:=rfl
  have hr:b.swap.rightBit=b.leftBit:=rfl
  simp only [canonicalFirstFrequencyRadius,globalFirstFrequencyScale,sourceGlobalBlock,
    cube_swap_support,cube_swap_sum,hl,hr,
    cubeActiveSupport_swap,primeSubsetGenerator_norm_eq_productNorm,
    CubeCoordinates.aLabel_left p b hb,CubeCoordinates.aLabel_right p b hb]
  change (Ksrc/K)*(primeProductNorm p D*primeProductNorm p
    (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*
    (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))*
    (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)))/Ksrc = _
  have hC:primeProductNorm p C≠0:=(primeProductNorm_pos p hp C).ne'
  have hL:primeProductNorm p b.leftDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  have hR:primeProductNorm p b.rightDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  simp only [primeProductNorm]
  simp only [primeProductNorm] at hC hL hR
  field_simp

end

theorem full_uniform_canonicalSource_kernel_tail (A : ℕ) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι),b.Admissible → ∀ C D:Finset ι,Disjoint C b.support →
      ∀(Ψ₁ Ψ₂:O→*ℂ),(∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      ∀(m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (G₁ G₂ M₁ M₂ Ksrc K ell:ℝ),
      0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
      let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
      let U₁:=X₁*Real.exp M₁
      let U₂:=X₂*Real.exp M₂
      let slow:=Ksrc/(primeProductNorm p D*primeProductNorm p
        (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*U₁*U₂)
      let T:=firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun S=>g₁ (columnLog p ell S)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun S=>g₂ (columnLog p ell S)))
        W (fun _=>1) (fun _=>1) 1 1 Ksrc
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤
      (128*U₁)*(128*U₂)*(G₁*G₂*Ksrc)*
        ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,Ctail,hCtail,hbound⟩:=full_uniform_actualFirstKernel_disk_remainder A
  refine ⟨s,Ctail,hCtail,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool b hb C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂
  dsimp only
  let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
  let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
  have hX₁:0<X₁:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hX₂:0<X₂:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hFB:Disjoint (pool\(b.support∪C)) b.support:=Finset.disjoint_left.mpr (fun i hi hb=>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hb))
  let C₁:=originalLabelColumn p hg b.support b.leftBit b.rightBit true
    (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) (∏i∈C,p i) f
  let C₂:=originalLabelColumn p hg b.support b.leftBit b.rightBit false
    (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) (∏i∈C,p i) f
  have hcoef₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₁ N‖≤G₁:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit true Ψ₁ hΨ₁ m₁ _ f _ N).trans (hg₁ _)
  have hcoef₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₂ N‖≤G₂:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit false Ψ₂ hΨ₂ m₂ _ f _ N).trans (hg₂ _)
  have hs₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₁ N≠0):columnLog p X₁ N≤M₁:=
    hM₁ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit true Ψ₁ m₁ _ f _ N hn)
  have hs₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₂ N≠0):columnLog p X₂ N≤M₂:=
    hM₂ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit false Ψ₂ m₂ _ f _ N hn)
  have h:=hbound p hp hinj hcop hg hc (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit hFB C₁ C₂ W
    G₁ G₂ X₁ X₂ Ksrc (Ksrc/K) M₁ M₂ hG₁ hG₂ hX₁ hX₂ hKsrc (div_pos hKsrc hK).le
    hcoef₁ hcoef₂ hs₁ hs₂ (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
  rw [canonicalFirstFrequencyRadius_eq_global p hp b hb C D Ksrc K ell hKsrc hK] at h
  simp only [primeSubsetGenerator_norm_eq_productNorm] at h
  have heq := fun h:O=>canonical_log_kernel p hp hcop hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ f
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h g₁ g₂ W Ksrc ell hell
  simp_rw [heq]
  exact h

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0218

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.CanonicalDensity
Source SHA256: 110aad3190ef2f2bfb7dc422ed4f02f4b8dbd5b7eba685c841b0b38771fd52bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0219


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

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve

theorem outsideIdealsUpTo_mono (S : Finset (Ideal O)) {D E : ℕ} (hDE : D ≤ E) :
    outsideIdealsUpTo S D ⊆ outsideIdealsUpTo S E := by
  intro I hI
  obtain ⟨hpos,hn,hS⟩ := mem_outsideIdealsUpTo.mp hI
  exact mem_outsideIdealsUpTo.mpr ⟨hpos,hn.trans hDE,hS⟩

theorem outside_row_cutoff_stable (S : Finset (Ideal O)) (hbad : fixedBadPrimes ⊆ S)
    {D E : ℕ} (hDE : D ≤ E) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hW : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D) (z : O) :
    idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z =
    idealRowSum (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
      (outside_good S E hbad) χ (fun n => W (n/Z)) z := by
  have hsub := outsideIdealsUpTo_mono S hDE
  unfold idealRowSum
  calc
    _ = ∑ I ∈ outsideIdealsUpTo S D,
        ShortDraftHeckeBridge.baseChangeWeight χ I * W ((Ideal.absNorm I : ℝ)/Z) *
        idealSexticRow (outsideIdealsUpTo S E) (outsideIdealsUpTo_ne_bot S E)
          (outside_good S E hbad) I z := by
      apply Finset.sum_congr rfl
      intro I hI
      rw [idealSexticRow_ambient (outsideIdealsUpTo S D) (outsideIdealsUpTo S E)
        (outsideIdealsUpTo_ne_bot S D) (outsideIdealsUpTo_ne_bot S E)
        (outside_good S D hbad) (outside_good S E hbad) I hI (hsub hI) z]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro I hIE hID
      have hw : W ((Ideal.absNorm I : ℝ)/Z) = 0 := by
        by_contra hn
        have hbound : (Ideal.absNorm I : ℝ) ≤ D :=
          ((div_le_iff₀ hZ).mp (hW _ hn)).trans hD
        have hnat : Ideal.absNorm I ≤ D := by exact_mod_cast hbound
        obtain ⟨hpos,_,hS⟩ := mem_outsideIdealsUpTo.mp hIE
        exact hID (mem_outsideIdealsUpTo.mpr ⟨hpos,hnat,hS⟩)
      rw [hw,mul_zero,zero_mul]

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def canonicalCubeDualFinite (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑h∈(T D).erase 0,actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

def canonicalCubeDualTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
      ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val

theorem canonicalCubeBeforePoisson_split
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) (T:Finset ι→Finset O)
    (hT:∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,(0:O)∈T D):
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K+
      canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T+
      canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T := by
  rw [canonicalCubeBeforePoisson_eq_all_modes p hp hcop hg hinj hc]
  · unfold canonicalCubeDualZero canonicalCubeDualFinite canonicalCubeDualTail
    rw [←mul_add,←mul_add,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply congrArg
    apply Finset.sum_congr rfl
    intro D hD
    rw [actualFirstKernel_truncate p hp hcop hg _ _ _ _ _ _ _ _ _ _ _ _ _ hK _
      (primeSubsetGenerator_ne_zero _ _) (T D)]
    rw [←Finset.sum_erase_add _ _ (hT D hD)]
    ring
  · exact hK

theorem canonicalCubeDualFinite_eq_raw_blocks
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι) (labels:Finset (Ideal O))
    (a:Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ))
    (K ell:ℝ) (T:Finset ι→Finset O):
    (∑I∈labels,a I*canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W K T)=
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      rawCanonicalBlock p hp hcop hg pool (sourceGlobalBlock b C D) (labels.product ((T D).erase 0))
        (fun x=>a x.1*canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator x.1)) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell := by
  simp only [canonicalCubeDualFinite,rawCanonicalBlock,sourceGlobalBlock,
    CubeCoordinates.swap_swap,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro h hh
  ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]

def canonicalSourceBlocks (pool:Finset ι) (bs:Finset (CubeCoordinates ι)):Finset (GlobalCubeBlock ι):=
  bs.biUnion (fun b=>(pool\b.support).powerset.biUnion (fun C=>
    (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.image
      (sourceGlobalBlock b C)))

theorem canonicalSourceBlocks_mem (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (q:GlobalCubeBlock ι):
    q∈canonicalSourceBlocks pool bs ↔ ∃b∈bs,∃C∈(pool\b.support).powerset,
      ∃D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        sourceGlobalBlock b C D=q := by
  simp only [canonicalSourceBlocks,Finset.mem_biUnion,Finset.mem_image]

theorem sum_canonicalSourceBlocks {M:Type*} [AddCommMonoid M]
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (f:GlobalCubeBlock ι→M):
    (∑q∈canonicalSourceBlocks pool bs,f q)=
      ∑b∈bs,∑C∈(pool\b.support).powerset,
        ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          f (sourceGlobalBlock b C D) := by
  unfold canonicalSourceBlocks
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro C hC
      rw [Finset.sum_image]
      intro D hD E hE he
      exact congrArg GlobalCubeBlock.firstDivisor he
    · intro C hC D hD hne
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      obtain ⟨E,hE,he⟩:=Finset.mem_image.mp hq
      obtain ⟨F,hF,hf⟩:=Finset.mem_image.mp hq'
      exact hne (congrArg GlobalCubeBlock.common (he.trans hf.symm))
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨C,hC,E,hE,he⟩:=by
      simpa only [Finset.mem_biUnion,Finset.mem_image] using hq
    obtain ⟨D,hD,F,hF,hf⟩:=by
      simpa only [Finset.mem_biUnion,Finset.mem_image] using hq'
    have hswap:=congrArg (fun q:GlobalCubeBlock ι=>q.cube.swap) (he.trans hf.symm)
    exact hne (by simpa only [sourceGlobalBlock,CubeCoordinates.swap_swap] using hswap)

theorem canonicalSourceBlocks_admissible (pool:Finset ι) (bs:Finset (CubeCoordinates ι))
    (hadm:∀b∈bs,b.Admissible) (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    GlobalCubeAdmissible q := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  have ha:=hadm b hb
  constructor
  · constructor
    · change b.rightDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.2
    · change b.leftDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.1
  constructor
  · change Disjoint C b.swap.support
    rw [cube_swap_support]
    exact Finset.disjoint_left.mpr (fun i hi hbi=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hbi)
  · change D⊆C∪b.swap.support
    rw [cube_swap_support]
    exact (Finset.mem_powerset.mp hD).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))

theorem canonicalSourceBlocks_cube_norms
    (p:ι→O) (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (B:ℝ)
    (hleft:∀b∈bs,‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hright:∀b∈bs,‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct p q.cube.support q.cube.leftExponent)‖^2≤B ∧
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p q.cube.support q.cube.rightExponent)‖^2≤B := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  change ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.swap.support b.rightExponent)‖^2≤B ∧
    ‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.swap.support b.leftExponent)‖^2≤B
  rw [cube_swap_support]
  exact ⟨hright b hb,hleft b hb⟩

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels

variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

def canonicalSourceCutoff (K ell:ℝ) (b:CubeCoordinates ι) (C D:Finset ι):Finset O:=
  firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma canonicalSourceCutoff_zero (K ell:ℝ) (hK:0≤K) (b:CubeCoordinates ι) (C D:Finset ι):
    (0:O)∈canonicalSourceCutoff p K ell b C D := by
  apply firstFrequencyDisk_zero
  unfold globalFirstFrequencyScale
  simp only [primeProductNorm]
  positivity

def canonicalSourceTotal (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc

def canonicalSourceZero (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc

def canonicalSourceFinite (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)

def canonicalSourceTail (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)

def canonicalBlockFrequencies (K ell:ℝ) (labels:Finset (Ideal O)) (q:GlobalCubeBlock ι):Finset (Ideal O×O):=
  labels.product ((firstFrequencyDisk (globalFirstFrequencyScale p K ell q)).erase 0)

def canonicalBlockCoefficient (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (q:GlobalCubeBlock ι) (x:Ideal O×O):ℂ:=
  a q.cube.swap q.common x.1*canonicalCubeOuter p hp hcop hg q.cube.swap q.common
    Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1)

theorem canonicalSourceFinite_eq_raw
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):
    canonicalSourceFinite p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell=
      ∑q∈canonicalSourceBlocks pool bs,rawCanonicalBlock p hp hcop hg pool q
        (canonicalBlockFrequencies p K ell labels q)
        (canonicalBlockCoefficient p hp hcop hg a Ψ₁ Ψ₂ m₁ m₂ q)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell := by
  rw [sum_canonicalSourceBlocks]
  unfold canonicalSourceFinite
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  rw [canonicalCubeDualFinite_eq_raw_blocks]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [canonicalBlockFrequencies,canonicalSourceCutoff,
    sourceGlobalBlock]
  rfl

theorem canonicalSourceTotal_split
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ) (hKsrc:0<Ksrc) (hK:0≤K):
    canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell=
      canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell+
      canonicalSourceFinite p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell+
      canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell := by
  unfold canonicalSourceTotal canonicalSourceZero canonicalSourceFinite canonicalSourceTail
  have hsplit (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):=
    canonicalCubeBeforePoisson_split p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc hKsrc (canonicalSourceCutoff p K ell b C)
      (fun D hD=>canonicalSourceCutoff_zero p K ell hK b C D)
  simp_rw [hsplit]
  simp only [mul_add,Finset.sum_add_distrib]

theorem canonicalBlockCoefficient_bound
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (Γ K ell:ℝ) (hΓ:0≤Γ) (hΨ₁:∀u,‖Ψ₁ u‖≤1) (hΨ₂:∀u,‖Ψ₂ u‖≤1)
    (ha:∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ)
    (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs)
    (x:Ideal O×O) (hx:x∈canonicalBlockFrequencies p K ell labels q):
    ‖canonicalBlockCoefficient p hp hcop hg a Ψ₁ Ψ₂ m₁ m₂ q x‖≤Γ := by
  have hI:x.1∈labels:=(Finset.mem_product.mp hx).1
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  simp only [canonicalBlockCoefficient,sourceGlobalBlock,CubeCoordinates.swap_swap,norm_mul]
  exact (mul_le_mul (ha b hb C hC x.1 hI)
    (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
    (norm_nonneg _) hΓ).trans_eq (mul_one Γ)

end

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

theorem canonicalSource_twoPassage_quantitative
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀t,g₁ t≠0→|t|≤M₁) (hg₂ : ∀t,g₂ t≠0→|t|≤M₂)
    (hV₁ : ∀t,V₁ t≠0→|t|≤N₁) (hV₂ : ∀t,V₂ t≠0→|t|≤N₂)
    (hWin₁ : ∀t,g₁ t≠0→V₁ t=1) (hWin₂ : ∀t,g₂ t≠0→V₂ t=1)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃(windows₁ windows₂ : Fin 7→ℝ→ℂ) (Cfirst C₁ Cd₁ Ct₁ C₂ Cd₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Cd₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Cd₂ ∧ 0<Ct₂ ∧
      (∀i,HasCompactSupport (windows₁ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₁ i)) ∧
      (∀i t,windows₁ i t≠0→|t|≤M₁+6+1) ∧
      (∀i,HasCompactSupport (windows₂ i)) ∧ (∀i,ContDiff ℝ ∞ (windows₂ i)) ∧
      (∀i t,windows₂ i t≠0→|t|≤M₂+6+1) ∧
      ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
      (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (Γ Ksrc K ell B F H U:ℝ),
      0≤Γ → 0<Ksrc → 0<K → 0<ell → 1≤B → 0<F → 0≤H → 1≤U →
      ell*Real.exp M₁≤U → ell*Real.exp M₂≤U →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,Squarefree I) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      ‖(ell*B^2*F:ℂ)⁻¹*
        (canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
         canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell)‖≤
      (Ksrc/K)*Cfirst*(globalFirstRowCap K ell B F)^deltaLoss*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψ₁ m₁ windows₁ C₁ Cd₁ Ct₁ Γ ε K ell B F M₁ H U A J N true)*
        Real.sqrt (globalFirstQuantitativeBudget p hp hcop hg pool (canonicalSourceBlocks pool bs)
          Ψ₂ m₂ windows₂ C₂ Cd₂ Ct₂ Γ ε K ell B F M₂ H U A J N false) := by
  obtain ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,htransfer⟩:=
    padded_rawCanonicalTwoPassage_quantitative W g₁ g₂ V₁ V₂ M₁ M₂ N₁ N₂ hM₁ hM₂ hN₁ hN₂
      hg₁ hg₂ hV₁ hV₂ hWin₁ hWin₂ ε deltaLoss hε hδ A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Cd₁,Ct₁,C₂,Cd₂,Ct₂,hCf,hC₁,hCd₁,hCt₁,hC₂,hCd₂,hCt₂,
    hw₁,hs₁,hb₁,hw₂,hs₂,hb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U
    hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂ ha hadm hleft hright hsf hf
  have hcenter : canonicalSourceTotal p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceZero p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell-
      canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell=
      canonicalSourceFinite p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell := by
    rw [canonicalSourceTotal_split p hp hcop hg hinj hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell hKsrc hK.le]
    ring
  rw [hcenter,canonicalSourceFinite_eq_raw]
  apply htransfer p hp hinj hcop hg hc hpr pool (canonicalSourceBlocks pool bs)
    (canonicalBlockFrequencies p K ell labels) (canonicalBlockCoefficient p hp hcop hg a Ψ₁ Ψ₂ m₁ m₂)
    (fun _=>Γ) Ψ₁ Ψ₂ m₁ m₂ Γ Ksrc K ell B F H U hΓ hKsrc hK hell hB hF hH hU hMU₁ hMU₂ hΨ₁ hΨ₂
  · exact fun q hq=>⟨hΓ,le_rfl⟩
  · exact fun q hq x hx=>canonicalBlockCoefficient_bound p hp hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ Γ K ell hΓ hΨ₁ hΨ₂ ha q hq x hx
  · exact canonicalSourceBlocks_admissible pool bs hadm
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).1
  · exact fun q hq=>(canonicalSourceBlocks_cube_norms p pool bs B hleft hright q hq).2
  · intro q hq x hx
    exact hsf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).1
  · intro q hq x hx
    exact hf x.1 (Finset.mem_product.mp hx).1
  · intro q hq x hx
    exact (mem_firstFrequencyDisk _ _).mp (Finset.mem_erase.mp (Finset.mem_product.mp hx).2).2

end SecondPassArithmetic

open MeasureTheory
open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (firstLogDensity)

theorem initial_subunit_row_le_label (Z X lengthScale K R κ : ℝ)
    (hZ : 1 ≤ Z) (hX : X ≤ 1) (hL : 0 ≤ lengthScale) (hK : 0 ≤ K)
    (hR : 1 ≤ R) (hκ : 0 ≤ κ) (hinv : K*R ≤ X*lengthScale*Z^(-κ)) : K ≤ lengthScale := by
  have hpow : Z^(-κ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by linarith)
  have hpow0 : 0 ≤ Z^(-κ) := Real.rpow_nonneg (zero_le_one.trans hZ) _
  calc
    K ≤ K*R := le_mul_of_one_le_right hK hR
    _ ≤ X*lengthScale*Z^(-κ) := hinv
    _ ≤ 1*lengthScale*Z^(-κ) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hX hL) hpow0
    _ ≤ lengthScale := by simpa only [one_mul,mul_one] using mul_le_mul_of_nonneg_left hpow hL

theorem initial_subunit_density_bound {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hKL : K ≤ lengthScale) (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      (initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3)*(X*lengthScale)^2 := by
  let C := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hd := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X lengthScale K A Vmax J hX hL hK hA hVmax hV₁ hV₂ hs₁ hs₂ hT
  change _/(X*lengthScale) ≤ C*K*X at hd
  have hraw := (div_le_iff₀ (mul_pos hX (zero_lt_one.trans_le hL))).mp hd
  calc
    _ ≤ (C*K*X)*(X*lengthScale) := hraw
    _ ≤ (C*lengthScale*X)*(X*lengthScale) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hKL hC) hX.le)
      (mul_nonneg hX.le (zero_le_one.trans hL))
    _ = _ := by dsimp only [C]; ring

lemma initialErrorFrequencyBound_ge_one (a b Z H : ℝ) (hZ : 0 < Z) (hH : 0 < H) :
    1 ≤ initialErrorFrequencyBound a b Z H := by
  have ht := initialTailHeight_pos Z H (initialErrorWindow a b) hZ hH
  have hv : 0 ≤ initialTailHeight Z H (initialErrorWindow a b)*
      (1+Z*Real.exp (initialErrorWindow a b))^3/H := by positivity
  unfold initialErrorFrequencyBound
  nlinarith [sq_nonneg (initialTailHeight Z H (initialErrorWindow a b)*
      (1+Z*Real.exp (initialErrorWindow a b))^3/H)]

lemma initialErrorRowBound_ge_one (a b Z H : ℝ) (hZ : 1 ≤ Z) (hH : 1 ≤ H) :
    1 ≤ initialErrorRowBound a b Z H := by
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le hZ (Real.one_le_exp hM))
    (initialErrorFrequencyBound_ge_one a b Z H (zero_lt_one.trans_le hZ) (zero_lt_one.trans_le hH))

end InitialMeanSquare

open MeasureTheory
open scoped BigOperators Classical ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm)

abbrev OutsidePrimeIndex (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) :=
  primePool (outsideSquarefreeIdeals S D)

def outsidePrime (S : Finset (Ideal ActualEisensteinCubic.O)) (D : ℕ) : OutsidePrimeIndex S D → ActualEisensteinCubic.O :=
  poolPrimary (outsideSquarefreeIdeals S D)

lemma outsidePrime_ne_zero (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,outsidePrime S D i ≠ 0 :=
  poolPrimary_ne_zero _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_maximal (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,(Ideal.span {outsidePrime S D i}).IsMaximal := by
  intro i
  rw [show Ideal.span {outsidePrime S D i}=i.val from
    poolPrimary_span _ (outsideSquarefree_admissible S D hbad) i]
  infer_instance

lemma outsidePrime_coprime (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {outsidePrime S D i})) :=
  poolPrimary_coprime _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_good (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,lambda ∉ Ideal.span {outsidePrime S D i} :=
  poolPrimary_good _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_odd (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {outsidePrime S D i}) ≠ 2 :=
  poolPrimary_odd _ (outsideSquarefree_admissible S D hbad)

lemma outsidePrime_injective (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    Function.Injective (fun i => Ideal.span {outsidePrime S D i}) := by
  intro i j hij
  apply Subtype.ext
  simpa only [outsidePrime,poolPrimary_span _ (outsideSquarefree_admissible S D hbad)] using hij

lemma outsidePrime_primary (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ) :
    ∀ i,lambda^2 ∣ outsidePrime S D i-1 := by
  intro i
  exact (CompletedGauss.primaryPrime_spec i.val (outsidePrime_ne_zero S hbad D i)).2.2.2

def initialExcludedNorm (S : Finset (Ideal ActualEisensteinCubic.O)) : ℝ :=
  max 1 (∏ P ∈ S,(Ideal.absNorm P : ℝ))

lemma initialExcludedNorm_ge_one (S : Finset (Ideal ActualEisensteinCubic.O)) : 1 ≤ initialExcludedNorm S :=
  le_max_left _ _

def outsideCanonicalDensity {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (D : ℕ)
    (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ) (X : ℝ) (J : ℕ) : ℝ :=
  letI := outsidePrime_maximal S hbad D
  densityChildEnergy (outsidePrime S D) (outsidePrime_ne_zero S hbad D)
    (outsidePrime_coprime S hbad D) (outsidePrime_good S hbad D) Finset.univ
    (secondRayMinus (conjugateMonoid (normCharacter χ)) ray)
    (secondRayPlus (conjugateMonoid (normCharacter χ)) ray)
    (primeSubsetGenerator (fun i => Ideal.span {outsidePrime S D i}) R) T V₁ V₂ X X (2*J)

def HasInitialCanonicalDensity {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) : Prop :=
  ∀ deltaLoss : ℝ,0 < deltaLoss → ∀ P : ℕ,∃ J : ℕ,
    ∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
    ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ P ≤ E ∧ ∀ (D : ℕ) (Z X lengthScale K : ℝ)
      (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
      1 ≤ Z → Cpool*Z^E ≤ D → 1 ≤ X → 1 ≤ lengthScale → 1 ≤ K →
      X ≤ Z^P → lengthScale ≤ Z^P → K ≤ Z^P →
      initialExcludedNorm S*primeProductNorm (outsidePrime S D) R ≤ Z^P →
      X*lengthScale ≤ Z^2 →
      K*(initialExcludedNorm S*primeProductNorm (outsidePrime S D) R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) →
      (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
        z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) →
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^deltaLoss*(X*lengthScale)^2

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0219

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.RetainedDensity
Source SHA256: 1723ab7836b304eb9ec5388dd105613bace95e7c2a8e2c728ecfe75774b97ca0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0220


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
open FirstPassCubeLabels (primeProductNorm)

lemma initialLogLabel_ge_one (j : SecondLogIndex) : 1 ≤ initialLogLabel j :=
  one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _))
    (Real.one_le_exp (by norm_num))

lemma initialLogColumn_pos (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 < Z) (hB : 0 < B) :
    0 < initialLogColumn Z B j :=
  div_pos hZ (mul_pos (mul_pos (normLogScale_pos _) (normLogScale_pos _)) hB)

lemma initialLogColumn_le (Z B : ℝ) (j : SecondLogIndex) (hZ : 0 ≤ Z) (hB : 1 ≤ B) :
    initialLogColumn Z B j ≤ Z := div_le_self hZ
  (one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (normLogScale_ge_one _) (normLogScale_ge_one _)) hB)

lemma initialLogLabel_cap (U Kmax : ℝ) (hU : 1 ≤ U) (j : SecondLogIndex)
    (hj : j ∈ secondLogBinBox U Kmax) : initialLogLabel j ≤ U^2*Real.exp 2 := by
  have hj' : j.1 < normLogBin U+1 ∧ j.2.1 < normLogBin U+1 ∧ j.2.2 < normLogBin Kmax+1 := by
    simpa only [secondLogBinBox,Finset.mem_product,Finset.mem_range] using hj
  have he : secondLogE j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogE normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.1
  have hv : secondLogV j ≤ U := by
    apply le_trans _ (normLogBin_scale_bounds U hU).1
    unfold secondLogV normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast Nat.le_of_lt_succ hj'.2.1
  unfold initialLogLabel
  simpa only [pow_two] using mul_le_mul_of_nonneg_right
    (mul_le_mul he hv (normLogScale_pos _).le (zero_le_one.trans hU)) (Real.exp_pos 2).le

theorem initial_radial_invariant (Z B c σ θ deltaLoss κ : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hB : 0 < B) (hc : 0 ≤ c) (hcZ : c ≤ Z^deltaLoss)
    (hmargin : deltaLoss+θ ≤ σ-κ)
    (hrad : initialRadial Z (Z^(1+σ)) B j ≤ Z^θ) :
    (secondLogK j*Real.exp 2)*(c*B) ≤
      initialLogColumn Z B j*initialLogLabel j*Z^(-κ) := by
  have hZ0 := zero_lt_one.trans_le hZ
  have hH : 0 < Z^(1+σ) := Real.rpow_pos_of_pos hZ0 _
  have hm : 0 < initialLogColumn Z B j*initialLogLabel j := by
    rw [initial_log_mass Z B hB.ne' j]
    positivity
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    rw [show -σ=(1 : ℝ)-(1+σ) by ring,Real.rpow_sub hZ0,Real.rpow_one]
  have hid : (secondLogK j*Real.exp 2)*(c*B)/(initialLogColumn Z B j*initialLogLabel j)=
      c*(Z/(Z^(1+σ)))*(Z^(1+σ)*secondLogK j*B^2/Z^2) := by
    rw [initial_log_mass Z B hB.ne' j]
    have hE := (Real.exp_pos (2 : ℝ)).ne'
    have hz := hZ0.ne'
    have hh := hH.ne'
    field_simp

  rw [mul_comm (initialLogColumn Z B j*initialLogLabel j)]
  apply (div_le_iff₀ hm).mp
  rw [hid,he]
  calc
    c*Z^(-σ)*(Z^(1+σ)*secondLogK j*B^2/Z^2) ≤ c*Z^(-σ)*Z^θ :=
      mul_le_mul_of_nonneg_left hrad (mul_nonneg hc (Real.rpow_nonneg hZ0.le _))
    _ ≤ Z^deltaLoss*Z^(-σ)*Z^θ := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcZ (Real.rpow_nonneg hZ0.le _)) (Real.rpow_nonneg hZ0.le _)
    _ = Z^(deltaLoss-σ+θ) := by rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]; congr 1
    _ ≤ Z^(-κ) := Real.rpow_le_rpow_of_exponent_le hZ (by linarith)

theorem initial_large_threshold (a b c deltaLoss : ℝ) (hc : 1 ≤ c) (hδ : 0 < deltaLoss) :
    ∃ Z0 : ℝ,1 ≤ Z0 ∧ ∀ Z : ℝ,Z0 ≤ Z →
      Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss := by
  let M := initialErrorWindow a b
  let Q := initialPolynomialCap a b
  let Z0 := 1+Real.exp 2+c*Real.exp M+Q*Real.exp 2+(Real.exp M)^2*Real.exp 2+c^(1/deltaLoss)
  have hc0 := (zero_lt_one.trans_le hc).le
  have hQ := initialPolynomialCap_ge_one a b
  have hQ0 : 0 ≤ Q := zero_le_one.trans hQ
  have he2 := Real.exp_pos (2 : ℝ)
  have heM := Real.exp_pos M
  have hr : 0 ≤ c^(1/deltaLoss) := Real.rpow_nonneg hc0 _
  have hp : 0 ≤ (Real.exp M)^2*Real.exp 2 := by positivity
  have hcp : 0 ≤ c*Real.exp M := by positivity
  have hqp : 0 ≤ Q*Real.exp 2 := by positivity
  have hZ0 : 1 ≤ Z0 := by dsimp [Z0]; linarith
  refine ⟨Z0,hZ0,?_⟩
  intro Z hZ
  have hzroot : c^(1/deltaLoss) ≤ Z := by dsimp [Z0] at hZ; linarith
  have hroot : (c^(1/deltaLoss))^deltaLoss=c := by
    rw [←Real.rpow_mul hc0]
    have hd : (1/deltaLoss)*deltaLoss=1 := by field_simp
    rw [hd,Real.rpow_one]
  refine ⟨?_,?_,?_,?_,?_⟩
  · dsimp [Z0] at hZ; linarith
  · change c*Real.exp M ≤ Z; dsimp [Z0] at hZ; linarith
  · change Q*Real.exp 2 ≤ Z; dsimp [Z0] at hZ; linarith
  · change (Real.exp M)^2*Real.exp 2 ≤ Z; dsimp [Z0] at hZ; linarith
  · rw [←hroot]
    exact Real.rpow_le_rpow hr hzroot hδ.le

theorem initial_large_bin_geometry {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (F R : Finset ι) (a b Z σ θ deltaLoss c : ℝ) (j : SecondLogIndex)
    (hZ : 1 ≤ Z) (hc : 1 ≤ c)
    (hR : R ∈ boundedPrimeSupports p F (Z*Real.exp (initialErrorWindow a b)))
    (hj : j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b))
      (initialErrorRowBound a b Z (Z^(1+σ))))
    (hσ : 0 ≤ σ) (hmargin : deltaLoss+θ ≤ σ-(1 : ℝ)/20)
    (hlarge : Real.exp 2 ≤ Z ∧ c*Real.exp (initialErrorWindow a b) ≤ Z ∧
      initialPolynomialCap a b*Real.exp 2 ≤ Z ∧
      (Real.exp (initialErrorWindow a b))^2*Real.exp 2 ≤ Z ∧ c ≤ Z^deltaLoss)
    (hrad : initialRadial Z (Z^(1+σ)) (primeProductNorm p R) j ≤ Z^θ) :
    let X := initialLogColumn Z (primeProductNorm p R) j
    let lengthScale := initialLogLabel j
    let K := secondLogK j*Real.exp 2
    X ≤ Z^20 ∧ lengthScale ≤ Z^20 ∧ K ≤ Z^20 ∧ c*primeProductNorm p R ≤ Z^20 ∧
      X*lengthScale ≤ Z^2 ∧ K*(c*primeProductNorm p R) ≤ X*lengthScale*Z^(-(1 : ℝ)/20) := by
  dsimp only
  have hZ0 := zero_lt_one.trans_le hZ
  have hB := primeProductNorm_ge_one p hp R
  have hBp := zero_lt_one.trans_le hB
  have hU : 1 ≤ Z*Real.exp (initialErrorWindow a b) := one_le_mul_of_one_le_of_one_le hZ
    (Real.one_le_exp (by unfold initialErrorWindow; positivity))
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
  have hBcap := (Finset.mem_filter.mp hR).2
  have hKcap := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
  have hKbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
    (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
  have hL := initialLogLabel_cap _ _ hU j hj
  have hp20 (n : ℕ) (hn : n ≤ 20) : Z^n ≤ Z^20 := pow_le_pow_right₀ hZ hn
  have hinv := initial_radial_invariant Z (primeProductNorm p R) c σ θ deltaLoss
    ((1 : ℝ)/20) j hZ hBp (zero_le_one.trans hc) hlarge.2.2.2.2 hmargin hrad
  rw [show -((1 : ℝ)/20)=(-1 : ℝ)/20 by ring] at hinv
  refine ⟨?_,?_,?_,?_,?_,hinv⟩
  · exact (initialLogColumn_le Z _ j hZ0.le hB).trans (by simpa using hp20 1 (by decide))
  · apply hL.trans
    calc
      _ = ((Real.exp (initialErrorWindow a b))^2*Real.exp 2)*Z^2 := by ring
      _ ≤ Z*Z^2 := mul_le_mul_of_nonneg_right hlarge.2.2.2.1 (sq_nonneg Z)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 3 (by decide)
  · calc
      _ ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
        mul_le_mul_of_nonneg_right (hKbin.trans hKcap) (Real.exp_pos _).le
      _ = (initialPolynomialCap a b*Real.exp 2)*Z^17 := by ring
      _ ≤ Z*Z^17 := mul_le_mul_of_nonneg_right hlarge.2.2.1 (pow_nonneg hZ0.le _)
      _ ≤ Z^20 := by simpa [pow_succ,mul_comm] using hp20 18 (by decide)
  · calc
      _ ≤ c*(Z*Real.exp (initialErrorWindow a b)) := mul_le_mul_of_nonneg_left hBcap (zero_le_one.trans hc)
      _ = (c*Real.exp (initialErrorWindow a b))*Z := by ring
      _ ≤ Z*Z := mul_le_mul_of_nonneg_right hlarge.2.1 hZ0.le
      _ ≤ Z^20 := by simpa [pow_two] using hp20 2 (by decide)
  · rw [initial_log_mass Z (primeProductNorm p R) hBp.ne' j]
    calc
      _ ≤ Z*Real.exp 2 := mul_le_mul_of_nonneg_right (div_le_self hZ0.le hB) (Real.exp_pos _).le
      _ ≤ Z^2 := by simpa [pow_two] using mul_le_mul_of_nonneg_left hlarge.1 hZ0.le

end

section

open MeasureTheory
open scoped BigOperators Classical
open ActualEisensteinCubic SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (firstLogDensity)

theorem initial_density_elementary_squared_mass {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V₁ V₂ : ℝ → ℂ)
    (X lengthScale K A Vmax : ℝ) (J : ℕ) (hX : 0 < X) (hL : 1 ≤ lengthScale) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hVmax : 0 ≤ Vmax)
    (hV₁ : ∀ t,‖V₁ t‖ ≤ Vmax) (hV₂ : ∀ t,‖V₂ t‖ ≤ Vmax)
    (hs₁ : ∀ t,V₁ t ≠ 0 → |t| ≤ A) (hs₂ : ∀ t,V₂ t ≠ 0 → |t| ≤ A)
    (hT : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J) ≤
      (initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3)*K*(X*lengthScale)^2 := by
  let C := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hC : 0 ≤ C := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hd := childDensity_elementary_all_scales p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X lengthScale K A Vmax J hX hL hK hA hVmax hV₁ hV₂ hs₁ hs₂ hT
  change _/(X*lengthScale) ≤ C*K*X at hd
  have hraw := (div_le_iff₀ (mul_pos hX (zero_lt_one.trans_le hL))).mp hd
  have hbase : 0 ≤ (C*K*X)*(X*lengthScale) := by positivity
  calc
    _ ≤ (C*K*X)*(X*lengthScale) := hraw
    _ ≤ ((C*K*X)*(X*lengthScale))*lengthScale := le_mul_of_one_le_right hbase hL
    _ = _ := by dsimp only [C]; ring

end

section

open MeasureTheory
open scoped BigOperators Classical ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity)

theorem HasInitialCanonicalDensity.retained_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (a b σ θ ν η : ℝ) (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ J : ℕ,∀ V₁ V₂ : ℝ → ℂ,HasCompactSupport V₁ → HasCompactSupport V₂ →
      ContDiff ℝ ∞ V₁ → ContDiff ℝ ∞ V₂ →
      ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧ ∀ (D : ℕ) (Z : ℝ)
        (R : Finset (OutsidePrimeIndex S D)) (ray : SecondRayIndex) (j : SecondLogIndex)
        (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)),
        1 ≤ Z → Cpool*Z^E ≤ D →
        R ∈ boundedPrimeSupports (outsidePrime S D) Finset.univ (Z*Real.exp (initialErrorWindow a b)) →
        j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z (Z^(1+σ))) →
        initialRadial Z (Z^(1+σ)) (primeProductNorm (outsidePrime S D) R) j ≤ Z^θ →
        (∀ z ∈ T,Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧
          z.2 ≠ 0 ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2) →
        outsideCanonicalDensity χ S hbad D ray R T V₁ V₂
          (initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j) J ≤
        C*Z^η*(initialLogColumn Z (primeProductNorm (outsidePrime S D) R) j*initialLogLabel j)^2 := by
  obtain ⟨J,hJ⟩ := hcan η hη 20
  refine ⟨J,?_⟩
  intro V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂
  obtain ⟨Cc,Cpool,E,hCc,hCpool,hPE,hcanonical⟩ := hJ V₁ V₂ hVc₁ hVc₂ hVs₁ hVs₂
  obtain ⟨A,Vmax,hA,hVmax,hV₁,hV₂,hs₁,hs₂⟩ :=
    initial_two_windows_bounded V₁ V₂ hVc₁ hVc₂ hVs₁.continuous hVs₂.continuous
  obtain ⟨Z0,hZ0,hthreshold⟩ := initial_large_threshold a b (initialExcludedNorm S) ν
    (initialExcludedNorm_ge_one S) hν
  let Ce := initialElementaryConstant A Vmax*(∫ t : ℝ,firstLogDensity 0 t)^3
  let K0 := initialPolynomialCap a b*Z0^17*Real.exp 2
  let C := Cc+Ce*(K0+1)+1
  have hI : 0 ≤ ∫ t : ℝ,firstLogDensity 0 t :=
    integral_nonneg (fun t => FirstPassCubeLabels.firstLogDensity_nonneg 0 t)
  have hCe : 0 ≤ Ce := mul_nonneg (initialElementaryConstant_nonneg A Vmax) (pow_nonneg hI _)
  have hcap := initialPolynomialCap_ge_one a b
  have hK0 : 0 ≤ K0 := by dsimp [K0]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hCcC : Cc ≤ C := by dsimp [C]; nlinarith
  have hCeC : Ce ≤ C := by dsimp [C]; nlinarith
  have hCeKC : Ce*K0 ≤ C := by dsimp [C]; nlinarith
  refine ⟨C,Cpool,E,hC,hCpool,hPE,?_⟩
  intro D Z R ray j T hZ hpool hR hj hrad hT
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let X := initialLogColumn Z (primeProductNorm p R) j
  let lengthScale := initialLogLabel j
  let Kr := secondLogK j*Real.exp 2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ Z^(1+σ) := Real.one_le_rpow hZ (by linarith)
  have hB := primeProductNorm_ge_one p hp R
  have hBpos := zero_lt_one.trans_le hB
  have hX : 0 < X := initialLogColumn_pos Z _ j hZp hBpos
  have hL : 1 ≤ lengthScale := initialLogLabel_ge_one j
  have hKr : 1 ≤ Kr := one_le_mul_of_one_le_of_one_le
    (normLogScale_ge_one _) (Real.one_le_exp (by norm_num))
  have hZη : 1 ≤ Z^η := Real.one_le_rpow hZ hη.le
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hΨ₁ : ∀ z,‖secondRayMinus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayMinus_norm_le Ψ ray z).trans (hΨ z)
  have hΨ₂ : ∀ z,‖secondRayPlus Ψ ray z‖ ≤ 1 :=
    fun z => (secondRayPlus_norm_le Ψ ray z).trans (hΨ z)
  have hTb : ∀ z ∈ T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ lengthScale ∧
      ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ Kr := by
    intro z hz
    exact ⟨(hT z hz).1.1,(hT z hz).2.1,(hT z hz).2.2.2⟩
  have promote (d : ℝ) (hd : d ≤ C)
      (he : outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ d*(X*lengthScale)^2) :
      outsideCanonicalDensity χ S hbad D ray R T V₁ V₂ X J ≤ C*Z^η*(X*lengthScale)^2 :=
    he.trans (mul_le_mul_of_nonneg_right (hd.trans (le_mul_of_one_le_right hC.le hZη)) (sq_nonneg _))
  by_cases hzlarge : Z0 ≤ Z
  · have hgeom := initial_large_bin_geometry p hp Finset.univ R a b Z σ θ ν (initialExcludedNorm S)
      j hZ (initialExcludedNorm_ge_one S) hR hj hσ hmargin (hthreshold Z hzlarge) hrad
    dsimp only at hgeom
    by_cases hxlarge : 1 ≤ X
    · exact (hcanonical D Z X lengthScale Kr R ray T hZ hpool hxlarge hL hKr
        hgeom.1 hgeom.2.1 hgeom.2.2.1 hgeom.2.2.2.1 hgeom.2.2.2.2.1 hgeom.2.2.2.2.2 hT).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCcC (Real.rpow_nonneg hZp.le _)) (sq_nonneg _))
    · have hKL : Kr ≤ lengthScale := initial_subunit_row_le_label Z X lengthScale Kr
        (initialExcludedNorm S*primeProductNorm p R) ((1 : ℝ)/20) hZ (le_of_not_ge hxlarge)
        (zero_le_one.trans hL) (zero_le_one.trans hKr)
        (one_le_mul_of_one_le_of_one_le (initialExcludedNorm_ge_one S) hB)
        (by norm_num) (by simpa only [Kr,X,lengthScale,neg_div] using hgeom.2.2.2.2.2)
      apply promote Ce hCeC
      exact initial_subunit_density_bound p hp hcop hg (outsidePrime_odd S hbad D)
        (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hKL hA hVmax hV₁ hV₂ hs₁ hs₂ hTb
  · have hKmax := initialErrorRowBound_ge_one a b Z (Z^(1+σ)) hZ hH
    have hkr : Kr ≤ K0 := by
      have hbin := initial_bin_row_scale_le (Z*Real.exp (initialErrorWindow a b))
        (initialErrorRowBound a b Z (Z^(1+σ))) hKmax j hj
      have hcapZ := (initial_actual_bin_polynomial_caps a b Z (Z^(1+σ)) hZ hH).2
      have hpow : Z^17 ≤ Z0^17 := pow_le_pow_left₀ hZp.le (le_of_not_ge hzlarge) 17
      calc
        Kr ≤ (initialPolynomialCap a b*Z^17)*Real.exp 2 :=
          mul_le_mul_of_nonneg_right (hbin.trans hcapZ) (Real.exp_pos _).le
        _ ≤ K0 := mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (zero_le_one.trans hcap)) (Real.exp_pos _).le
    apply promote (Ce*Kr) ((mul_le_mul_of_nonneg_left hkr hCe).trans hCeKC)
    exact initial_density_elementary_squared_mass p hp hcop hg (outsidePrime_odd S hbad D)
      (outsidePrime_injective S hbad D) Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
      hΨ₁ hΨ₂ _ T V₁ V₂ X lengthScale Kr A Vmax J hX hL hKr hA hVmax hV₁ hV₂ hs₁ hs₂ hTb

end

section

open scoped BigOperators Classical
open SecondPassArithmetic

theorem initial_log_harmonic_small_power (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ,0 < C ∧ ∀ (Y U Kmax : ℝ),1 ≤ Y → 0 < U → 0 < Kmax → U ≤ Y → Kmax ≤ Y →
      ((secondLogBinBox U Kmax).card : ℝ)*(128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Y^η := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power η hη
  refine ⟨128*Real.exp 1*C,by positivity,?_⟩
  intro Y U Kmax hY hU hK hUY hKY
  let B := 1+Real.log 27+22*Real.log Y
  have hlog := Real.log_nonneg hY
  have h27 : 0 ≤ Real.log 27 := Real.log_nonneg (by norm_num)
  have hB : 1 ≤ B := by dsimp [B]; linarith
  have hu := normLogBin_le_log_upper U Y hU hUY hY
  have hk := normLogBin_le_log_upper Kmax Y hK hKY hY
  have huB : (normLogBin U : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hkB : (normLogBin Kmax : ℝ)+1 ≤ B := by dsimp [B]; linarith
  have hcard : ((secondLogBinBox U Kmax).card : ℝ) ≤ B^3 := by
    rw [secondLogBinBox_card,Nat.cast_mul,Nat.cast_pow,Nat.cast_add,Nat.cast_add,Nat.cast_one]
    calc
      _ ≤ B^2*B := mul_le_mul (pow_le_pow_left₀ (by positivity) huB 2) hkB (by positivity) (sq_nonneg B)
      _ = _ := by ring
  have hh : 128*Real.exp 1*(normLogBin U+1 : ℝ) ≤ 128*Real.exp 1*B :=
    mul_le_mul_of_nonneg_left huB (by positivity)
  calc
    _ ≤ B^3*(128*Real.exp 1*B) := mul_le_mul hcard hh (by positivity) (pow_nonneg (zero_le_one.trans hB) _)
    _ = 128*Real.exp 1*B^4 := by ring
    _ ≤ 128*Real.exp 1*B^10 := mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hB (by decide)) (by positivity)
    _ ≤ 128*Real.exp 1*(C*Y^η) := mul_le_mul_of_nonneg_left (hbound Y hY) (by positivity)
    _ = _ := by ring

theorem initial_row_log_budget (η Ccap : ℝ) (hη : 0 < η) (hcap : 1 ≤ Ccap) :
    ∃ C : ℝ,0 < C ∧ ∀ (Z U Kmax : ℝ),1 ≤ Z → 0 < U → 0 < Kmax →
      U ≤ Ccap*Z^17 → Kmax ≤ Ccap*Z^17 →
      (Kmax*Real.exp 2)^η*((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ)) ≤ C*Z^(34*η) := by
  obtain ⟨C,hC,hlog⟩ := initial_log_harmonic_small_power η hη
  refine ⟨C*(Real.exp 2)^η*Ccap^(2*η),by positivity,?_⟩
  intro Z U Kmax hZ hU hK hUY hKY
  have hZ0 := zero_lt_one.trans_le hZ
  have hcap0 := zero_lt_one.trans_le hcap
  let Y := Ccap*Z^17
  have hY : 1 ≤ Y := one_le_mul_of_one_le_of_one_le hcap (one_le_pow₀ hZ)
  have hlogs := hlog Y U Kmax hY hU hK hUY hKY
  have hrow : (Kmax*Real.exp 2)^η ≤ (Y*Real.exp 2)^η := Real.rpow_le_rpow
    (mul_pos hK (Real.exp_pos _)).le (mul_le_mul_of_nonneg_right hKY (Real.exp_pos _).le) hη.le
  calc
    _ = (Kmax*Real.exp 2)^η*(((secondLogBinBox U Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin U+1 : ℝ))) := by ring
    _ ≤ (Y*Real.exp 2)^η*(C*Y^η) := mul_le_mul hrow hlogs (by positivity) (by positivity)
    _ = C*(Real.exp 2)^η*Y^(2*η) := by
      rw [Real.mul_rpow (zero_le_one.trans hY) (Real.exp_pos _).le]
      rw [show 2*η=η+η by ring,Real.rpow_add (zero_lt_one.trans_le hY)]
      ring
    _ = (C*(Real.exp 2)^η*Ccap^(2*η))*Z^(34*η) := by
      dsimp [Y]
      rw [Real.mul_rpow hcap0.le (pow_nonneg hZ0.le _),←Real.rpow_natCast_mul hZ0.le]
      norm_num
      ring_nf

end

section

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm firstLogDensity normalizedColumn columnLog)

theorem HasInitialCanonicalDensity.retained_source {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ θ ν η : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : 0 ≤ σ) (hν : 0 < ν) (hη : 0 < η)
    (hmargin : ν+θ ≤ σ-(1 : ℝ)/20) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hcop := outsidePrime_coprime S hbad D
      let hg := outsidePrime_good S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
      let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp (initialErrorWindow a b)),
        ∑ j ∈ secondLogBinBox (Z*Real.exp (initialErrorWindow a b)) (initialErrorRowBound a b Z H),
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray
            (initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z (initialErrorWindow a b) j))
            G G W H‖ else 0) ≤ C*H*Z^(35*η) := by
  obtain ⟨J,hJ⟩ := HasInitialCanonicalDensity.retained_density χ S hbad hcan a b σ θ ν η hσ hν hη hmargin
  have hM : 0 ≤ initialErrorWindow a b := by unfold initialErrorWindow; positivity
  obtain ⟨windows,Ct,Cs,hCt,hCs,hwc,hws,ht⟩ :=
    initial_subbin_transfer U hUc hUs g W (initialErrorWindow a b) hM hU hgs η hη 0 (2*J)
  obtain ⟨Ce,Cpool,E,hCe,hCpool,hPE,henergy⟩ := hJ (windows 5) (windows 6) (hwc 5) (hwc 6) (hws 5) (hws 6)
  obtain ⟨Cl,hCl,hlog⟩ := initial_row_log_budget η (initialPolynomialCap a b) hη (initialPolynomialCap_ge_one a b)
  let C0 := Ct*Real.exp 4*Ce*Cs*initialRayMass*Cl
  have hray := initialRayMass_nonneg
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  refine ⟨C0+1,Cpool,E,by linarith,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hKmax : 1 ≤ Kmax := initialErrorRowBound_ge_one a b Z H hZ hH
  let B : SecondRayIndex → Finset (OutsidePrimeIndex S D) → SecondLogIndex → Frequency → ℝ :=
    fun ray R j => Classical.choose
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  have hB (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) :=
    Classical.choose_spec
      (ht p hp hcop hg (outsidePrime_injective S hbad D) (outsidePrime_odd S hbad D)
        (outsidePrime_primary S hbad D) Finset.univ R Ψ 1 ray K Z H M j (s R j)
        hZp hHp hΨ (Finset.filter_subset _ _))
  let d := H*Real.exp 4*(Ce*Z^η)*Cs*(Kmax*Real.exp 2)^η
  have hd : 0 ≤ d := by dsimp [d]; positivity
  have hterm (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D))
      (hR : R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M))
      (j : SecondLogIndex) (hj : j ∈ secondLogBinBox (Z*Real.exp M) Kmax)
      (hlow : initialRadial Z H (primeProductNorm p R) j ≤ Z^θ) :
      initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j) ≤
        d/primeProductNorm p R*‖secondRayCoefficient ray‖ := by
    have hT := initial_squarefree_target_geometry p hp hg (outsidePrime_odd S hbad D)
      Finset.univ R K Z M j
    have hTe : ∀ z ∈ sourceIdealTarget ((s R j).image (sourceObservation p)),
        Admissible z.1 ∧ (Ideal.absNorm z.1 : ℝ) ≤ initialLogLabel j ∧ z.2 ≠ 0 ∧
        ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ secondLogK j*Real.exp 2 := by
      intro z hz
      exact ⟨(hT z hz).1,(hT z hz).2.1,(hT z hz).2.2.1,(hT z hz).2.2.2.trans
        (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) (normLogScale_pos _).le)⟩
    have he := henergy D Z R ray j _ hZ hpool hR hj hlow hTe
    have he' :
        densityChildEnergy p hp hcop hg Finset.univ (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (1*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (sourceIdealTarget ((s R j).image (sourceObservation p)))
          (windows 5) (windows 6) (initialLogColumn Z (primeProductNorm p R) j)
          (initialLogColumn Z (primeProductNorm p R) j) (2*J) ≤
          (Ce*Z^η)*(initialLogColumn Z (primeProductNorm p R) j*initialLogLabel j)^2 := by
      simpa only [outsideCanonicalDensity,one_mul] using he
    exact initial_bin_cost_uniform p hp hcop hg Finset.univ R Ψ 1 ray K Z H M Kmax η Cs
      (Ce*Z^η) hZp hHp hKmax hη.le hCs (by positivity) j hj windows (B ray R j) (2*J) 0
      (hB ray R j).1 (hB ray R j).2.1 he'
  have hsum :
      (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
        ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
        if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖ else 0) ≤
      Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by
    apply le_trans _ (mul_le_mul_of_nonneg_left
      (initial_harmonic_aggregation p (outsidePrime_injective S hbad D) Finset.univ
        (Z*Real.exp M) Kmax d hd
        (fun ray R j => if initialRadial Z H (primeProductNorm p R) j ≤ Z^θ then
          initialSquarefreeBinCost p hp hcop hg Finset.univ R Ψ 1 ray K Z H M η j windows (B ray R j)
          else 0) (by
          intro ray R hR j hj
          split_ifs with hlow
          · exact hterm ray R hR j hj hlow
          · have hRp := FirstPassCubeLabels.primeProductNorm_pos p hp R
            positivity)) hCt)
    simp only [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro ray hray
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    split_ifs with hlow
    · convert (hB ray R j).2.2 using 1 ;
        dsimp only [initialSquarefreeBinCost,s,G,B] ; ring
    · simp
  have hlogBound := hlog Z (Z*Real.exp M) Kmax hZ (by positivity) (zero_lt_one.trans_le hKmax)
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).1
    (initial_actual_bin_polynomial_caps a b Z H hZ hH).2
  calc
    _ ≤ Ct*(d*initialRayMass*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := hsum
    _ = (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*
        ((Kmax*Real.exp 2)^η*((secondLogBinBox (Z*Real.exp M) Kmax).card : ℝ)*
        (128*Real.exp 1*(normLogBin (Z*Real.exp M)+1 : ℝ))) := by dsimp [d]; ring
    _ ≤ (Ct*Real.exp 4*Ce*Cs*initialRayMass)*H*Z^η*(Cl*Z^(34*η)) :=
      mul_le_mul_of_nonneg_left hlogBound (by positivity)
    _ = C0*H*Z^(35*η) := by
      rw [show 35*η=η+34*η by ring,Real.rpow_add hZp]
      dsimp [C0]
      ring
    _ ≤ (C0+1)*H*Z^(35*η) := by
      gcongr
      linarith

end

open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open SecondPassArithmetic SecondPassIntegration JointLogSeparation
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog)

theorem HasInitialCanonicalDensity.nonzero_source_bound {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ,ℂ)) (a b σ ε : ℝ)
    (hU : ∀ t,g t ≠ 0 → U t=1)
    (hgs : ∀ t,g t ≠ 0 → |t| ≤ initialErrorWindow a b)
    (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ (C Cpool : ℝ) (E : ℕ),0 < C ∧ 1 ≤ Cpool ∧ 20 ≤ E ∧
      ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → Cpool*Z^E ≤ D →
      let p := outsidePrime S D
      let hp := outsidePrime_ne_zero S hbad D
      let hg := outsidePrime_good S hbad D
      let hinj := outsidePrime_injective S hbad D
      letI := outsidePrime_maximal S hbad D
      let Ψ := conjugateMonoid (normCharacter χ)
      let H := Z^(1+σ)
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1
        (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V)
        W H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ C*H*Z^ε := by
  let η := min 1 (ε/100)
  let ν := (σ-(1 : ℝ)/20)/3
  have hη : 0 < η := lt_min zero_lt_one (by positivity)
  have hη1 : η ≤ 1 := min_le_left _ _
  have hηε : 35*η ≤ ε := by
    have hh : η ≤ ε/100 := min_le_right _ _
    linarith
  have hν : 0 < ν := by dsimp [ν]; linarith
  have hσ0 : 0 ≤ σ := by linarith
  have hmargin : ν+ν ≤ σ-(1 : ℝ)/20 := by dsimp [ν]; linarith
  obtain ⟨Cl,Cpool,E,hCl,hCpool,hPE,hlow⟩ := HasInitialCanonicalDensity.retained_source χ S hbad hcan U hUc hUs g W
    a b σ ν ν η hU hgs hσ0 hν hη hmargin
  obtain ⟨Ch,hCh,hhigh⟩ := initial_high_radial_source U hUc hUs g W a b ν 1 η hU hgs hν hη hη1
  refine ⟨Cl+Ch,Cpool,E,by positivity,hCpool,hPE,?_⟩
  intro D Z hZ hpool
  dsimp only
  let p := outsidePrime S D
  let hp := outsidePrime_ne_zero S hbad D
  let hcop := outsidePrime_coprime S hbad D
  let hg := outsidePrime_good S hbad D
  let hinj := outsidePrime_injective S hbad D
  let := outsidePrime_maximal S hbad D
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let M := initialErrorWindow a b
  let K := fun (_ _ : Finset (OutsidePrimeIndex S D)) => initialErrorCutoff a b Z H
  let Kmax := initialErrorRowBound a b Z H
  let G := fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V
  let s := fun (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    initialSquarefreeSector p (secondLogSector p ∅ Finset.univ K R Z M j)
  let f := fun (ray : SecondRayIndex) (R : Finset (OutsidePrimeIndex S D)) (j : SecondLogIndex) =>
    ‖secondExpansionSource p hp hcop hg Finset.univ Ψ 1 1 1 ray (s R j) G G W H‖
  let Lsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if initialRadial Z H (primeProductNorm p R) j ≤ Z^ν then f ray R j else 0
  let Hsum := ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
    ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,
      if Z^ν < initialRadial Z H (primeProductNorm p R) j then f ray R j else 0
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hΨ : ∀ z,‖Ψ z‖ ≤ 1 := conjugateMonoid_norm_le_one (normCharacter χ) (normCharacter_norm_le_one χ)
  have hL : Lsum ≤ Cl*H*Z^(35*η) := hlow D Z hZ hpool
  have hHi : Hsum ≤ Ch*Z^(-(1 : ℝ)) :=
    hhigh p hp hcop hg hinj (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D)
      Finset.univ Ψ 1 Z H hZ hH hΨ (fun _ R j => s R j) (fun _ _ _ => Finset.filter_subset _ _)
  have hrow : ∀ R ∈ (Finset.univ : Finset (OutsidePrimeIndex S D)).powerset,
      ∀ x ∈ secondSupportedSector p Finset.univ K R Z M,elementNorm (sourceObservation p x).1 ≤ Kmax := by
    intro R hR x hx
    exact initialErrorRowBound_valid p hp Finset.univ R a b Z H hZp hHp x hx
  have htotal := initial_nonzero_source_norm_le_squarefree_bins p hp hcop hg hinj
    (outsidePrime_odd S hbad D) (outsidePrime_primary S hbad D) Finset.univ Ψ 1 g W
    Z H M Kmax hZp hgs K hrow
  have hpart : (∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j)=Lsum+Hsum := by
    dsimp only [Lsum,Hsum]
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hh : initialRadial Z H (primeProductNorm p R) j ≤ Z^ν
    · rw [ite_eq_left hh,ite_eq_right (not_lt.mpr hh),add_zero]
    · rw [ite_eq_right hh,ite_eq_left (lt_of_not_ge hh),zero_add]
  have hpower : Z^(35*η) ≤ Z^ε := Real.rpow_le_rpow_of_exponent_le hZ hηε
  have hsmall : Z^(-(1 : ℝ)) ≤ H*Z^ε := by
    have h1 : Z^(-(1 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hZ (by norm_num)
    exact h1.trans (one_le_mul_of_one_le_of_one_le hH (Real.one_le_rpow hZ hε.le))
  calc
    _ ≤ ∑ ray : SecondRayIndex,∑ R ∈ boundedPrimeSupports p Finset.univ (Z*Real.exp M),
      ∑ j ∈ secondLogBinBox (Z*Real.exp M) Kmax,f ray R j := htotal
    _ = Lsum+Hsum := hpart
    _ ≤ Cl*H*Z^(35*η)+Ch*Z^(-(1 : ℝ)) := add_le_add hL hHi
    _ ≤ Cl*H*Z^ε+Ch*(H*Z^ε) := add_le_add
      (mul_le_mul_of_nonneg_left hpower (mul_nonneg hCl.le hHp.le))
      (mul_le_mul_of_nonneg_left hsmall hCh.le)
    _ = (Cl+Ch)*H*Z^ε := by ring

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0220

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.CanonicalTailBounds
Source SHA256: 4a7fe863e5abd113e7c98a36506f20bb80f89253e9b01aba0c31d6bd71b1173d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0221


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace InitialMeanSquare
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic SecondPassIntegration
open FirstPassCubeLabels (normalizedColumn columnLog)

theorem outside_mean_square_of_canonical_density {q : ℕ} (χ : DirichletCharacter ℂ q)
    (S : Finset (Ideal ActualEisensteinCubic.O)) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S,Prime P)
    (hcan : HasInitialCanonicalDensity χ S hbad)
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (σ ε : ℝ) (hσ : (1 : ℝ)/20 < σ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (D : ℕ) (Z : ℝ),1 ≤ Z → b*Z ≤ D →
      ∀ T : Finset ActualEisensteinCubic.O,
      (∀ z ∈ T,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Z^(1+σ)) →
      (∀ z ∈ T,z ≠ 0) →
      (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
        (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2) ≤ C*Z*(Z^(1+σ))*Z^ε := by
  let g0 := initialLogProfile W a b ha hs hW
  let g := conjugateProfile g0
  let M := initialErrorWindow a b
  have hM : 0 ≤ M := by dsimp [M,initialErrorWindow]; positivity
  have hg0 : ∀ t,g0 t ≠ 0 → |t| ≤ M := initialLogProfile_support W a b ha hs hW
  have hg : ∀ t,g t ≠ 0 → |t| ≤ M := conjugateProfile_support_bound g0 M hg0
  obtain ⟨U,hUc,hUs,hUeq,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  have hU : ∀ t,g t ≠ 0 → U t=1 := fun t ht => hUeq t (hg t ht)
  obtain ⟨Cs,Cpool,E,hCs,hCpool,hE,hsource⟩ := HasInitialCanonicalDensity.nonzero_source_bound χ S hbad hcan
    U hUc hUs g rowMajorant a b σ ε hU hg hσ hε
  obtain ⟨Ce,hCe,herrors⟩ := outside_mean_square_source_with_errors W a b ha hs hW
  refine ⟨Cs+Ce,by positivity,?_⟩
  intro D Z hZ hD T hT hT0
  let Db : ℕ := max D ⌈Cpool*Z^E⌉₊
  have hDDb : D ≤ Db := le_max_left _ _
  have hpool : Cpool*Z^E ≤ (Db : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right D ⌈Cpool*Z^E⌉₊)
  have hDb : b*Z ≤ (Db : ℝ) := hD.trans (by exact_mod_cast hDDb)
  let p := outsidePrime S Db
  let hp := outsidePrime_ne_zero S hbad Db
  let hg := outsidePrime_good S hbad Db
  let hinj := outsidePrime_injective S hbad Db
  let := outsidePrime_maximal S hbad Db
  let Ψ := conjugateMonoid (normCharacter χ)
  let H := Z^(1+σ)
  let G := fun V => normalizedColumn p (fun T => g0 (columnLog p Z T)) V
  let MS := ∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S Db) (outsideIdealsUpTo_ne_bot S Db)
    (outside_good S Db hbad) χ (fun n => W (n/Z)) z‖^2
  have hZp := zero_lt_one.trans_le hZ
  have hH : 1 ≤ H := Real.one_le_rpow hZ (by linarith)
  have hHp := zero_lt_one.trans_le hH
  have hεZ : 1 ≤ Z^ε := Real.one_le_rpow hZ hε.le
  have he := herrors χ S Db hbad hSp Z H hZp hHp hDb T hT hT0
  have hsrc := hsource Db Z hZ hpool
  have hstar : (fun V => star (G V)) =
      (fun V => normalizedColumn p (fun T => g (columnLog p Z T)) V) := by
    funext V
    exact star_normalizedColumn p g0 Z V
  have hsrc' :
      ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
        rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖ ≤ Cs*H*Z^ε := by
    rw [hstar]
    exact hsrc
  change MS/Z ≤
    ‖truncatedSecondSource p hp hg hinj Finset.univ Ψ 1 1 1 (fun V => star (G V))
      rowMajorant H (fun _ _ => (initialErrorCutoff a b Z H).erase 0)‖+Ce*H-‖G ∅‖^2 at he
  have herr : Ce*H ≤ Ce*H*Z^ε := le_mul_of_one_le_right (mul_nonneg hCe.le hHp.le) hεZ
  have hnorm : MS/Z ≤ (Cs+Ce)*H*Z^ε := by
    nlinarith [sq_nonneg ‖G ∅‖]
  have hfinal := (div_le_iff₀ hZp).mp hnorm
  have hMS : (∑ z ∈ T,‖idealRowSum (outsideIdealsUpTo S D) (outsideIdealsUpTo_ne_bot S D)
      (outside_good S D hbad) χ (fun n => W (n/Z)) z‖^2)=MS := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [outside_row_cutoff_stable S hbad hDDb χ W b Z hZp (fun t ht => (hs ht).2) hD z]
  rw [hMS]
  convert hfinal using 1 ; dsimp only [H] ; ring

end InitialMeanSquare

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

lemma firstTail_inverse_scale_bound (K D U:ℝ) (hK:0<K) (hD:0<D) (hU:D≤U):
    ((min 1 (K/D))⁻¹)^2≤(1+U/K)^2 := by
  have hU0:0≤U/K:=div_nonneg (hD.le.trans hU) hK.le
  have hi:(min 1 (K/D))⁻¹≤1+U/K:=by
    by_cases h:1≤K/D
    · rw [min_eq_left h,inv_one];linarith
    · rw [min_eq_right (le_of_lt (lt_of_not_ge h)),inv_div]
      exact (div_le_div_of_nonneg_right hU hK.le).trans (by linarith)
  exact pow_le_pow_left₀ (inv_nonneg.mpr (le_min zero_le_one (div_pos hK hD).le)) hi 2

lemma firstTail_scalar_bound (K D E U₁ U₂ lengthScale B G₁ G₂ P H:ℝ) (A:ℕ)
    (hK:0<K) (hD:0<D) (hE:0<E) (hU₁:0<U₁) (hU₂:0<U₂)
    (hL:0≤lengthScale) (hG₁:0≤G₁) (hG₂:0≤G₂) (hP:0≤P) (hH:0≤H)
    (hDb:D≤lengthScale*B^2) (hEb:E≤B^2) (hU₁b:U₁≤lengthScale) (hU₂b:U₂≤lengthScale):
    (128*U₁)*(128*U₂)*(G₁*G₂*K)*
      (P/((min 1 (K/(D*E*U₁*U₂)))^2*(1+H)^A))≤
    (128*lengthScale)^2*(G₁*G₂*K)*P*(1+lengthScale^3*B^4/K)^2/(1+H)^A := by
  have hden:D*E*U₁*U₂≤lengthScale^3*B^4:=by
    calc
      _ ≤ (lengthScale*B^2)*B^2*lengthScale*lengthScale:=mul_le_mul
        (mul_le_mul (mul_le_mul hDb hEb hE.le (mul_nonneg hL (sq_nonneg _))) hU₁b hU₁.le (by positivity))
        hU₂b hU₂.le (by positivity)
      _ = _:=by ring
  have hi:=firstTail_inverse_scale_bound K (D*E*U₁*U₂) (lengthScale^3*B^4) hK (by positivity) hden
  have hpref:(128*U₁)*(128*U₂)*(G₁*G₂*K)≤(128*lengthScale)^2*(G₁*G₂*K):=by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    calc
      _ ≤ (128*lengthScale)*(128*lengthScale):=mul_le_mul (mul_le_mul_of_nonneg_left hU₁b (by norm_num))
        (mul_le_mul_of_nonneg_left hU₂b (by norm_num)) (by positivity) (by positivity)
      _ = _:=by ring
  calc
    _ = ((128*U₁)*(128*U₂)*(G₁*G₂*K))*P*((min 1 (K/(D*E*U₁*U₂)))⁻¹)^2/(1+H)^A:=by
      simp only [div_eq_mul_inv,mul_inv_rev,inv_pow];ring
    _ ≤ _:=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul (mul_le_mul_of_nonneg_right hpref hP) hi (sq_nonneg _) (by positivity)

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeCoordinates_radical_bound (b:CubeCoordinates ι) (B:ℝ) (hB:0≤B)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B):
    primeProductNorm p b.support≤B^2 := by
  have hd:(∏i∈b.support,p i)∣primeProduct p b.support b.leftExponent*primeProduct p b.support b.rightExponent:=by
    rw [←primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (b.support_pos i hi)
  have hb0:=mul_ne_zero (primeProduct_ne_zero p hp b.support b.leftExponent)
    (primeProduct_ne_zero p hp b.support b.rightExponent)
  have hn:=element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma cubeSourceDivisor_norm_bound (b:CubeCoordinates ι) (C D:Finset ι) (B lengthScale:ℝ)
    (hB:0≤B) (hL:0≤lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):
    primeProductNorm p D≤lengthScale*B^2 := by
  calc
    _ ≤ primeProductNorm p (C∪b.support):=primeProductNorm_mono p hp
      (hD.trans (Finset.union_subset_union_right (Finset.filter_subset _ _)))
    _ = primeProductNorm p C*primeProductNorm p b.support:=primeProductNorm_union p _ _ hCB
    _ ≤ _:=mul_le_mul hC (cubeCoordinates_radical_bound p hp b B hB hb₁ hb₂)
      (primeProductNorm_pos p hp _).le hL

lemma cubeSourceDivisors_card
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (b:CubeCoordinates ι) (C:Finset ι) (B lengthScale:ℝ) (hB:0<B) (hL:0<lengthScale) (hCB:Disjoint C b.support)
    (hb₁:‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hb₂:‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B)
    (hC:primeProductNorm p C≤lengthScale):
    ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)≤128*(lengthScale*B^2) := by
  let M:=C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
  have he:boundedPrimeSupports p M (lengthScale*B^2)=M.powerset:=by
    apply Finset.filter_eq_self.mpr
    intro D hD
    exact cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB.le hL.le hCB hb₁ hb₂ hC (Finset.mem_powerset.mp hD)
  rw [←he]
  exact boundedPrimeSupports_card_positive p hp hinj M _ (mul_pos hL (sq_pos_of_pos hB))

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
lemma sourceMobiusDivisor_norm_le_one (D:Finset ι):
    ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)‖≤1 := by
  have hmu : ‖(UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)‖≤1 := by
    unfold UniqueFactorizationMonoid.moebius
    split_ifs <;> simp
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (primeProductNorm_pos p hp D)]
  exact (div_le_div_of_nonneg_right hmu (primeProductNorm_pos p hp D).le).trans
    ((div_le_one (primeProductNorm_pos p hp D)).mpr (primeProductNorm_ge_one p hp D))

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem canonicalCubeDualTail_support
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ) (m₁ m₂ f:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ))
    (ell K M:ℝ) (hell:0<ell) (hgM:∀t,g₁ t≠0→t≤M)
    (hC:¬primeProductNorm p C≤ell*Real.exp M) (T:Finset ι→Finset ActualEisensteinCubic.O):
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K T=0 := by
  have hz (S:Finset ι):g₁ (columnLog p ell ((b.rightDivisor∪C)∪S))=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  have hcoef (S:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun R=>g₁ (columnLog p ell R)) S=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_uniform_canonicalSourceTail_bound (ε:ℝ) (hε:0<ε) (A:ℕ):
    ∃(s:Finset (ℕ×ℕ)) (C:ℝ),0<C ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal ActualEisensteinCubic.O))
      (a:CubeCoordinates ι→Finset ι→Ideal ActualEisensteinCubic.O→ℂ) (Ψ₁ Ψ₂:ActualEisensteinCubic.O→*ℂ)
      (m₁ m₂:ActualEisensteinCubic.O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell → 1≤B → 1≤F → 1≤lengthScale →
      ell*Real.exp M₁≤lengthScale → ell*Real.exp M₂≤lengthScale →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      ‖canonicalSourceTail p hp hcop hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell‖≤
      C*B^(4+ε)*lengthScale^4*F*Γ*(G₁*G₂*Ksrc)*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*
        (1+lengthScale^3*B^4/Ksrc)^2/(1+(Ksrc/K)/Real.exp (M₁+M₂))^A := by
  obtain ⟨s,Ct,hCt,hkernel⟩:=full_uniform_canonicalSource_kernel_tail A
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨s,Cb*128^5*Ct,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ M₁ M₂ Ksrc K ell B F lengthScale
    hΓ hG₁ hG₂ hKsrc hK hell hB hF hL hL₁ hL₂ hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hg₁ hg₂ hM₁ hM₂
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hL0:0<lengthScale:=zero_lt_one.trans_le hL
  let P:=Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  let H:ℝ:=(Ksrc/K)/Real.exp (M₁+M₂)
  let Q:ℝ:=(128*lengthScale)^2*(G₁*G₂*Ksrc)*P*(1+lengthScale^3*B^4/Ksrc)^2/(1+H)^A
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hB0.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    change ‖eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal ActualEisensteinCubic.O):ℂ:=
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) lengthScale) (I:Ideal ActualEisensteinCubic.O):
      ‖z b C I‖≤(128*(lengthScale*B^2))*Q:=by
    have hCb:primeProductNorm p C≤lengthScale:=(Finset.mem_filter.mp hC).2
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hiB=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hiB)
    let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
    let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
    let U₁:=X₁*Real.exp M₁
    let U₂:=X₂*Real.exp M₂
    let E:=primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)
    have hU₁:0<U₁:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hU₂:0<U₂:=mul_pos (div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))) (Real.exp_pos _)
    have hE:0<E:=primeProductNorm_pos p hp _
    have hU₁b:U₁≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₁).le).trans hL₁
    have hU₂b:U₂≤lengthScale:=(mul_le_mul_of_nonneg_right (div_le_self hell.le
      (one_le_mul_of_one_le_of_one_le (primeProductNorm_ge_one p hp _) (primeProductNorm_ge_one p hp _))) (Real.exp_pos M₂).le).trans hL₂
    have hEb:E≤B^2:=(primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
      (cubeCoordinates_radical_bound p hp b B hB0.le (hb₁ b hb) (hb₂ b hb))
    have hlocal (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
        ‖∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
          (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
          (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
          (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
          W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖≤Q:=by
      have hDb:=cubeSourceDivisor_norm_bound p hp b C D B lengthScale hB0.le hL0.le hCB (hb₁ b hb) (hb₂ b hb) hCb (Finset.mem_powerset.mp hD)
      exact (hkernel p hp hinj hcop hg hc pool b (hadm b hb) C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I) g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂).trans
        (firstTail_scalar_bound Ksrc (primeProductNorm p D) E U₁ U₂ lengthScale B G₁ G₂ P H A
          hKsrc (primeProductNorm_pos p hp _) hE hU₁ hU₂ hL0.le hG₁ hG₂ hP hH hDb hEb hU₁b hU₂b)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    calc
      _ ≤ ‖∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)/(primeProductNorm p D:ℂ)*
          ∑'h:{h:ActualEisensteinCubic.O // h∉canonicalSourceCutoff p K ell b C D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
            (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
            (canonicalCubeResidual p hg b C true Ψ₁ m₁ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₁ (columnLog p ell S)))
            (canonicalCubeResidual p hg b C false Ψ₂ m₂ (ConcretePrimeRowBridge.idealGenerator I) (fun S=>g₂ (columnLog p ell S)))
            W (fun _=>1) (fun _=>1) 1 1 Ksrc (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val‖:=
        mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
      _ ≤ ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,Q:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D) (hlocal D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul Q)
      _ = ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*Q:=by simp
      _ ≤ _:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B lengthScale hB0 hL0 hCB (hb₁ b hb) (hb₂ b hb) hCb) hQ
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      (128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤ell*Real.exp M₁:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h.trans hL₁⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from canonicalCubeDualTail_support p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell Ksrc M₁ hell hM₁ hn _,mul_zero]
    rw [heq]
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,‖a b C I*z b C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) lengthScale,∑I∈labels,Γ*((128*(lengthScale*B^2))*Q):=by
        apply Finset.sum_le_sum
        intro C hC
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I) (norm_nonneg _) hΓ
      _ = ((boundedPrimeSupports p (pool\b.support) lengthScale).card:ℝ)*(labels.card:ℝ)*Γ*((128*(lengthScale*B^2))*Q):=by simp;ring
      _ ≤ _:=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_right _ hΓ
        exact mul_le_mul (boundedPrimeSupports_card_positive p hp hinj _ lengthScale hL0) hlabel (Nat.cast_nonneg _) (by positivity)
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _ ≤ ∑b∈bs,‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,(128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q):=Finset.sum_le_sum hcommon
    _ = (bs.card:ℝ)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=by simp
    _ ≤ (Cb*B^(1+ε)*B)*((128*lengthScale)*(128*F)*Γ*((128*(lengthScale*B^2))*Q)):=
      mul_le_mul_of_nonneg_right hbcount (by positivity)
    _ = _:=by
      dsimp [Q,P,H]
      rw [Real.rpow_add hB0,Real.rpow_add hB0]
      norm_num
      ring

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,lambda∉Ideal.span {p i})

theorem globalBin_canonical_child_bound
    (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool) (j:GlobalLogIndex)
    (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (V₁ V₂:ℝ→ℂ) (C E ε K ell B F:ℝ) (A J:ℕ)
    (hC:0≤C) (hE:0≤E) (hε:0<ε) (hK:0<K) (hell:0<ell) (hB:0<B) (hF:0<F)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (he:∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
      densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J≤
        E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2):
    (∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
      globalDescentWeight C ε 0 0 K ell B F A J j ray q*
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J/
        (globalPooledColumnScale ell j*globalPooledLabelScale j)))≤
    E*C*globalRayTripleConstant*((ell*B^3)*F)*(globalBinLossScale B j)^ε/
      (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A := by
  let M:=globalPooledColumnScale ell j*globalPooledLabelScale j
  have hM:0<M:=mul_pos (globalPooledColumnScale_pos ell hell j)
    (zero_lt_one.trans_le (globalPooledLabelScale_ge_one j))
  calc
    _ ≤ ∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*(E*M):=by
      apply Finset.sum_le_sum
      intro ray hray
      apply Finset.sum_le_sum
      intro q hq
      apply mul_le_mul_of_nonneg_left _ (globalDescentWeight_nonneg C ε 0 0 K ell B F A J j ray q hC hK hell hB hF)
      apply (div_le_iff₀ hM).mpr
      simpa only [M,pow_two,mul_assoc] using he ray q hq
    _ = E*(∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*M):=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hray
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ ≤ E*((C*(globalBinLossScale B j)^ε/
        (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^A)*
        globalRayTripleConstant*((ell*B^3)*F)):=by
      apply mul_le_mul_of_nonneg_left _ hE
      simpa only [norm_zero,add_zero,one_pow,mul_one,globalRayTripleConstant,M] using
        globalDescentWeight_mass p hp C ε 0 0 K ell B F A J hC hε hK hell hB hF side source j hk hb₁ hb₂
    _ = _:=by ring

end

theorem globalSelected_canonical_child_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Cbox:ℝ,0<Cbox ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i})
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (V₁ V₂:ℝ→ℂ) (C E K ell B F M H U:ℝ) (A J:ℕ)
      (keep:GlobalLogIndex→Prop) [DecidablePred keep],
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        ∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
        densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter keep,
        ∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
        globalDescentWeight C ε 0 0 K ell B F A J j ray q*
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J/
          (globalPooledColumnScale ell j*globalPooledLabelScale j)))≤
        E*C*globalRayTripleConstant*((ell*B^3)*F)*Cbox*U^(deltaLoss+8*ε) := by
  obtain ⟨Cbox,hCbox,hbox⟩:=globalLogBox_total_loss deltaLoss hδ ε hε.le
  refine ⟨Cbox,hCbox,?_⟩
  intro ι _ p hp _ hcop hg pool source side Ψ m V₁ V₂ C E K ell B F M H U A J keep _
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let Q:=E*C*globalRayTripleConstant*((ell*B^3)*F)
  have hB0:0<B:=zero_lt_one.trans_le hB
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hQ:0≤Q:=by dsimp [Q,globalRayTripleConstant];positivity
  have hloss (j:GlobalLogIndex):0≤(globalBinLossScale B j)^ε:=by
    unfold globalBinLossScale
    have hx:=globalLogRep_pos j 4
    have hl:=globalPooledLabelScale_ge_one j
    positivity
  calc
    _ ≤ ∑j∈S.filter keep,Q*(globalBinLossScale B j)^ε:=by
      apply Finset.sum_le_sum
      intro j hj
      have hb:=globalBin_canonical_child_bound p hp hcop hg pool source side j Ψ m V₁ V₂ C E ε K ell B F A J
        hC hE hε hK hell hB0 hF0 hk hb₁ hb₂ (he j hj)
      apply hb.trans
      apply div_le_self (mul_nonneg hQ (hloss j))
      have hr:=globalBinRadial_pos ell (globalPooledRowScale K ell B F j) hell
        (globalPooledRowScale_pos K ell B F hK hell hB0 hF0 j) j
      exact one_le_pow₀ (by linarith)
    _ ≤ ∑j∈S,Q*(globalBinLossScale B j)^ε:=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun j hj hnot=>mul_nonneg hQ (hloss j))
    _ = Q*∑j∈S,(globalBinLossScale B j)^ε:=by rw [Finset.mul_sum]
    _ ≤ Q*(Cbox*U^(deltaLoss+8*ε)):=mul_le_mul_of_nonneg_left
      (hbox K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hQ
    _ = _:=by dsimp [Q];ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)

theorem globalPooled_mass_le_parent (_K ell B F:ℝ) (hell:0<ell) (hB:0<B) (hF:0<F)
    (j:GlobalLogIndex) (hJ:globalLogRep j 4≤B^2) (hlarge:Real.exp 4≤B*F):
    globalPooledColumnScale ell j*globalPooledLabelScale j≤(ell*B^3)*F := by
  have hD:=globalPooledDelta_pos B F hB hF j
  have hM:0<(ell*B^3)*F:=by positivity
  rw [globalPooled_mass ell B F hB hF j]
  calc
    _ ≤ Real.exp 4*((ell*B^3)*F)*B^2/(globalPooledDelta B F j*B^2):=by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hJ (by positivity)
    _ = Real.exp 4*((ell*B^3)*F)/globalPooledDelta B F j:=by field_simp
    _ ≤ (ell*B^3)*F:=by
      apply (div_le_iff₀ hD).mpr
      have he:=hlarge.trans (globalPooledDelta_ge B F hB.le hF.le j)
      nlinarith

variable {ι:Type*} [DecidableEq ι]
  (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
omit hp in
theorem globalArithmeticTargets_nonzero (source:Finset (GlobalSecondData ι)) (side:Bool)
    (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hk:∀x∈source,x.source.frequency≠0):
    ∀z∈globalArithmeticTargets p source side q j,z.2≠0 := by
  intro z hz
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hz
  have hxs:x∈source:=(Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  exact actualSecondRow_ne_zero p _ _ _ (hk x hxs)

include hp in

theorem globalRetained_canonical_geometry
    (source:Finset (GlobalSecondData ι)) (side:Bool) (q:Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O×Ideal ActualEisensteinCubic.O) (j:GlobalLogIndex)
    (hq:q∈globalBinTriples p source side j)
    (Z η Ksrc K ell B F:ℝ) (m:ActualEisensteinCubic.O)
    (hZ:1<Z) (hη:η≤(1:ℝ)/1000) (hKsrc:0<Ksrc) (hK:0<K) (hKle:K≤Ksrc)
    (hell:0<ell) (hB:0<B) (hF:1≤F) (hprogress:Z^((1:ℝ)/1000)≤B*F)
    (hlarge:Real.exp 4≤B*F) (hstart:Ksrc≤Z^3)
    (hk:∀x∈source,x.source.frequency≠0)
    (hb₁:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂:∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hretained:globalBinRadial ell (globalPooledRowScale K ell B F j) j≤Z^η):
    let X:=globalPooledColumnScale ell j
    let lengthScale:=globalPooledLabelScale j
    let Kchild:=globalLogRep j 8*Real.exp 1
    0<X ∧ 1≤lengthScale ∧ 1≤Kchild ∧ X*lengthScale≤(ell*B^3)*F ∧
      Kchild≤Ksrc/Z^((1:ℝ)/1000) ∧ fixedDepthRank Z Kchild+1≤fixedDepthRank Z Ksrc ∧
      fixedDepthRank Z Ksrc≤3000 ∧ Kchild*‖eisEmbedding (fixedTripleMask m q)‖^2/(X*lengthScale)≤
        Z^η*(K*‖eisEmbedding m‖^2/((ell*B^3)*F)) ∧
      (∀z∈globalArithmeticTargets p source side q j,
        Squarefree z.1 ∧ z.2≠0 ∧ (Ideal.absNorm z.1:ℝ)≤lengthScale ∧ ‖eisEmbedding z.2‖^2≤Kchild) := by
  obtain ⟨x,hx,hqx⟩:=Finset.mem_image.mp hq
  obtain ⟨hxs,hj⟩:=Finset.mem_filter.mp hx
  have hF0:0<F:=zero_lt_one.trans_le hF
  have hJ:globalLogRep j 4≤B^2:=by
    simpa only [hj] using globalPooled_J_bound p hp B hB side x (hk x hxs) (hb₁ x hxs) (hb₂ x hxs)
  have hD:Z^η≤globalPooledDelta B F j:=
    (Real.rpow_le_rpow_of_exponent_le hZ.le hη).trans
      (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
  have hr:globalLogRep j 8*Real.exp 1≤K/globalPooledDelta B F j:=
    globalPooledRow_contraction K ell B F hK hell hB hF0 j hJ (hretained.trans hD)
  have hKchild:1≤globalLogRep j 8*Real.exp 1:=one_le_mul_of_one_le_of_one_le
    (globalLogRep_ge_one j 8) (Real.one_le_exp (by norm_num))
  have hsmall:globalLogRep j 8*Real.exp 1≤Ksrc/Z^((1:ℝ)/1000):=by
    apply hr.trans
    calc
      _ ≤ K/Z^((1:ℝ)/1000):=div_le_div_of_nonneg_left hK.le
        (Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
        (hprogress.trans (globalPooledDelta_ge B F hB.le hF0.le j))
      _ ≤ _:=div_le_div_of_nonneg_right hKle (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  have hinv:=globalBin_invariant_small_padding p hp Z η K ell B F hZ hK hell hB hF side x
    (hk x hxs) m (hb₁ x hxs) (hb₂ x hxs) (by simpa only [hj] using hretained)
  simp only [hj,hqx] at hinv
  refine ⟨globalPooledColumnScale_pos ell hell j,globalPooledLabelScale_ge_one j,hKchild,
    globalPooled_mass_le_parent K ell B F hell hB hF0 j hJ hlarge,hsmall,
    fixedDepthRank_step Z Ksrc _ hZ hKsrc hKchild hsmall,
    fixedDepthRank_initial Z Ksrc hZ hKsrc hstart,hinv,?_⟩
  intro z hz
  have hb:=globalArithmeticTargets_bounds p hp source side q j hk z hz
  exact ⟨globalArithmeticTargets_squarefree p source side q j z hz,
    globalArithmeticTargets_nonzero p source side q j hk z hz,hb.2.1,hb.2.2⟩

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0221

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ReopenedFibers
Source SHA256: 47a6cabf590d0fbff7882955afb52dae789c4164c8b2f65fc9bd5a01859d693c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0222


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

open scoped BigOperators Classical
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open SecondPassIntegration (densityChildEnergy)
open ConcreteTraceCRT (eisEmbedding)

theorem globalChildBudget_canonical_bound (deltaLoss:ℝ) (hδ:0<deltaLoss) (ε:ℝ) (hε:0<ε):
    ∃Clo Chi:ℝ,0<Clo ∧ 0<Chi ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→ActualEisensteinCubic.O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (ActualEisensteinCubic.O⧸Ideal.span {p i})≠2)
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (pool:Finset ι) (source:Finset (GlobalSecondData ι)) (side:Bool)
      (Ψ:ActualEisensteinCubic.O→*ℂ) (m:ActualEisensteinCubic.O) (windows:Fin 7→ℝ→ℂ)
      (C E K ell B F M H U Z θ A₀ Vmax:ℝ) (N J:ℕ),
      0≤C → 0≤E → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z → 0≤A₀ → 0≤Vmax →
      (∀t,‖windows 5 t‖≤Vmax) → (∀t,‖windows 6 t‖≤Vmax) →
      (∀t,windows 5 t≠0→|t|≤A₀) → (∀t,windows 6 t≠0→|t|≤A₀) →
      (∀u,‖Ψ u‖≤1) → (∀x∈source,x.source.frequency≠0) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∀j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),
        ∀ray:SecondRayIndex,∀q∈globalBinTriples p source side j,
        densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)≤
          E*(globalPooledColumnScale ell j*globalPooledLabelScale j)^2) →
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H (N+1) (2*J) side≤
        C*globalRayTripleConstant*((ell*B^3)*F)*U^(deltaLoss+8*ε)*
          (E*Clo+globalTerminalConstant A₀ Vmax*K*Chi/Z^(θ*N)) := by
  obtain ⟨Clo,hClo,hlow⟩:=globalSelected_canonical_child_bound deltaLoss hδ ε hε
  obtain ⟨Chi,hChi,hhigh⟩:=globalChild_large_radial_bound deltaLoss hδ ε hε
  refine ⟨Clo,Chi,hClo,hChi,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool source side Ψ m windows C E K ell B F M H U Z θ A₀ Vmax N J
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂ he
  have hlo:=hlow p hp hcop hg pool source side Ψ m (windows 5) (windows 6) C E K ell B F M H U (N+1) (2*J)
    (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ)
    hC hE hU hK hell hB hF hH hKU hellU hBU hHU heU hk hb₁ hb₂ he
  have hhi:=hhigh p hp hcop hg hc hinj pool Ψ m (windows 5) (windows 6) C K ell B F M H U Z θ A₀ Vmax N J
    source side hC hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA hV hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂
  let S:=globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let f:=fun j:GlobalLogIndex=>∑ray:SecondRayIndex,∑q∈globalBinTriples p source side j,
      globalDescentWeight C ε 0 0 K ell B F (N+1) (2*J) j ray q*
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J)/
        (globalPooledColumnScale ell j*globalPooledLabelScale j))
  have hsplit:(∑j∈S,f j)=
      (∑j∈S.filter (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ),f j)+
      (∑j∈S.filter (fun j=>Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),f j):=by
    simpa only [not_lt] using (Finset.sum_filter_add_sum_filter_not S
      (fun j=>globalBinRadial ell (globalPooledRowScale K ell B F j) j<Z^θ) f).symm
  change (∑j∈S,f j)≤_
  rw [hsplit]
  apply (add_le_add hlo hhi).trans_eq
  ring

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

def reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) : Finset (CubeCoordinates ι) :=
  (((v₁.support ∪ v₂.support).powerset).product
    ((v₁.support ∪ v₂.support).powerset)).image
    (fun A => ⟨v₁,v₂,A.2,A.1⟩)

lemma mem_reopenedCubeFiber (v₁ v₂ : ι →₀ ℕ) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFiber v₁ v₂ ↔
      b.leftExponent=v₁ ∧ b.rightExponent=v₂ ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨h₂,h₁⟩ := Finset.mem_product.mp hA
    exact ⟨rfl,rfl,Finset.mem_powerset.mp h₁,Finset.mem_powerset.mp h₂⟩
  · rintro ⟨hl,hr,hb⟩
    apply Finset.mem_image.mpr
    refine ⟨(b.rightDivisor,b.leftDivisor),?_,?_⟩
    · apply Finset.mem_product.mpr
      have hs : b.support=v₁.support∪v₂.support := by rw [CubeCoordinates.support,hl,hr]
      exact ⟨Finset.mem_powerset.mpr (hs ▸ hb.2),Finset.mem_powerset.mpr (hs ▸ hb.1)⟩
    · exact CubeCoordinates.ext hl.symm hr.symm rfl rfl

def reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) : Finset (CubeCoordinates ι) :=
  (Q.product Q).biUnion (fun v => reopenedCubeFiber v.2 v.1)

lemma mem_reopenedCubeFamily (Q : Finset (ι →₀ ℕ)) (b : CubeCoordinates ι) :
    b ∈ reopenedCubeFamily Q ↔ b.leftExponent ∈ Q ∧ b.rightExponent ∈ Q ∧ b.Admissible := by
  constructor
  · intro hb
    obtain ⟨v,hv,hb⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    exact ⟨hl ▸ (Finset.mem_product.mp hv).2,hr ▸ (Finset.mem_product.mp hv).1,ha⟩
  · rintro ⟨hl,hr,ha⟩
    exact Finset.mem_biUnion.mpr ⟨(b.rightExponent,b.leftExponent),Finset.mem_product.mpr ⟨hr,hl⟩,
      (mem_reopenedCubeFiber _ _ b).mpr ⟨rfl,rfl,ha⟩⟩

lemma reopenedCubeFamily_admissible (Q : Finset (ι →₀ ℕ)) :
    ∀ b ∈ reopenedCubeFamily Q,b.Admissible :=
  fun b hb => ((mem_reopenedCubeFamily Q b).mp hb).2.2

lemma reopenedCubeFamily_support (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (hQ : ∀ v ∈ Q,v.support ⊆ pool) :
    ∀ b ∈ reopenedCubeFamily Q,b.support ⊆ pool := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  exact Finset.union_subset (hQ _ hl) (hQ _ hr)

theorem sum_reopenedCubeFamily {M : Type*} [AddCommMonoid M]
    (Q : Finset (ι →₀ ℕ)) (f : CubeCoordinates ι → M) :
    (∑ b ∈ reopenedCubeFamily Q,f b) =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ A₂ ∈ (v₁.support∪v₂.support).powerset,
        ∑ A₁ ∈ (v₁.support∪v₂.support).powerset,f ⟨v₁,v₂,A₁,A₂⟩ := by
  unfold reopenedCubeFamily
  rw [Finset.sum_biUnion]
  · change (∑ x ∈ Q ×ˢ Q,∑ i ∈ reopenedCubeFiber x.2 x.1,f i)=_
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro v₂ hv₂
    apply Finset.sum_congr rfl
    intro v₁ hv₁
    unfold reopenedCubeFiber
    rw [Finset.sum_image]
    · change (∑ x ∈ (v₁.support∪v₂.support).powerset ×ˢ (v₁.support∪v₂.support).powerset,
        f ⟨v₁,v₂,x.2,x.1⟩)=_
      rw [Finset.sum_product]
    · intro A hA B hB he
      exact Prod.ext (congrArg CubeCoordinates.rightDivisor he) (congrArg CubeCoordinates.leftDivisor he)
  · intro v hv w hw hne
    apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨hbl,hbr,ha⟩ := (mem_reopenedCubeFiber v.2 v.1 b).mp hb
    obtain ⟨hcl,hcr,hc⟩ := (mem_reopenedCubeFiber w.2 w.1 b).mp hc
    exact hne (Prod.ext (hbr.symm.trans hcr) (hbl.symm.trans hcl))

omit [DecidableEq ι] in
lemma primeProduct_finsupp_support (p : ι → ActualEisensteinCubic.O) (B : Finset ι) (v : ι →₀ ℕ)
    (hv : v.support ⊆ B) : primeProduct p B v=primeProduct p v.support v := by
  unfold primeProduct
  symm
  apply Finset.prod_subset hv
  intro i hi hn
  have hv0 : v i=0 := by simpa only [Finsupp.mem_support_iff,not_not] using hn
  simp only [hv0,pow_zero]

lemma reopenedCubeFamily_cube_norms (p : ι → ActualEisensteinCubic.O) (Q : Finset (ι →₀ ℕ)) (B : ℝ)
    (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ b ∈ reopenedCubeFamily Q,
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 ≤ B := by
  intro b hb
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  rw [primeProduct_finsupp_support p b.support b.leftExponent Finset.subset_union_left,
    primeProduct_finsupp_support p b.support b.rightExponent Finset.subset_union_right]
  exact ⟨hQ _ hl,hQ _ hr⟩

def reopenedPairCoefficient (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (_C : Finset ι) (I : Ideal ActualEisensteinCubic.O) : ℂ :=
  star (β I b.rightExponent)*β I b.leftExponent

omit [DecidableEq ι] in
lemma reopenedPairCoefficient_independent_common (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (b : CubeCoordinates ι) (C D : Finset ι) (I : Ideal ActualEisensteinCubic.O) :
    reopenedPairCoefficient β b C I=reopenedPairCoefficient β b D I := rfl

lemma reopenedPairCoefficient_bound (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ) :
    ∀ b ∈ reopenedCubeFamily Q,∀ C,∀ I ∈ labels,
      ‖reopenedPairCoefficient β b C I‖ ≤ Γ^2 := by
  intro b hb C I hI
  obtain ⟨hl,hr,ha⟩ := (mem_reopenedCubeFamily Q b).mp hb
  simp only [reopenedPairCoefficient,norm_mul,norm_star]
  simpa only [pow_two] using mul_le_mul (hβ I hI _ hr) (hβ I hI _ hl) (norm_nonneg _) hΓ

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

theorem reopenedCanonicalRow_smoothed_eq_source {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ)) (K ell : ℝ) (hK : 0 < K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/K)*
      (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceTotal p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W K ell := by
  rw [canonicalSourceTotal,sum_reopenedCubeFamily]
  simp only [reopenedPairCoefficient,CubeCoordinates.support]
  calc
    _ = ∑ I ∈ labels,∑ v₂ ∈ Q,∑ v₁ ∈ Q,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      apply Finset.sum_congr rfl
      intro I hI
      exact reopenedCanonicalRow_smoothed_expand p hp hcop hg pool Q hQ (β I) Ψ m
        (idealGenerator I) (fun S => g (columnLog p ell S)) W K hK
    _ = ∑ v₂ ∈ Q,∑ v₁ ∈ Q,∑ I ∈ labels,(star (β I v₂)*β I v₁)*
        canonicalCubeCorrelation p hp hcop hg pool (v₁.support∪v₂.support) v₁ v₂
          Ψ Ψ m m (idealGenerator I) (fun S => g (columnLog p ell S))
          (fun S => g (columnLog p ell S)) W K := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v₂ hv₂
      apply Finset.sum_congr rfl
      intro v₁ hv₁
      have hs : v₁.support∪v₂.support ⊆ pool := Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂)
      simp_rw [canonicalCubeCorrelation_eq_blocks p hp hcop hg hinj hpr pool v₁ v₂ hs,
        Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₂ hA₂
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro A₁ hA₁
      rw [Finset.sum_comm]

end
section

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]

theorem reopenedCubeFamily_card (Q : Finset (ι →₀ ℕ)) :
    (reopenedCubeFamily Q).card =
      ∑ v₂ ∈ Q,∑ v₁ ∈ Q,(2^((v₁.support∪v₂.support).card))^2 := by
  have h := sum_reopenedCubeFamily Q (fun _ => (1 : ℕ))
  simpa [pow_two] using h

theorem reopenedCubeFamily_card_le (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (hQ : ∀ v ∈ Q,v.support ⊆ pool) :
    (reopenedCubeFamily Q).card ≤ Q.card^2*(2^pool.card)^2 := by
  rw [reopenedCubeFamily_card]
  calc
    _ ≤ ∑ v₂ ∈ Q,∑ v₁ ∈ Q,(2^pool.card)^2 := by
      apply Finset.sum_le_sum
      intro v₂ hv₂
      apply Finset.sum_le_sum
      intro v₁ hv₁
      have hc := Finset.card_le_card (Finset.union_subset (hQ v₁ hv₁) (hQ v₂ hv₂))
      exact pow_le_pow_left₀ (by positivity) (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 2) hc) 2
    _ = _ := by simp [pow_two,mul_assoc]

theorem reopenedSourceBlocks_bounds (p : ι → ActualEisensteinCubic.O) (pool : Finset ι) (Q : Finset (ι →₀ ℕ))
    (B : ℝ) (hQ : ∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) :
    ∀ q ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q),GlobalCubeAdmissible q ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.leftExponent)‖^2 ≤ B ∧
      ‖eisEmbedding (primeProduct p q.cube.support q.cube.rightExponent)‖^2 ≤ B := by
  intro q hq
  exact ⟨canonicalSourceBlocks_admissible pool _ (reopenedCubeFamily_admissible Q) q hq,
    canonicalSourceBlocks_cube_norms p pool _ B
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).1)
      (fun b hb => (reopenedCubeFamily_cube_norms p Q B hQ b hb).2) q hq⟩

end

theorem reopenedCubeFamily_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → ActualEisensteinCubic.O) (_hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (Q : Finset (ι →₀ ℕ)) (B : ℝ),1 ≤ B →
      (∀ v ∈ Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ B) →
      ((reopenedCubeFamily Q).card : ℝ) ≤ C*B^(2+ε) := by
  obtain ⟨C,hC,hcount⟩ := cube_coordinates_parity_count ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Q B hB hQ
  have hBp := zero_lt_one.trans_le hB
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hactive (b : CubeCoordinates ι) (hbf : b ∈ reopenedCubeFamily Q) :
      ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖ ≤ B := by
    have hn : primeProductNorm p (cubeActiveSupport b.support
        (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) ≤ B^2 :=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cubeCoordinates_radical_bound p hp b B hBp.le (hb b hbf).1 (hb b hbf).2)
    change ‖eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2 ≤ B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏ i ∈ cubeActiveSupport b.support
      (fun i => b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  have h := hcount p hp hinj (reopenedCubeFamily Q) B B hB hBp.le
    (reopenedCubeFamily_admissible Q) (fun b hb' => (hb b hb').1)
    (fun b hb' => (hb b hb').2) hactive
  apply h.trans_eq
  calc
    C*B^(1+ε)*B = C*(B^(1+ε)*B^(1 : ℝ)) := by rw [Real.rpow_one]; ring
    _ = C*B^((1+ε)+1) := by rw [Real.rpow_add hBp (1+ε) (1 : ℝ)]
    _ = C*B^(2+ε) := by congr 2; ring

end

open ActualEisensteinCubic FirstPassCubeLabels
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)

theorem reopenedCanonicalRow_smoothed_split {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (hQ : ∀ v ∈ Q,v.support ⊆ pool)
    (labels : Finset (Ideal ActualEisensteinCubic.O)) (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (g W : 𝓢(ℝ,ℂ)) (Ksrc K ell : ℝ)
    (hKsrc : 0 < Ksrc) (hK : 0 ≤ K) :
    (∑ I ∈ labels,∑' z : ActualEisensteinCubic.O,W (‖eisEmbedding z‖^2/Ksrc)*
      (‖reopenedCanonicalRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun S => g (columnLog p ell S)) z‖^2 : ℝ)) =
    canonicalSourceZero p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc ell+
    canonicalSourceFinite p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell+
    canonicalSourceTail p hp hcop hg pool (reopenedCubeFamily Q) labels
      (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell := by
  rw [reopenedCanonicalRow_smoothed_eq_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m g W Ksrc ell hKsrc]
  exact canonicalSourceTotal_split p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m g g W Ksrc K ell hKsrc hK

theorem reopenedCanonicalBlockCoefficient_bound {ι : Type*} [DecidableEq ι]
    (p : ι → ActualEisensteinCubic.O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (ActualEisensteinCubic.O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (labels : Finset (Ideal ActualEisensteinCubic.O))
    (β : Ideal ActualEisensteinCubic.O → (ι →₀ ℕ) → ℂ) (Γ : ℝ) (hΓ : 0 ≤ Γ)
    (hβ : ∀ I ∈ labels,∀ v ∈ Q,‖β I v‖ ≤ Γ)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (hΨ : ∀ u,‖Ψ u‖ ≤ 1) (m : ActualEisensteinCubic.O) (K ell : ℝ)
    (b : GlobalCubeBlock ι) (hb : b ∈ canonicalSourceBlocks pool (reopenedCubeFamily Q))
    (x : Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O) (hx : x ∈ canonicalBlockFrequencies p K ell labels b) :
    ‖canonicalBlockCoefficient p hp hcop hg (reopenedPairCoefficient β) Ψ Ψ m m b x‖ ≤ Γ^2 := by
  exact canonicalBlockCoefficient_bound p hp hcop hg hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (Γ^2) K ell (sq_nonneg _) hΨ hΨ
    (fun b hb C hC I hI => reopenedPairCoefficient_bound Q labels β Γ hΓ hβ b hb C I hI) b hb x hx

end SecondPassArithmetic

namespace CubicEisenstein
open MeasureTheory
open scoped SchwartzMap

lemma euclideanIntegral_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     ∫p,g p) =
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanIntegrable_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (g : EuclideanSpatial→ℝ) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Integrable g volume) ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeIntegral_eq_borel (g : EuclideanSpatial→ℝ) :
    (∫p,g p)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     ∫p,g p) :=
  euclideanIntegral_borel_transport inferInstance inferInstance g

lemma euclideanNativeIntegrable_iff_borel (g : EuclideanSpatial→ℝ) :
    Integrable g volume ↔
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Integrable g volume) :=
  euclideanIntegrable_borel_transport inferInstance inferInstance g

def euclideanLp_borel_transport (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) :
    (letI : MeasurableSpace EuclideanSpatial := m
     letI : BorelSpace EuclideanSpatial := hm
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) := by
  have he := hm.measurable_eq
  subst m
  exact LinearIsometryEquiv.refl ℂ _

def euclideanNativeLpBorelEquiv : EuclideanL2 ≃ₗᵢ[ℂ]
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     Lp ℂ 2 (volume : Measure EuclideanSpatial)) :=
  euclideanLp_borel_transport inferInstance inferInstance

lemma euclideanLp_borel_transport_schwartz (m : MeasurableSpace EuclideanSpatial)
    (hm : @BorelSpace EuclideanSpatial inferInstance m) (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanLp_borel_transport m hm
      (letI : MeasurableSpace EuclideanSpatial := m
       letI : BorelSpace EuclideanSpatial := hm
       f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) := by
  have he := hm.measurable_eq
  subst m
  rfl

lemma euclideanNativeLpBorelEquiv_schwartz (f : 𝓢(EuclideanSpatial,ℂ)) :
    euclideanNativeLpBorelEquiv (f.toLp 2 volume)=
    (letI : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
     letI : BorelSpace EuclideanSpatial := ⟨rfl⟩
     f.toLp 2 volume) :=
  euclideanLp_borel_transport_schwartz inferInstance inferInstance f

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff SchwartzMap

namespace CubicEisenstein
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean

lemma euclideanOriginalMeasurable_eq_borel :
    (inferInstance : MeasurableSpace EuclideanSpatial)=borel EuclideanSpatial :=
  BorelSpace.measurable_eq

local instance : MeasurableSpace EuclideanSpatial := borel EuclideanSpatial
local instance : BorelSpace EuclideanSpatial := ⟨rfl⟩

def kernelLocalizedRealTest (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) : C1c (E := EuclideanSpatial) :=
  ⟨fun p => projection (kernelLocalizedField χ f p),
    (projection.contDiff.comp (kernelLocalizedField_smooth χ f)).of_le (by simp),
    (kernelLocalizedField_compact χ f).comp_left (map_zero projection)⟩

lemma sourceC1c_toL2_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2 («μ» := volume) g‖^2=∫p,‖g.1 p‖^2 := by
  calc
    ‖toL2 («μ» := volume) g‖^2=inner ℝ (toL2 («μ» := volume) g) (toL2 («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2 («μ» := volume) g p) (toL2 («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)
        (((memLp_of_mem_C1c («μ» := volume) g.2).toLp g.1) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma sourceC1c_toL2Grad_norm_sq (g : C1c (E := EuclideanSpatial)) :
    ‖toL2Grad («μ» := volume) g‖^2=∫p,‖grad g.1 p‖^2 := by
  calc
    ‖toL2Grad («μ» := volume) g‖^2=inner ℝ (toL2Grad («μ» := volume) g) (toL2Grad («μ» := volume) g) :=
      (real_inner_self_eq_norm_sq _).symm
    _ = ∫p,inner ℝ (toL2Grad («μ» := volume) g p) (toL2Grad («μ» := volume) g p) := rfl
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [(memLp_grad_of_mem_C1c («μ» := volume) g.2).coeFn_toLp] with p hp
      change inner ℝ (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)
        (((memLp_grad_of_mem_C1c («μ» := volume) g.2).toLp (grad g.1)) p)=_
      rw [hp,real_inner_self_eq_norm_sq]

lemma kernelLocalizedRealTest_grad_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) (p : EuclideanSpatial) :
    ‖grad (kernelLocalizedRealTest χ f projection).1 p‖^2≤
      ∑j : Fin 3,‖fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)‖^2 := by
  have hdiff : DifferentiableAt ℝ (kernelLocalizedField χ f) p :=
    ((kernelLocalizedField_smooth χ f).differentiable (by simp)).differentiableAt
  have hd := (projection.hasFDerivAt.comp p hdiff.hasFDerivAt).fderiv
  change fderiv ℝ (kernelLocalizedRealTest χ f projection).1 p=_ at hd
  unfold grad
  rw [LinearIsometryEquiv.norm_map,hd,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual]
  apply Finset.sum_le_sum
  intro j hj
  have hh := hprojection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j))
  change (projection (fderiv ℝ (kernelLocalizedField χ f) p (EuclideanSpace.basisFun (Fin 3) ℝ j)))^2≤_
  simp only [Real.norm_eq_abs] at hh
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hh 2

lemma kernelLocalizedRealTest_energy_le (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖) :
    ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
      ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤
        ‖kernelLocalizedH1 χ f‖^2 := by
  let g := kernelLocalizedRealTest χ f projection
  rw [sourceC1c_toL2_norm_sq,sourceC1c_toL2Grad_norm_sq,kernelLocalizedH1_norm_sq,
    ←integral_add (memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq]
  rw [euclideanNativeIntegral_eq_borel]
  have hden := (euclideanNativeIntegrable_iff_borel (kernelLocalizedDensity χ f)).mp
    (kernelLocalizedDensity_integrable χ f)
  apply integral_mono
    ((memLp_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq.add
      (memLp_grad_of_mem_C1c («μ» := volume) g.2).norm.integrable_sq)
    hden
  intro p
  have hm := hprojection (kernelLocalizedField χ f p)
  have hg := kernelLocalizedRealTest_grad_le χ f projection hprojection p
  change ‖projection (kernelLocalizedField χ f p)‖^2+_≤_
  unfold kernelLocalizedDensity
  nlinarith [norm_nonneg (projection (kernelLocalizedField χ f p)),norm_nonneg (kernelLocalizedField χ f p)]

lemma kernelLocalizedRealTest_support (χ : PositiveChartCutoff) (f : kernelSmoothTests)
    (projection : ℂ →L[ℝ] ℝ) :
    Function.support (kernelLocalizedRealTest χ f projection).1⊆tsupport χ.func := by
  intro p hp
  apply kernelLocalizedField_tsupport χ f
  apply subset_tsupport
  intro hz
  apply hp
  change projection (kernelLocalizedField χ f p)=0
  rw [hz,map_zero]

theorem kernelLocalizedReal_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (projection : ℂ →L[ℝ] ℝ) (hprojection : ∀z,‖projection z‖≤‖z‖)
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)) '' family)) := by
  obtain ⟨C,hC,hbound⟩ := kernelLocalizedH1_bounded χ hinj
  have hCB : 0≤C*B := mul_nonneg hC hB
  have henergy : ∀f∈family,
      ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2+
        ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖^2≤C*B := by
    intro f hf
    exact (kernelLocalizedRealTest_energy_le χ f projection hprojection).trans
      ((hbound f).trans (mul_le_mul_of_nonneg_left (hfamily f hf) hC))
  have hh := euclidean_C1c_family_precompact (tsupport χ.func) χ.compact
    ((fun f => kernelLocalizedRealTest χ f projection) '' family) (Real.sqrt (C*B))
    (by
      rintro _ ⟨f,hf,rfl⟩
      exact kernelLocalizedRealTest_support χ f projection)
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection))])
    (by
      rintro _ ⟨f,hf,rfl⟩
      have he := henergy f hf
      have hs := Real.sq_sqrt hCB
      have hn := Real.sqrt_nonneg (C*B)
      nlinarith [sq_nonneg ‖toL2 («μ» := volume) (kernelLocalizedRealTest χ f projection)‖,
        norm_nonneg (toL2Grad («μ» := volume) (kernelLocalizedRealTest χ f projection))])
  simpa only [Set.image_image,Function.comp_def] using hh

abbrev RellichRealL2 := Lp ℝ 2 (volume : Measure EuclideanSpatial)
abbrev RellichComplexL2 := Lp ℂ 2 (volume : Measure EuclideanSpatial)

def kernelComplexL2Assemble : (RellichRealL2 × RellichRealL2) →L[ℝ] RellichComplexL2 :=
  (Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.fst ℝ RellichRealL2 RellichRealL2)+
  (Complex.I • Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial)).comp
    (ContinuousLinearMap.snd ℝ RellichRealL2 RellichRealL2)

lemma kernelComplexL2Assemble_localized (χ : PositiveChartCutoff) (f : kernelSmoothTests) :
    kernelComplexL2Assemble
      (toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
        toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM))=
      (kernelLocalizedSchwartz χ f).toLp 2 volume := by
  let r := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM)
  let i := toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)
  let R := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) r
  let I := Complex.ofRealCLM.compLpL 2 (volume : Measure EuclideanSpatial) i
  have hr : (r : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).re :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM).2).coeFn_toLp
  have hi : (i : EuclideanSpatial→ℝ)=ᵐ[volume]fun p => (kernelLocalizedField χ f p).im :=
    (memLp_of_mem_C1c («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM).2).coeFn_toLp
  change R+Complex.I•I=(kernelLocalizedSchwartz χ f).toLp 2 volume
  apply Lp.ext
  filter_upwards [hr,hi,Complex.ofRealCLM.coeFn_compLpL r,Complex.ofRealCLM.coeFn_compLpL i,
    Lp.coeFn_add R (Complex.I•I),Lp.coeFn_smul Complex.I I,
    (kernelLocalizedSchwartz χ f).coeFn_toLp 2 volume] with p hrp hip hR hI ha hs hf
  rw [ha,Pi.add_apply,hs,Pi.smul_apply,hR,hI,hrp,hip,hf]
  change ((kernelLocalizedField χ f p).re:ℂ)+Complex.I*((kernelLocalizedField χ f p).im:ℂ)=kernelLocalizedField χ f p
  simpa only [mul_comm] using Complex.re_add_im (kernelLocalizedField χ f p)

theorem kernelLocalizedComplex_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => (kernelLocalizedSchwartz χ f).toLp 2 volume) '' family)) := by
  have hr := kernelLocalizedReal_family_precompact χ hinj Complex.reCLM
    (fun z => by change ‖z.re‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm z) family B hB hfamily
  have hi := kernelLocalizedReal_family_precompact χ hinj Complex.imCLM
    (fun z => by change ‖z.im‖≤‖z‖; simpa only [Real.norm_eq_abs] using Complex.abs_im_le_norm z) family B hB hfamily
  have hc := (hr.prod hi).image kernelComplexL2Assemble.continuous
  apply hc.closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.reCLM),
    toL2 («μ» := volume) (kernelLocalizedRealTest χ f Complex.imCLM)),?_,?_⟩
  · exact ⟨subset_closure ⟨f,hf,rfl⟩,subset_closure ⟨f,hf,rfl⟩⟩
  · exact kernelComplexL2Assemble_localized χ f

theorem kernelLocalizedNative_family_precompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func))
    (family : Set kernelSmoothTests) (B : ℝ) (hB : 0≤B)
    (hfamily : ∀f∈family,‖kernelSmoothTestsToL2 f‖^2+kernelDirichletEnergy f≤B) :
    IsCompact (closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)) := by
  have hc := kernelLocalizedComplex_family_precompact χ hinj family B hB hfamily
  apply (hc.image euclideanNativeLpBorelEquiv.symm.continuous).closure_of_subset
  rintro _ ⟨f,hf,rfl⟩
  refine ⟨(kernelLocalizedSchwartz χ f).toLp 2 volume,subset_closure ⟨f,hf,rfl⟩,?_⟩
  apply euclideanNativeLpBorelEquiv.injective
  simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [kernelL2Localize_core χ hinj]
  exact (euclideanNativeLpBorelEquiv_schwartz _).symm

def kernelEnergyLocalizeL2 (χ : PositiveChartCutoff) : KernelEnergyGraph →L[ℂ] EuclideanL2 :=
  (kernelL2Localize χ).comp kernelEnergyMass

theorem kernelEnergyLocalizeL2_isCompact (χ : PositiveChartCutoff)
    (hinj : Set.InjOn kernelEuclideanProjection (tsupport χ.func)) :
    IsCompactOperator (kernelEnergyLocalizeL2 χ) := by
  let family : Set kernelSmoothTests := {f | ‖kernelEnergyGraphCore f‖≤2}
  let C := closure ((fun f => kernelL2Localize χ (kernelSmoothTestsToL2 f)) '' family)
  have hc : IsCompact C := kernelLocalizedNative_family_precompact χ hinj family 4 (by norm_num) (by
    intro f hf
    rw [←kernelEnergyGraphCore_norm_sq]
    change ‖kernelEnergyGraphCore f‖≤2 at hf
    nlinarith [norm_nonneg (kernelEnergyGraphCore f)])
  let T := kernelEnergyLocalizeL2 χ
  have hclosed : IsClosed (T ⁻¹' C) := hc.isClosed.preimage T.continuous
  have hsub : closure (kernelEnergyGraphCore ''
      (kernelEnergyGraphCore ⁻¹' Metric.ball (0 : KernelEnergyGraph) 2))⊆T ⁻¹' C := by
    apply hclosed.closure_subset_iff.mpr
    rintro _ ⟨f,hf,rfl⟩
    change kernelL2Localize χ (kernelEnergyMass (kernelEnergyGraphCore f))∈C
    rw [kernelEnergyMass_core]
    apply subset_closure
    refine ⟨f,?_,rfl⟩
    change ‖kernelEnergyGraphCore f‖≤2
    exact le_of_lt (by simpa only [Set.mem_preimage,Metric.mem_ball,dist_zero_right] using hf)
  have hball : Metric.ball (0 : KernelEnergyGraph) 2⊆T ⁻¹' C := by
    intro u hu
    exact hsub (kernelEnergyGraphCore_dense.subset_closure_image_preimage_of_isOpen
      Metric.isOpen_ball hu)
  refine ⟨C,hc,?_⟩
  exact Filter.mem_of_superset (Metric.ball_mem_nhds (0 : KernelEnergyGraph) (by norm_num : (0 : ℝ)<2)) hball

end CubicEisenstein

end

end OAI
end OAIOriginalModule0222

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.ReopeningSeparation
Source SHA256: 79b1ffd159e3d6f3249876a22ab5476fc73d6bb81398c8cbee40b0ff98a52dfc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0223


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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog primeProductNorm)
open FourierBridge (logPhase)
open JointLogSeparation (frequencyTwist)

def normPhase (t : ℝ) : ActualEisensteinCubic.O →* ℂ where
  toFun z := if z=0 then 0 else logPhase t (Real.log (‖eisEmbedding z‖^2))
  map_one' := by simp [FourierBridge.logPhase_zero]
  map_mul' a b := by
    by_cases ha : a=0
    · simp [ha]
    by_cases hb : b=0
    · simp [hb]
    simp only [ite_eq_right ha,ite_eq_right hb,ite_eq_right (mul_ne_zero ha hb),map_mul,norm_mul,mul_pow]
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero ha)))
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero hb))),FourierBridge.logPhase_add]

@[simp] theorem normPhase_zero (t : ℝ) : normPhase t 0=0 := by simp [normPhase]

theorem normPhase_of_ne_zero (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) :
    normPhase t z=logPhase t (Real.log (‖eisEmbedding z‖^2)) := by simp [normPhase,hz]

theorem normPhase_norm (t : ℝ) (z : ActualEisensteinCubic.O) (hz : z≠0) : ‖normPhase t z‖=1 := by
  rw [normPhase_of_ne_zero t z hz,FourierBridge.logPhase_norm]

theorem normPhase_norm_le_one (t : ℝ) (z : ActualEisensteinCubic.O) : ‖normPhase t z‖≤1 := by
  by_cases hz : z=0
  · simp [hz]
  · rw [normPhase_norm t z hz]

theorem normPhase_add (s t : ℝ) : normPhase (s+t)=normPhase s*normPhase t := by
  ext z
  by_cases hz : z=0
  · simp [hz]
  · simp only [MonoidHom.mul_apply,normPhase_of_ne_zero _ z hz,JointLogSeparation.logPhase_add_frequency]

theorem normPhase_star (t : ℝ) (z : ActualEisensteinCubic.O) : star (normPhase t z)=normPhase (-t) z := by
  by_cases hz : z=0
  · simp [hz]
  · simp only [normPhase_of_ne_zero _ z hz,SecondPassIntegration.logPhase_conjugate]

def normHeightTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) : ActualEisensteinCubic.O →* ℂ := Ψ*normPhase t

theorem normHeightTwist_norm_le (Ψ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) (z : ActualEisensteinCubic.O) :
    ‖normHeightTwist Ψ t z‖≤‖Ψ z‖ := by
  simp only [normHeightTwist,MonoidHom.mul_apply,norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (normPhase_norm_le_one t z)

theorem normHeightTwist_twice (Ψ : ActualEisensteinCubic.O →* ℂ) (s t : ℝ) :
    normHeightTwist (normHeightTwist Ψ s) t=normHeightTwist Ψ (s+t) := by
  simp only [normHeightTwist,normPhase_add,mul_assoc]

theorem normHeightTwist_mul (Ψ Ξ : ActualEisensteinCubic.O →* ℂ) (t : ℝ) :
    normHeightTwist (Ψ*Ξ) t=normHeightTwist Ψ t*Ξ := by
  unfold normHeightTwist
  ac_rfl

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem logPhase_columnLog (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    logPhase t (columnLog p X S)=
      logPhase t (-Real.log X)*normPhase t (∏i∈S,p i) := by
  rw [normPhase_of_ne_zero t _ (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))]
  rw [columnLog,Real.log_div (FirstPassCubeLabels.primeProductNorm_pos p hp S).ne' hX.ne']
  rw [sub_eq_add_neg,FourierBridge.logPhase_add]
  exact mul_comm _ _

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem canonicalSourceCoefficient_frequencyTwist (Ψ : ActualEisensteinCubic.O →* ℂ) (m f : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) (S : Finset ι) :
    canonicalSourceCoefficient p hp hcop hg Ψ m f
      (fun U=>frequencyTwist g t (columnLog p X U)) S=
    logPhase t (-Real.log X)*canonicalSourceCoefficient p hp hcop hg (normHeightTwist Ψ t) m f
      (fun U=>g (columnLog p X U)) S := by
  simp only [canonicalSourceCoefficient,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y=
    logPhase t (-Real.log X)*fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,JointLogSeparation.frequencyTwist_apply,
    logPhase_columnLog p hp X t hX S,normHeightTwist,MonoidHom.mul_apply]
  ring

theorem fixedChildRow_frequencyTwist_norm (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (g : 𝓢(ℝ,ℂ)) (X t : ℝ) (hX : 0<X) :
    ‖fixedChildRow p hp hcop hg pool Ψ m (fun U=>frequencyTwist g t (columnLog p X U)) f y‖=
    ‖fixedChildRow p hp hcop hg pool (normHeightTwist Ψ t) m
      (fun U=>g (columnLog p X U)) f y‖ := by
  rw [fixedChildRow_frequencyTwist p hp hcop hg pool Ψ m f y g X t hX,norm_mul,FourierBridge.logPhase_norm,one_mul]

end SecondPassArithmetic

section

open scoped BigOperators Classical
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FourierBridge (logPhase)
open FirstPassCubeLabels (columnLog)

def secondSignedHeight (negative : Bool) (a b : ℝ) : ℝ :=
  if negative then b-a else a-b

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)

include hp in
omit [DecidableEq ι] in
theorem fixedSecondTest_normPhase (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (negative : Bool) (S : Finset ι) :
    fixedSecondTest p V X a b negative S=
      logPhase (secondSignedHeight negative a b) (-Real.log X)*
      normPhase (secondSignedHeight negative a b) (∏i∈S,p i)*
      fixedSecondTest p V X 0 0 negative S := by
  have hz (x : ℝ) : logPhase 0 x=1 := by simp [FourierBridge.logPhase]
  cases negative <;>
    simp only [secondSignedHeight,fixedSecondTest,JointLogSeparation.fixedColumnTest,
      Bool.false_eq_true,ite_false,ite_true,sub_self,hz,mul_one,star_mul,
      SecondPassIntegration.logPhase_conjugate,neg_sub] <;>
    rw [logPhase_columnLog p hp X _ hX S] ; ring

variable [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem fixedChildRow_secondTest_normPhase (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f y : ActualEisensteinCubic.O)
    (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X) (negative : Bool) :
    fixedChildRow p hp hcop hg pool Ψ m (fixedSecondTest p V X a b negative) f y=
      logPhase (secondSignedHeight negative a b) (-Real.log X)*
      fixedChildRow p hp hcop hg pool (normHeightTwist Ψ (secondSignedHeight negative a b)) m
        (fixedSecondTest p V X 0 0 negative) f y := by
  unfold fixedChildRow
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  simp only [secondChildColumn,fixedSecondTest_normPhase p hp V X a b hX negative S,
    normHeightTwist,MonoidHom.mul_apply]
  ring

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem childEnergy_normHeight (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool Ψ m T V X testNegative rowNegative a b=
      childEnergy p hp hcop hg pool (normHeightTwist Ψ (secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  unfold childEnergy idealChildRow
  simp_rw [fixedChildRow_secondTest_normPhase p hp hcop hg pool Ψ m _ _ V X a b hX testNegative,
    norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem childEnergy_previousNormHeight (pool : Finset ι) (Ψ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O)
    (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O)) (V : ℝ → ℂ) (X t a b : ℝ) (hX : 0<X)
    (testNegative rowNegative : Bool) :
    childEnergy p hp hcop hg pool (normHeightTwist Ψ t) m T V X testNegative rowNegative a b=
      childEnergy p hp hcop hg pool (normHeightTwist Ψ (t+secondSignedHeight testNegative a b))
        m T V X testNegative rowNegative 0 0 := by
  rw [childEnergy_normHeight p hp hcop hg pool (normHeightTwist Ψ t) m T V X a b hX
    testNegative rowNegative,normHeightTwist_twice]

end SecondPassIntegration

open scoped BigOperators Classical
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic

theorem firstCoreTwist_normHeight (negative : Bool) (χ : RayFourExpansion.RayCharacter)
    (Ψ : ActualEisensteinCubic.O →* ℂ) (r : FirstCoreIndex) (t : ℝ) :
    firstCoreTwist negative χ (normHeightTwist Ψ t) r=
      normHeightTwist (firstCoreTwist negative χ Ψ r) t := by
  unfold firstCoreTwist normHeightTwist
  ac_rfl

theorem secondRayMinus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayMinus (normHeightTwist Ψ t) r=normHeightTwist (secondRayMinus Ψ r) t := by
  unfold secondRayMinus normHeightTwist
  ac_rfl

theorem secondRayPlus_normHeight (Ψ : ActualEisensteinCubic.O →* ℂ) (r : SecondRayIndex) (t : ℝ) :
    secondRayPlus (normHeightTwist Ψ t) r=normHeightTwist (secondRayPlus Ψ r) t := by
  unfold secondRayPlus normHeightTwist
  ac_rfl

end SecondPassArithmetic

namespace SecondPassIntegration
open ActualEisensteinCubic SecondPassArithmetic

private theorem sqrt_height_weight (B t : ℝ) (hB : 0≤B) (J : ℕ) :
    Real.sqrt (B*(1+‖t‖)^(2*J))=Real.sqrt B*(1+‖t‖)^J := by
  rw [show 2*J=J*2 from Nat.mul_comm _ _,pow_mul,Real.sqrt_mul hB,
    Real.sqrt_sq (pow_nonneg (by positivity : 0≤1+‖t‖) J)]

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem densityChildEnergy_normHeight_polynomial
    (pool : Finset ι) (Ψ₁ Ψ₂ : ActualEisensteinCubic.O →* ℂ) (m : ActualEisensteinCubic.O) (T : Finset (Ideal ActualEisensteinCubic.O × ActualEisensteinCubic.O))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ B₁ B₂ : ℝ) (J : ℕ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hB₁ : 0≤B₁) (hB₂ : 0≤B₂)
    (h₁ : ∀t,childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t) m T V₁ X₁ true false 0 0≤
      B₁*(1+‖t‖)^(2*J))
    (h₂ : ∀t,childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t) m T V₂ X₂ false true 0 0≤
      B₂*(1+‖t‖)^(2*J)) :
    densityChildEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂)
      m T V₁ V₂ X₁ X₂ (2*J)≤
      Real.sqrt B₁*Real.sqrt B₂*(1+‖t₁‖)^J*(1+‖t₂‖)^J*
        (∫t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  have ha₁ (a : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₁ t₁) m T V₁ X₁ true false a 0≤
      (B₁*(1+‖t₁‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hcop hg pool Ψ₁ m T V₁ X₁ t₁ a 0 hX₁ true false]
    simp only [secondSignedHeight,ite_true,zero_sub,←sub_eq_add_neg]
    calc
      _ ≤ B₁*(1+‖t₁-a‖)^(2*J) := h₁ (t₁-a)
      _ ≤ B₁*((1+‖t₁‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity)
          (JointLogSeparation.one_add_norm_sub_le t₁ a) _) hB₁
      _ = _ := by rw [mul_pow]; ring
  have ha₂ (a : ℝ) : childEnergy p hp hcop hg pool (normHeightTwist Ψ₂ t₂) m T V₂ X₂ false true a 0≤
      (B₂*(1+‖t₂‖)^(2*J))*(1+‖a‖)^(2*J) := by
    rw [childEnergy_previousNormHeight p hp hcop hg pool Ψ₂ m T V₂ X₂ t₂ a 0 hX₂ false true]
    simp only [secondSignedHeight,Bool.false_eq_true,ite_false,sub_zero]
    have hsum : 1+‖t₂+a‖≤(1+‖t₂‖)*(1+‖a‖) := by
      simpa only [sub_neg_eq_add,norm_neg] using JointLogSeparation.one_add_norm_sub_le t₂ (-a)
    calc
      _ ≤ B₂*(1+‖t₂+a‖)^(2*J) := h₂ (t₂+a)
      _ ≤ B₂*((1+‖t₂‖)*(1+‖a‖))^(2*J) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hsum _) hB₂
      _ = _ := by rw [mul_pow]; ring
  have hd := densityChildEnergy_polynomial_bound p hp hcop hg pool
    (normHeightTwist Ψ₁ t₁) (normHeightTwist Ψ₂ t₂) m T V₁ V₂ X₁ X₂ J
    (B₁*(1+‖t₁‖)^(2*J)) (B₂*(1+‖t₂‖)^(2*J))
    (mul_nonneg hB₁ (by positivity)) (mul_nonneg hB₂ (by positivity)) ha₁ ha₂
  rw [sqrt_height_weight B₁ t₁ hB₁ J,sqrt_height_weight B₂ t₂ hB₂ J] at hd
  exact hd.trans_eq (by ring)

end SecondPassIntegration
end

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog)
open FourierBridge (logPhase)
open JointLogSeparation (frequencyTwist)

variable {ι : Type*} [DecidableEq ι] (p : ι → ActualEisensteinCubic.O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

theorem reopenedCanonicalRow_frequencyTwist (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z=
      logPhase t (-Real.log X)*reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z := by
  unfold reopenedCanonicalRow
  simp_rw [canonicalSourceCoefficient_frequencyTwist p hp hcop hg Ψ m f g X t hX,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro S hS
  ring

theorem reopenedCanonicalRow_frequencyTwist_norm (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (β : (ι→₀ℕ)→ℂ) (Ψ : ActualEisensteinCubic.O →* ℂ) (m f z : ActualEisensteinCubic.O) (g : 𝓢(ℝ,ℂ))
    (X t : ℝ) (hX : 0<X) :
    ‖reopenedCanonicalRow p hp hcop hg pool Q β Ψ m f
      (fun S=>frequencyTwist g t (columnLog p X S)) z‖=
      ‖reopenedCanonicalRow p hp hcop hg pool Q β (normHeightTwist Ψ t) m f
        (fun S=>g (columnLog p X S)) z‖ := by
  rw [reopenedCanonicalRow_frequencyTwist p hp hcop hg pool Q β Ψ m f z g X t hX,
    norm_mul,FourierBridge.logPhase_norm,one_mul]

theorem reopenedSource_frequencyTwist
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
