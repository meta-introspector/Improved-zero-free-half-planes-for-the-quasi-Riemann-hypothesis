Source SHA256: 8c80c67bfaa27f8c7a2b1c58c630141574f40bdeac1114db09cd54c7b648695e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0181


namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss QuadraticSquarefreeKernel

def squarefreeHighRange (M K : ℝ) : Finset (Ideal O) :=
  (idealRange M).filter (fun I => K<(Ideal.absNorm I:ℝ))

def annularLift (M K : ℝ) (I : squarefreeHighRange M K) : Ideal O :=
  liftedRow M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1.1
    (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).2

theorem annularLift_injective (M K : ℝ) : Function.Injective (annularLift M K) := by
  intro I J h
  have he := congrArg squarefreePart h
  apply Subtype.ext
  simpa only [annularLift,
    liftedRow_squarefreePart M I.val (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1,
    liftedRow_squarefreePart M J.val (mem_idealRange.mp (Finset.mem_filter.mp J.property).1).1] using he

theorem annularLift_properties (M K : ℝ) (I : squarefreeHighRange M K) :
    Supported (annularLift M K I) ∧ K<(Ideal.absNorm (squarefreePart (annularLift M K I)):ℝ) ∧
      M<(Ideal.absNorm (annularLift M K I):ℝ) ∧ (Ideal.absNorm (annularLift M K I):ℝ)≤49*M := by
  have hi := mem_idealRange.mp (Finset.mem_filter.mp I.property).1
  have hn := liftedRow_bounds M I.val hi.1.1 hi.2
  refine ⟨liftedRow_supported M I.val hi.1 hi.2,?_,hn⟩
  simpa only [annularLift,liftedRow_squarefreePart M I.val hi.1] using (Finset.mem_filter.mp I.property).2

theorem annularLift_row_sum (M N K : ℝ) (I : squarefreeHighRange M K)
    (a : idealRange N → ℂ)
    (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑J : idealRange N, quadraticRow J.val (primaryGenerator (annularLift M K I))*a J) =
      ∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J := by
  apply Finset.sum_congr rfl
  intro J _
  by_cases hz : a J=0
  · simp only [hz,mul_zero]
  · rw [annularLift,liftedRow_character M I.val
      (mem_idealRange.mp (Finset.mem_filter.mp I.property).1).1 _ J.val
      (mem_idealRange.mp J.property).1 (hcop J hz)]

lemma exists_lifted_annular_scale (M x : ℝ) (hM : 0<M) (hx : M<x) (hupper : x≤49*M) :
    ∃j : Fin 7, ((2:ℝ)^j.val*M)/2≤x ∧ x≤(2:ℝ)^j.val*M := by
  have hratio : 1≤x/M := (le_div_iff₀ hM).mpr (by linarith)
  obtain ⟨k,hlo,hhi⟩ := exists_nat_pow_near hratio (by norm_num : (1:ℝ)<2)
  have hratioU : x/M≤49 := (div_le_iff₀ hM).mpr hupper
  have hk : k<6 := by
    by_contra hn
    have h6 : 6≤k := by omega
    have hp : (2:ℝ)^6≤(2:ℝ)^k := pow_le_pow_right₀ (by norm_num) h6
    norm_num at hp
    linarith
  refine ⟨⟨k+1,by omega⟩,?_,?_⟩
  · have hl := (le_div_iff₀ hM).mp hlo
    simpa only [pow_succ,mul_assoc,mul_div_assoc,mul_div_cancel_left₀ _ (by norm_num : (2:ℝ)≠0)] using hl
  · exact ((div_lt_iff₀ hM).mp hhi).le

lemma sum_injective_mask_le {ι : Type*} [Fintype ι]
    (f : ι → Ideal O) (hf : Function.Injective f) (S : Finset (Ideal O))
    (v : Ideal O → ℝ) (hv : ∀I, 0≤v I) :
    (∑i, if f i∈S then v (f i) else 0)≤∑I∈S,v I := by
  classical
  rw [←Finset.sum_filter]
  rw [←Finset.sum_image (f := v) (g := f) (by intro i hi j hj he; exact hf he)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hI
    exact (Finset.mem_filter.mp hi).2
  · intro I hI hnot
    exact hv I

theorem squarefreeHigh_energy_le_annuli (M N K : ℝ) (hM : 0<M)
    (a : idealRange N → ℂ) (hcop : ∀J, a J≠0 → IsCoprime liftingPrime J.val) :
    (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K a := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hE (I : Ideal O) : 0≤E I := sq_nonneg _
  have hlift :
      (∑I : squarefreeHighRange M K, E I.val) = ∑I : squarefreeHighRange M K, E (annularLift M K I) := by
    apply Finset.sum_congr rfl
    intro I _
    dsimp only [E]
    rw [annularLift_row_sum M N K I a hcop]
  change (∑I : squarefreeHighRange M K, E I.val)≤_
  rw [hlift]
  have hpoint (I : squarefreeHighRange M K) : E (annularLift M K I) ≤
      ∑j : Fin 7, if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := by
    have hp := annularLift_properties M K I
    obtain ⟨j,hjlo,hjhi⟩ := exists_lifted_annular_scale M _ hM hp.2.2.1 hp.2.2.2
    have hMj : 0<(2:ℝ)^j.val*M := by positivity
    have hm : annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K :=
      mem_highKernelRange.mpr ⟨hp.1,by linarith,hp.2.1⟩
    have hw : annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)=1 := by
      apply QuadraticInitialBound.annularSieveBump_eq_one
      · exact (le_div_iff₀ hMj).mpr (by linarith)
      · exact (div_le_one hMj).mpr hjhi
    have hh := Finset.single_le_sum (s := (Finset.univ : Finset (Fin 7)))
      (f := fun j => if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
        annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0)
      (fun j _ => by split_ifs; exact mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE _); exact le_rfl)
      (Finset.mem_univ j)
    simpa only [hm,ite_true,hw,one_mul] using hh
  calc
    _ ≤ ∑I : squarefreeHighRange M K, ∑j : Fin 7,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 :=
      Finset.sum_le_sum (fun I _ => hpoint I)
    _ = ∑j : Fin 7, ∑I : squarefreeHighRange M K,
        if annularLift M K I∈highKernelRange (2*((2:ℝ)^j.val*M)) K then
          annularHighWeight ((2:ℝ)^j.val*M) (annularLift M K I)*E (annularLift M K I) else 0 := Finset.sum_comm
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j _
      rw [annularHighEnergy,Finset.sum_coe_sort (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)]
      exact sum_injective_mask_le (annularLift M K) (annularLift_injective M K)
        (highKernelRange (2*((2:ℝ)^j.val*M)) K)
        (fun I => annularHighWeight ((2:ℝ)^j.val*M) I*E I)
        (fun I => mul_nonneg QuadraticInitialBound.annularSieveBump.nonneg (hE I))

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
open FiniteSieveRestriction

def liftingDivisibleColumns (N : ℝ) : Finset (idealRange N) :=
  Finset.univ.filter (fun J => liftingPrime∣J.val)

def liftingQuotientColumn (N : ℝ) (J : liftingDivisibleColumns N) : idealRange N :=
  ⟨idealQuotient liftingPrime J.val.val, by
    have hd := (Finset.mem_filter.mp J.property).2
    have hj := mem_idealRange.mp J.val.property
    refine mem_idealRange.mpr ⟨admissible_idealQuotient hj.1 hd,?_⟩
    have hn := idealQuotient_norm_le liftingPrime_prime.ne_zero hd N hj.2
    rw [liftingPrime_norm] at hn
    have hN : 0≤N := (Nat.cast_nonneg _).trans hj.2
    exact hn.trans (by norm_num; linarith)⟩

theorem liftingQuotientColumn_injective (N : ℝ) : Function.Injective (liftingQuotientColumn N) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  exact idealQuotient_injective_on liftingPrime
    (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2 (congrArg Subtype.val h)

def liftingFreeCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  fun J => if liftingPrime∣J.val then 0 else a J

def liftingDividedCoefficient (N : ℝ) (a : idealRange N → ℂ) : idealRange N → ℂ :=
  extendByZero Finset.univ (liftingQuotientColumn N) (fun J : liftingDivisibleColumns N => a J.val)

theorem liftingFreeCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingFreeCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  apply ideals_coprime_of_relprime
  apply liftingPrime_prime.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hJ (by simp only [liftingFreeCoefficient,hd,ite_true])

theorem liftingDividedCoefficient_coprime (N : ℝ) (a : idealRange N → ℂ)
    (J : idealRange N) (hJ : liftingDividedCoefficient N a J≠0) : IsCoprime liftingPrime J.val := by
  classical
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have hdiv := (Finset.mem_filter.mp I.property).2
  have hsf : Squarefree (liftingPrime*idealQuotient liftingPrime I.val.val) := by
    rw [idealQuotient_mul hdiv]
    exact (mem_idealRange.mp I.val.property).1.2.1
  exact ideals_coprime_of_relprime _ _ (squarefree_mul_iff.mp hsf).1

theorem liftingDividedCoefficient_row_sum (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) =
      ∑J : liftingDivisibleColumns N, quadraticRow (idealQuotient liftingPrime J.val.val) z*a J.val := by
  simpa only [liftingDividedCoefficient,liftingQuotientColumn] using
    extendByZero_matrix Finset.univ (liftingQuotientColumn N)
      (fun J : liftingDivisibleColumns N => a J.val) (fun (_ : Unit) J => quadraticRow J.val z) ()

theorem liftingCoefficient_row_split (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    (∑J : idealRange N, quadraticRow J.val z*a J) =
      (∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J) +
      quadraticRow liftingPrime z*(∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J) := by
  rw [liftingDividedCoefficient_row_sum,Finset.mul_sum,
    Finset.sum_coe_sort (liftingDivisibleColumns N)
      (fun J => quadraticRow liftingPrime z*(quadraticRow (idealQuotient liftingPrime J.val) z*a J))]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val
  · simp only [hd,ite_true,liftingFreeCoefficient,mul_zero,zero_add]
    rw [quadraticRow_divisor_factor J.val liftingPrime (mem_idealRange.mp J.property).1 hd z]
    ring
  · simp only [hd,ite_false,liftingFreeCoefficient,add_zero]

theorem liftingCoefficient_energy (N : ℝ) (a : idealRange N → ℂ) :
    (∑J : idealRange N, ‖liftingFreeCoefficient N a J‖^2) +
      (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2) = ∑J, ‖a J‖^2 := by
  have he := extendByZero_energy Finset.univ (liftingQuotientColumn N)
    (fun J : liftingDivisibleColumns N => a J.val) (liftingQuotientColumn_injective N).injOn
  change (∑J : idealRange N, ‖liftingDividedCoefficient N a J‖^2)=
    ∑J : liftingDivisibleColumns N, ‖a J.val‖^2 at he
  rw [he,Finset.sum_coe_sort (liftingDivisibleColumns N) (fun J => ‖a J‖^2)]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val <;>
    simp only [liftingFreeCoefficient,hd,ite_true,ite_false,norm_zero,zero_pow (by decide : 2≠0),zero_add,add_zero]

theorem liftingCoefficient_row_energy (N : ℝ) (a : idealRange N → ℂ) (z : O) :
    ‖∑J : idealRange N, quadraticRow J.val z*a J‖^2 ≤
      2*(‖∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J‖^2 +
        ‖∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J‖^2) := by
  rw [liftingCoefficient_row_split]
  let u := ∑J : idealRange N, quadraticRow J.val z*liftingFreeCoefficient N a J
  let v := ∑J : idealRange N, quadraticRow J.val z*liftingDividedCoefficient N a J
  change ‖u+quadraticRow liftingPrime z*v‖^2≤2*(‖u‖^2+‖v‖^2)
  have hp : ‖quadraticRow liftingPrime z*v‖≤‖v‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
  have hn : ‖u+quadraticRow liftingPrime z*v‖≤‖u‖+‖v‖ := by
    linarith [norm_add_le u (quadraticRow liftingPrime z*v)]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

theorem liftingFreeCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N X (liftingFreeCoefficient N a) := by
  intro J hJ
  have hj : a J≠0 := by
    intro hz
    exact hJ (by simp only [liftingFreeCoefficient,hz,ite_self])
  exact ha J hj

theorem liftingDividedCoefficient_shell (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : CoefficientOnShell N (X/7) (liftingDividedCoefficient N a) := by
  classical
  intro J hJ
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have he : liftingDividedCoefficient N a (liftingQuotientColumn N I)=a I.val :=
    extendByZero_apply_image _ _ _ (liftingQuotientColumn_injective N).injOn I (Finset.mem_univ I)
  have hn : a I.val≠0 := by rwa [he] at hJ
  have hs := ha I.val hn
  change (X/7)/2<(Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ) ∧
    (Ideal.absNorm (idealQuotient liftingPrime I.val.val):ℝ)≤X/7
  rw [idealQuotient_norm_eq liftingPrime I.val.val liftingPrime_prime.ne_zero
    (Finset.mem_filter.mp I.property).2,liftingPrime_norm]
  norm_num only [Nat.cast_ofNat]
  constructor <;> linarith

theorem coefficientOnShell_zero_or_scale (N X : ℝ) (a : idealRange N → ℂ)
    (ha : CoefficientOnShell N X a) : (∀J, a J=0) ∨ 1≤X := by
  classical
  by_cases h : ∀J, a J=0
  · exact Or.inl h
  · push Not at h
    obtain ⟨J,hJ⟩ := h
    have hnorm : 1≤(Ideal.absNorm J.val:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hz => (mem_idealRange.mp J.property).1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    exact Or.inr (hnorm.trans (ha J hJ).2)

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss FiniteSieveOperator

def ballQuadraticEnergy (M N : ℝ) (a : idealRange N → ℂ) : ℝ :=
  ∑I : idealRange M, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2

theorem ballQuadraticEnergy_low_high (M N K : ℝ) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      ∑I : squarefreeHighRange M K, ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2 := by
  classical
  let E := fun I : Ideal O => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2
  have hs : (idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K) ⊆ idealRange K := by
    intro I hI
    exact mem_idealRange.mpr ⟨(mem_idealRange.mp (Finset.mem_filter.mp hI).1).1,(Finset.mem_filter.mp hI).2⟩
  have hlo : (∑I∈(idealRange M).filter (fun I => (Ideal.absNorm I:ℝ)≤K), E I) ≤
      sieveNorm K N*(∑J, ‖a J‖^2) := by
    calc
      _ ≤ ∑I∈idealRange K,E I := Finset.sum_le_sum_of_subset_of_nonneg hs (fun I hI hnot => sq_nonneg _)
      _ = ballQuadraticEnergy K N a := (Finset.sum_coe_sort (idealRange K) E).symm
      _ ≤ _ := FiniteSieveOperator.energy_bound (matrix K N) a
  change (∑I : idealRange M,E I.val)≤_+(∑I : squarefreeHighRange M K,E I.val)
  rw [Finset.sum_coe_sort (idealRange M) E,
    ←Finset.sum_filter_add_sum_filter_not (idealRange M) (fun I => (Ideal.absNorm I:ℝ)≤K) E]
  rw [Finset.sum_coe_sort (squarefreeHighRange M K) E]
  simp only [not_le,squarefreeHighRange]
  linarith

theorem ballQuadraticEnergy_lifted_annuli (M N K : ℝ) (hM : 0<M) (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      2*((∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingFreeCoefficient N a)) +
        ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingDividedCoefficient N a)) := by
  have hlo := ballQuadraticEnergy_low_high M N K a
  have hs : (∑I : squarefreeHighRange M K,
      ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*a J‖^2) ≤
      2*((∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2) +
        ∑I : squarefreeHighRange M K,
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) := by
    calc
      _ ≤ ∑I : squarefreeHighRange M K, 2*(
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingFreeCoefficient N a J‖^2 +
          ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I.val)*liftingDividedCoefficient N a J‖^2) :=
        Finset.sum_le_sum (fun I _ => liftingCoefficient_row_energy N a (primaryGenerator I.val))
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have hfree := squarefreeHigh_energy_le_annuli M N K hM (liftingFreeCoefficient N a)
    (liftingFreeCoefficient_coprime N a)
  have hdiv := squarefreeHigh_energy_le_annuli M N K hM (liftingDividedCoefficient N a)
    (liftingDividedCoefficient_coprime N a)
  linarith

end

open ActualEisensteinCubic CompletedGauss

theorem ballQuadraticEnergy_mono {M M' N : ℝ} (hM : M≤M') (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a≤ballQuadraticEnergy M' N a := by
  unfold ballQuadraticEnergy
  rw [Finset.sum_coe_sort (idealRange M)
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2),
    Finset.sum_coe_sort (idealRange M')
    (fun I => ‖∑J : idealRange N, quadraticRow J.val (primaryGenerator I)*a J‖^2)]
  exact Finset.sum_le_sum_of_subset_of_nonneg (idealRange_mono hM) (fun I hI hnot => sq_nonneg _)

theorem ballQuadraticEnergy_coefficientAtScale (M N X : ℝ) (a : idealRange N → ℂ)
    (ha : ∀J, a J≠0 → (Ideal.absNorm J.val:ℝ)≤X) :
    ballQuadraticEnergy M N a=ballQuadraticEnergy M X (coefficientAtScale N X a) := by
  unfold ballQuadraticEnergy
  simp_rw [coefficientAtScale_row_sum N X a ha]

theorem ballQuadraticEnergy_column_shells (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M N (dyadicColumnCoefficient N lengthScale hNL j a) := by
  simpa only [one_mul,ballQuadraticEnergy] using
    weighted_energy_column_shells N lengthScale hNL
      (fun I : idealRange M => fun J : idealRange N => quadraticRow J.val (primaryGenerator I.val))
      (fun _ => (1:ℝ)) (fun _ => by norm_num) a

theorem ballQuadraticEnergy_column_shells_at_scale (M N : ℝ) (lengthScale : ℕ) (hNL : N≤(2:ℝ)^lengthScale)
    (a : idealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ (lengthScale+1:ℝ)*∑j : Fin (lengthScale+1),
      ballQuadraticEnergy M ((2:ℝ)^j.val)
        (coefficientAtScale N ((2:ℝ)^j.val) (dyadicColumnCoefficient N lengthScale hNL j a)) := by
  apply (ballQuadraticEnergy_column_shells M N lengthScale hNL a).trans_eq
  apply congrArg (fun x : ℝ => (lengthScale + 1 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro j _
  exact ballQuadraticEnergy_coefficientAtScale M N _ _
    (fun J hJ => (dyadicColumnCoefficient_shell N lengthScale hNL j a J hJ).2)

theorem columnDyadicLength_scale_upper (N : ℝ) (hN : 1≤N) :
    (2:ℝ)^columnDyadicLength N≤2*N := by
  have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hq : 0≤Real.log N/Real.log 2 := div_nonneg (Real.log_nonneg hN) hlog.le
  have hceil := Nat.ceil_lt_add_one hq
  calc
    _ = (2:ℝ)^((columnDyadicLength N:ℕ):ℝ) := (Real.rpow_natCast _ _).symm
    _ ≤ (2:ℝ)^(Real.log N/Real.log 2+1) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hceil.le
    _ = 2*N := by
      rw [Real.rpow_add (by norm_num : (0:ℝ)<2),Real.rpow_one]
      have he : (2:ℝ)^(Real.log N/Real.log 2)=N :=
        Real.rpow_logb (by norm_num) (by norm_num) (by linarith)
      rw [he,mul_comm]

theorem columnDyadicScale_bounds (N : ℝ) (hN : 1≤N) (j : Fin (columnDyadicLength N+1)) :
    1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤2*N := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  exact (pow_le_pow_right₀ (by norm_num) (by omega : j.val≤columnDyadicLength N)).trans
    (columnDyadicLength_scale_upper N hN)

end

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss
open IdealCoprimeSieveOperator DivisorBlockCauchy

theorem gcdPool_admissible {n : Type*} [Fintype n] (cols : n → Ideal O)
    (hcols : ∀j, Admissible (cols j)) (D : Ideal O) (hD : D∈gcdPool cols) : Admissible D := by
  obtain ⟨⟨j,k⟩,_,rfl⟩ := Finset.mem_image.mp hD
  exact admissible_of_dvd (hcols j) (GCDMonoid.gcd_dvd_left _ _)

theorem annularHighEnergy_gcd_reduction (M N K H : ℝ) (hN : 1≤N) (hH : 0<H)
    (ε : ℝ) (hε : 0<ε) (a : idealRange N → ℂ) :
    annularHighEnergy M N K a ≤ 16*((∑c : EisensteinEPrimaryPhase.Coord,
      ∑D∈(gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H),
        ‖annularRayGcdBlock M N K D c a‖) +
      highKernelNorm (2*M) (N/H) K*(supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
  have h := highKernel_weighted_energy_ray_gcd_reduction ε hε H hH
    (fun I : highKernelRange (2*M) K => I.val) (fun J : idealRange N => J.val)
    Subtype.val_injective Subtype.val_injective (2*M) N K hN (fun I => I.property)
    (fun J => mem_idealRange.mp J.property) (fun I => annularHighWeight M I.val) 1 (by norm_num)
    (fun I => ⟨QuadraticInitialBound.annularSieveBump.nonneg,QuadraticInitialBound.annularSieveBump.le_one⟩) a
  simpa only [annularHighEnergy,annularRayGcdBlock,one_mul] using h

theorem HasSieveExponent.annular_energy_from_scalar_cost {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0<CD ∧ 0<CS ∧ 0<CT ∧ 0<CP ∧ 0<CH ∧
      ∀ (ε : ℝ) (hε : 0<ε) (M N K T H C : ℝ),
      1≤M → 1≤N → 1≤K → 4≤T → 0<H → H≤N/2 → 0≤C →
      (∀D∈gcdPool (fun J : idealRange N => J.val), (Ideal.absNorm D:ℝ)≤H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (commonMaskIdeal D) K (N/(Ideal.absNorm D:ℝ)) M T
          (fun _ : Unit => (1:ℂ)) QuadraticInitialBound.annularSieveCutoff≤C) →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤
        16*((C/6)*(divisorConstant ε hε*N^ε) +
          (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
            (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2)*∑J,‖a J‖^2 := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hsmall⟩ :=
    hexp.annular_small_gcd_complete hα deltaLoss hδ l A
  obtain ⟨CH,hCH,hhigh⟩ := hexp.high_kernel deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,?_⟩
  intro ε hε M N K T H C hM hN hK hT hH hHN hC hcost a ha
  classical
  let S := (gcdPool (fun J : idealRange N => J.val)).filter (fun D => (Ideal.absNorm D:ℝ)≤H)
  have hb (D : Ideal O) (hD : D∈S) (c : EisensteinEPrimaryPhase.Coord) :
      ‖annularRayGcdBlock M N K D c a‖ ≤
        (C/6)*∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 := by
    have hd := Finset.mem_filter.mp hD
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hd.1
    have hh := hsmall ε hε M N N K T hM hK hT a ha D hadm.1 (hd.2.trans hHN) c
    rw [poissonComparisonMajorant_energy_factor] at hh
    have hbound := mul_le_mul_of_nonneg_right (hcost D hd.1 hd.2)
      (show 0≤∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2 by positivity)
    change _ ≤ C*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hbound
    have hn : ‖(6:ℂ)*annularRayGcdBlock M N K D c a‖=6*‖annularRayGcdBlock M N K D c a‖ := by
      rw [norm_mul]
      norm_num
    rw [hn] at hh
    change _≤_*(∑j : gcdRaySupport (fun I : idealRange N => I.val) a D c, ‖a j.val‖^2) at hh
    nlinarith
  have hs := gcdRaySupport_weighted_sum_bound ε hε S (fun J : idealRange N => J.val)
    (fun J => (mem_idealRange.mp J.property).1.1) a N (C/6) (by positivity)
    (fun J hJ => (mem_idealRange.mp J.property).2)
    (fun D c => ‖annularRayGcdBlock M N K D c a‖) hb
  have hNH : 1≤N/H := (le_div_iff₀ hH).mpr (by linarith)
  have hh := hhigh (2*M) (N/H) K (by linarith) hNH hK
  have hred := annularHighEnergy_gcd_reduction M N K H hN hH ε hε a
  apply hred.trans
  have hsupp := (supportConstant_pos ε hε).le
  have hdiv := (divisorConstant_pos ε hε).le
  calc
    _ ≤ 16*((C/6)*(divisorConstant ε hε*N^ε)*∑J,‖a J‖^2 +
      (CH*((2*M)*(N/H))^deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H)^α))*
        (supportConstant ε hε*divisorConstant ε hε)*(N^ε)^2*∑J,‖a J‖^2) := by
      gcongr
    _ = _ := by ring

end

section

def cutoffRescaleCoefficient (C η r q : ℝ) : ℝ := C*r*q^2/(r/q)^η

theorem cutoffRescaleCoefficient_eq (C η r q : ℝ) (hr : 0<r) (hq : 0<q) :
    cutoffRescaleCoefficient C η r q=C*r^(1-η)*q^(2+η) := by
  rw [cutoffRescaleCoefficient,Real.div_rpow hr.le hq.le,
    Real.rpow_sub hr,Real.rpow_one,Real.rpow_add hq,Real.rpow_two]
  have hrp : r^η≠0 := (Real.rpow_pos_of_pos hr η).ne'
  have hqp : q^η≠0 := (Real.rpow_pos_of_pos hq η).ne'
  field_simp

theorem cutoffRescaleCoefficient_bounds (C η r q : ℝ)
    (hC : 0≤C) (hη : 0≤η) (hη1 : η≤1) (hr : 1≤r) (hr64 : r≤64) (hq : 1≤q) (hq7 : q≤7) :
    C≤cutoffRescaleCoefficient C η r q ∧ cutoffRescaleCoefficient C η r q≤21952*C := by
  rw [cutoffRescaleCoefficient_eq C η r q (by linarith) (by linarith)]
  have hrlo : 1≤r^(1-η) := Real.one_le_rpow hr (by linarith)
  have hqlo : 1≤q^(2+η) := Real.one_le_rpow hq (by linarith)
  have hrup : r^(1-η)≤r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr (show 1-η≤1 by linarith)
  have hqup : q^(2+η)≤q^3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hq (show 2+η≤(3:ℝ) by linarith)
  constructor
  · calc
      C = C*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ C*r*q^3 := by gcongr
      _ ≤ C*64*7^3 := by gcongr
      _ = _ := by ring

theorem selectedPoissonK_rescale (C M X η r q : ℝ)
    (hM : 0<M) (hX : 0<X) (hr : 0<r) (hq : 0<q) :
    selectedPoissonK (cutoffRescaleCoefficient C η r q) (r*M) (X/q) η =
      selectedPoissonK C M X η := by
  unfold selectedPoissonK selectedPoissonT cutoffRescaleCoefficient
  have he : (r*M)*(X/q)=(r/q)*(M*X) := by ring
  rw [he,Real.mul_rpow (by positivity : 0≤r/q) (by positivity : 0≤M*X)]
  have hp : (r/q)^η≠0 := (Real.rpow_pos_of_pos (by positivity) η).ne'
  field_simp

end

open scoped BigOperators Classical

def largeGcdThreshold (α N : ℝ) : ℝ := N^(1-1/α)

theorem largeGcdThreshold_quotient_power (α N : ℝ) (hα : α≠0) (hN : 0<N) :
    (N/largeGcdThreshold α N)^α=N := by
  have he : N/largeGcdThreshold α N=N^(1/α) := by
    rw [show 1/α=1-(1-1/α) by ring,Real.rpow_sub hN,Real.rpow_one]
    rfl
  rw [he,←Real.rpow_mul hN.le]
  field_simp
  rw [Real.rpow_one]

theorem largeGcdThreshold_bounds (α N : ℝ) (hα1 : 1≤α) (hα2 : α≤2) (hN : 4≤N) :
    1≤largeGcdThreshold α N ∧ largeGcdThreshold α N≤N/2 := by
  have hα : 0<α := by linarith
  have hN0 : 0<N := by linarith
  have ha : 0≤1-1/α := by
    have hi : 1/α≤1 := (div_le_one hα).mpr hα1
    linarith
  have hb : 1-1/α≤(1/2:ℝ) := by
    have hi : (1/2:ℝ)≤1/α := (le_div_iff₀ hα).mpr (by linarith)
    linarith
  refine ⟨Real.one_le_rpow (by linarith) ha,?_⟩
  calc
    largeGcdThreshold α N ≤ N^(1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
    _ ≤ N/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩

theorem high_kernel_chosen_scale (M N K : ℝ) (hM : 0<M) (_hN : 0<N) (hK : 0<K)
    (hcut : N^2/M≤K) : Real.sqrt ((2*M)/K)*N≤2*M := by
  have hNK : N^2≤M*K := by
    have h := (div_le_iff₀ hM).mp hcut
    nlinarith
  let s := Real.sqrt ((2*M)/K)
  have hs0 : 0≤s := Real.sqrt_nonneg _
  have hs : s^2*K=2*M := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hK.ne']
  have hb : s^2*N^2≤2*M^2 := by
    calc
      _ ≤ s^2*(M*K) := mul_le_mul_of_nonneg_left hNK (sq_nonneg s)
      _ = (s^2*K)*M := by ring
      _ = _ := by rw [hs]; ring
  change s*N≤2*M
  nlinarith [sq_nonneg (s*N)]

theorem chosen_large_gcd_main (α M N K : ℝ) (hα : α≠0)
    (hM : 0<M) (hN : 0<N) (hK : 0<K) (hcut : N^2/M≤K) :
    2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α≤4*M := by
  rw [largeGcdThreshold_quotient_power α N hα hN]
  linarith [high_kernel_chosen_scale M N K hM hN hK hcut]

theorem chosen_large_gcd_full (α deltaLoss C M N K : ℝ) (hα1 : 1≤α) (hα2 : α≤2)
    (hδ : 0≤deltaLoss) (hC : 0≤C) (hM : 0<M) (hN : 4≤N) (hK : 0<K)
    (hcut : N^2/M≤K) :
    C*((2*M)*(N/largeGcdThreshold α N))^deltaLoss*
      (2*M+Real.sqrt ((2*M)/K)*(N/largeGcdThreshold α N)^α) ≤
        (4*C*2^deltaLoss)*(M*N)^deltaLoss*M := by
  have hh := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hH : 0<largeGcdThreshold α N := by linarith
  have hN0 : 0<N := by linarith
  have hp : ((2*M)*(N/largeGcdThreshold α N))^deltaLoss≤(2*(M*N))^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ
    have hn := div_le_self hN0.le hh.1
    nlinarith
  have hm := chosen_large_gcd_main α M N K (by linarith) hM hN0 hK hcut
  calc
    _ ≤ C*(2*(M*N))^deltaLoss*(4*M) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (by positivity)]; ring

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0181

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.PoissonConstants
Source SHA256: f4855c14105e6b2f236d0ff171fb786ae907d49a845ac49f44b8419dca14da30
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0182


namespace OAI

noncomputable section

namespace CanonicalQuadraticSieve

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

section

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

theorem list_exists_positive_bound (xs : List ℝ) :
    ∃ H : ℝ, 1≤H ∧ ∀x∈xs, x≤H := by
  induction xs with
  | nil => exact ⟨1,le_rfl,by simp⟩
  | cons x xs ih =>
    obtain ⟨H,hH,hxs⟩ := ih
    refine ⟨max H x, hH.trans (le_max_left _ _), ?_⟩
    intro y hy
    simp only [List.mem_cons] at hy
    rcases hy with rfl | hy
    · exact le_max_right _ _
    · exact (hxs y hy).trans (le_max_left _ _)

def poissonPrimitiveConstants
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [divisorConstant η hη, 2+1/(η*Real.log 2), 256,
   supportConstant η hη, divisorExponentConstant hexp η hη,
   ‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ‖quadraticTransformedSquareProfile W 0‖,
   dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant, CD, CS, CT, CP,
   sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W),
   sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W),
   sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, D^η]

theorem poissonPrimitiveConstants_nonneg
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (D : ℝ) (hD : 0≤D) (W : 𝓢(ℝ,ℂ)) :
    ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, 0≤x := by
  intro x hx
  simp only [poissonPrimitiveConstants,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact (divisorConstant_pos η hη).le
  · have : 0<Real.log 2 := Real.log_pos (by norm_num); positivity
  · norm_num
  · exact (supportConstant_pos η hη).le
  · exact (divisorExponentConstant_pos hexp η hη).le
  · positivity
  · positivity
  · exact dualMiddleDecayConstant_nonneg _
  · positivity
  · exact originalMiddleDecayConstant_nonneg _
  · exact nonzeroLatticeEnvelopeConstant_nonneg
  · exact hCD
  · exact hCS
  · exact hCT
  · exact hCP
  · positivity
  · positivity
  · positivity
  · exact Real.rpow_nonneg hD _

theorem poissonUnitBudget_power_envelope
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    {α : ℝ} (hexp : HasSieveExponent α) (η : ℝ) (hη : 0<η)
    (G : Ideal O) (hG : G≠0) (K N P D H : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 1≤K) (hN : 1≤N) (hP : 1≤P) (hD : 1≤D) (hH : 1≤H)
    (hconst : ∀x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W, x≤H)
    (hscales : ∀x∈([(Ideal.absNorm G:ℝ), K,N,(2*K)*N,N*N,
      (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ), 0≤x ∧ x≤D*P^4) :
    ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp η hη η hη G K N W,
      0≤x ∧ x≤(H*P^(4*η))^8 := by
  let V := H*P^(4*η)
  have hP0 : 0<P := by linarith
  have hR : 1≤P^(4*η) := Real.one_le_rpow hP (by positivity)
  have hV : 1≤V := by dsimp [V]; nlinarith
  have hCV (x : ℝ)
      (hx : x∈poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W) :
      0≤x ∧ x≤V := by
    refine ⟨poissonPrimitiveConstants_nonneg sD sS sT CD CS CT CP hCD hCS hCT hCP
      hexp η hη D (by linarith) W x hx, ?_⟩
    have hh := hconst x hx
    dsimp [V]
    nlinarith
  have hpow (x : ℝ)
      (hx : x∈([(Ideal.absNorm G:ℝ),K,N,(2*K)*N,N*N,
        (Ideal.absNorm G:ℝ)*(N*N),K*N] : List ℝ)) : 0≤x^η ∧ x^η≤V := by
    have hx0 := (hscales x hx).1
    refine ⟨Real.rpow_nonneg hx0 _, ?_⟩
    have hDpow : D^η≤H := hconst _ (by simp [poissonPrimitiveConstants])
    calc
      _ ≤ (D*P^4)^η := Real.rpow_le_rpow hx0 (hscales x hx).2 hη.le
      _ = D^η*P^(4*η) := by
        rw [Real.mul_rpow (by linarith : 0≤D) (by positivity : 0≤P^4)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
      _ ≤ V := mul_le_mul_of_nonneg_right hDpow (by positivity)
  let prims := poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W ++
    [(Ideal.absNorm G:ℝ)^η,K^η,N^η,((2*K)*N)^η,(N*N)^η,
      ((Ideal.absNorm G:ℝ)*(N*N))^η,(K*N)^η]
  have hprims : ∀x∈prims, 0≤x ∧ x≤V := by
    intro x hx
    simp only [prims,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with hx|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact hCV x hx
    all_goals exact hpow _ (by simp)
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈prims) (hn : xs.length≤8) : xs.prod≤V^8 :=
    list_prod_budget xs prims V hV hprims hx hn
  have hp1 (x : ℝ) (hx : x∈prims) : x≤V^8 := by
    simpa using hp [x] (by simpa using hx) (by simp)
  intro x hx
  simp only [poissonUnitBudget,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨by positivity, ?_⟩
    apply ((IdealDivisorBound.ideal_divisor_small_power η hη).choose_spec.2 G hG).trans
    have hh := hp [divisorConstant η hη,(Ideal.absNorm G:ℝ)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength K+1:ℕ) ≤ (2+1/(η*Real.log 2))*K^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη K hK).trans
    have hh := hp [2+1/(η*Real.log 2),K^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨by positivity, ?_⟩
    apply (show (columnDyadicLength N+1:ℕ) ≤ (2+1/(η*Real.log 2))*N^η by
      simpa only [Nat.cast_add,Nat.cast_one] using columnDyadicLength_small_power η hη N hN).trans
    have hh := hp [2+1/(η*Real.log 2),N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [256,supportConstant η hη,divisorConstant η hη,N^η,N^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [divisorExponentConstant hexp η hη,((2*K)*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖quadraticTransformedSquareProfile W 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨dualMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [dualMiddleDecayConstant (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [‖paperRadialFourier (quadraticSquareProfile W) 0‖] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨originalMiddleDecayConstant_nonneg _, ?_⟩
    have hh := hp [originalMiddleDecayConstant (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · refine ⟨nonzeroLatticeEnvelopeConstant_nonneg, ?_⟩
    have hh := hp [nonzeroLatticeEnvelopeConstant] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl
      simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,(N*N)^η,CD,sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,((Ideal.absNorm G:ℝ)*(N*N))^η,CS,sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [CT,sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  · have hs := (supportConstant_pos η hη).le
    have hd := (divisorConstant_pos η hη).le
    have he := (divisorExponentConstant_pos hexp η hη).le
    refine ⟨by positivity, ?_⟩
    have hh := hp [supportConstant η hη,N^η,CP,(K*N)^η] (by
      intro y hy
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl <;>
        simp only [prims,poissonPrimitiveConstants,List.mem_append,List.mem_cons,
          List.not_mem_nil,or_false,true_or,or_true]) (by simp)
    simpa only [divisorConstant,V,List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh

end

section

theorem selectedPoisson_upper (C C1 M X η : ℝ)
    (hC : 4≤C) (hCC : C≤C1) (hM : 1≤M) (hX : 1≤X)
    (hη : 0≤η) (hη1 : η≤1) :
    4≤selectedPoissonT C M X η ∧
    (M*X)^η≤selectedPoissonT C M X η ∧
    selectedPoissonK C M X η≤C1*(M*X)^3 := by
  have hC10 : 0≤C1 := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hP0 : 0<M*X := by positivity
  have hR : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 4≤selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  refine ⟨hT,by dsimp [selectedPoissonT]; nlinarith,?_⟩
  have hXP : X≤M*X := by nlinarith
  have hfrac : X^2/M≤(M*X)^2 :=
    (div_le_self (sq_nonneg _) hM).trans (pow_le_pow_left₀ hX0.le hXP 2)
  have hrpow : (M*X)^η≤M*X := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hP hη1
  calc
    selectedPoissonK C M X η = C*(M*X)^η*(X^2/M) := by
      unfold selectedPoissonK selectedPoissonT
      ring
    _ ≤ C1*(M*X)*(M*X)^2 := by gcongr
    _ = C1*(M*X)^3 := by ring

theorem poisson_seven_scale_bounds (g K N P B C1 : ℝ)
    (hP : 1≤P) (hB : 1≤B) (hC1 : 1≤C1)
    (hg0 : 0≤g) (hK0 : 0≤K) (hN0 : 0≤N)
    (hg : g≤B*P) (hK : K≤C1*P^3) (hN : N≤P) :
    ∀x∈([g,K,N,(2*K)*N,N*N,g*(N*N),K*N] : List ℝ),
      0≤x ∧ x≤(2*C1+B)*P^4 := by
  have hP0 : 0≤P := by linarith
  have hD : 1≤2*C1+B := by linarith
  have hp14 : P≤P^4 := by
    simpa only [pow_one] using pow_le_pow_right₀ hP (show 1≤4 by omega)
  have hp24 : P^2≤P^4 := pow_le_pow_right₀ hP (by omega)
  have hp34 : P^3≤P^4 := pow_le_pow_right₀ hP (by omega)
  intro x hx
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · refine ⟨hg0, hg.trans ?_⟩
    calc
      B*P ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hK0,hK.trans ?_⟩
    calc
      C1*P^3 ≤ C1*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨hN0,hN.trans (hp14.trans ?_)⟩
    nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      2*K*N ≤ 2*(C1*P^3)*P := by gcongr
      _ = (2*C1)*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      N*N ≤ P*P := by gcongr
      _ = P^2 := by ring
      _ ≤ P^4 := hp24
      _ ≤ (2*C1+B)*P^4 := by nlinarith [show 0≤P^4 by positivity]
  · refine ⟨by positivity,?_⟩
    calc
      g*(N*N) ≤ (B*P)*(P*P) := by gcongr
      _ = B*P^3 := by ring
      _ ≤ B*P^4 := by gcongr
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith
  · refine ⟨by positivity,?_⟩
    calc
      K*N ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ (2*C1+B)*P^4 := by gcongr; linarith

theorem power_cutoff_dominates (P T η : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l) :
    P^4≤T^l := by
  have hp0 : 0<P := by linarith
  calc
    P^4 = P^(4:ℝ) := by rw [Real.rpow_ofNat]
    _ ≤ P^(η*l) := Real.rpow_le_rpow_of_exponent_le hP hpow
    _ = (P^η)^l := by rw [Real.rpow_mul hp0.le,Real.rpow_natCast]
    _ ≤ T^l := pow_le_pow_left₀ (Real.rpow_nonneg hp0.le _) hT l

theorem poisson_truncation_small (P T η K M N C1 : ℝ) (l : ℕ)
    (hP : 1≤P) (hT : P^η≤T) (hpow : 4≤η*l)
    (_hK : 0≤K) (hM : 0≤M) (hN : 0≤N) (hC1 : 0≤C1)
    (hKP : K≤C1*P^3) (hMP : M≤P) (hNP : N≤P) :
    K*M/T^l≤C1 ∧ K*N/T^l≤C1 := by
  have hp0 : 0<P := by linarith
  have htpos : 0<T := lt_of_lt_of_le (Real.rpow_pos_of_pos hp0 _) hT
  have hcut := power_cutoff_dominates P T η l hP hT hpow
  have hb (Y : ℝ) (hY : 0≤Y) (hYP : Y≤P) : K*Y/T^l≤C1 := by
    apply (div_le_iff₀ (pow_pos htpos _)).mpr
    calc
      K*Y ≤ (C1*P^3)*P := by gcongr
      _ = C1*P^4 := by ring
      _ ≤ C1*T^l := by gcongr
  exact ⟨hb M hM hMP,hb N hN hNP⟩

theorem poisson_tail_abstract (B P t K η M : ℝ) (A : ℕ)
    (hB : 1≤B) (hP : 1≤P) (hM : 0≤M)
    (ht : 1/(B*P^2)≤t) (hu : P^η≤1+t*K) (hA : 4≤η*A) :
    M/((min 1 t)^2*(1+t*K)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hP0 : 0<P := by linarith
  have hBP : 1≤B*P^2 := by nlinarith [sq_nonneg (P-1)]
  have hinv : 1/(B*P^2)≤1 := (div_le_one (by positivity)).mpr hBP
  have htlo : 1/(B*P^2)≤min 1 t := le_min hinv ht
  have htpos : 0<min 1 t := lt_of_lt_of_le (by positivity) htlo
  have hup : 0<1+t*K := lt_of_lt_of_le (Real.rpow_pos_of_pos hP0 _) hu
  have hpow := power_cutoff_dominates P (1+t*K) η A hP hu hA
  have hprod : 1/B^2≤(min 1 t)^2*(1+t*K)^A := by
    calc
      1/B^2 = (1/(B*P^2))^2*P^4 := by field_simp
      _ ≤ (min 1 t)^2*(1+t*K)^A := by gcongr
  apply (div_le_iff₀ (by positivity : 0<(min 1 t)^2*(1+t*K)^A)).mpr
  have hh := mul_le_mul_of_nonneg_left hprod (show 0≤B^2*M by positivity)
  have he : (B^2*M)*(1/B^2)=M := by field_simp
  rw [he] at hh
  exact hh

theorem selectedPoisson_tail_shape (C B M X q η : ℝ) (A : ℕ)
    (hC : B≤C) (hB : 1≤B) (hM : 1≤M) (hX : 1≤X)
    (hq : 1≤q) (_hη : 0≤η) (hA : 4≤η*A) :
    M/((min 1 (M/((B*q)*(X/q)*(X/q))))^2*
      (1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤B^2*M := by
  have hB0 : 0<B := by linarith
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hq0 : 0<q := by linarith
  have hC0 : 0<C := by linarith
  have hP : 1≤M*X := by nlinarith
  have hXP : X≤M*X := by nlinarith
  have hMQ : 1≤M*q := by nlinarith
  have hEq : M/((B*q)*(X/q)*(X/q))=M*q/(B*X^2) := by field_simp
  have ht : 1/(B*(M*X)^2)≤M/((B*q)*(X/q)*(X/q)) := by
    rw [hEq]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    calc
      1*(B*X^2) ≤ B*(M*X)^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hX0.le hXP 2) hB0.le
      _ ≤ (M*q)*(B*(M*X)^2) := by nlinarith [show 0≤B*(M*X)^2 by positivity]
  have hu : (M*X)^η≤1+(M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η := by
    rw [selectedPoisson_radial_identity C B M X q η hM0 hX0 hq0 hB0]
    have hp : 0≤(M*X)^η := Real.rpow_nonneg (by positivity) _
    have hb : (M*X)^η≤selectedPoissonT C M X η*q/B := by
      apply (le_div_iff₀ hB0).mpr
      dsimp [selectedPoissonT]
      calc
        (M*X)^η*B = B*(M*X)^η := by ring
        _ ≤ C*(M*X)^η := mul_le_mul_of_nonneg_right hC hp
        _ ≤ C*(M*X)^η*q := le_mul_of_one_le_right (by positivity) hq
    linarith
  exact poisson_tail_abstract B (M*X) _ _ η M A hB hP hM0.le ht hu hA

theorem selectedPoisson_principal_shape (C M X N η α : ℝ)
    (hC : 4≤C) (hM : 1≤M) (hX : 1≤X) (hN : 0≤N) (hNX : N≤X)
    (hη : 0≤η) (hα : 1/2≤α) :
    Real.sqrt (M/selectedPoissonK C M X η)*N+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
    M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
  have hM0 : 0<M := by linarith
  have hX0 : 0<X := by linarith
  have hP : 1≤M*X := by nlinarith
  have hpow : 1≤(M*X)^η := Real.one_le_rpow hP hη
  have hT : 1≤selectedPoissonT C M X η := by dsimp [selectedPoissonT]; nlinarith
  have hT0 : 0<selectedPoissonT C M X η := by linarith
  have hK0 : 0<selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have hfrac : M/selectedPoissonK C M X η≤(M/X)^2 := by
    apply (div_le_iff₀ hK0).mpr
    have he : (M/X)^2*selectedPoissonK C M X η=M*selectedPoissonT C M X η := by
      unfold selectedPoissonK
      field_simp
    rw [he]
    nlinarith
  have hsqrt : Real.sqrt (M/selectedPoissonK C M X η)≤M/X := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by positivity,hfrac⟩
  have hfirst : Real.sqrt (M/selectedPoissonK C M X η)*N≤M := by
    calc
      _ ≤ (M/X)*X := by gcongr
      _ = M := by field_simp
  have hsecond : Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2) ≤
      selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
    calc
      _ ≤ Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) := by
        gcongr ; linarith
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_right hT
          (show 0≤Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) by positivity)
        nlinarith
  exact add_le_add hfirst hsecond

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy EisensteinSchwartzPoisson

def poissonShape (M X α : ℝ) : ℝ := M+X+X^(2*α-1)*M^(1-α)
def poissonShapeConstant (B C1 : ℝ) : ℝ := 2+4*C1^3+B^2+C1

theorem poisson_envelope_identity (H C P η Z : ℝ) (hP : 0<P) :
    262144*((H*P^(4*η))^8)^8*(C*P^(3*η)*Z) =
      (262144*H^64*C)*P^(259*η)*Z := by
  have hp : (P^(4*η))^64*P^(3*η)=P^(259*η) := by
    calc
      _ = P^((4*η)*64)*P^(3*η) := by rw [Real.rpow_mul hP.le (4*η) 64,Real.rpow_ofNat]
      _ = P^((4*η)*64+3*η) := (Real.rpow_add hP _ _).symm
      _ = _ := by congr 1; ring
  calc
    _ = (262144*H^64*C)*((P^(4*η))^64*P^(3*η))*Z := by ring
    _ = _ := by rw [hp]

theorem poissonComparisonMajorant_selected_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (η : ℝ) (hη : 0<η) (hη1 : η≤1) (l A : ℕ)
    (hl : 4≤η*l) (hA : 4≤η*A)
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    (hCD : 0≤CD) (hCS : 0≤CS) (hCT : 0≤CT) (hCP : 0≤CP)
    (B C1 : ℝ) (hB : 1≤B) (hC1 : 1≤C1) (W : 𝓢(ℝ,ℂ)) :
    ∃ Cfinal : ℝ, 0<Cfinal ∧
      ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
        1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
        1≤selectedPoissonK C M X η →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
        (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
        (fun _ : Unit => (1:ℂ)) W ≤
        Cfinal*(M*X)^(259*η)*poissonShape M X α := by
  let D := 2*C1+B
  have hD : 1≤D := by dsimp [D]; linarith only [hC1,hB]
  obtain ⟨H,hH,hconst⟩ := list_exists_positive_bound
    (poissonPrimitiveConstants sD sS sT CD CS CT CP hexp η hη D W)
  let Cshape := poissonShapeConstant B C1
  have hC10 : 0≤C1 := le_trans zero_le_one hC1
  have hCs : 1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3,sq_nonneg B]
  have hCsC : C1≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [pow_nonneg hC10 3,sq_nonneg B]
  have hCsB : B^2≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,pow_nonneg hC10 3]
  have hCsMid : 1+4*C1^3≤Cshape := by
    dsimp [Cshape,poissonShapeConstant]
    nlinarith only [hC10,sq_nonneg B]
  refine ⟨262144*H^64*Cshape,by positivity,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  have hM0 : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hX0 : 0<X := lt_of_lt_of_le zero_lt_one hX
  have hq0 : 0<q := lt_of_lt_of_le zero_lt_one hq
  have hP : 1≤M*X := by nlinarith only [hM,hX]
  have hP0 : 0<M*X := by positivity
  have hMP : M≤M*X := by nlinarith only [hM,hX]
  have hXP : X≤M*X := by nlinarith only [hM,hX]
  have hN : 1≤X/q := (le_div_iff₀ hq0).mpr (by simpa using hqX)
  have hNX : X/q≤X := div_le_self hX0.le hq
  have hNP : X/q≤M*X := hNX.trans hXP
  obtain ⟨hT,hTP,hKP⟩ := selectedPoisson_upper C C1 M X η hC hCC hM hX hη.le hη1
  have hKg : 0≤selectedPoissonK C M X η := le_trans zero_le_one hK
  have hg : (Ideal.absNorm G:ℝ)≤B*(M*X) := by rw [hGN]; gcongr; exact hqX.trans hXP
  have hb := poissonUnitBudget_power_envelope sD sS sT CD CS CT CP hCD hCS hCT hCP
    hexp η hη G hG (selectedPoissonK C M X η) (X/q) (M*X) D H W
    hK hN hP hD hH hconst
    (poisson_seven_scale_bounds (Ideal.absNorm G:ℝ) (selectedPoissonK C M X η) (X/q)
      (M*X) B C1 hP hB hC1 (Nat.cast_nonneg _) hKg (by positivity) hg hKP hNP)
  let R := (M*X)^(3*η)
  have hR : 1≤R := Real.one_le_rpow hP (by positivity)
  let Z := X^(2*α-1)*M^(1-α)
  have hZ : 0≤Z := by dsimp [Z]; positivity
  let S := Cshape*R*poissonShape M X α
  have hshape : 1≤poissonShape M X α := by
    change 1≤M+X+Z
    linarith only [hM,hX,hZ]
  have hshape0 : 0≤poissonShape M X α := le_trans zero_le_one hshape
  have hMshape : M≤poissonShape M X α := by
    change M≤M+X+Z
    linarith only [hX,hZ]
  have hXshape : X≤poissonShape M X α := by
    change X≤M+X+Z
    linarith only [hM,hZ]
  have hZshape : Z≤poissonShape M X α := by
    change Z≤M+X+Z
    linarith only [hM,hX]
  have hRshape : 1≤R*poissonShape M X α := by nlinarith only [hR,hshape]
  have hshapeS : poissonShape M X α≤S := by
    calc
      poissonShape M X α ≤ R*poissonShape M X α := le_mul_of_one_le_left hshape0 hR
      _ ≤ Cshape*(R*poissonShape M X α) :=
        le_mul_of_one_le_left (mul_nonneg (by linarith only [hR]) hshape0) hCs
      _ = S := by dsimp [S]; ring
  have hMS : M≤S := hMshape.trans hshapeS
  have hNS : X/q≤S := hNX.trans (hXshape.trans hshapeS)
  have hMiddle : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2) ≤
      4*C1^3*R*poissonShape M X α := by
    apply (selectedPoisson_middle_bound C M X η α hC hM hX hη.le hα2).trans
    change 4*C^3*R*Z≤4*C1^3*R*poissonShape M X α
    gcongr
  have hmidS : selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)≤S :=
    hMiddle.trans (by dsimp [S]; gcongr; linarith only [hCsMid])
  have hprS : Real.sqrt (M/selectedPoissonK C M X η)*(X/q)+
      Real.sqrt M*(selectedPoissonK C M X η)^(α-1/2)≤S := by
    apply (selectedPoisson_principal_shape C M X (X/q) η α hC hM hX (by positivity) hNX hη.le hα).trans
    calc
      M+selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η)^(α-1/2)
          ≤ poissonShape M X α+4*C1^3*R*poissonShape M X α := add_le_add hMshape hMiddle
      _ ≤ R*poissonShape M X α+4*C1^3*R*poissonShape M X α :=
        add_le_add (le_mul_of_one_le_left hshape0 hR) (le_refl _)
      _ = (1+4*C1^3)*R*poissonShape M X α := by ring
      _ ≤ S := by dsimp [S]; gcongr
  obtain ⟨hED,hES⟩ := poisson_truncation_small (M*X) (selectedPoissonT C M X η) η
    (selectedPoissonK C M X η) M (X/q) C1 l hP hTP hl hKg hM0.le (by positivity) hC10 hKP hMP hNP
  have hC1S : C1≤S := by
    calc
      C1 ≤ Cshape := hCsC
      _ ≤ Cshape*(R*poissonShape M X α) := le_mul_of_one_le_right (by positivity) hRshape
      _ = S := by dsimp [S]; ring
  have htailS : M/((min 1 (M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q))))^2*
      (1+(M/((Ideal.absNorm G:ℝ)*(X/q)*(X/q)))*selectedPoissonK C M X η)^A)≤S := by
    rw [hGN]
    apply (selectedPoisson_tail_shape C B M X q η A hBC hB hM hX hq hη.le hA).trans
    calc
      B^2*M ≤ B^2*(R*poissonShape M X α) := by
        gcongr
        exact hMshape.trans (le_mul_of_one_le_left hshape0 hR)
      _ ≤ Cshape*(R*poissonShape M X α) := by gcongr
      _ = S := by dsimp [S]; ring
  have hV : 1≤H*(M*X)^(4*η) := by
    have hh := Real.one_le_rpow hP (show 0≤4*η by positivity)
    nlinarith only [hH,hh]
  have hU : 1≤(H*(M*X)^(4*η))^8 := one_le_pow₀ hV
  apply (poissonComparisonMajorant_unit_box sD sS sT CD CS CT CP l A hexp η hη η hη G
    (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
    ((H*(M*X)^(4*η))^8) S W hKg (by positivity) hM0.le (by linarith only [hT]) hU (by dsimp [S]; positivity)
    hb hMS hNS hmidS hprS (hED.trans hC1S) (hES.trans hC1S) htailS).trans_eq
  exact poisson_envelope_identity H Cshape (M*X) η (poissonShape M X α) hP0

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0182

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.SelectedExponents
Source SHA256: 583b72b9f05ab3e90f3f86962eeebc227c1405f7a7bc333026837ce78e1a9139
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0183



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

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic IdealCoprimeSieveOperator

theorem poissonComparisonMajorant_small_power
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (hα2 : α≤2)
    (ρ : ℝ) (hρ : 0<ρ) :
    ∃ (η : ℝ) (hη : 0<η), η≤1 ∧ 259*η≤ρ ∧
    ∃ (l A : ℕ), 4≤η*l ∧ 4≤η*A ∧
      ∀ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
        0≤CD → 0≤CS → 0≤CT → 0≤CP →
      ∀ (B C1 : ℝ), 1≤B → 1≤C1 → ∀ (W : 𝓢(ℝ,ℂ)),
      ∃ Cfinal : ℝ, 0<Cfinal ∧
        ∀ (C M X q : ℝ) (G : Ideal O), 4≤C → B≤C → C≤C1 →
          1≤M → 1≤X → 1≤q → q≤X → G≠0 → (Ideal.absNorm G:ℝ)=B*q →
          1≤selectedPoissonK C M X η →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη G
          (selectedPoissonK C M X η) (X/q) M (selectedPoissonT C M X η)
          (fun _ : Unit => (1:ℂ)) W ≤
          Cfinal*(M*X)^ρ*poissonShape M X α := by
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : 259*η≤ρ := by
    have hh : η≤ρ/600 := min_le_right _ _
    linarith
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith
  refine ⟨η,hη,hη1,hηρ,l,l,horder,horder,?_⟩
  intro sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  obtain ⟨Cfinal,hCf,hbound⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l l horder horder sD sS sT CD CS CT CP hCD hCS hCT hCP B C1 hB hC1 W
  refine ⟨Cfinal,hCf,?_⟩
  intro C M X q G hC hBC hCC hM hX hq hqX hG hGN hK
  apply (hbound C M X q G hC hBC hCC hM hX hq hqX hG hGN hK).trans
  have hP : 1≤M*X := by nlinarith
  have hshape : 0≤poissonShape M X α := by unfold poissonShape; positivity
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hP hηρ) hCf.le) hshape

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

namespace CubicEisenstein

lemma hyperbolicHeight_continuous : Continuous hyperbolicHeight := by
  apply Continuous.quotient_lift
  have he (i j : Fin 2) : Continuous (fun g : SL(2,ℂ) => g i j) :=
    (continuous_apply j).comp ((continuous_apply i).comp continuous_complexSL_coe)
  apply Continuous.inv₀
  · exact ((he 1 0).norm.pow 2).add ((he 1 1).norm.pow 2)
  · intro g
    exact (rowEnergy_pos _ (complexBottomRow_ne_zero g)).ne'

lemma matrixCross_eq_gram (g : SL(2,ℂ)) : matrixCross g=matrixGram g 0 1 := by
  simp only [matrixCross,matrixGram,Matrix.mul_apply,Fin.sum_univ_two,Matrix.star_apply]

lemma hyperbolicGram_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicGram (upperPoint z v hv) 0 1=z/(v:ℂ) := by
  change matrixGram (upperSection z v hv) 0 1=_
  rw [←matrixCross_eq_gram]
  have hh := matrixCross_upperSection (1:SL(2,ℂ)) z v hv
  simpa [Matrix.one_apply] using hh

def hyperbolicHorizontal (w : HyperbolicSpace) : ℂ :=
  hyperbolicGram w 0 1*(hyperbolicHeight w:ℂ)

lemma hyperbolicHorizontal_continuous : Continuous hyperbolicHorizontal := by
  unfold hyperbolicHorizontal
  exact ((continuous_apply 1).comp ((continuous_apply 0).comp hyperbolicGram_continuous)).mul
    (Complex.continuous_ofReal.comp hyperbolicHeight_continuous)

@[simp] lemma hyperbolicHorizontal_upperPoint (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHorizontal (upperPoint z v hv)=z := by
  simp only [hyperbolicHorizontal,hyperbolicGram_upperPoint,hyperbolicHeight_upperPoint]
  exact div_mul_cancel₀ z (Complex.ofReal_ne_zero.mpr hv.ne')

def hyperbolicCoordinates (w : HyperbolicSpace) : UpperCoordinates :=
  ⟨(hyperbolicHorizontal w,hyperbolicHeight w),hyperbolicHeight_pos w⟩

lemma hyperbolicCoordinates_continuous : Continuous hyperbolicCoordinates :=
  (hyperbolicHorizontal_continuous.prodMk hyperbolicHeight_continuous).subtype_mk _

lemma upperCoordinates_left_inverse : Function.LeftInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro p
  apply Subtype.ext
  exact Prod.ext (hyperbolicHorizontal_upperPoint _ _ _) (hyperbolicHeight_upperPoint _ _ _)

lemma upperCoordinates_right_inverse : Function.RightInverse hyperbolicCoordinates
    (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2) := by
  intro w
  obtain ⟨z,v,hv,rfl⟩ := upperPoint_surjective w
  exact congrArg (fun p : UpperCoordinates => upperPoint p.1.1 p.1.2 p.2)
    (upperCoordinates_left_inverse ⟨(z,v),hv⟩)

def upperCoordinatesHomeomorph : UpperCoordinates ≃ₜ HyperbolicSpace where
  toFun p := upperPoint p.1.1 p.1.2 p.2
  invFun := hyperbolicCoordinates
  left_inv := upperCoordinates_left_inverse
  right_inv := upperCoordinates_right_inverse
  continuous_toFun := continuous_upperCoordinates
  continuous_invFun := hyperbolicCoordinates_continuous

lemma fundamentalSet_measure_le_cover (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (hH : H≤CubicKubota.levelThree) (B : Set HyperbolicSpace)
    (hB : ∀w,∃M:H,M • w∈B) :
    hyperbolicVolume (hyperbolicFundamentalSet H)≤hyperbolicVolume B := by
  rw [(hyperbolicFundamentalSet_isFundamentalDomain H hH).measure_eq_tsum B]
  apply le_trans (measure_mono ?_) (measure_iUnion_le _)
  intro w hw
  obtain ⟨M,hM⟩ := hB w
  apply Set.mem_iUnion.mpr
  refine ⟨M⁻¹,?_,hw⟩
  exact ⟨M • w,hM,inv_smul_smul M w⟩

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

def spatialHeightSplit : EuclideanSpatial ≃ᵐ ℝ × (Fin 2 → ℝ) :=
  (MeasurableEquiv.toLp 2 (Fin 3 → ℝ)).symm.trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2)

lemma spatialHeightSplit_fst (p : EuclideanSpatial) : (spatialHeightSplit p).1=p 2 := rfl
lemma spatialHeightSplit_snd_zero (p : EuclideanSpatial) : (spatialHeightSplit p).2 0=p 0 := rfl
lemma spatialHeightSplit_snd_one (p : EuclideanSpatial) : (spatialHeightSplit p).2 1=p 1 := rfl

lemma spatialHeightSplit_preserves_volume : MeasurePreserving spatialHeightSplit volume volume :=
  (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).comp
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3))

def horizontalUnitBox : Set (Fin 2 → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-1) 1)
lemma horizontalUnitBox_measurable : MeasurableSet horizontalUnitBox :=
  MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
lemma horizontalUnitBox_volume : volume horizontalUnitBox=4 := by
  rw [horizontalUnitBox,volume_pi_pi]
  norm_num

def euclideanCuspBox (a : ℝ) : Set EuclideanSpatial :=
  spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox)
lemma euclideanCuspBox_measurable (a : ℝ) : MeasurableSet (euclideanCuspBox a) :=
  spatialHeightSplit.measurable (measurableSet_Ioi.prod horizontalUnitBox_measurable)
lemma euclideanCuspBox_positive (a : ℝ) (ha : 0≤a) : euclideanCuspBox a ⊆ euclideanUpperHalf := by
  intro p hp
  exact ha.trans_lt hp.1

theorem euclideanCuspBox_volume (a : ℝ) (ha : 0<a) :
    hyperbolicEuclideanVolume (euclideanCuspBox a)=4*ENNReal.ofReal (1/(2*a^2)) := by
  unfold hyperbolicEuclideanVolume
  rw [withDensity_apply _ (euclideanCuspBox_measurable a),
    Measure.restrict_restrict (euclideanCuspBox_measurable a),
    Set.inter_eq_left.mpr (euclideanCuspBox_positive a ha.le)]
  change (∫⁻p in spatialHeightSplit ⁻¹' (Set.Ioi a ×ˢ horizontalUnitBox),
    ENNReal.ofReal (((spatialHeightSplit p).1^3)⁻¹))=_
  rw [spatialHeightSplit_preserves_volume.setLIntegral_comp_preimage
    (f := fun q : ℝ × (Fin 2 → ℝ) => ENNReal.ofReal ((q.1^3)⁻¹))
    (measurableSet_Ioi.prod horizontalUnitBox_measurable) (by fun_prop)]
  change (∫⁻q : ℝ × (Fin 2 → ℝ) in Set.Ioi a ×ˢ horizontalUnitBox,
    ENNReal.ofReal ((q.1^3)⁻¹) ∂((volume : Measure ℝ).prod volume))=_
  rw [setLIntegral_prod _ (by fun_prop)]
  simp only [lintegral_const,Measure.restrict_apply MeasurableSet.univ,Set.univ_inter,
    horizontalUnitBox_volume]
  rw [lintegral_mul_const _ (by fun_prop),cusp_height_volume a ha]
  exact mul_comm _ _

local notation "O" => ActualEisensteinCubic.O

instance fullSLMeasurableAction : MeasurableConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨fun g => (continuous_hyperbolic_action g).measurable⟩
instance fullSLVolumeInvariant : SMulInvariantMeasure (SL(2,ℂ)) HyperbolicSpace hyperbolicVolume where
  measure_preimage_smul g s hs := by
    have he := congrArg (fun ν : Measure HyperbolicSpace => ν s) (hyperbolicVolume_invariant g)
    simpa only [Measure.map_apply (continuous_hyperbolic_action g).measurable hs] using he

def hyperbolicCuspBox (a : ℝ) : Set HyperbolicSpace :=
  {w | ‖hyperbolicHorizontal w‖≤1 ∧ a<hyperbolicHeight w}

lemma hyperbolicCuspBox_measurable (a : ℝ) : MeasurableSet (hyperbolicCuspBox a) :=
  (isClosed_le hyperbolicHorizontal_continuous.norm continuous_const).measurableSet.inter
    (isOpen_lt continuous_const hyperbolicHeight_continuous).measurableSet

lemma hyperbolicCuspBox_volume_le (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)≤4*ENNReal.ofReal (1/(2*a^2)) := by
  rw [hyperbolicVolume,Measure.map_apply euclideanToHyperbolic_measurable
    (hyperbolicCuspBox_measurable a),←euclideanCuspBox_volume a ha]
  apply measure_mono_ae
  filter_upwards [hyperbolicEuclideanVolume_ae_positive] with p hp hB
  rw [Set.mem_preimage,euclideanToHyperbolic_positive p hp] at hB
  change ‖hyperbolicHorizontal (upperPoint _ _ hp)‖≤1 ∧ a<hyperbolicHeight (upperPoint _ _ hp) at hB
  rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint] at hB
  refine ⟨hB.2,?_⟩
  intro j hj
  fin_cases j
  · change -1≤p 0 ∧ p 0≤1
    have hh := (Complex.abs_re_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh
  · change -1≤p 1 ∧ p 1≤1
    have hh := (Complex.abs_im_le_norm ((p 0:ℂ)+Complex.I*(p 1:ℂ))).trans hB.1
    simpa using abs_le.mp hh

lemma hyperbolicCuspBox_volume_lt_top (a : ℝ) (ha : 0<a) :
    hyperbolicVolume (hyperbolicCuspBox a)<⊤ :=
  (hyperbolicCuspBox_volume_le a ha).trans_lt (ENNReal.mul_lt_top (by norm_num) ENNReal.ofReal_lt_top)

theorem hyperbolicFundamentalSet_volume_lt_top (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] :
    hyperbolicVolume (hyperbolicFundamentalSet H)<⊤ := by
  obtain ⟨S,hS⟩ := finiteIndex_ford_cover H
  let a : ℝ := Real.sqrt (2/3)/2
  have ha : 0<a := by dsimp [a]; positivity
  let B : Set HyperbolicSpace := ⋃r∈S,integralComplexMatrix r⁻¹ • hyperbolicCuspBox a
  have hcover : ∀w,∃M:H,M • w∈B := by
    intro w
    obtain ⟨M,r,hr,z,v,hv,hM,hz,hfloor⟩ := hS w
    refine ⟨M,?_⟩
    rw [integralSubgroup_smul,hM]
    apply Set.mem_iUnion.mpr
    refine ⟨r,Set.mem_iUnion.mpr ⟨hr,?_⟩⟩
    apply Set.mem_smul_set.mpr
    refine ⟨upperPoint z v hv,?_,rfl⟩
    change ‖hyperbolicHorizontal (upperPoint z v hv)‖≤1 ∧ a<hyperbolicHeight (upperPoint z v hv)
    rw [hyperbolicHorizontal_upperPoint,hyperbolicHeight_upperPoint]
    refine ⟨?_,?_⟩
    · rw [Complex.normSq_eq_norm_sq] at hz
      nlinarith [norm_nonneg z]
    · dsimp [a] at *
      linarith
  apply (fundamentalSet_measure_le_cover H hH B hcover).trans_lt
  apply (measure_biUnion_finset_le S (fun r => integralComplexMatrix r⁻¹ • hyperbolicCuspBox a)).trans_lt
  apply ENNReal.sum_lt_top.mpr
  intro r hr
  rw [measure_smul]
  exact hyperbolicCuspBox_volume_lt_top a ha

lemma integralQuotientVolume_univ (H : Subgroup (SL(2,O))) :
    integralQuotientVolume H Set.univ=hyperbolicVolume (hyperbolicFundamentalSet H) := by
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection H) MeasurableSet.univ]
  simp

theorem integralQuotientVolume_finite (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) [H.FiniteIndex] : IsFiniteMeasure (integralQuotientVolume H) :=
  ⟨by rw [integralQuotientVolume_univ]; exact hyperbolicFundamentalSet_volume_lt_top H hH⟩

instance kernelQuotientVolume_finite : IsFiniteMeasure (integralQuotientVolume globalKubotaKernel) := by
  let : globalKubotaKernel.FiniteIndex := globalKubotaKernel_finiteIndex
  exact integralQuotientVolume_finite globalKubotaKernel globalKubotaKernel_le_levelThree

end CubicEisenstein

namespace CanonicalQuadraticSieve

section

theorem improved_threshold_ge_column (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N≤M := by
  have hp : 1≤2-1/α := by
    have hh : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα
    linarith
  calc
    N = N^(1:ℝ) := (Real.rpow_one N).symm
    _ ≤ N^(2-1/α) := Real.rpow_le_rpow_of_exponent_le hN hp
    _ ≤ M := hM

theorem improved_threshold_power (α N M : ℝ) (hα : 0<α) (hN : 0<N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)≤M^α := by
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hN.le _) hM hα.le
  rw [←Real.rpow_mul hN.le] at hh
  have he : (2-1/α)*α=2*α-1 := by field_simp
  rwa [he] at hh

theorem improved_threshold_main (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : N^(2*α-1)*M^(1-α)≤M := by
  have hNM := improved_threshold_ge_column α N M hα hN hM
  have hM0 : 0<M := by linarith
  have hh := improved_threshold_power α N M (by linarith) (by linarith) hM
  calc
    _ ≤ M^α*M^(1-α) := mul_le_mul_of_nonneg_right hh (Real.rpow_nonneg hM0.le _)
    _ = M := by rw [←Real.rpow_add hM0]; simp

theorem improved_threshold_shape (α N M : ℝ) (hα : 1≤α) (hN : 1≤N)
    (hM : N^(2-1/α)≤M) : M+N+N^(2*α-1)*M^(1-α)≤3*M := by
  linarith [improved_threshold_main α N M hα hN hM,
    improved_threshold_ge_column α N M hα hN hM]

theorem improved_threshold_reciprocal (α N M : ℝ) (_hα : 0<α) (hN : 0<N) (hM0 : 0<M)
    (hM : N^(2-1/α)≤M) : N^2/M≤N^(1/α) := by
  apply (div_le_iff₀ hM0).mpr
  have he : N^2=N^(2-1/α)*N^(1/α) := by
    rw [←Real.rpow_add hN]
    convert (Real.rpow_two N).symm using 1 ; ring_nf
  rw [he]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hN.le (1/α))

theorem improved_threshold_low (α C η N M : ℝ) (hα : 0<α) (hC : 0<C)
    (hN : 0<N) (hM0 : 0<M) (hM : N^(2-1/α)≤M) :
    (selectedPoissonK C M N η)^α≤C^α*(M*N)^(η*α)*N := by
  have hk : selectedPoissonK C M N η≤C*(M*N)^η*N^(1/α) := by
    unfold selectedPoissonK selectedPoissonT
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (improved_threshold_reciprocal α N M hα hN hM0 hM) (by positivity)
  have hk0 : 0≤selectedPoissonK C M N η := by
    unfold selectedPoissonK selectedPoissonT
    positivity
  calc
    _ ≤ (C*(M*N)^η*N^(1/α))^α := Real.rpow_le_rpow hk0 hk hα.le
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0≤C*(M*N)^η) (by positivity),
        Real.mul_rpow hC.le (by positivity),←Real.rpow_mul (by positivity : 0≤M*N),
        ←Real.rpow_mul hN.le]
      have he : (1/α)*α=1 := by field_simp
      rw [he,Real.rpow_one]

theorem sieveNorm_large_rows (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hlarge : N^2≤M) :
    sieveNorm M N≤5*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤2*N := by
    have h := Nat.ceil_lt_add_one (by linarith : 0≤N)
    linarith
  have hsq : (⌈N⌉₊:ℝ)^2≤4*M := by
    calc
      _ ≤ (2*N)^2 := pow_le_pow_left₀ (Nat.cast_nonneg _) hceil 2
      _ = 4*N^2 := by ring
      _ ≤ 4*M := by linarith
  have hh := sieveNorm_initial M N hM hN
  have hC := QuadraticInitialBound.initialSieveConstant_pos
  nlinarith

theorem hasSieveExponent_of_threshold_band (β : ℝ) (_hβ1 : 1≤β) (hβ2 : β≤2)
    (hband : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^β≤M → M≤N^2 → sieveNorm M N≤C*(M*N)^ρ*M) :
    HasSieveExponent β := by
  intro ε hε
  have hρ : 0<ε/3 := by positivity
  obtain ⟨C,hC,hbound⟩ := hband (ε/3) hρ
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  refine ⟨C+5*I,by positivity,?_⟩
  intro M N hM hN
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hMN : 1≤M*N := by nlinarith
  have hpow : 1≤(M*N)^ε := Real.one_le_rpow hMN hε.le
  have hNb : 0≤N^β := Real.rpow_nonneg hN0.le _
  by_cases hlarge : N^2≤M
  · calc
      _ ≤ 5*I*M := sieveNorm_large_rows M N hM hN hlarge
      _ = (5*I)*1*M := by ring
      _ ≤ (C+5*I)*(M*N)^ε*(M+N^β) := by gcongr <;> linarith
  · let R := max M (N^β)
    have hNβsq : N^β≤N^2 := by
      simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hN hβ2
    have hR : 1≤R := hM.trans (le_max_left _ _)
    have hRM : M≤R := le_max_left _ _
    have hRN : N^β≤R := le_max_right _ _
    have hRsq : R≤N^2 := max_le (le_of_not_ge hlarge) hNβsq
    have hb := hbound R N hR hN hRN hRsq
    have hmono := sieveNorm_mono hRM (le_refl N)
    have hN2 : 1≤N^2 := one_le_pow₀ hN
    have hM3 : M≤M^3 := by
      simpa only [pow_one] using pow_le_pow_right₀ hM (show (1:ℕ)≤3 by decide)
    have hRN2 : R≤M*N^2 := by
      apply max_le
      · nlinarith
      · exact hNβsq.trans (by nlinarith)
    have hprod : R*N≤(M*N)^3 := by
      calc
        _ ≤ (M*N^2)*N := mul_le_mul_of_nonneg_right hRN2 hN0.le
        _ = M*N^3 := by ring
        _ ≤ M^3*N^3 := mul_le_mul_of_nonneg_right hM3 (by positivity)
        _ = _ := by ring
    have hRprod : (R*N)^(ε/3)≤(M*N)^ε := by
      calc
        _ ≤ ((M*N)^3)^(ε/3) := Real.rpow_le_rpow (by positivity) hprod hρ.le
        _ = _ := by
          rw [←Real.rpow_natCast (M*N) 3,←Real.rpow_mul (by positivity : 0≤M*N)]
          congr 1
          ring
    have hRadd : R≤M+N^β := max_le (by linarith) (by linarith)
    exact hmono.trans (hb.trans (by gcongr ; linarith))

open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_of_shell_threshold (β : ℝ) (hβ1 : 1≤β) (hβ2 : β≤2)
    (hshell : ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M X : ℝ,
      1≤M → 1≤X → X^β≤M → ∀a : idealRange X → ℂ, CoefficientOnShell X X a →
      ballQuadraticEnergy M X a≤C*(M*X)^ρ*M*∑J,‖a J‖^2) :
    HasSieveExponent β := by
  apply hasSieveExponent_of_threshold_band β hβ1 hβ2
  intro ε hε
  have hρ : 0<ε/2 := by positivity
  obtain ⟨C,hC,hbound⟩ := hshell (ε/2) hρ
  let lengthScale := 2+1/((ε/2)*Real.log 2)
  have hL : 0<lengthScale := by
    have hlog : 0<Real.log 2 := Real.log_pos (by norm_num)
    dsimp only [lengthScale]
    positivity
  refine ⟨4*C*8^(ε/2)*lengthScale,by positivity,?_⟩
  intro M N hM hN hMN hMsq
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hprod : 0<M*N := by positivity
  apply FiniteSieveOperator.squared_norm_le_of_energy (matrix M N) _ (by positivity)
  intro a
  let a' := fun j : Fin (columnDyadicLength N+1) =>
    coefficientAtScale N ((2:ℝ)^j.val)
      (dyadicColumnCoefficient N (columnDyadicLength N) (columnDyadicLength_cover N) j a)
  have hpart := ballQuadraticEnergy_column_shells_at_scale M N (columnDyadicLength N)
    (columnDyadicLength_cover N) a
  have hj (j : Fin (columnDyadicLength N+1)) :
      ballQuadraticEnergy M ((2:ℝ)^j.val) (a' j) ≤
        (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
    let X := (2:ℝ)^j.val
    have hx := columnDyadicScale_bounds N hN j
    have hβ0 : 0≤β := by linarith
    have hXpow : X^β≤4*M := by
      calc
        _ ≤ (2*N)^β := Real.rpow_le_rpow (by positivity) hx.2 hβ0
        _ = 2^β*N^β := Real.mul_rpow (by norm_num) hN0.le
        _ ≤ 4*N^β := by
          have ht : (2:ℝ)^β≤4 := by
            have ht := Real.rpow_le_rpow_of_exponent_le
              (by norm_num : (1:ℝ)≤2) hβ2
            norm_num at ht
            exact ht
          exact mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg hN0.le _)
        _ ≤ 4*M := by linarith
    have hshell' : CoefficientOnShell X X (a' j) :=
      coefficientAtScale_shell N X _ (dyadicColumnCoefficient_shell N _ _ j a)
    have hb := hbound (4*M) X (by linarith) hx.1 hXpow (a' j) hshell'
    have hp : ((4*M)*X)^(ε/2)≤8^(ε/2)*(M*N)^(ε/2) := by
      calc
        _ ≤ (8*(M*N))^(ε/2) := Real.rpow_le_rpow (by positivity) (by nlinarith [hx.2]) hρ.le
        _ = _ := Real.mul_rpow (by norm_num) hprod.le
    apply (ballQuadraticEnergy_mono (by linarith : M≤4*M) (a' j)).trans
    apply hb.trans
    calc
      _ ≤ C*(8^(ε/2)*(M*N)^(ε/2))*(4*M)*∑J,‖a' j J‖^2 := by gcongr
      _ = _ := by ring
  have he : (∑j : Fin (columnDyadicLength N+1), ∑J,‖a' j J‖^2)=∑J,‖a J‖^2 :=
    dyadicColumnCoefficient_at_scale_energy N _ _ a
  have hlen : (columnDyadicLength N+1:ℝ)≤lengthScale*(M*N)^(ε/2) := by
    apply (columnDyadicLength_small_power (ε/2) hρ N hN).trans
    change lengthScale*N^(ε/2)≤lengthScale*(M*N)^(ε/2)
    gcongr
    nlinarith
  change ballQuadraticEnergy M N a≤_
  apply hpart.trans
  calc
    _ ≤ (columnDyadicLength N+1:ℝ)*
        ∑j : Fin (columnDyadicLength N+1),
          (4*C*8^(ε/2)*(M*N)^(ε/2)*M)*∑J,‖a' j J‖^2 := by
      gcongr with j
      exact hj j
    _ = (columnDyadicLength N+1:ℝ)*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by
      rw [←Finset.mul_sum,he]
      ring
    _ ≤ (lengthScale*(M*N)^(ε/2))*(4*C*8^(ε/2)*(M*N)^(ε/2)*M)*(∑J,‖a J‖^2) := by gcongr
    _ = _ := by
      have hp : (M*N)^(ε/2)*(M*N)^(ε/2)=(M*N)^ε := by
        rw [←Real.rpow_add hprod]
        congr 1
        ring
      calc
        _ = (4*C*8^(ε/2)*lengthScale)*((M*N)^(ε/2)*(M*N)^(ε/2))*M*(∑J,‖a J‖^2) := by ring
        _ = _ := by rw [hp]

end

open ActualEisensteinCubic IdealCoprimeSieveOperator DivisorBlockCauchy

def fixedBadNorm : ℝ := Ideal.absNorm (∏P∈fixedBadPrimes,P)
def fixedCutoffBase : ℝ := max 4 fixedBadNorm

theorem fixedBadNorm_one_le : 1≤fixedBadNorm := by
  have h1 : Admissible (1 : Ideal O) := by
    refine ⟨one_ne_zero, isUnit_one.squarefree, ?_⟩
    intro P hP
    simp only [UniqueFactorizationMonoid.normalizedFactors_one, Multiset.notMem_zero] at hP
  have he := commonMaskIdeal_eq_fixed_mul (1 : Ideal O) h1
  rw [mul_one] at he
  have hn : (∏P∈fixedBadPrimes,P)≠0 := by
    rw [←he]
    exact (commonMaskIdeal_squarefree 1).ne_zero
  unfold fixedBadNorm
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hn (Ideal.absNorm_eq_zero_iff.mp h))

theorem fixedCutoffBase_bounds : 4≤fixedCutoffBase ∧ fixedBadNorm≤fixedCutoffBase :=
  ⟨le_max_left _ _,le_max_right _ _⟩

theorem HasSieveExponent.annular_selected_bound {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) (C1 : ℝ) (hC1 : 1≤C1) :
    ∃ C : ℝ, 0<C ∧ ∀ (c M N : ℝ),
      fixedCutoffBase≤c → c≤C1 → 1≤M → 4≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK c M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N (selectedPoissonK c M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hα : 1/2≤α := by linarith
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,henergy⟩ :=
    hexp.annular_energy_from_scalar_cost hα η hη l A
  obtain ⟨CF,hCF,hscalar⟩ := poissonComparisonMajorant_selected_power hexp hα hα2
    η hη hη1 l A hl hA sD sS sT CD CS CT CP hCD.le hCS.le hCT.le hCP.le
    fixedBadNorm C1 fixedBadNorm_one_le hC1 QuadraticInitialBound.annularSieveCutoff
  have hdiv : 0<divisorConstant η hη := divisorConstant_pos η hη
  let SD := supportConstant η hη*divisorConstant η hη
  have hSD : 0<SD := mul_pos (supportConstant_pos η hη) (divisorConstant_pos η hη)
  let F := 16*(3*CF*divisorConstant η hη + 4*CH*2^η*SD)
  refine ⟨F,by dsimp [F]; positivity,?_⟩
  intro c M N hc hc1 hM hN hthreshold hK a ha
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hN1 : 1≤N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hc4 : 4≤c := fixedCutoffBase_bounds.1.trans hc
  have hcB : fixedBadNorm≤c := fixedCutoffBase_bounds.2.trans hc
  have hT : 4≤selectedPoissonT c M N η := by
    have hp := Real.one_le_rpow hP hη.le
    unfold selectedPoissonT
    nlinarith
  have hcut : N^2/M≤selectedPoissonK c M N η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    have hp : 0≤N^2/M := by positivity
    nlinarith
  have hH := largeGcdThreshold_bounds α N hα1 hα2 hN
  have hcost : ∀D∈gcdPool (fun J : idealRange N => J.val),
      (Ideal.absNorm D:ℝ)≤largeGcdThreshold α N →
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp η hη η hη
        (commonMaskIdeal D) (selectedPoissonK c M N η) (N/(Ideal.absNorm D:ℝ)) M
        (selectedPoissonT c M N η) (fun _ : Unit => (1:ℂ))
        QuadraticInitialBound.annularSieveCutoff ≤ 3*CF*(M*N)^(259*η)*M := by
    intro D hD hd
    have hadm := gcdPool_admissible (fun J : idealRange N => J.val)
      (fun J => (mem_idealRange.mp J.property).1) D hD
    have hd1 : 1≤(Ideal.absNorm D:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hadm.1 (Ideal.absNorm_eq_zero_iff.mp hz))
    have hgn : (Ideal.absNorm (commonMaskIdeal D):ℝ)=fixedBadNorm*(Ideal.absNorm D:ℝ) := by
      rw [commonMaskIdeal_norm D hadm, Nat.cast_mul]
      rfl
    have hb := hscalar c M N (Ideal.absNorm D:ℝ) (commonMaskIdeal D) hc4 hcB hc1 hM hN1 hd1
      (by linarith [hH.2]) (commonMaskIdeal_squarefree D).ne_zero hgn hK
    apply hb.trans
    have hs : poissonShape M N α≤3*M := improved_threshold_shape α N M hα1 hN1 hthreshold
    calc
      _ ≤ CF*(M*N)^(259*η)*(3*M) := mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have he := henergy η hη M N (selectedPoissonK c M N η) (selectedPoissonT c M N η)
    (largeGcdThreshold α N) (3*CF*(M*N)^(259*η)*M) hM hN1 hK hT
    (by linarith [hH.1]) hH.2 (by positivity) hcost a ha
  have hhigh := chosen_large_gcd_full α η CH M N (selectedPoissonK c M N η)
    hα1 hα2 hη.le hCH.le hM0 hN (by linarith) hcut
  have hn : N^η≤(M*N)^η := Real.rpow_le_rpow hN0.le (by nlinarith) hη.le
  have hcombine1 : (M*N)^(259*η)*(M*N)^η=(M*N)^(260*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  have hcombine2 : (M*N)^η*((M*N)^η)^2=(M*N)^(3*η) := by
    rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
    congr 1
    ring
  have hpow : (M*N)^(3*η)≤(M*N)^(260*η) :=
    Real.rpow_le_rpow_of_exponent_le hP (by linarith)
  have hfirst : (3*CF*(M*N)^(259*η)*M/6)*(divisorConstant η hη*N^η) ≤
      (3*CF*divisorConstant η hη)*(M*N)^(260*η)*M := by
    calc
      _ ≤ (3*CF*(M*N)^(259*η)*M)*(divisorConstant η hη*(M*N)^η) := by
        gcongr
        nlinarith [show 0≤3*CF*(M*N)^(259*η)*M by positivity]
      _ = _ := by rw [←hcombine1]; ring
  have hsecond : (CH*((2*M)*(N/largeGcdThreshold α N))^η*
      (2*M+Real.sqrt ((2*M)/selectedPoissonK c M N η)*(N/largeGcdThreshold α N)^α))*
      SD*(N^η)^2 ≤ (4*CH*2^η*SD)*(M*N)^(260*η)*M := by
    calc
      _ ≤ ((4*CH*2^η)*(M*N)^η*M)*SD*((M*N)^η)^2 := by gcongr
      _ = (4*CH*2^η*SD)*(M*N)^(3*η)*M := by rw [←hcombine2]; ring
      _ ≤ _ := by gcongr
  apply he.trans
  change 16*(_+_*SD*(N^η)^2)*_≤_
  calc
    _ ≤ 16*((3*CF*divisorConstant η hη)*(M*N)^(260*η)*M+
      (4*CH*2^η*SD)*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) (by norm_num))
        (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
    _ = _ := by dsimp [F]; ring

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0183

/-! Original module: OAI.NumberTheory.DirichletL.Eisenstein.CompactProfiles
Source SHA256: ab018d028523f35991c994f8d50a3cb7ef5454e4a3c3d5574c7d41899a26f72a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0184


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

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

lemma cosetHeight_continuous (r : CuspCosets) : Continuous (cosetHeight r) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    have heq : cosetHeight (cosetOf M)=(fun w => hyperbolicHeight (complexMatrix M • w)) :=
      funext (cosetHeight_cosetOf M)
    change Continuous (cosetHeight (cosetOf M))
    rw [heq]
    exact hyperbolicHeight_continuous.comp (continuous_hyperbolic_action _)

lemma cuspCutoffCorrection_measurable (Y : ℝ) (F : ℝ → ℂ) (hF : Measurable F) :
    Measurable (cuspCutoffCorrection Y F) := by
  unfold cuspCutoffCorrection
  apply Measurable.tsum
  intro r
  apply Measurable.ite
  · exact (isOpen_lt continuous_const (cosetHeight_continuous r)).measurableSet
  · exact measurable_const.mul (hF.comp (cosetHeight_continuous r).measurable)
  · exact measurable_const

lemma cuspCutoffCorrection_norm_le (F : ℝ → ℂ) (C : ℝ) (hC : 0≤C)
    (hF : ∀v,‖F v‖≤C) (w : HyperbolicSpace) : ‖cuspCutoffCorrection 1 F w‖≤C := by
  by_cases hh : ∃r : CuspCosets,1<cosetHeight r w
  · obtain ⟨r,hr⟩ := hh
    rw [cuspCutoffCorrection_eq 1 le_rfl F w r hr,norm_mul,norm_inv,
      norm_cosetCharacter,inv_one,one_mul]
    exact hF _
  · have hz : cuspCutoffCorrection 1 F w=0 := by
      unfold cuspCutoffCorrection
      have hz : (fun r => cuspCutoffTerm 1 F r w)=(fun _ : CuspCosets => (0:ℂ)) := by
        funext r
        simp [cuspCutoffTerm,show ¬1<cosetHeight r w from fun h => hh ⟨r,h⟩]
      rw [hz,tsum_zero]
    rw [hz,norm_zero]
    exact hC

lemma smoothCuspSeedDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (smoothCuspSeedDefect a b s) :=
  cuspCutoffCorrection_measurable 1 _ (cuspSeedDefectProfile_continuous a b s ha hab).measurable

lemma smoothCuspSeedDefect_bounded (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    ∃C : ℝ, 0≤C ∧ ∀w,‖smoothCuspSeedDefect a b s w‖≤C := by
  obtain ⟨C,hC⟩ := (cuspSeedDefectProfile_hasCompactSupport a b s hab).exists_bound_of_continuous
    (cuspSeedDefectProfile_continuous a b s ha hab)
  refine ⟨max C 0,le_max_right _ _,fun w => ?_⟩
  exact cuspCutoffCorrection_norm_le _ _ (le_max_right _ _) (fun v => (hC v).trans (le_max_left _ _)) w

lemma kernelQuotientDefect_measurable (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    Measurable (kernelQuotientDefect a b s) :=
  measurable_from_quotient.mpr (smoothCuspSeedDefect_measurable a b s ha hab)

theorem kernelQuotientDefect_memLp (a b : ℝ) (s : ℂ) (ha : 0<a) (hab : a<b) :
    MemLp (kernelQuotientDefect a b s) 2 (integralQuotientVolume globalKubotaKernel) := by
  obtain ⟨C,hC,hbound⟩ := smoothCuspSeedDefect_bounded a b s ha hab
  apply MemLp.of_bound (kernelQuotientDefect_measurable a b s ha hab).aestronglyMeasurable C
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w => exact hbound w

def kernelL2Defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  (kernelQuotientDefect_memLp a b s ha hab).toLp (kernelQuotientDefect a b s)

lemma kernelL2Defect_ae_eq (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    kernelL2Defect a b ha hab s =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelQuotientDefect a b s :=
  MemLp.coeFn_toLp _

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

lemma cuspCutoffCorrection_add (F G : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (F+G) w=cuspCutoffCorrection 1 F w+cuspCutoffCorrection 1 G w := by
  unfold cuspCutoffCorrection
  rw [←(cuspCutoffTerm_summable 1 le_rfl F w).tsum_add (cuspCutoffTerm_summable 1 le_rfl G w)]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.add_apply]
  split_ifs <;> simp [mul_add]

lemma cuspCutoffCorrection_smul (c : ℂ) (F : ℝ → ℂ) (w : HyperbolicSpace) :
    cuspCutoffCorrection 1 (c • F) w=c • cuspCutoffCorrection 1 F w := by
  unfold cuspCutoffCorrection
  rw [smul_eq_mul,←tsum_mul_left]
  apply tsum_congr
  intro r
  simp only [cuspCutoffTerm,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> ring

def compactHeightProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) : ℝ → ℂ :=
  (Set.Icc a b).indicator (fun v => F (Set.projIcc a b hab v))

lemma compactHeightProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (compactHeightProfile a b hab F) :=
  (F.continuous.comp continuous_projIcc).measurable.indicator measurableSet_Icc

lemma compactHeightProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) (v : ℝ) :
    ‖compactHeightProfile a b hab F v‖≤‖F‖ := by
  unfold compactHeightProfile
  by_cases hv : v∈Set.Icc a b
  · rw [Set.indicator_of_mem hv]
    exact F.norm_coe_le_norm _
  · rw [Set.indicator_of_notMem hv,norm_zero]
    exact norm_nonneg _

lemma compactHeightProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (F+G)=compactHeightProfile a b hab F+compactHeightProfile a b hab G := by
  funext v
  simp [compactHeightProfile,Set.indicator_add]

lemma compactHeightProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    compactHeightProfile a b hab (c • F)=c • compactHeightProfile a b hab F := by
  funext v
  by_cases hv : v∈Set.Icc a b <;> simp [compactHeightProfile,hv]

def kernelCompactProfile (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    IntegralOrbitQuotient globalKubotaKernel → ℂ :=
  Quotient.lift (cuspCutoffCorrection 1 (compactHeightProfile a b hab F)) (by
    rintro w u ⟨M,hM⟩
    rw [←hM]
    obtain ⟨hM,hchar⟩ := (globalKubotaKernel_mem (M:SL(2,ActualEisensteinCubic.O))).mp M.property
    have he := cuspCutoffCorrection_automorphy 1 le_rfl (compactHeightProfile a b hab F)
      (⟨(M:SL(2,ActualEisensteinCubic.O)),hM⟩ : CubicKubota.levelThree) w
    rw [hchar,one_mul] at he
    exact he.symm)

lemma kernelCompactProfile_measurable (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    Measurable (kernelCompactProfile a b hab F) :=
  measurable_from_quotient.mpr (cuspCutoffCorrection_measurable 1 _
    (compactHeightProfile_measurable a b hab F))

lemma kernelCompactProfile_norm_le (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ))
    (q : IntegralOrbitQuotient globalKubotaKernel) : ‖kernelCompactProfile a b hab F q‖≤‖F‖ := by
  induction q using Quotient.inductionOn with
  | _ w =>
    exact cuspCutoffCorrection_norm_le _ _ (norm_nonneg F)
      (compactHeightProfile_norm_le a b hab F) w

lemma kernelCompactProfile_memLp (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    MemLp (kernelCompactProfile a b hab F) 2 (integralQuotientVolume globalKubotaKernel) :=
  MemLp.of_bound (kernelCompactProfile_measurable a b hab F).aestronglyMeasurable ‖F‖
    (Filter.Eventually.of_forall (kernelCompactProfile_norm_le a b hab F))

lemma kernelCompactProfile_add (a b : ℝ) (hab : a≤b) (F G : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (F+G)=kernelCompactProfile a b hab F+kernelCompactProfile a b hab G := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_add,cuspCutoffCorrection_add]
    rfl

lemma kernelCompactProfile_smul (a b : ℝ) (hab : a≤b) (c : ℂ) (F : C(Set.Icc a b,ℂ)) :
    kernelCompactProfile a b hab (c • F)=c • kernelCompactProfile a b hab F := by
  funext q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 _ w=_
    rw [compactHeightProfile_smul,cuspCutoffCorrection_smul]
    rfl

def compactProfileL2Linear (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →ₗ[ℂ] KernelQuotientL2 where
  toFun F := (kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)
  map_add' F G := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_add,MemLp.coeFn_toLp,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_add]
  map_smul' c F := by
    apply Lp.ext
    grw [MemLp.coeFn_toLp,Lp.coeFn_smul,MemLp.coeFn_toLp]
    rw [kernelCompactProfile_smul]
    exact Filter.Eventually.of_forall (fun _ => rfl)

lemma compactProfileL2Linear_bound (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    ‖compactProfileL2Linear a b hab F‖≤
      (measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹)*‖F‖ := by
  apply Lp.norm_le_of_ae_bound (norm_nonneg F)
  filter_upwards [MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)] with q hq
  change ‖((kernelCompactProfile_memLp a b hab F).toLp (kernelCompactProfile a b hab F)) q‖≤‖F‖
  rw [hq]
  exact kernelCompactProfile_norm_le a b hab F q

def compactProfileL2 (a b : ℝ) (hab : a≤b) : C(Set.Icc a b,ℂ) →L[ℂ] KernelQuotientL2 :=
  (compactProfileL2Linear a b hab).mkContinuous
    ((measureUnivNNReal (integralQuotientVolume globalKubotaKernel) : ℝ)^((2:ℝ)⁻¹))
    (compactProfileL2Linear_bound a b hab)

lemma compactProfileL2_ae_eq (a b : ℝ) (hab : a≤b) (F : C(Set.Icc a b,ℂ)) :
    compactProfileL2 a b hab F =ᵐ[integralQuotientVolume globalKubotaKernel]
      kernelCompactProfile a b hab F :=
  MemLp.coeFn_toLp (kernelCompactProfile_memLp a b hab F)

def compactLogProfile (a b : ℝ) (ha : 0<a) : C(Set.Icc a b,ℂ) :=
  ⟨fun v => (Real.log (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    (continuous_subtype_val.log (fun v => (ha.trans_le v.2.1).ne'))⟩

def compactDefectSecond (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)^2*((deriv (deriv (cuspTransition a b)) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    have hdd := (contDiff_infty_iff_deriv.mp hd).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).pow 2 |>.mul
      (Complex.continuous_ofReal.comp (hdd.continuous.comp continuous_subtype_val))

def compactDefectFirst (a b : ℝ) : C(Set.Icc a b,ℂ) where
  toFun v := (v:ℂ)*((deriv (cuspTransition a b) (v:ℝ):ℝ):ℂ)
  continuous_toFun := by
    have hd := (contDiff_infty_iff_deriv.mp (cuspTransition_contDiff a b)).2
    exact (Complex.continuous_ofReal.comp continuous_subtype_val).mul
      (Complex.continuous_ofReal.comp (hd.continuous.comp continuous_subtype_val))

def compactDefectProfile (a b : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a b,ℂ) :=
  NormedSpace.exp (s • compactLogProfile a b ha)*
    (compactDefectSecond a b+(2*s-1) • compactDefectFirst a b)

lemma compactDefectProfile_apply (a b : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a b) :
    compactDefectProfile a b ha s v=cuspSeedDefectProfile a b s v := by
  have hexp := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a b ha)
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v*
    (compactDefectSecond a b v+(2*s-1)*compactDefectFirst a b v)=_
  change (NormedSpace.exp (s • compactLogProfile a b ha)) v=
    NormedSpace.exp ((s • compactLogProfile a b ha) v) at hexp
  rw [hexp,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,
    compactDefectSecond,compactDefectFirst,cuspSeedDefectProfile,positiveHeightPower,
    logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]
  ring

lemma compactDefectProfile_entire (a b : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactDefectProfile a b ha) := by
  have he := differentiable_exp_smul_const ℂ (compactLogProfile a b ha)
  exact he.mul ((differentiable_const _).add
    (((differentiable_const (2:ℂ)).mul differentiable_id |>.sub (differentiable_const 1)).smul
      (differentiable_const (compactDefectFirst a b))))

lemma compactHeightProfile_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactHeightProfile a b hab.le (compactDefectProfile a b ha s)=cuspSeedDefectProfile a b s := by
  funext v
  by_cases hv : v∈Set.Icc a b
  · rw [compactHeightProfile,Set.indicator_of_mem hv,Set.projIcc_of_mem hab.le hv,
      compactDefectProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem hv]
    have hout : v<a ∨ b<v := by simpa only [Set.mem_Icc,not_and_or,not_le] using hv
    exact (cuspSeedDefectProfile_zero a b s v hab hout).symm

lemma compactProfileL2_actual_defect (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    compactProfileL2 a b hab.le (compactDefectProfile a b ha s)=kernelL2Defect a b ha hab s := by
  apply Lp.ext
  grw [compactProfileL2_ae_eq,kernelL2Defect_ae_eq]
  apply Filter.Eventually.of_forall
  intro q
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a b hab.le (compactDefectProfile a b ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedDefectProfile a b s) w
    rw [compactHeightProfile_actual_defect a b ha hab s]

theorem kernelL2Defect_entire (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Differentiable ℂ (kernelL2Defect a b ha hab) := by
  have heq : kernelL2Defect a b ha hab=
      fun s => compactProfileL2 a b hab.le (compactDefectProfile a b ha s) :=
    funext (fun s => (compactProfileL2_actual_defect a b ha hab s).symm)
  rw [heq]
  exact (compactProfileL2 a b hab.le).differentiable.comp (compactDefectProfile_entire a b ha)

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassIntegration
open ActualEisensteinCubic JointLogSeparation FirstPassCubeLabels SecondPassArithmetic

theorem full_uniform_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W g₁ g₂ X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) A₁ A₂ W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro ι _ p hp _ hcop hg
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  apply secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs g₁ g₂ W hU₁ hU₂ windows
  · exact hwo _ _ _ _ _ hz hud hue huv hkap
  · exact fun a ha => hwt A₁ _ hA₁ hz 5 a ha
  · exact fun a ha => hwt A₂ _ hA₂ hz 6 a ha

theorem full_uniform_twisted_normalized_child_tests
    (g₁ g₂ W : 𝓢(ℝ, ℂ)) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hg₁ : ∀ s, g₁ s ≠ 0 → |s| ≤ A) (hg₂ : ∀ s, g₂ s ≠ 0 → |s| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ, ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ j, HasCompactSupport (windows j)) ∧
      (∀ j, ContDiff ℝ ∞ (windows j)) ∧
      (∀ j s, windows j s ≠ 0 → |s| ≤ A+B+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i}), ∀ (θ₁ θ₂ D E V₀ X X₀ K Y : ℝ), 0 < D → 0 < E → 0 < V₀ → 0 < X → 0 < X₀ → 0 < K →
      ∀ (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O),
        d ≠ 0 → e ≠ 0 → k ≠ 0 →
        |Real.log (primeProductNorm p V * X₀ / X)| ≤ B →
        |Real.log (elementNorm d / D)| ≤ B →
        |Real.log (elementNorm e / E)| ≤ B →
        |Real.log (primeProductNorm p V / V₀)| ≤ B →
        |Real.log (elementNorm (d*e*k) / K)| ≤ B →
        secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k (-k)
          (radialPairKernel p e k W (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) X X Y) =
        (X : ℂ)⁻¹ * postCommonSmoothPair p hp hcop hg F Ψ₁ Ψ₂ (m*r)
          (c*e*∏ i ∈ V, p i) (d*e*k) (d*e*(-k)) (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows
          (Real.log (primeProductNorm p V * X₀ / X)) (Real.log (elementNorm d / D))
          (Real.log (elementNorm e / E)) (Real.log (primeProductNorm p V / V₀))
          (Real.log (elementNorm (d*e*k) / K)) X₀ X₀ (Y*K/(D*E^2*V₀^2*X₀^2)) := by
  obtain ⟨U, hUc, hUs, hUone, hUsupp, hUzero⟩ :=
    FourierBridge.exists_complex_smooth_cutoff A hA
  have hU₁ : ∀ s, g₁ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₁ s hs)
  have hU₂ : ∀ s, g₂ s ≠ 0 → U s = 1 := fun s hs => hUone s (hg₂ s hs)
  let A₁ := conjugateProfile (halfNormalizationCLM U g₁)
  let A₂ := halfNormalizationCLM U g₂
  have hA₁ : ∀ s, A₁ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply halfNormalization_support_bound U hUc hUs g₁ A hg₁ s
    intro hz
    exact hs (by simp [A₁, hz])
  have hA₂ : ∀ s, A₂ s ≠ 0 → |s| ≤ A :=
    halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨windows, hwc, hws, hwb, hwo, hwt⟩ := exists_fixed_sector_windows A B hA hB
  refine ⟨A₁, A₂, windows, hwc, hws, hwb, ?_⟩
  intro ι _ p hp _ hcop hg
    θ₁ θ₂ D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK F V Ψ₁ Ψ₂ m r c d e k hd he hk hz hud hue huv hkap
  have htw₁ : ∀ s, frequencyTwist g₁ θ₁ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have htw₂ : ∀ s, frequencyTwist g₂ θ₂ s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₁ : ∀ s, frequencyTwist A₁ (-θ₁) s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₁ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hsupp₂ : ∀ s, frequencyTwist A₂ θ₂ s ≠ 0 → |s| ≤ A := by
    intro s hs
    apply hA₂ s
    intro hz
    exact hs (by simp [frequencyTwist_apply, hz])
  have hh := secondChildKernelPair_eq_postCommon p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k hd he hk
    D E V₀ X X₀ K Y hD hE hV₀ hX hX₀ hK U hUc hUs
    (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂ windows
  dsimp only at hh
  rw [normalized_conjugate_frequencyTwist U hUc hUs,
    halfNormalization_twist U hUc hUs] at hh
  exact hh (hwo _ _ _ _ _ hz hud hue huv hkap)
    (fun a ha => hwt (frequencyTwist A₁ (-θ₁)) _ hsupp₁ hz 5 a ha)
    (fun a ha => hwt (frequencyTwist A₂ θ₂) _ hsupp₂ hz 6 a ha)

end SecondPassIntegration

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM)
open SecondPassFiber (newRow)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLiteralTerm (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι) : ℂ :=
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    secondExpansionSource p hp hcop hg (globalSecondRawPool F x) Ψ m' c d ray {x.source}
      (fun A => normalizedColumn p (fun S => g₁ (columnLog p X S)) A)
      (fun A => normalizedColumn p (fun S => g₂ (columnLog p X S)) A) W Y

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] hp in
theorem globalResidualScale_eq (ell : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    secondExpansionScale p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor))
      (expansionSupportData x.common x.firstDivisor x.source) = globalActualResidualScale p ell side x := by
  simp only [secondExpansionScale,expansionSupportData,primeSubsetGenerator_norm_eq_productNorm,globalActualResidualScale]
  ring

end

theorem globalSecondLiteralTerm_fixed_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray g₁ g₂ W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            A₁ A₂ W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A 6 hA (by norm_num) h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray ell Y side x hell hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)
  have hr : Ideal.span {secondMaskQuotient p x.source.divisor x.source.sourceCommon hE}=Ideal.span {r} := by
    rw [secondMaskQuotient_span]
    exact (ConcretePrimeRowBridge.span_idealGenerator _).symm
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.source.sourceCommon x.source.divisor hE (globalSecondRawPool F x) x.source.overlap Ψ Ψ
    m' c d x.source.frequency r ray hr X Y hX U hUc hUs g₁ g₂ W hU₁ hU₂
  have hscale : X/(‖ConcreteTraceCRT.eisEmbedding e‖^2*‖ConcreteTraceCRT.eisEmbedding r‖^2)=
      globalActualResidualScale p ell side x := globalResidualScale_eq p ell side x
  dsimp only at hnorm
  rw [hscale] at hnorm
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hid' := hid p hp hcop hg (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7)
    (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) (globalLogRep j 8) Y
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalActualResidualScale_pos p hp ell hell side x) (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
    (globalSecondRawPool F x) x.source.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    m' r c d e x.source.frequency (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) hk
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  rw [hid'] at hnorm
  have hgoal := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    ((Y : ℂ)*secondSourceCommonCoefficient p hg Ψ m' c d x.source.sourceCommon x.source.divisor) * z) hnorm
  have hrow : newRow (globalSecondTuple p x) = d*e*x.source.frequency := rfl
  have hlabel : globalSecondLabel p x = c*e*∏ i ∈ x.source.overlap,p i := rfl
  have hmask : globalSecondRawMask p m x = m'*r := rfl
  have hz : globalBinZ p ell side j x =
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j /
        globalActualResidualScale p ell side x) := rfl
  have hud : globalBinUd p j x = Real.log (SecondPassIntegration.elementNorm d/globalLogRep j 5) := rfl
  have hue : globalBinUe p j x = Real.log (SecondPassIntegration.elementNorm e/globalLogRep j 6) := rfl
  have huv : globalBinUv p j x = Real.log (primeProductNorm p x.source.overlap/globalLogRep j 7) := rfl
  have hkap : globalBinKap p j x = Real.log (SecondPassIntegration.elementNorm (d*e*x.source.frequency)/globalLogRep j 8) := rfl
  change globalSecondLiteralTerm p hp hcop hg F Ψ m ray g₁ g₂ W ell Y side x = _
  rw [hrow,hlabel,hmask,hz,hud,hue,huv,hkap]
  have hq := secondExpansionQuotient_of_subset p x.source hE
  simp only [globalSecondLiteralTerm,secondExpansionSource,Finset.sum_singleton,hq,
    globalSecondOuterWeight,secondNormalizedExpansionWeight,
    globalResidualScale_eq p ell side x,globalBinRadial,m',c,d,e,r,X,j,mul_neg,mul_assoc] at hgoal ⊢
  exact hgoal

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)
open JointLogSeparation (halfNormalizationCLM frequencyTwist frequencyTwist_apply halfNormalization_twist)
open SecondPassFiber (newRow)

theorem globalSecondLiteralTerm_twisted_profiles
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g₁ g₂ W : 𝓢(ℝ,ℂ)) (A : ℝ) (hA : 0 ≤ A)
    (hU₁ : ∀ t,g₁ t ≠ 0 → U t=1) (hU₂ : ∀ t,g₂ t ≠ 0 → U t=1)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ A) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ A) :
    ∃ (A₁ A₂ : 𝓢(ℝ,ℂ)) (windows : Fin 7 → ℝ → ℂ),
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ A+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i,p i ≠ 0)
        [∀ i,(Ideal.span {p i}).IsMaximal]
        (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
        (hg : ∀ i,lambda ∉ Ideal.span {p i})
        (_hinj : Function.Injective (fun i => Ideal.span {p i}))
        (_hpr : ∀ i,lambda^2 ∣ p i-1)
        (F : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
        (θ₁ θ₂ ell Y : ℝ) (side : Bool) (x : GlobalSecondData ι),
        0 < ell → x.source.divisor ⊆ x.source.sourceCommon → x.source.frequency ≠ 0 →
        let j := globalScaleIndex p side x
        globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x =
          globalSecondOuterWeight p hp hcop hg Ψ m ray ell Y side x *
          postCommonSmoothPair p hp hcop hg (globalSecondRawPool F x)
            (secondRayMinus Ψ ray) (secondRayPlus Ψ ray) (globalSecondRawMask p m x)
            (globalSecondLabel p x) (newRow (globalSecondTuple p x)) (-newRow (globalSecondTuple p x))
            (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows (globalBinZ p ell side j x) (globalBinUd p j x)
            (globalBinUe p j x) (globalBinUv p j x) (globalBinKap p j x)
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (globalBinRadial ell Y j) := by
  have h1 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₁ A hg₁
  have h2 := SecondPassIntegration.halfNormalization_support_bound U hUc hUs g₂ A hg₂
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := SecondPassIntegration.full_uniform_twisted_normalized_child_tests
    (halfNormalizationCLM U g₁) (halfNormalizationCLM U g₂) W A 6 hA (by norm_num) h1 h2
  refine ⟨A₁,A₂,windows,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr F Ψ m ray θ₁ θ₂ ell Y side x hell hE hk
  dsimp only
  let j := globalScaleIndex p side x
  let X := globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon
  let r := primeSubsetGenerator (fun i => Ideal.span {p i}) (x.source.sourceCommon\x.source.divisor)
  let c := secondBaseLabel p x.cube.support x.common x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.source.divisor
  let m' := m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  have hX : 0 < X := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp _)
  have hr : Ideal.span {secondMaskQuotient p x.source.divisor x.source.sourceCommon hE}=Ideal.span {r} := by
    rw [secondMaskQuotient_span]
    exact (ConcretePrimeRowBridge.span_idealGenerator _).symm
  have htw₁ : ∀ t, frequencyTwist g₁ θ₁ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₁ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have htw₂ : ∀ t, frequencyTwist g₂ θ₂ t ≠ 0 → U t = 1 := by
    intro t ht
    apply hU₂ t
    intro hz
    exact ht (by simp [frequencyTwist_apply,hz])
  have hnorm := weighted_secondRayChild_normalized p hp hcop hg hinj hpr
    x.source.sourceCommon x.source.divisor hE (globalSecondRawPool F x) x.source.overlap Ψ Ψ
    m' c d x.source.frequency r ray hr X Y hX U hUc hUs (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W htw₁ htw₂
  have hscale : X/(‖ConcreteTraceCRT.eisEmbedding e‖^2*‖ConcreteTraceCRT.eisEmbedding r‖^2)=
      globalActualResidualScale p ell side x := globalResidualScale_eq p ell side x
  dsimp only at hnorm
  rw [hscale,halfNormalization_twist U hUc hUs,halfNormalization_twist U hUc hUs] at hnorm
  have hcoords := globalPooled_log_coordinates p hp ell hell side x hk
  have hid' := hid p hp hcop hg θ₁ θ₂ (globalLogRep j 5) (globalLogRep j 6) (globalLogRep j 7)
    (globalActualResidualScale p ell side x) (globalPooledColumnScale ell j) (globalLogRep j 8) Y
    (globalLogRep_pos j 5) (globalLogRep_pos j 6) (globalLogRep_pos j 7)
    (globalActualResidualScale_pos p hp ell hell side x) (globalPooledColumnScale_pos ell hell j) (globalLogRep_pos j 8)
    (globalSecondRawPool F x) x.source.overlap (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
    m' r c d e x.source.frequency (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _) hk
    hcoords.1 hcoords.2.1 hcoords.2.2.1 hcoords.2.2.2.1 hcoords.2.2.2.2
  rw [hid'] at hnorm
  have hgoal := congrArg (fun z : ℂ => (primeProductNorm p x.firstCommon : ℂ)⁻¹ *
    ((Y : ℂ)*secondSourceCommonCoefficient p hg Ψ m' c d x.source.sourceCommon x.source.divisor) * z) hnorm
  have hrow : newRow (globalSecondTuple p x) = d*e*x.source.frequency := rfl
  have hlabel : globalSecondLabel p x = c*e*∏ i ∈ x.source.overlap,p i := rfl
  have hmask : globalSecondRawMask p m x = m'*r := rfl
  have hz : globalBinZ p ell side j x =
      Real.log (primeProductNorm p x.source.overlap*globalPooledColumnScale ell j /
        globalActualResidualScale p ell side x) := rfl
  have hud : globalBinUd p j x = Real.log (SecondPassIntegration.elementNorm d/globalLogRep j 5) := rfl
  have hue : globalBinUe p j x = Real.log (SecondPassIntegration.elementNorm e/globalLogRep j 6) := rfl
  have huv : globalBinUv p j x = Real.log (primeProductNorm p x.source.overlap/globalLogRep j 7) := rfl
  have hkap : globalBinKap p j x = Real.log (SecondPassIntegration.elementNorm (d*e*x.source.frequency)/globalLogRep j 8) := rfl
  change globalSecondLiteralTerm p hp hcop hg F Ψ m ray (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell Y side x = _
  rw [hrow,hlabel,hmask,hz,hud,hue,huv,hkap]
  have hq := secondExpansionQuotient_of_subset p x.source hE
  simp only [globalSecondLiteralTerm,secondExpansionSource,Finset.sum_singleton,hq,
    globalSecondOuterWeight,secondNormalizedExpansionWeight,
    globalResidualScale_eq p ell side x,globalBinRadial,m',c,d,e,r,X,j,mul_neg,mul_assoc] at hgoal ⊢
  exact hgoal

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0184

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.LiteralSources
Source SHA256: 4888ef5a4c4276d7c5930e802c627829cc5ea1159310e09a6acb2bc4d7c399fc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0185


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

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SecondPassArithmetic
open ActualEisensteinCubic
open JointLogSeparation (frequencyTwist)
open SecondPassIntegration (densityChildEnergy)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalSecondLiteralBinSource (γ : GlobalSecondData ι → ℂ)
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (g₁ g₂ W : 𝓢(ℝ,ℂ)) (ell Y : ℝ) : ℂ :=
  ∑ ray : SecondRayIndex,∑ x∈globalLogSector p s side j,
    γ x * globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g₁ g₂ W ell Y side x

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem sum_globalArithmeticBin {M : Type*} [AddCommMonoid M]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
    (f : GlobalSecondData ι → M) :
    ∑ x∈globalLogSector p s side j,f x =
    ∑ q∈globalBinTriples p s side j,∑ x∈globalArithmeticBin p s side q j,f x := by
  have h := sum_globalSecondFixedTriple p (globalLogSector p s side j) f
  simpa only [globalBinTriples,globalLogSector,globalArithmeticBin,Finset.filter_filter,and_comm] using h
end

theorem globalSecondLiteralBinSource_transfer
    (ε : ℝ) (hε : 0 < ε) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (M : ℝ) (hM : 0 ≤ M)
    (hg₁ : ∀ t,g₁ t ≠ 0 → |t| ≤ M) (hg₂ : ∀ t,g₂ t ≠ 0 → |t| ≤ M)
    (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0 ≤ C ∧
      (∀ i,HasCompactSupport (windows i)) ∧
      (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t| ≤ M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (θ₁ θ₂ K ell B F : ℝ) (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex)
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (γ : GlobalSecondData ι → ℂ) (Γ : ℝ),
      0 < K → 0 < ell → 0 < B → 0 < F → 0 ≤ Γ → (∀ x∈s,‖γ x‖ ≤ Γ) → (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ x∈s,GlobalSecondAdmissible x) → (∀ x∈s,x.source.frequency ≠ 0) →
      globalBinFirstCoefficient K ell B F j *
      ‖globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
        (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j)‖ ≤
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        globalDescentWeight (Γ*C) ε θ₁ θ₂ K ell B F A J j ray q *
        (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
          (fixedTripleMask m q) (globalArithmeticTargets p s side q j) (windows 5) (windows 6)
          (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
          (globalPooledColumnScale ell j*globalPooledLabelScale j)) := by
  obtain ⟨U,hUc,hUs,hUone,hUsupp,hUzero⟩ := FourierBridge.exists_complex_smooth_cutoff M hM
  obtain ⟨A₁,A₂,windows,hwc,hws,hwb,hid⟩ := globalSecondLiteralTerm_twisted_profiles U hUc hUs
    g₁ g₂ W M hM (fun t ht => hUone t (hg₁ t ht)) (fun t ht => hUone t (hg₂ t ht)) hg₁ hg₂
  obtain ⟨C,hC,htrans⟩ := weightedGlobalPositiveBin_transfer ε hε A₁ A₂ W windows
    (fun _ => M+6+1) (fun _ => by linarith) hwb hwc (fun i => (hws i).continuous) A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr θ₁ θ₂ K ell B F s side j pool Ψ m γ Γ hK hell hB hF hΓ hγ hΨ hs hk
  have heq : globalSecondLiteralBinSource p hp hcop hg γ s side j pool Ψ m
      (frequencyTwist g₁ θ₁) (frequencyTwist g₂ θ₂) W ell (globalPooledRowScale K ell B F j) =
      ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p s side j,
        weightedGlobalArithmeticBinSource p hp hcop hg γ s side q j pool Ψ m ray
          (frequencyTwist A₁ (-θ₁)) (frequencyTwist A₂ θ₂) W windows ell (globalPooledRowScale K ell B F j) := by
    unfold globalSecondLiteralBinSource
    apply Finset.sum_congr rfl
    intro ray hray
    rw [sum_globalArithmeticBin p s side j]
    apply Finset.sum_congr rfl
    intro q hq
    unfold weightedGlobalArithmeticBinSource globalSecondRawSource
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨hxs,hxq,hxj⟩ := Finset.mem_filter.mp hx
    have h := hid p hp hcop hg hinj hpr pool Ψ m ray θ₁ θ₂ ell
      (globalPooledRowScale K ell B F j) side x hell (hs x hxs).2.1 (hk x hxs)
    dsimp only at h
    rw [hxj] at h
    rw [h,mul_assoc]
  rw [heq]
  simpa only [globalDescentWeight,norm_neg] using
    htrans p hp hcop hg hinj hc (-θ₁) θ₂ K ell B F s side j pool Ψ m γ Γ
      hK hell hB hF hΓ hγ hΨ hs hk

end SecondPassArithmetic

namespace CubicEisenstein
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise

local notation "O" => ActualEisensteinCubic.O

lemma complex_norm_mul_add_sq (a b c d : ℂ) :
    ‖a*c+b*d‖^2≤(‖a‖^2+‖b‖^2)*(‖c‖^2+‖d‖^2) := by
  have ht : ‖a*c+b*d‖≤‖a‖*‖c‖+‖b‖*‖d‖ := by simpa only [norm_mul] using norm_add_le (a*c) (b*d)
  have hs := pow_le_pow_left₀ (norm_nonneg (a*c+b*d)) ht 2
  nlinarith only [hs,sq_nonneg (‖a‖*‖d‖-‖b‖*‖c‖)]

lemma matrixFrobenius_nonneg (g : SL(2,ℂ)) : 0≤matrixFrobenius g := by
  unfold matrixFrobenius rowEnergy
  positivity

lemma matrixFrobenius_mul_le (g h : SL(2,ℂ)) :
    matrixFrobenius (g*h)≤matrixFrobenius g*matrixFrobenius h := by
  have hb (i j : Fin 2) := complex_norm_mul_add_sq (g i 0) (g i 1) (h 0 j) (h 1 j)
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow,Matrix.SpecialLinearGroup.coe_mul,
    Matrix.mul_apply,Fin.sum_univ_two]
  nlinarith only [hb 0 0,hb 0 1,hb 1 0,hb 1 1]

lemma matrixFrobenius_inv (g : SL(2,ℂ)) : matrixFrobenius g⁻¹=matrixFrobenius g := by
  rw [Matrix.SpecialLinearGroup.SL2_inv_expl]
  simp only [matrixFrobenius,rowEnergy,complexMatrixRow]
  change ‖g 1 1‖^2+‖-g 0 1‖^2+(‖-g 1 0‖^2+‖g 0 0‖^2)=_
  simp only [norm_neg]
  ring

lemma hyperbolicFrobenius_nonneg (w : HyperbolicSpace) : 0≤hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ g => exact matrixFrobenius_nonneg g

lemma matrixFrobenius_le_displacement (g : SL(2,ℂ)) (w : HyperbolicSpace) :
    matrixFrobenius g≤hyperbolicFrobenius (g • w)*hyperbolicFrobenius w := by
  induction w using Quotient.inductionOn with
  | _ h =>
    change matrixFrobenius g≤matrixFrobenius (g*h)*matrixFrobenius h
    have hb := matrixFrobenius_mul_le (g*h) h⁻¹
    simpa only [mul_inv_cancel_right,matrixFrobenius_inv] using hb

instance integralSubgroupContinuousAction (H : Subgroup (SL(2,O))) :
    ContinuousConstSMul H HyperbolicSpace :=
  ⟨fun M => continuous_hyperbolic_action (integralComplexMatrix (M:SL(2,O)))⟩

instance integralSubgroupProperlyDiscontinuous (H : Subgroup (SL(2,O))) :
    ProperlyDiscontinuousSMul H HyperbolicSpace where
  finite_disjoint_inter_image := by
    intro source target hsource htarget
    obtain ⟨C,hC⟩ := hsource.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    obtain ⟨D,hD⟩ := htarget.exists_bound_of_continuousOn hyperbolicFrobenius_continuous.continuousOn
    have hfin : Set.Finite {M : H | matrixFrobenius (integralComplexMatrix (M:SL(2,O)))≤
        max D 0*max C 0} := by
      have hf := Set.Finite.preimage (f := fun M : H => (M:SL(2,O))) Subtype.val_injective.injOn
        (integral_frobenius_sublevel_finite 1 (max D 0*max C 0))
      simpa only [mul_one,Set.preimage_ofPred_eq] using hf
    apply hfin.subset
    rintro M ⟨u,⟨w,hw,rfl⟩,hu⟩
    have hb := matrixFrobenius_le_displacement (integralComplexMatrix (M:SL(2,O))) w
    apply hb.trans
    apply mul_le_mul
    · exact ((le_abs_self _).trans (hD _ hu)).trans (le_max_left _ _)
    · exact ((le_abs_self _).trans (hC _ hw)).trans (le_max_left _ _)
    · exact hyperbolicFrobenius_nonneg _
    · exact le_max_right _ _

end CubicEisenstein

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise

namespace CubicEisenstein

section
local notation "O" => ActualEisensteinCubic.O

instance upperCoordinatesLocallyCompact : LocallyCompactSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).locallyCompactSpace
instance hyperbolicLocallyCompact : LocallyCompactSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
instance hyperbolicSecondCountable : SecondCountableTopology HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.secondCountableTopology

instance upperCoordinatesPolish : PolishSpace UpperCoordinates :=
  (isOpen_lt continuous_const continuous_snd : IsOpen {p : ℂ×ℝ | 0<p.2}).polishSpace
instance hyperbolicPolish : PolishSpace HyperbolicSpace :=
  upperCoordinatesHomeomorph.symm.isClosedEmbedding.polishSpace

lemma integralOrbitRel_eq (H : Subgroup (SL(2,O))) :
    integralOrbitRel H=MulAction.orbitRel H HyperbolicSpace := by
  ext u v
  change (∃M:H,M • u=v) ↔ ∃M:H,M • v=u
  constructor
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩
  · rintro ⟨M,hM⟩
    exact ⟨M⁻¹,by rw [←hM,inv_smul_smul]⟩

instance integralOrbitQuotientT2 (H : Subgroup (SL(2,O))) : T2Space (IntegralOrbitQuotient H) := by
  change T2Space (Quotient (integralOrbitRel H))
  rw [integralOrbitRel_eq]
  infer_instance

lemma integralSubgroupFree (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCancelSMul H HyperbolicSpace :=
  isCancelSMul_iff_eq_one_of_smul_eq.mpr (subgroup_action_free H hH)

lemma integralOrbitProjection_eq_iff (H : Subgroup (SL(2,O))) (u v : HyperbolicSpace) :
    integralOrbitProjection H u=integralOrbitProjection H v ↔ u∈MulAction.orbit H v := by
  constructor
  · intro he
    obtain ⟨M,hM⟩ := Quotient.exact he.symm
    exact ⟨M,hM⟩
  · rintro ⟨M,hM⟩
    apply Eq.symm
    apply Quotient.sound
    exact ⟨M,hM⟩

theorem integralOrbitProjection_quotientCovering (H : Subgroup (SL(2,O)))
    (hH : H≤CubicKubota.levelThree) : IsQuotientCoveringMap (integralOrbitProjection H) H := by
  let : IsCancelSMul H HyperbolicSpace := integralSubgroupFree H hH
  have hq : Topology.IsQuotientMap (integralOrbitProjection H) := isQuotientMap_quotient_mk'
  exact hq.isQuotientCoveringMap_of_properlyDiscontinuousSMul (integralOrbitProjection_eq_iff H _ _)

lemma integralOrbitProjection_covering (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsCoveringMap (integralOrbitProjection H) :=
  (integralOrbitProjection_quotientCovering H hH).isCoveringMap

lemma integralOrbitProjection_openQuotient (H : Subgroup (SL(2,O))) (hH : H≤CubicKubota.levelThree) :
    IsOpenQuotientMap (integralOrbitProjection H) :=
  ⟨Quotient.mk_surjective,continuous_integralOrbitProjection H,
    (integralOrbitProjection_covering H hH).isOpenMap⟩

instance kernelQuotientLocallyCompact : LocallyCompactSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree).locallyCompactSpace
instance kernelQuotientSecondCountable : SecondCountableTopology (IntegralOrbitQuotient globalKubotaKernel) :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    (integralOrbitProjection_openQuotient globalKubotaKernel globalKubotaKernel_le_levelThree)

instance kernelQuotientBorel : BorelSpace (IntegralOrbitQuotient globalKubotaKernel) :=
  Quotient.borelSpace

lemma kernelQuotient_localHomeomorph : IsLocalHomeomorph (integralOrbitProjection globalKubotaKernel) :=
  (integralOrbitProjection_covering globalKubotaKernel globalKubotaKernel_le_levelThree).isLocalHomeomorph

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

lemma integralOrbitProjection_preimage_image (H : Subgroup (SL(2,ActualEisensteinCubic.O)))
    (S : Set HyperbolicSpace) :
    integralOrbitProjection H ⁻¹' (integralOrbitProjection H '' S)=⋃M:H,M • S := by
  ext w
  constructor
  · rintro ⟨u,hu,he⟩
    obtain ⟨M,hM⟩ := (integralOrbitProjection_eq_iff H w u).mp he.symm
    exact Set.mem_iUnion.mpr ⟨M,⟨u,hu,hM⟩⟩
  · intro hw
    obtain ⟨M,u,hu,rfl⟩ := Set.mem_iUnion.mp hw
    exact ⟨u,hu,(integralOrbitProjection_eq H M u).symm⟩

lemma kernelProjection_translates_disjoint (S : Set HyperbolicSpace)
    (hS : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    Pairwise (fun M N : globalKubotaKernel => Disjoint (M • S) (N • S)) := by
  let : IsCancelSMul globalKubotaKernel HyperbolicSpace :=
    integralSubgroupFree globalKubotaKernel globalKubotaKernel_le_levelThree
  intro M N hMN
  apply Set.disjoint_left.mpr
  rintro _ ⟨w,hw,rfl⟩ ⟨u,hu,he⟩
  have hwu : w=u := hS hw hu (by
    calc
      integralOrbitProjection globalKubotaKernel w=
          integralOrbitProjection globalKubotaKernel (M • w) := (integralOrbitProjection_eq _ M w).symm
      _=integralOrbitProjection globalKubotaKernel (N • u) := congrArg _ he.symm
      _=integralOrbitProjection globalKubotaKernel u := integralOrbitProjection_eq _ N u)
  subst u
  exact hMN (IsCancelSMul.right_cancel M N w he.symm)

theorem kernelProjection_measure_image (S : Set HyperbolicSpace) (hS : MeasurableSet S)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) S) :
    integralQuotientVolume globalKubotaKernel (integralOrbitProjection globalKubotaKernel '' S)=
      hyperbolicVolume S := by
  have himg := hS.image_of_continuousOn_injOn
    (continuous_integralOrbitProjection globalKubotaKernel).continuousOn hinj
  rw [integralQuotientVolume,Measure.map_apply (measurable_integralOrbitProjection _) himg,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) himg),
    integralOrbitProjection_preimage_image,Set.iUnion_inter]
  rw [measure_iUnion]
  · exact (globalKubotaKernel_isFundamentalDomain.measure_eq_tsum S).symm
  · intro M N hMN
    exact (kernelProjection_translates_disjoint S hinj hMN).mono Set.inter_subset_left Set.inter_subset_left
  · intro M
    exact (hS.const_smul M).inter (hyperbolicFundamentalSet_measurable _)

theorem kernelProjection_measurePreserving_on (U : Set HyperbolicSpace) (hU : MeasurableSet U)
    (hinj : Set.InjOn (integralOrbitProjection globalKubotaKernel) U) :
    MeasurePreserving (integralOrbitProjection globalKubotaKernel)
      (hyperbolicVolume.restrict U)
      ((integralQuotientVolume globalKubotaKernel).restrict (integralOrbitProjection globalKubotaKernel '' U)) := by
  refine ⟨measurable_integralOrbitProjection _,?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB),Measure.restrict_apply hB]
  have hset : B∩(integralOrbitProjection globalKubotaKernel '' U)=
      integralOrbitProjection globalKubotaKernel '' (integralOrbitProjection globalKubotaKernel ⁻¹' B∩U) := by
    ext q
    constructor
    · rintro ⟨hq,w,hw,rfl⟩
      exact ⟨w,⟨hq,hw⟩,rfl⟩
    · rintro ⟨w,⟨hw,hu⟩,rfl⟩
      exact ⟨hw,⟨w,hu,rfl⟩⟩
  rw [hset,kernelProjection_measure_image _ (((measurable_integralOrbitProjection _) hB).inter hU)
    (hinj.mono Set.inter_subset_right)]

theorem kernelL2_continuous_compact_approx (f : KernelQuotientL2) (ε : ℝ≥0∞) (hε : ε≠0) :
    ∃g : IntegralOrbitQuotient globalKubotaKernel → ℂ,
      HasCompactSupport g ∧ eLpNorm ((f : _ → ℂ)-g) 2 (integralQuotientVolume globalKubotaKernel)≤ε ∧
      Continuous g ∧ MemLp g 2 (integralQuotientVolume globalKubotaKernel) := by
  exact (Lp.memLp f).exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) hε

end CubicEisenstein

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label)

@[ext] structure GlobalFirstData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι

namespace GlobalFirstData
variable {ι : Type*}
def append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : GlobalSecondData ι :=
  ⟨b.cube,b.firstCommon,b.common,b.firstDivisor,x⟩
end GlobalFirstData

namespace GlobalSecondData
variable {ι : Type*}
def first (x : GlobalSecondData ι) : GlobalFirstData ι :=
  ⟨x.cube,x.firstCommon,x.common,x.firstDivisor⟩
@[simp] theorem append_first (x : GlobalSecondData ι) : x.first.append x.source=x := by cases x; rfl
@[simp] theorem first_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).first=b := rfl
@[simp] theorem source_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).source=x := rfl
end GlobalSecondData

section
variable {ι : Type*} [DecidableEq ι]

def globalFirstRawPool (pool : Finset ι) (b : GlobalFirstData ι) : Finset ι :=
  (pool\(b.cube.support∪b.common))\b.firstCommon

def globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : Finset (GlobalSecondData ι) :=
  s.biUnion (fun b => (secondExpansionPool (globalFirstRawPool pool b) (cutoff b)).image b.append)

theorem mem_globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (x : GlobalSecondData ι) :
    x∈globalFirstExpansionPool pool s cutoff ↔
      x.first∈s ∧ x.source∈secondExpansionPool (globalFirstRawPool pool x.first) (cutoff x.first) := by
  simp only [globalFirstExpansionPool,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,z,hz,rfl⟩
    exact ⟨hb,hz⟩
  · rintro ⟨hb,hx⟩
    exact ⟨x.first,hb,x.source,hx,x.append_first⟩

theorem sum_globalFirstExpansionPool {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (f : GlobalSecondData ι → M) :
    ∑ x∈globalFirstExpansionPool pool s cutoff,f x =
    ∑ b∈s,∑ x∈secondExpansionPool (globalFirstRawPool pool b) (cutoff b),f (b.append x) := by
  unfold globalFirstExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro x hx y hy heq
    exact congrArg GlobalSecondData.source heq
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalSecondData.first heq).symm

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstBlockColumnScale (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  ell/(primeProductNorm p (b.cube.sideDivisor side)*primeProductNorm p b.common)

def globalFirstBlockLabel (b : GlobalFirstData ι) : O :=
  secondBaseLabel p b.cube.support b.common b.cube.leftExponent b.cube.rightExponent b.cube.leftBit b.cube.rightBit

def globalFirstBlockBadLabel (b : GlobalFirstData ι) : O :=
  b0Label p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit

def globalFirstBlockTest (g : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : Finset ι → ℂ :=
  normalizedColumn p (fun A => g (columnLog p
    (globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon) A))

def globalFirstTruncatedSource
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondSource p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

theorem globalFirstTruncatedSource_eq_literal
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstExpansionPool pool s cutoff,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  unfold globalFirstTruncatedSource
  simp_rw [truncatedSecondSource_eq_expansionPool p hp hcop hg hinj hc hpr]
  rw [Finset.sum_comm]
  simp_rw [sum_globalFirstExpansionPool]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold secondExpansionSource
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [globalSecondLiteralTerm,GlobalFirstData.append,GlobalSecondData.first,
    globalSecondRawPool,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    globalFirstBlockTest,globalFirstBlockColumnScale,globalFirstColumnScale,
    secondExpansionSource,Finset.sum_singleton,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstCoreRow (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayCharacter)
    (r : FirstCoreIndex) (t : ℝ) (b : GlobalFirstData ι) (z : O) : ℂ :=
  firstCoreInputRow p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t z

def globalFirstCoreCorrection (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) : ℝ :=
  ‖firstCoreTest (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b)) side t b.firstCommon ∅‖^2

def globalFirstSourceTail (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    secondSourceTail p hp hg hinj (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

def globalFirstSourceZero
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℂ :=
  ∑ b∈s,w b*(primeProductNorm p b.firstCommon : ℂ)⁻¹*
    truncatedSecondZero p hg (globalFirstRawPool pool b) Ψ
      (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
      (globalFirstBlockTest p g ell side b) W (Y b) (cutoff b)

theorem globalFirstTruncatedSource_split
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      globalFirstTruncatedSource p hp hg hinj pool s w (fun b G E => (cutoff b G E).erase 0) Ψ m g W ell side Y +
      globalFirstSourceZero p hg pool s w cutoff Ψ m g W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceZero
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  rw [truncatedSecondSource_eq_nonzero_add_zero]
  exact mul_add _ _ _

theorem globalFirstCoreRows_smoothed
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b) :
    (∑ b∈s,w b*∑' z : O,W (‖eisEmbedding z‖^2/Y b)*
      (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)) =
      globalFirstTruncatedSource p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y +
      globalFirstSourceTail p hp hg hinj pool s w cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) W ell side Y := by
  unfold globalFirstTruncatedSource globalFirstSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  have hX : 0 < globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have he := firstCoreInputRow_smoothed_truncated p hp hg hinj hc
    (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m g V W (globalFirstBlockColumnScale p ell side b) hX (Y b) (hY b hb)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (cutoff b)
  dsimp only at he
  have he' := congrArg (fun z : ℂ => w b*z) he
  simpa only [globalFirstCoreRow,globalFirstRawPool,globalFirstBlockBadLabel,globalFirstBlockLabel,
    secondBaseLabel,globalFirstBlockTest,mul_add,mul_assoc,Complex.ofReal_inv] using he'

theorem globalFirstCoreRows_finite_le_sources
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (hw : ∀ b∈s,0 ≤ w b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (hell : 0 < ell) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (hY : ∀ b∈s,0 < Y b)
    (T : GlobalFirstData ι → Finset O)
    (hT : ∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y b)
    (hT0 : ∀ b∈s,∀ z∈T b,z ≠ 0) :
    (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      ‖globalFirstTruncatedSource p hp hg hinj pool s (fun b => w b)
        (fun b G E => (cutoff b G E).erase 0) (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceZero p hg pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => w b) cutoff (firstCoreTwist side χ Ψ r) m
        (firstCoreModeProfile g V side t) rowMajorant ell side Y‖ := by
  have henergy : (∑ b∈s,w b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
      globalFirstCoreCorrection p g V ell side t b)) ≤
      (∑ b∈s,(w b : ℂ)*∑' z : O,rowMajorant (‖eisEmbedding z‖^2/Y b)*
        (‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2 : ℝ)).re := by
    rw [Complex.re_sum]
    apply Finset.sum_le_sum
    intro b hb
    have hh := firstCoreInputRow_finite_le_corrected_source p hg
      (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
      side χ Ψ m (normalizedColumn p (fun A => g (columnLog p (globalFirstBlockColumnScale p ell side b) A)))
      V (columnLog p (globalFirstBlockColumnScale p ell side b))
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r t (T b) (Y b) (hY b hb) (hT b hb) (hT0 b hb)
    have hh' := mul_le_mul_of_nonneg_left (le_sub_iff_add_le.mp hh) (hw b hb)
    simpa only [globalFirstCoreRow,globalFirstCoreCorrection,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero] using hh'
  rw [globalFirstCoreRows_smoothed p hp hg hinj hc pool s (fun b => w b) cutoff Ψ m g V rowMajorant ell hell side χ r t Y hY,
    globalFirstTruncatedSource_split] at henergy
  exact henergy.trans ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans
    (add_le_add (norm_add_le _ _) le_rfl)))

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0185

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.PooledRows
Source SHA256: 23d203cb634c40ccf0ee52be065d76b368cfaafc9c4493f45d6ff1eded361ce7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0186


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

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]

def GlobalFirstAdmissible (b : GlobalFirstData ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor ⊆ b.common∪b.cube.support

variable (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstIndex (side : Bool) (b : GlobalFirstData ι) : GlobalLogIndex :=
  globalScaleIndex p side (b.append ⟨∅,∅,∅,1⟩)

def globalFirstPooledRow (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalPooledRowScale K ell B F (globalFirstIndex p side b)

def globalFirstCoefficient (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalBinFirstCoefficient K ell B F (globalFirstIndex p side b)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalPooledRowScale_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalPooledRowScale K ell B F (globalScaleIndex p side x)=
      globalFirstPooledRow p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=1 ∨ i=4 ∨ i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl|rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstPooledRow globalPooledRowScale
  rw [hc 1 (by simp),hc 4 (by simp),hc 5 (by simp)]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalBinFirstCoefficient_first (K ell B F : ℝ) (side : Bool) (x : GlobalSecondData ι) :
    globalBinFirstCoefficient K ell B F (globalScaleIndex p side x)=
      globalFirstCoefficient p K ell B F side x.first := by
  have hc (i : Fin 10) (hi : i=5 ∨ i=9) :
      globalLogRep (globalScaleIndex p side x) i=globalLogRep (globalFirstIndex p side x.first) i := by
    rcases hi with rfl|rfl <;>
      simp [globalLogRep,globalFirstIndex,globalScaleIndex,globalScaleVector,GlobalFirstData.append,GlobalSecondData.first,globalCubeJNorm,globalCubeActiveRoot]
  unfold globalFirstCoefficient globalBinFirstCoefficient
  rw [hc 5 (by simp),hc 9 (by simp)]

def globalFirstConcreteCutoff (K ell B F M H : ℝ) (side : Bool) (b : GlobalFirstData ι) :
    Finset ι → Finset ι → Finset O :=
  firstCoreSecondCutoff p b.firstCommon (globalFirstBlockColumnScale p ell side b)
    (globalFirstPooledRow p K ell B F side b) M H

def globalFirstSupportedPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) : Finset (GlobalSecondData ι) :=
  (globalFirstExpansionPool pool s cutoff).filter (fun x =>
    SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstSupportedPool_admissible (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s cutoff ell M side) : GlobalSecondAdmissible x := by
  have hm := (mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1
  have hb := hs x.first hm.1
  have hE := ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.1
  exact ⟨hb.1,hE,hb.2.1,hb.2.2⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstSupportedPool_frequency_ne_zero (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (ell M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side) :
    x.source.frequency ≠ 0 := by
  have hm := (mem_globalFirstExpansionPool pool s _ x).mp (Finset.mem_filter.mp hx).1
  exact (Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2).1

include hp in

theorem globalFirstSupportedPool_index_mem_box
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (x : GlobalSecondData ι)
    (hx : x∈globalFirstSupportedPool p pool s
      (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side) :
    globalScaleIndex p side x ∈ globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) := by
  have hm := (mem_globalFirstExpansionPool pool s _ x).mp (Finset.mem_filter.mp hx).1
  have hk := (Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2)
  apply globalScaleIndex_mem_uniform_box p hp K ell B F M H hK hell hB hF hH side x
    (globalFirstSupportedPool_admissible p pool s hs _ ell M side x hx)
    (Finset.mem_filter.mp hx).2 (hb₁ x.first hm.1) (hb₂ x.first hm.1) hk.1
  simpa only [globalFirstConcreteCutoff,globalPooledRowScale_first,globalFirstBlockColumnScale,
    globalFirstColumnScale,GlobalSecondData.first] using hk.2

end
section

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm primeProduct)
open ConcreteTraceCRT (eisEmbedding)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalSecondLiteralTerm_zero_of_not_support
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (ray : SecondRayIndex)
    (g W : 𝓢(ℝ,ℂ)) (ell Y M : ℝ) (side : Bool) (x : GlobalSecondData ι)
    (hell : 0<ell) (hgM : ∀ t,g t ≠ 0 → |t|≤M) (hE : x.source.divisor⊆x.source.sourceCommon)
    (hs : ¬SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source) :
    globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell Y side x=0 := by
  have hX := div_pos (globalFirstColumnScale_pos p hp ell hell x side)
    (FirstPassCubeLabels.primeProductNorm_pos p hp x.firstCommon)
  have hz := secondExpansionSource_singleton_zero_of_not_support p hp hcop hg hinj
    (globalSecondRawPool pool x) Ψ (m*globalFirstBlockBadLabel p x.first)
    (globalFirstBlockLabel p x.first) (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    ray g W (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) Y M hX hgM x.source hE hs
  unfold globalSecondLiteralTerm
  dsimp only
  simp only [globalFirstBlockBadLabel,globalFirstBlockLabel,GlobalSecondData.first] at hz
  rw [hz,mul_zero]

theorem globalFirstTruncatedSource_eq_supported
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ)) (ell M : ℝ) (hell : 0<ell)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    globalFirstTruncatedSource p hp hg hinj pool s w cutoff Ψ m g W ell side Y =
      ∑ ray : SecondRayIndex,∑ x∈globalFirstSupportedPool p pool s cutoff ell M side,
        w x.first*globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell (Y x.first) side x := by
  rw [globalFirstTruncatedSource_eq_literal p hp hcop hg hinj hc hpr]
  apply Finset.sum_congr rfl
  intro ray hray
  unfold globalFirstSupportedPool
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hs : SecondSourceSupport p (globalFirstColumnScale p ell x side/primeProductNorm p x.firstCommon) M x.source
  · rw [ite_eq_left hs]
  · rw [ite_eq_right hs,globalSecondLiteralTerm_zero_of_not_support p hp hcop hg hinj pool Ψ m ray g W ell (Y x.first) M side x hell hgM]
    · ring
    · exact ((mem_secondExpansionPool _ _ _).mp ((mem_globalFirstExpansionPool pool s cutoff x).mp hx).2).2.1
    · exact hs

theorem globalFirstTruncatedSource_eq_bins
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i,lambda^2 ∣ p i-1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (hs : ∀ b∈s,GlobalFirstAdmissible b)
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (K ell B F M H : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool)
    (hb₁ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    globalFirstTruncatedSource p hp hg hinj pool s
      (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m g W ell side
      (globalFirstPooledRow p K ell B F side) =
      ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinFirstCoefficient K ell B F j : ℂ)*
          globalSecondLiteralBinSource p hp hcop hg (fun x => w x.first) source side j pool Ψ m
            g g W ell (globalPooledRowScale K ell B F j) := by
  dsimp only
  rw [globalFirstTruncatedSource_eq_supported p hp hcop hg hinj hc hpr]
  · let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
    let source := globalFirstSupportedPool p pool s cutoff ell M side
    have hmap : ∀ x∈source,globalScaleIndex p side x∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H) :=
      fun x hx => globalFirstSupportedPool_index_mem_box p hp pool s hs K ell B F M H hK hell hB hF hH side hb₁ hb₂ x hx
    change (∑ ray : SecondRayIndex,∑ x∈source,
      (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x) = _
    simp only [globalSecondLiteralBinSource,Finset.mul_sum]
    conv_rhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro ray hray
    have hsplit := Finset.sum_fiberwise_of_maps_to hmap
      (fun x => (w x.first*globalFirstCoefficient p K ell B F side x.first)*
        globalSecondLiteralTerm p hp hcop hg pool Ψ m ray g g W ell
          (globalFirstPooledRow p K ell B F side x.first) side x)
    rw [← hsplit]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro x hx
    have hxj := (Finset.mem_filter.mp hx).2
    have hy := globalPooledRowScale_first p K ell B F side x
    have hc' := globalBinFirstCoefficient_first p K ell B F side x
    rw [hxj] at hy hc'
    rw [← hy,← hc']
    ring
  · exact hell
  · exact hgM

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy)
open JointLogSeparation (frequencyTwist)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalChildBudget (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε θ₁ θ₂ K ell B F M H : ℝ) (A J : ℕ) (side : Bool) : ℝ :=
  ∑ j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
    ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p source side j,
      globalDescentWeight C ε θ₁ θ₂ K ell B F A J j ray q *
      (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
        (fixedTripleMask m q) (globalArithmeticTargets p source side q j) (windows 5) (windows 6)
        (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) J /
        (globalPooledColumnScale ell j*globalPooledLabelScale j))

end

theorem globalFirstTruncatedSource_actual_transfer
    (ε : ℝ) (hε : 0<ε) (g W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0≤C ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℂ) (Γ θ K ell B F H : ℝ) (side : Bool)
      (Ψ : O →* ℂ) (m : O),
      0≤Γ → (∀ b∈s,‖w b‖≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
      let source := globalFirstSupportedPool p pool s cutoff ell M side
      ‖globalFirstTruncatedSource p hp hg hinj pool s
        (fun b => w b*globalFirstCoefficient p K ell B F side b) cutoff Ψ m
        (frequencyTwist g θ) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
      globalChildBudget p hp hcop hg pool source Ψ m windows (Γ*C) ε θ θ K ell B F M H A J side := by
  obtain ⟨windows,C,hC,hwc,hws,hwb,htrans⟩ := globalSecondLiteralBinSource_transfer ε hε g g W M hM hgM hgM A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ θ K ell B F H side Ψ m hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂
  dsimp only
  let cutoff := fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0
  let source := globalFirstSupportedPool p pool s cutoff ell M side
  have htw : ∀ t,frequencyTwist g θ t ≠ 0 → |t|≤M := by
    intro t ht
    apply hgM t
    intro hz
    exact ht (by simp [JointLogSeparation.frequencyTwist_apply,hz])
  rw [globalFirstTruncatedSource_eq_bins p hp hcop hg hinj hc hpr pool s hs w Ψ m
    (frequencyTwist g θ) W K ell B F M H hK hell hB hF hH htw side hb₁ hb₂]
  apply (norm_sum_le _ _).trans
  unfold globalChildBudget
  apply Finset.sum_le_sum
  intro j hj
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF j)]
  apply htrans p hp hcop hg hinj hc hpr θ θ K ell B F source side j pool Ψ m
    (fun x => w x.first) Γ hK hell hB hF hΓ
  · intro x hx
    exact hw x.first ((mem_globalFirstExpansionPool pool s cutoff x).mp (Finset.mem_filter.mp hx).1).1
  · exact hΨ
  · exact fun x hx => globalFirstSupportedPool_admissible p pool s hs cutoff ell M side x hx
  · exact fun x hx => globalFirstSupportedPool_frequency_ne_zero p pool s
      (globalFirstConcreteCutoff p K ell B F M H side) ell M side x hx

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstCoreRows_actual_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C : ℝ),0≤C ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex) (t : ℝ)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let cutoff := globalFirstConcreteCutoff p K ell B F M H side
      let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      let profile := firstCoreModeProfile g V side t
      (∑ b∈s,weight b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
        globalFirstCoreCorrection p g V ell side t b)) ≤
      globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side +
      ‖globalFirstSourceZero p hg pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ +
      ‖globalFirstSourceTail p hp hg hinj pool s (fun b => weight b) cutoff Ψmode m profile rowMajorant ell side
        (globalFirstPooledRow p K ell B F side)‖ := by
  have hbase : ∀ x,firstCoreBaseProfile g V side x≠0 → |x|≤M := by
    intro x hx
    apply hgM x
    intro hz
    exact hx (by rw [firstCoreBaseProfile_apply,hz,zero_mul])
  obtain ⟨windows,C,hC,hwc,hws,hwb,htrans⟩ := globalFirstTruncatedSource_actual_transfer
    ε hε (firstCoreBaseProfile g V side) rowMajorant M hM hbase A J
  refine ⟨windows,C,hC,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H Ψ m χ r t T hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
  dsimp only
  let cutoff := globalFirstConcreteCutoff p K ell B F M H side
  let source := globalFirstSupportedPool p pool s (fun b G E => (cutoff b G E).erase 0) ell M side
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  have hweight : ∀ b∈s,0≤weight b := by
    intro b hb
    exact mul_nonneg (hw b hb).1 (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hY : ∀ b∈s,0<globalFirstPooledRow p K ell B F side b := by
    intro b hb
    exact globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hsource := htrans p hp hcop hg hinj hc hpr pool s (fun b => (w b : ℂ)) Γ
    (firstCoreModeHeight side t) K ell B F H side Ψmode m hΓ
    (fun b hb => by rw [Complex.norm_real,Real.norm_of_nonneg (hw b hb).1]; exact (hw b hb).2)
    hK hell hB hF hH hs (fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)) hb₁ hb₂
  have hfinite := globalFirstCoreRows_finite_le_sources p hp hg hinj hc pool s weight hweight cutoff Ψ m g V ell hell
    side χ r t (globalFirstPooledRow p K ell B F side) hY T hT hT0
  have hheight : ‖firstCoreModeHeight side t‖=‖t‖ := by cases side <;> simp [firstCoreModeHeight]
  have hbudget : globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε
      (firstCoreModeHeight side t) (firstCoreModeHeight side t) K ell B F M H A J side =
      globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side := by
    simp only [globalChildBudget,globalDescentWeight,hheight]
  dsimp only at hsource
  change _ ≤ globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε
    (firstCoreModeHeight side t) (firstCoreModeHeight side t) K ell B F M H A J side at hsource
  rw [hbudget] at hsource
  apply hfinite.trans
  apply add_le_add
  · apply add_le_add
    · simpa only [weight,firstCoreModeProfile,Complex.ofReal_mul] using hsource
    · exact le_rfl
  · exact le_rfl

end SecondPassArithmetic

open scoped BigOperators Classical
namespace InitialMeanSquare

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum
abbrev O := ActualEisensteinCubic.O

structure Datum where
  divisor : Ideal O
  shared : Ideal O
  frequency : O
  deriving DecidableEq

def newRow (x : Datum) : O := idealGenerator x.divisor*x.frequency
def newLabel (x : Datum) : Ideal O := x.divisor*x.shared
def oldCommon (b : Ideal O) (x : Datum) : Ideal O := b*x.divisor
def observation (x : Datum) : O × Ideal O := (newRow x,newLabel x)

theorem span_newRow (x : Datum) :
    Ideal.span {newRow x}=x.divisor*Ideal.span {x.frequency} := by
  rw [newRow,←Ideal.span_singleton_mul_span_singleton,span_idealGenerator]

theorem divisor_dvd_row (x : Datum) : x.divisor∣Ideal.span {newRow x} := by
  rw [span_newRow]
  exact dvd_mul_right _ _

theorem divisor_dvd_label (x : Datum) : x.divisor∣newLabel x := dvd_mul_right _ _

theorem divisor_ne_zero_of_row (x : Datum) (hx : newRow x≠0) : x.divisor≠0 := by
  intro hd
  have hs : Ideal.span {newRow x}=(0 : Ideal O) := by rw [span_newRow,hd,zero_mul]
  exact hx (Ideal.span_singleton_eq_bot.mp hs)

theorem divisor_injective_on_fiber (y : O) (f : Ideal O) (hy : y≠0) :
    Set.InjOn Datum.divisor {x : Datum | observation x=(y,f)} := by
  intro x hx z hz hd
  have hxrow : newRow x=y := congrArg Prod.fst hx
  have hzrow : newRow z=y := congrArg Prod.fst hz
  have hxlabel : newLabel x=f := congrArg Prod.snd hx
  have hzlabel : newLabel z=f := congrArg Prod.snd hz
  have hdx := divisor_ne_zero_of_row x (by rwa [hxrow])
  have hshared : x.shared=z.shared := by
    apply mul_left_cancel₀ hdx
    calc
      x.divisor*x.shared = f := hxlabel
      _ = z.divisor*z.shared := hzlabel.symm
      _ = x.divisor*z.shared := by rw [hd]
  have hfreq : x.frequency=z.frequency := by
    apply mul_left_cancel₀ (idealGenerator_ne_zero x.divisor hdx)
    calc
      idealGenerator x.divisor*x.frequency = y := hxrow
      _ = idealGenerator z.divisor*z.frequency := hzrow.symm
      _ = idealGenerator x.divisor*z.frequency := by rw [hd]
  cases x
  cases z
  simp_all

theorem fiber_card_le (s : Finset Datum) (y : O) (f : Ideal O) (hy : y≠0) :
    (s.filter (fun x => observation x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn Datum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : newRow x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he]
    exact divisor_dvd_row x
  · intro x hx z hz he
    exact divisor_injective_on_fiber y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he

theorem fiber_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (y : O) (f : Ideal O), y≠0 →
      ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
        C*(Ideal.absNorm (Ideal.span {y}):ℝ)^ε := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s y f hy
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by
    intro hz
    exact hy (Ideal.span_singleton_eq_bot.mp hz)
  exact (show ((s.filter (fun x => observation x=(y,f))).card:ℝ)≤
    (idealDivisors (Ideal.span {y})).card by exact_mod_cast fiber_card_le s y f hy).trans (hdiv _ hyI)

theorem weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (s : Finset Datum) (t : Finset (O×Ideal O))
      (w : Datum→ℂ) (P : O×Ideal O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,observation x∈t) →
      (∀y∈t,y.1≠0) → (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (observation x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hfiber⟩ := fiber_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro s t w P A K hA hK hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t observation w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hc := (hfiber s y.1 y.2 (ht y hy)).trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le)
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hc hA) (sq_nonneg ‖P y‖)
  simpa only [Prod.eta,mul_assoc] using hh

theorem norm_newRow (x : Datum) :
    Ideal.absNorm (Ideal.span {newRow x})=Ideal.absNorm x.divisor*Ideal.absNorm (Ideal.span {x.frequency}) := by
  rw [span_newRow,map_mul]

theorem norm_newLabel (x : Datum) :
    Ideal.absNorm (newLabel x)=Ideal.absNorm x.divisor*Ideal.absNorm x.shared := by
  rw [newLabel,map_mul]

theorem norm_oldCommon (b : Ideal O) (x : Datum) :
    Ideal.absNorm (oldCommon b x)=Ideal.absNorm b*Ideal.absNorm x.divisor := by
  rw [oldCommon,map_mul]

end

theorem label_and_mask (b : Ideal O) (x : Datum)
    (hC : Squarefree (oldCommon b x)) (hs : Squarefree x.shared)
    (hcop : IsCoprime (oldCommon b x) x.shared) :
    Squarefree (newLabel x) ∧ IsCoprime b (newLabel x) := by
  have hC' : Squarefree (b*x.divisor) := hC
  have hcop' : IsCoprime (b*x.divisor) x.shared := hcop
  have hds : IsCoprime x.divisor x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_left _ _)
  have hbs : IsCoprime b x.shared :=
    hcop'.of_isCoprime_of_dvd_left (dvd_mul_right _ _)
  have hbd : IsCoprime b x.divisor := by
    apply Ideal.isCoprime_iff_gcd.mpr
    have hh := (IsRelPrime.of_squarefree_mul hC')
      (GCDMonoid.gcd_dvd_left b x.divisor) (GCDMonoid.gcd_dvd_right b x.divisor)
    simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp hh
  exact ⟨squarefree_mul_iff.mpr ⟨hds.isRelPrime,hC'.of_mul_right,hs⟩,hbd.mul_right hbs⟩

def columnScale (Z B F : ℝ) : ℝ := Z/(B*F)
def rowScale (Z H B : ℝ) : ℝ := Z^2/(H*B^2)

theorem initial_prefactor (Z H b d : ℝ) (hd : d≠0) :
    H*(b*d)/(Z^2*d)=H*b/Z^2 := by field_simp

theorem initial_column_scale (Z b d s : ℝ) :
    Z/((b*d)*s)=columnScale Z b (d*s) := by unfold columnScale; ring

theorem initial_row_bound (Z H b d h : ℝ) (hH : 0<H) (hb : 0<b) (hd : 0<d)
    (hh : h≤Z^2*d/(H*(b*d)^2)) : d*h≤rowScale Z H b := by
  have h := mul_le_mul_of_nonneg_left hh hd.le
  have he : d*(Z^2*d/(H*(b*d)^2))=rowScale Z H b := by
    unfold rowScale
    field_simp

  exact h.trans_eq he

theorem initial_mass (Z B F : ℝ) (hF : F≠0) : columnScale Z B F*F=Z/B := by
  unfold columnScale
  field_simp

theorem initial_invariant_identity (Z H B F R : ℝ)
    (hZ : Z≠0) (hB : B≠0) (hF : F≠0) :
    rowScale Z H B*R/(columnScale Z B F*F)=(Z/H)*(R/B) := by
  unfold rowScale columnScale
