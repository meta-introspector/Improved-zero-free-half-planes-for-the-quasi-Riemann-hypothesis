import Lean.Elab.Tactic.Omega
-- import Mathlib.Algebra.BigOperators.Field
-- import Mathlib.Algebra.BigOperators.Fin
-- import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
-- import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
-- import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
-- import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
-- import Mathlib.Algebra.BigOperators.Ring.Finset
-- import Mathlib.Algebra.Group.AddChar
-- import Mathlib.Algebra.Group.Commute.Units
-- import Mathlib.Algebra.Group.Pi.Units
-- import Mathlib.Algebra.GroupWithZero.Units.Fintype
-- import Mathlib.Algebra.Module.ZLattice.Summable
-- import Mathlib.Algebra.Order.Archimedean.Basic
-- import Mathlib.Algebra.Order.BigOperators.Group.Finset
-- import Mathlib.Algebra.Order.BigOperators.Ring.Finset
-- import Mathlib.Algebra.Order.Floor.Semiring
-- import Mathlib.Algebra.Ring.NonZeroDivisors
-- import Mathlib.Algebra.Squarefree.Basic
-- import Mathlib.Analysis.Analytic.Constructions
-- import Mathlib.Analysis.Analytic.Uniqueness
-- import Mathlib.Analysis.Asymptotics.Arith
-- import Mathlib.Analysis.Asymptotics.Ring
-- import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
-- import Mathlib.Analysis.CStarAlgebra.Matrix
-- import Mathlib.Analysis.CStarAlgebra.Spectrum
-- import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
-- import Mathlib.Analysis.Calculus.ContDiff.Bounds
-- import Mathlib.Analysis.Calculus.ContDiff.Defs
-- import Mathlib.Analysis.Calculus.ContDiff.Deriv
-- import Mathlib.Analysis.Calculus.ContDiff.Operations
-- import Mathlib.Analysis.Calculus.Deriv.Mul
-- import Mathlib.Analysis.Calculus.Deriv.Shift
-- import Mathlib.Analysis.Calculus.Deriv.Star
-- import Mathlib.Analysis.Calculus.FDeriv.Measurable
-- import Mathlib.Analysis.Calculus.FDeriv.Mul
-- import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
-- import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
-- import Mathlib.Analysis.Calculus.ParametricIntegral
-- import Mathlib.Analysis.Calculus.SmoothSeries
-- import Mathlib.Analysis.Complex.Basic
-- import Mathlib.Analysis.Complex.BorelCaratheodory
-- import Mathlib.Analysis.Complex.BranchLogRoot
-- import Mathlib.Analysis.Complex.CauchyIntegral
-- import Mathlib.Analysis.Complex.Convex
-- import Mathlib.Analysis.Complex.ExponentialBounds
-- import Mathlib.Analysis.Complex.Hadamard
-- import Mathlib.Analysis.Complex.HalfPlane
-- import Mathlib.Analysis.Complex.Liouville
-- import Mathlib.Analysis.Complex.LocallyUniformLimit
-- import Mathlib.Analysis.Complex.Norm
-- import Mathlib.Analysis.Complex.Polynomial.Basic
-- import Mathlib.Analysis.Convolution
-- import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
-- import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
-- import Mathlib.Analysis.Distribution.TemperedDistribution
-- import Mathlib.Analysis.Fourier.AddCircleMulti
-- import Mathlib.Analysis.Fourier.Inversion
-- import Mathlib.Analysis.Fourier.PoissonSummation
-- import Mathlib.Analysis.Fourier.RiemannLebesgueLemma
-- import Mathlib.Analysis.InnerProductSpace.Adjoint
-- import Mathlib.Analysis.InnerProductSpace.Calculus
-- import Mathlib.Analysis.InnerProductSpace.Dual
-- import Mathlib.Analysis.InnerProductSpace.LinearPMap
-- import Mathlib.Analysis.InnerProductSpace.ProdL2
-- import Mathlib.Analysis.InnerProductSpace.Projection.Basic
-- import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
-- import Mathlib.Analysis.MellinInversion
-- import Mathlib.Analysis.MellinTransform
-- import Mathlib.Analysis.Meromorphic.Basic
-- import Mathlib.Analysis.Normed.Group.Tannery
-- import Mathlib.Analysis.Normed.Lp.SmoothApprox
-- import Mathlib.Analysis.Normed.Module.Connected
-- import Mathlib.Analysis.Normed.Module.FiniteDimension
-- import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn
-- import Mathlib.Analysis.Normed.Module.RCLike.Basic
-- import Mathlib.Analysis.Normed.Operator.Compact.Basic
-- import Mathlib.Analysis.Normed.Operator.Compact.FiniteDimension
-- import Mathlib.Analysis.Normed.Operator.Extend
-- import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
-- import Mathlib.Analysis.Normed.Ring.Finite
-- import Mathlib.Analysis.Normed.Ring.InfiniteSum
-- import Mathlib.Analysis.Real.Pi.Bounds
-- import Mathlib.Analysis.Real.Sqrt
-- import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
-- import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
-- import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
-- import Mathlib.Analysis.SpecialFunctions.Exp
-- import Mathlib.Analysis.SpecialFunctions.ExpDeriv
-- import Mathlib.Analysis.SpecialFunctions.Exponential
-- import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
-- import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
-- import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
-- import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
-- import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
-- import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
-- import Mathlib.Analysis.SpecialFunctions.Log.Summable
-- import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
-- import Mathlib.Analysis.SpecialFunctions.Pow.Complex
-- import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- import Mathlib.Analysis.SpecialFunctions.SmoothTransition
-- import Mathlib.Analysis.SpecialFunctions.Sqrt
-- import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
-- import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
-- import Mathlib.Analysis.SpecificLimits.Basic
-- import Mathlib.Analysis.SpecificLimits.Normed
-- import Mathlib.Analysis.SumIntegralComparisons
-- import Mathlib.Basic.NNReal.Basic
-- import Mathlib.Basic.Real.Basic
-- import Mathlib.Data.Finset.Image
-- import Mathlib.Data.Finset.Max
-- import Mathlib.Data.Finset.Powerset
-- import Mathlib.Data.Finsupp.Multiset
-- import Mathlib.Data.Fintype.EquivFin
-- import Mathlib.Data.Int.Order.Lemmas
-- import Mathlib.Data.Multiset.Interval
-- import Mathlib.Data.ZMod.Basic
-- import Mathlib.FieldTheory.Finite.Basic
-- import Mathlib.Geometry.Euclidean.Inversion.Calculus
-- import Mathlib.Geometry.Manifold.ContMDiff.Atlas
-- import Mathlib.Geometry.Manifold.ContMDiff.Basic
-- import Mathlib.Geometry.Manifold.PartitionOfUnity
-- import Mathlib.Geometry.Manifold.SmoothApprox
-- import Mathlib.GroupTheory.GroupAction.Quotient
-- import Mathlib.GroupTheory.Index
-- import Mathlib.LinearAlgebra.Matrix.FixedDetMatrices
-- import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
-- import Mathlib.LinearAlgebra.Matrix.ToLin
-- import Mathlib.LinearAlgebra.UnitaryGroup
-- import Mathlib.MeasureTheory.Constructions.HaarToSphere
-- import Mathlib.MeasureTheory.Function.ContinuousMapDense
-- import Mathlib.MeasureTheory.Function.Jacobian
-- import Mathlib.MeasureTheory.Function.L2Space
-- import Mathlib.MeasureTheory.Function.LocallyIntegrable
-- import Mathlib.MeasureTheory.Function.LpSpace.Basic
-- import Mathlib.MeasureTheory.Function.LpSpace.Complete
-- import Mathlib.MeasureTheory.Function.LpSpace.Indicator
-- import Mathlib.MeasureTheory.Group.FundamentalDomain
-- import Mathlib.MeasureTheory.Integral.Bochner.Basic
-- import Mathlib.MeasureTheory.Integral.DominatedConvergence
-- import Mathlib.MeasureTheory.Integral.Gamma
-- import Mathlib.MeasureTheory.Integral.IntegralEqImproper
-- import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
-- import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
-- import Mathlib.MeasureTheory.Integral.Prod
-- import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
-- import Mathlib.MeasureTheory.Measure.Haar.OfBasis
-- import Mathlib.MeasureTheory.Measure.Haar.Unique
-- import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
-- import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
-- import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
-- import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
-- import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
-- import Mathlib.MeasureTheory.Measure.Real
-- import Mathlib.MeasureTheory.Measure.WithDensity
-- import Mathlib.MeasureTheory.SpecificCodomains.Pi
-- import Mathlib.NumberTheory.ArithmeticFunction.Moebius
-- import Mathlib.NumberTheory.Chebyshev
-- import Mathlib.NumberTheory.Cyclotomic.Gal
-- import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
-- import Mathlib.NumberTheory.DirichletCharacter.Bounds
-- import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
-- import Mathlib.NumberTheory.GaussSum
-- import Mathlib.NumberTheory.JacobiSum.Basic
-- import Mathlib.NumberTheory.LSeries.Convolution
-- import Mathlib.NumberTheory.LSeries.Dirichlet
-- import Mathlib.NumberTheory.LSeries.DirichletContinuation
-- import Mathlib.NumberTheory.LSeries.Nonvanishing
-- import Mathlib.NumberTheory.LegendreSymbol.Complex
-- import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
-- import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.GaussSum
-- import Mathlib.NumberTheory.MulChar.Basic
-- import Mathlib.NumberTheory.MulChar.Duality
-- import Mathlib.NumberTheory.MulChar.Lemmas
-- import Mathlib.NumberTheory.NumberField.Basic
-- import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
-- import Mathlib.NumberTheory.NumberField.Cyclotomic.PID
-- import Mathlib.NumberTheory.NumberField.Cyclotomic.Three
-- import Mathlib.NumberTheory.NumberField.DedekindZeta
-- import Mathlib.NumberTheory.NumberField.Ideal.Asymptotics
-- import Mathlib.NumberTheory.NumberField.Norm
-- import Mathlib.Order.Filter.AtTopBot.Field
-- import Mathlib.Order.PiLex
-- import Mathlib.Order.Preorder.Finite
-- import Mathlib.Probability.Moments.Variance
-- import Mathlib.RingTheory.Coprime.Basic
-- import Mathlib.RingTheory.Ideal.IsPrincipal
-- import Mathlib.RingTheory.Ideal.Maps
-- import Mathlib.RingTheory.Ideal.Norm.AbsNorm
-- import Mathlib.RingTheory.Ideal.Quotient.Defs
-- import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
-- import Mathlib.RingTheory.Ideal.Quotient.Operations
-- import Mathlib.RingTheory.Ideal.Quotient.PowTransition
-- import Mathlib.RingTheory.Ideal.Span
-- import Mathlib.RingTheory.Multiplicity
-- import Mathlib.RingTheory.PowerBasis
-- import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
-- import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
-- import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
-- import Mathlib.RingTheory.UniqueFactorizationDomain.Multiplicity
-- import Mathlib.Tactic.ByContra
-- import Mathlib.Tactic.FieldSimp
-- import Mathlib.Tactic.FinCases
-- import Mathlib.Tactic.FunProp
-- import Mathlib.Tactic.Group
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Tactic.LinearCombination
-- import Mathlib.Tactic.NormNum
-- import Mathlib.Tactic.Positivity
-- import Mathlib.Tactic.Ring
-- import Mathlib.Tactic.Tauto
-- import Mathlib.Topology.Algebra.Module.LinearPMap
-- import Mathlib.Topology.Compactness.Lindelof
-- import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
-- import Mathlib.Topology.ContinuousMap.Bounded.Normed
-- import Mathlib.Topology.Covering.Quotient
-- import Mathlib.Topology.Instances.Matrix
-- import Mathlib.Topology.Maps.Proper.Basic
-- import Mathlib.Topology.MetricSpace.HausdorffDistance
-- import Mathlib.Topology.Order.ProjIcc
-- import PrimeNumberTheoremAnd.Wiener

/-! Pinned OAI dependency closure, consolidated without changing public namespaces.
Original module boundaries and hashes are preserved below. -/

/-! Original module: OAI.NumberTheory.DirichletL.Arithmetic.EisensteinCoordinates
Source SHA256: e3699b0164e7d25f292cfa429ee3ec9c0ab0cf4444cffc705ca57493ff006b13
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0001





















































































































































































namespace OAI










open scoped BigOperators

namespace ShortDraft

theorem eisenstein_ring_pid :
    IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  exact IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)

abbrev EisensteinCoordinates := ℤ × ℤ

def eisensteinMul (x y : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def eisensteinConj (x : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 - x.2, -x.2)

def eisensteinNorm (x : EisensteinCoordinates) : ℤ :=
  x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem eisenstein_norm_mul (x y : EisensteinCoordinates) :
    eisensteinNorm (eisensteinMul x y) = eisensteinNorm x * eisensteinNorm y := by
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  dsimp [eisensteinNorm, eisensteinMul]
  ring

theorem eisenstein_norm_conj (x : EisensteinCoordinates) :
    eisensteinNorm (eisensteinConj x) = eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm, eisensteinConj]
  ring

theorem eisenstein_mul_conj (x : EisensteinCoordinates) :
    eisensteinMul x (eisensteinConj x) = (eisensteinNorm x, 0) := by
  rcases x with ⟨a, b⟩
  apply Prod.ext <;> dsimp [eisensteinNorm, eisensteinConj, eisensteinMul] <;> ring

theorem eisenstein_norm_nonneg (x : EisensteinCoordinates) :
    0 ≤ eisensteinNorm x := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]

theorem eisenstein_norm_eq_zero_iff (x : EisensteinCoordinates) :
    eisensteinNorm x = 0 ↔ x = (0, 0) := by
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  constructor
  · intro h
    have hb : b = 0 := by
      nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
    have ha : a = 0 := by
      subst b
      nlinarith [sq_nonneg a]
    simp [ha, hb]
  · intro h
    simp_all

def DirichletTarget : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    (23 / 24 : ℝ) < s.re → ¬ (χ = 1 ∧ s = 1) →
      DirichletCharacter.LFunction χ s ≠ 0

theorem dirichlet_target_of_one_le_re
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 ≤ s.re) (hprincipal : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by
  exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hprincipal) hs

theorem dirichletTarget_iff_open_strip :
    DirichletTarget ↔
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        (23 / 24 : ℝ) < s.re → s.re < 1 →
          DirichletCharacter.LFunction χ s ≠ 0 := by
  constructor
  · intro h q _ χ s h23 _
    apply h q χ s h23
    intro ⟨_, hs⟩
    simp [hs] at *
  · intro h q _ χ s h23 hprincipal
    by_cases hs : s.re < 1
    · exact h q χ s h23 hs
    · exact dirichlet_target_of_one_le_re q χ s (le_of_not_gt hs) hprincipal

theorem cube_index_filter (b : ℕ) :
    (∑ h ∈ b.divisors, (ArithmeticFunction.moebius h : ℤ)) =
      if b = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℤ => f b)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [ArithmeticFunction.one_apply] at h
  simpa using h

private lemma square_le_two_squares {x y e : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (h : x ≤ y + e) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * e ^ 2 := by
  have h₁ : 0 ≤ y + e - x := sub_nonneg.mpr h
  have h₂ : 0 ≤ y + e + x := by nlinarith
  have h₃ := mul_nonneg h₁ h₂
  have h₄ := sq_nonneg (y - e)
  nlinarith

theorem finite_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (a : α → ℝ) (a₀ error bound : ℝ)
    (ha₀ : 0 ≤ a₀) (ha : ∀ u, 0 ≤ a u) (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, a₀ ≤ a (row p) + error)
    (hmean : (∑ u ∈ rows, (a u) ^ 2) ≤ bound) :
    (primes.card : ℝ) * a₀ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by
  have hselected : (∑ p ∈ primes, (a (row p)) ^ 2) ≤ bound := by
    calc
      (∑ p ∈ primes, (a (row p)) ^ 2) =
          ∑ u ∈ primes.image row, (a u) ^ 2 := by
            rw [Finset.sum_image hinj]
      _ ≤ ∑ u ∈ rows, (a u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hrows (by
          intro u _ _
          positivity)
      _ ≤ bound := hmean
  have hpoint (p : β) (hp : p ∈ primes) :
      a₀ ^ 2 ≤ 2 * (a (row p)) ^ 2 + 2 * error ^ 2 :=
    square_le_two_squares ha₀ (ha _) herror (happrox p hp)
  have hsum :
      (∑ p ∈ primes, a₀ ^ 2) ≤
        ∑ p ∈ primes, (2 * (a (row p)) ^ 2 + 2 * error ^ 2) :=
    Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith

theorem complex_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (error bound : ℝ)
    (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, ‖A untwisted - A (row p)‖ ≤ error)
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ bound) :
    (primes.card : ℝ) * ‖A untwisted‖ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by
  apply finite_row_extraction rows primes row (fun u ↦ ‖A u‖)
    ‖A untwisted‖ error bound (norm_nonneg _) (fun u ↦ norm_nonneg _) herror
    hrows hinj ?_ hmean
  intro p hp
  calc
    ‖A untwisted‖ = ‖(A untwisted - A (row p)) + A (row p)‖ := by
      rw [sub_add_cancel]
    _ ≤ ‖A untwisted - A (row p)‖ + ‖A (row p)‖ := norm_add_le _ _
    _ ≤ ‖A (row p)‖ + error := by linarith [happrox p hp]

theorem mean_square_exponent : (21 / 10 : ℚ) - 11 / 60 = 23 / 12 := by
  norm_num

theorem approximation_exponent : (2 : ℚ) - 11 / 30 = 49 / 30 := by
  norm_num

theorem zero_free_of_analytic_identity
    (σ : ℝ) (hσ : σ < 1) (L M W : ℂ → ℂ)
    (hL : AnalyticOnNhd ℂ L {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (heq : ∀ s : ℂ, 1 < s.re → L s * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hzeroIn : (2 : ℂ) ∈ {s : ℂ | σ < s.re} := by
    change σ < (2 : ℂ).re
    simpa using lt_trans hσ (show (1 : ℝ) < 2 by norm_num)
  have heventual : (fun s : ℂ => L s * M s) =ᶠ[nhds (2 : ℂ)] W := by
    filter_upwards [((Complex.isOpen_re_gt 1).mem_nhds (by norm_num : (2 : ℂ) ∈
        {s : ℂ | 1 < s.re}))] with s hs
    exact heq s hs
  have hident : Set.EqOn (fun s : ℂ => L s * M s) W {s | σ < s.re} :=
    (hL.mul hM).eqOn_of_preconnected_of_eventuallyEq hW
      ((convex_halfSpace_re_gt σ).isPreconnected) hzeroIn heventual
  intro hLρ
  have hρeq := hident hρ
  change L ρ * M ρ = W ρ at hρeq
  rw [hLρ, zero_mul] at hρeq
  exact hWρ hρeq.symm

theorem zero_free_of_regularized_analytic_identity
    (σ : ℝ) (hσ : σ < 1) (L Lregular M W : ℂ → ℂ)
    (hLregular : AnalyticOnNhd ℂ Lregular {s | σ < s.re})
    (hM : AnalyticOnNhd ℂ M {s | σ < s.re})
    (hW : AnalyticOnNhd ℂ W {s | σ < s.re})
    (hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      Lregular s = (s - 1) * L s)
    (heq : ∀ s : ℂ, 1 < s.re →
      Lregular s * M s = (s - 1) * W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by
  have hWregular :
      AnalyticOnNhd ℂ (fun s : ℂ => (s - 1) * W s) {s | σ < s.re} :=
    (analyticOnNhd_id.sub analyticOnNhd_const).mul hW
  have hWregularρ : (ρ - 1) * W ρ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hρone) hWρ
  have hLregularρ := zero_free_of_analytic_identity σ hσ Lregular M
    (fun s : ℂ => (s - 1) * W s) hLregular hM hWregular heq
    ρ hρ hWregularρ
  rw [hregular ρ hρ hρone] at hLregularρ
  exact (mul_ne_zero_iff.mp hLregularρ).2

theorem two_poisson_scale_substitution
    (K X F B L A C d t J Y g e ge v Li K' X' F' Δ : ℝ)
    (hK : K ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0)
    (ht : t ≠ 0) (hJ : J ≠ 0) (he : e ≠ 0)
    (hge : ge ≠ 0) (hv : v ≠ 0) (hL0 : L ≠ 0)
    (hL : L = X / B ^ 3)
    (hLi : Li = L / (A * C * t))
    (hg : g = e * ge)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J))
    (hK' : K' = d * e ^ 2 * Li ^ 2 / (Y * g ^ 2))
    (hX' : X' = Li / (g * v))
    (hF' : F' = J * C * e * v)
    (hΔ : Δ = B * F * A * t * ge) :
    K' = K * J / (Δ ^ 2 * B ^ 2) ∧
      X' * F' = X * F * J / (Δ * B ^ 2) := by
  constructor
  · rw [hK', hLi, hg, hY, hΔ]
    field_simp
  · rw [hX', hF', hLi, hL, hg, hΔ]
    field_simp

theorem two_poisson_budget
    (K X F R B J Δ K' childColumnMass R' : ℝ)
    (hK : 0 ≤ K) (hX : 0 < X) (hF : 0 < F)
    (hB : 0 < B) (hJpos : 0 < J) (hΔpos : 0 < Δ)
    (hJ : J ≤ B ^ 2) (hΔ : B * F ≤ Δ)
    (hK' : K' = K * J / (Δ ^ 2 * B ^ 2))
    (hM' : childColumnMass = X * F * J / (Δ * B ^ 2))
    (hR' : R' ≤ R * Δ) :
    K' * R' / childColumnMass ≤ K * R / (X * F) ∧
      K' ≤ K / (B * F) ^ 2 ∧
      childColumnMass ≤ X * F / (B * F) ∧
      (Δ * B ^ 2 / J) * childColumnMass = X * F := by
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hBF : 0 < B * F := mul_pos hB hF
  have hXF : 0 < X * F := mul_pos hX hF
  have hMpos : 0 < childColumnMass := by rw [hM']; positivity
  have hK'nonneg : 0 ≤ K' := by rw [hK']; positivity
  constructor
  · have hstep : K' * R' ≤ K' * (R * Δ) :=
      mul_le_mul_of_nonneg_left hR' hK'nonneg
    apply (div_le_div_iff₀ hMpos hXF).2
    calc
      K' * R' * (X * F) ≤ K' * (R * Δ) * (X * F) := by
        gcongr
      _ = (K * R / (X * F)) * childColumnMass * (X * F) := by
        rw [hK', hM']
        field_simp
      _ = K * R * childColumnMass := by field_simp
  constructor
  · rw [hK']
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hΔpos) hB2)
      (sq_pos_of_pos hBF)).2
    have hΔ2 : (B * F) ^ 2 ≤ Δ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hΔ)
        (show 0 ≤ Δ + B * F by positivity)]
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg hK (le_of_lt hB2)) (sub_nonneg.mpr hΔ2)]
  constructor
  · rw [hM']
    apply (div_le_div_iff₀ (mul_pos hΔpos hB2) hBF).2
    have hΔBF : B * F ≤ Δ := hΔ
    nlinarith [mul_nonneg (le_of_lt hXF) (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg (le_of_lt hXF) (le_of_lt hB2))
        (sub_nonneg.mpr hΔBF)]
  · rw [hM']
    field_simp

theorem two_poisson_charge
    (R R' b0 B F A t ge Δ : ℝ)
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hF : 1 ≤ F) (hA : 1 ≤ A)
    (ht : 0 ≤ t) (hge : 0 ≤ ge)
    (hb0B : b0 ≤ B)
    (hR' : R' ≤ R * b0 * t * ge)
    (hΔ : Δ = B * F * A * t * ge) : R' ≤ R * Δ := by
  calc
    R' ≤ R * b0 * t * ge := hR'
    _ ≤ R * B * t * ge := by gcongr
    _ ≤ R * (B * F * A * t * ge) := by
      have hBA : B ≤ B * F * A := by
        have hBF : B ≤ B * F := by nlinarith
        have hBFA : B * F ≤ B * F * A := by
          nlinarith [mul_nonneg (mul_nonneg hB (le_trans zero_le_one hF))
            (sub_nonneg.mpr hA)]
        exact hBF.trans hBFA
      nlinarith [mul_nonneg (mul_nonneg hR (sub_nonneg.mpr hBA))
        (mul_nonneg ht hge)]
    _ = R * Δ := by rw [hΔ]

theorem two_poisson_cost_identity
    (K A C d L B F c Y g e Li J t ge v X Δ : ℝ)
    (hK : K ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0) (hL : L ≠ 0)
    (hB : B ≠ 0) (hF : F ≠ 0) (hc : 0 < c)
    (hg : g ≠ 0) (he : e ≠ 0) (hLi : Li ≠ 0)
    (hJ : J ≠ 0) (hv : v ≠ 0)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J))
    (hM : X = Li / (g * v) * (J * C * e * v))
    (hΔ : Δ = B * F * A * t * ge) :
    (K * A * C / (d * L ^ 2 * B ^ 2 * F * Real.sqrt c)) *
      (Y * g / (e * Li)) *
      ((B * Real.sqrt c / J) * t * ge) * X = Δ * B ^ 2 / J := by
  have hcsqrt : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  rw [hY, hM, hΔ]
  field_simp

end ShortDraft

open MulChar AddChar

namespace ShortDraftLocal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem sextic_character_exponent (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ 3 := by
  calc
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ (-3 : ℤ) := by group
    _ = χ ^ 3 := by
      calc
        χ ^ (-3 : ℤ) = χ ^ ((-3 : ℤ) + 6) := by
          rw [zpow_add, zpow_ofNat, hχ, mul_one]
        _ = χ ^ 3 := by norm_num

theorem gaussSum_mulShift_any (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (a : F) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by
  by_cases ha : a = 0
  · subst a
    have hshift : ψ.mulShift (0 : F) = 1 := by
      ext x
      simp
    rw [hshift, gaussSum_one_right hχ]
    simp
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    simpa [hu.unit_spec] using gaussSum_mulShift_eq χ ψ hu.unit

theorem gaussSum_eq_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
  classical
  have hzero : χ (0 : F) * ψ (0 : F) = 0 := by simp
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, hzero, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F)
          (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by
      apply Finset.sum_subtype
      intro x
      simp
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun y : Fˣ => χ (y : F) * ψ (y : F))
        (fun x : {x : F // x ≠ 0} => χ x * ψ x) ?_).symm
      intro y
      rfl

omit [Fintype F] [DecidableEq F] in
theorem sextic_character_quadratic (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    (χ ^ 3)⁻¹ = χ ^ 3 := by
  calc
    (χ ^ 3)⁻¹ = χ ^ (-3 : ℤ) := by group
    _ = χ ^ 3 := by
      calc
        χ ^ (-3 : ℤ) = χ ^ ((-3 : ℤ) + 6) := by
          rw [zpow_add, zpow_ofNat, hχ, mul_one]
        _ = χ ^ 3 := by norm_num

theorem sextic_inversion_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by
  classical
  calc
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) (y⁻¹) * ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro y
          simp
    _ = ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by
      congr 1
      funext y
      rw [sextic_character_exponent χ hχ]
      have hy := sextic_character_quadratic χ hχ
      have hval : (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3) (y : F) := by
        calc
          (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3)⁻¹ (y : F) := by
            rw [MulChar.inv_apply', Units.val_inv_eq_inv_val]
          _ = (χ ^ 3) (y : F) := by rw [hy]
      rw [← Units.val_inv_eq_inv_val y, hval]

theorem sextic_inversion_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ 3) (ψ.mulShift a) := by
  rw [sextic_inversion_sum χ ψ hχ a, gaussSum_eq_units_sum]
  simp only [AddChar.mulShift_apply]

theorem sextic_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 3) ε * gaussSum (χ ^ 3) ψ * (χ ^ 3) x := by
  rw [sextic_inversion_gaussSum χ ψ hχ (ε * x)]
  rw [gaussSum_mulShift_any (χ ^ 3) ψ hχ₃ (ε * x)]
  rw [sextic_character_quadratic χ hχ, map_mul]
  ring

theorem additive_unit_sum (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (a : F) :
    (∑ y : Fˣ, ψ (a * (y : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hgauss : (∑ y : Fˣ, ψ (a * (y : F))) =
      gaussSum (1 : MulChar F ℂ) (ψ.mulShift a) := by
    rw [gaussSum_eq_units_sum]
    simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
  rw [hgauss]
  split_ifs with ha
  · subst a
    simp only [AddChar.mulShift_zero, gaussSum_one_one]
    exact_mod_cast (Nat.card_eq_fintype_card (α := Fˣ))
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    have hshift : ψ.mulShift a ≠ 1 := by
      intro heq
      exact hψ ((AddChar.mulShift_unit_eq_one_iff ψ hu).mp heq)
    exact gaussSum_one_left hshift

theorem sextic_fourth_mask (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hψ : ψ ≠ 1) (a : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) h *
      ψ (a * ((h⁻¹ : Fˣ) : F))) =
      if a = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  classical
  have hexp : ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = 1 := by
    calc
      ((χ⁻¹) ^ 4 * (χ⁻¹) ^ 2) = (χ ^ 6)⁻¹ := by group
      _ = 1 := by rw [hχ, inv_one]
  rw [hexp]
  simp only [MulChar.one_apply_coe, one_mul]
  calc
    (∑ h : Fˣ, ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, ψ (a * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp
    _ = _ := additive_unit_sum ψ hψ a

theorem active_zero_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ₂ : χ ^ 2 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
  classical
  have hquad : ((χ⁻¹) ^ 2)⁻¹ = χ ^ 2 := by group
  calc
    (∑ h : Fˣ, ((χ⁻¹) ^ 2) (h : F) *
      ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ ^ 2) (y : F) * ψ ((ε * x) * (y : F)) := by
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro h
          simp only [Equiv.inv_apply, Units.val_inv_eq_inv_val]
          rw [← hquad, MulChar.inv_apply', inv_inv]
    _ = gaussSum (χ ^ 2) (ψ.mulShift (ε * x)) := by
      rw [gaussSum_eq_units_sum]
      simp only [AddChar.mulShift_apply]
    _ = (χ ^ 2)⁻¹ ε * gaussSum (χ ^ 2) ψ * (χ ^ 2)⁻¹ x := by
      rw [gaussSum_mulShift_any (χ ^ 2) ψ hχ₂ (ε * x)]
      rw [map_mul]
      ring

theorem nontrivial_fourier_coefficient (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ t : F, χ t * ψ (-(h * t))) =
      χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by
  calc
    (∑ t : F, χ t * ψ (-(h * t))) =
        gaussSum χ ((ψ.mulShift (-1)).mulShift h) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) :=
      gaussSum_mulShift_any χ (ψ.mulShift (-1)) hχ h

theorem trivial_fourier_coefficient (ψ : AddChar F ℂ)
    (hψ : ψ ≠ 1) (h : F) :
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
      if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
  calc
    (∑ t : F, (1 : MulChar F ℂ) t * ψ (-(h * t))) =
        gaussSum (1 : MulChar F ℂ) (ψ.mulShift (-h)) := by
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
    _ = ∑ u : Fˣ, ψ ((-h) * (u : F)) := by
      rw [gaussSum_eq_units_sum]
      simp only [MulChar.one_apply_coe, one_mul, AddChar.mulShift_apply]
    _ = if h = 0 then (Fintype.card Fˣ : ℂ) else -1 := by
      simpa only [neg_eq_zero] using additive_unit_sum ψ hψ (-h)

theorem sextic_fourier_theta_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by
  classical
  have hχ₁ : χ ≠ 1 := by
    intro heq
    exact hχ₃ (by simp [heq])
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ((χ⁻¹) ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * (χ⁻¹) ^ 2) h *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ₁, map_mul]
    simp only [MulChar.mul_apply]
    ring
  rw [hsum, sextic_local_row χ ψ hχ hχ₃ ε x]
  ring

end ShortDraftLocal


end OAI
end OAIOriginalModule0001

/-! Original module: OAI.NumberTheory.DirichletL.Arithmetic.EisensteinIdeals
Source SHA256: 0207ad44950ad0ab475bbdc0d7da2200b55adc89b55a83d4ddf26fb954e0528f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0002


namespace OAI

open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap

noncomputable section

namespace ActualEisensteinSieve

abbrev K := CyclotomicField 3 ℚ
abbrev O := NumberField.RingOfIntegers K

private instance : IsCyclotomicExtension {3} ℚ K :=
  CyclotomicField.isCyclotomicExtension 3 ℚ

private instance : IsPrincipalIdealRing O :=
  IsCyclotomicExtension.Rat.three_pid K

def omega : O :=
  (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger

private def lambda : O := omega - 1

private def lambdaIdeal : Ideal O := Ideal.span {lambda}

private theorem lambda_prime : Prime lambda := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact (IsCyclotomicExtension.zeta_spec 3 ℚ K).zeta_sub_one_prime'

theorem lambda_maximal : lambdaIdeal.IsMaximal := by
  have hp : lambdaIdeal.IsPrime :=
    Ideal.isPrime_span_singleton_of_prime lambda_prime
  have hne : lambdaIdeal ≠ ⊥ := by
    exact Ideal.span_singleton_eq_bot.not.mpr lambda_prime.ne_zero
  exact hp.isMaximal hne

theorem lambda_card : Nat.card (O ⧸ lambdaIdeal) = 3 := by
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rw [lambdaIdeal, lambda, omega,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).card_quotient_toInteger_sub_one,
    (IsCyclotomicExtension.zeta_spec 3 ℚ K).norm_toInteger_sub_one_of_prime_ne_two'
      (by decide)]
  norm_num

example (P : Ideal O) [P.IsMaximal] : Field (O ⧸ P) := Ideal.Quotient.field P
example (P : Ideal O) [P.IsMaximal] : Finite (O ⧸ P) := inferInstance

private def localQuadratic (P : Ideal O) [P.IsMaximal] (x : O) : ℤ := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  exact quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x)

private theorem localQuadratic_one (P : Ideal O) [P.IsMaximal] :
    localQuadratic P 1 = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) 1 = 1
  exact map_one _

private theorem localQuadratic_mul (P : Ideal O) [P.IsMaximal] (x y : O) :
    localQuadratic P (x * y) = localQuadratic P x * localQuadratic P y := by
  simp [localQuadratic, map_mul]

private theorem localQuadratic_zero_iff (P : Ideal O) [P.IsMaximal] (x : O) :
    localQuadratic P x = 0 ↔ x ∈ P := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 0 ↔ x ∈ P
  rw [quadraticChar_eq_zero_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

private theorem exists_localQuadratic_neg_one (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    ∃ x : O, localQuadratic P x = -1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hodd
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨x, ?_⟩
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = -1
  exact ha

theorem localQuadratic_neg_one (P : Ideal O) [P.IsMaximal]
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    localQuadratic P (-1) = ZMod.χ₄ (Nat.card (O ⧸ P)) := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (-1) = ZMod.χ₄ (Nat.card (O ⧸ P))
  simpa only [Nat.card_eq_fintype_card] using quadraticChar_neg_one hodd

theorem localQuadratic_cube_root_one (P : Ideal O) [P.IsMaximal]
    (u : O) (hu : u ^ 3 = 1) : localQuadratic P u = 1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  let v : O ⧸ P := Ideal.Quotient.mk P u
  have hv3 : v ^ 3 = 1 := by
    simpa [v] using congrArg (Ideal.Quotient.mk P) hu
  have hvne : v ≠ 0 := by
    intro hv0
    simp [hv0] at hv3
  have hv4 : v ^ 4 = v := by
    calc
      v ^ 4 = v ^ 3 * v := by ring
      _ = v := by rw [hv3, one_mul]
  have hsq : quadraticChar (O ⧸ P) (v ^ 4) = 1 := by
    simpa only [← pow_mul] using quadraticChar_sq_one' (F := O ⧸ P)
      (a := v ^ 2) (pow_ne_zero _ hvne)
  change quadraticChar (O ⧸ P) v = 1
  rwa [hv4] at hsq

private theorem localQuadratic_trichotomy (P : Ideal O) [P.IsMaximal]
    (x : O) :
    localQuadratic P x = 0 ∨ localQuadratic P x = 1 ∨
      localQuadratic P x = -1 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 0 ∨
    quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = 1 ∨
    quadraticChar (O ⧸ P) (Ideal.Quotient.mk P x) = -1
  exact quadraticChar_isQuadratic (O ⧸ P) _

private instance : lambdaIdeal.IsMaximal := lambda_maximal

theorem lambda_residue_odd : ringChar (O ⧸ lambdaIdeal) ≠ 2 := by
  classical
  let : Field (O ⧸ lambdaIdeal) := Ideal.Quotient.field lambdaIdeal
  let : Fintype (O ⧸ lambdaIdeal) := Fintype.ofFinite (O ⧸ lambdaIdeal)
  intro hchar
  have hcard := FiniteField.even_card_of_char_two hchar
  rw [← Nat.card_eq_fintype_card, lambda_card] at hcard
  norm_num at hcard

theorem lambdaQuadratic_neg_one : localQuadratic lambdaIdeal (-1) = -1 := by
  rw [localQuadratic_neg_one lambdaIdeal lambda_residue_odd, lambda_card]
  rfl

private theorem finite_prod_trichotomy {ι : Type*} (s : Finset ι)
    (f : ι → ℤ)
    (hf : ∀ i ∈ s, f i = 0 ∨ f i = 1 ∨ f i = -1) :
    s.prod f = 0 ∨ s.prod f = 1 ∨ s.prod f = -1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs : ∀ j ∈ s, f j = 0 ∨ f j = 1 ∨ f j = -1 := by
        intro j hj
        exact hf j (Finset.mem_insert_of_mem hj)
      have ih' := ih hfs
      rcases hfi with h0 | h1 | hm
      · left; simp [Finset.prod_insert his, h0]
      · simpa [Finset.prod_insert his, h1] using ih'
      · rcases ih' with h0 | h1 | hm'
        · left; simp [Finset.prod_insert his, hm, h0]
        · right; right; simp [Finset.prod_insert his, hm, h1]
        · right; left; simp [Finset.prod_insert his, hm, hm']

private theorem crt_pair (I J : Ideal O) (h : IsCoprime I J)
    (a : O ⧸ I) (b : O ⧸ J) :
    ∃ x : O, Ideal.Quotient.mk I x = a ∧ Ideal.Quotient.mk J x = b := by
  let e := Ideal.quotientMulEquivQuotientProd I J h
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective (e.symm (a, b))
  have he : e (Ideal.Quotient.mk (I * J) x) = (a, b) := by
    rw [hx, e.apply_symm_apply]
  refine ⟨x, ?_, ?_⟩
  · simpa [e] using congrArg Prod.fst he
  · simpa [e] using congrArg Prod.snd he

private theorem localQuadratic_congr (P : Ideal O) [P.IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk P x = Ideal.Quotient.mk P y) :
    localQuadratic P x = localQuadratic P y := by
  simp only [localQuadratic, h]

theorem lambdaQuadratic_omega : localQuadratic lambdaIdeal omega = 1 := by
  apply (localQuadratic_congr lambdaIdeal omega 1 ?_).trans
    (localQuadratic_one lambdaIdeal)
  apply Ideal.Quotient.eq.mpr
  exact Ideal.subset_span (by simp [lambda, omega])

private theorem productQuadratic_detects_left
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ P) ≠ 2) :
    ∃ x : O,
      Ideal.Quotient.mk Q x = Ideal.Quotient.mk Q (1 : O) ∧
      localQuadratic P x * localQuadratic Q x = -1 := by
  obtain ⟨a, ha⟩ := exists_localQuadratic_neg_one P hodd
  obtain ⟨x, hP, hQ⟩ := crt_pair P Q hcop
    (Ideal.Quotient.mk P a) (Ideal.Quotient.mk Q (1 : O))
  refine ⟨x, hQ, ?_⟩
  rw [localQuadratic_congr P x a hP,
    localQuadratic_congr Q x 1 hQ, ha, localQuadratic_one]
  ring

theorem productQuadratic_not_factor_right
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ P) ≠ 2) :
    ¬ ∃ f : (O ⧸ Q) → ℤ, ∀ x : O,
      localQuadratic P x * localQuadratic Q x = f (Ideal.Quotient.mk Q x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hQ, hneg⟩ := productQuadratic_detects_left P Q hcop hodd
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg, hQ] at hx
  rw [localQuadratic_one P, localQuadratic_one Q] at h1
  norm_num at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk Q (1 : O)) := hx
      _ = f 1 := by simp
      _ = 1 := h1.symm
  norm_num at absurd

theorem productQuadratic_not_factor_left
    (P Q : Ideal O) [P.IsMaximal] [Q.IsMaximal]
    (hcop : IsCoprime P Q) (hodd : ringChar (O ⧸ Q) ≠ 2) :
    ¬ ∃ f : (O ⧸ P) → ℤ, ∀ x : O,
      localQuadratic P x * localQuadratic Q x = f (Ideal.Quotient.mk P x) := by
  intro h
  apply productQuadratic_not_factor_right Q P hcop.symm hodd
  obtain ⟨f, hf⟩ := h
  refine ⟨f, ?_⟩
  intro x
  rw [mul_comm]
  exact hf x

theorem finiteQuadratic_detects_prime
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ∃ x : O,
      (∀ j : ι, j ≠ i₀ → Ideal.Quotient.mk (P j) x = 1) ∧
      (∏ j : ι, localQuadratic (P j) x) = -1 := by
  classical
  obtain ⟨a, ha⟩ := exists_localQuadratic_neg_one (P i₀) (hodd i₀)
  let target (j : ι) : O ⧸ P j :=
    Ideal.Quotient.mk (P j) (if j = i₀ then a else 1)
  obtain ⟨x, hx⟩ := Ideal.pi_quotient_surjective hpair target
  have hlocal (j : ι) :
      localQuadratic (P j) x = if j = i₀ then -1 else 1 := by
    by_cases hj : j = i₀
    · subst j
      have hres : Ideal.Quotient.mk (P i₀) x = Ideal.Quotient.mk (P i₀) a := by
        simpa [target] using hx i₀
      simpa using (localQuadratic_congr (P i₀) x a hres).trans ha
    · have hres : Ideal.Quotient.mk (P j) x = Ideal.Quotient.mk (P j) (1 : O) := by
        simpa [target, hj] using hx j
      simpa [hj] using (localQuadratic_congr (P j) x 1 hres).trans
        (localQuadratic_one (P j))
  refine ⟨x, ?_, ?_⟩
  · intro j hj
    simpa [target, hj] using hx j
  · simp_rw [hlocal]
    simp

private def quadraticProduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) : ℤ :=
  ∏ i : ι, localQuadratic (P i) x

private theorem quadraticProduct_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : quadraticProduct P 1 = 1 := by
  simp [quadraticProduct, localQuadratic_one]

private theorem quadraticProduct_mul
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O) :
    quadraticProduct P (x * y) = quadraticProduct P x * quadraticProduct P y := by
  simp [quadraticProduct, localQuadratic_mul, Finset.prod_mul_distrib]

private theorem quadraticProduct_neg_one_square
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : quadraticProduct P (-1) ^ 2 = 1 := by
  calc
    quadraticProduct P (-1) ^ 2 =
        quadraticProduct P ((-1 : O) * (-1)) := by
          rw [pow_two, quadraticProduct_mul]
    _ = 1 := by simpa using quadraticProduct_one P

def correctedQuadraticProduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) : ℤ :=
  if quadraticProduct P (-1) = 1 then quadraticProduct P x
  else quadraticProduct P x * localQuadratic lambdaIdeal x

theorem correctedQuadraticProduct_neg_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P (-1) = 1 := by
  classical
  have hsq := quadraticProduct_neg_one_square P
  have hsign : quadraticProduct P (-1) = 1 ∨
      quadraticProduct P (-1) = -1 :=
    sq_eq_one_iff.mp hsq
  rcases hsign with h | h
  · simp [correctedQuadraticProduct, h]
  · simp [correctedQuadraticProduct, h, lambdaQuadratic_neg_one]

theorem correctedQuadraticProduct_omega
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P omega = 1 := by
  have hq : quadraticProduct P omega = 1 := by
    simp [quadraticProduct, localQuadratic_cube_root_one,
      (IsCyclotomicExtension.zeta_spec 3 ℚ K).toInteger_cube_eq_one,
      omega]
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, hq]
  · simp [correctedQuadraticProduct, h, hq, lambdaQuadratic_omega]

theorem correctedQuadraticProduct_one
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    correctedQuadraticProduct P 1 = 1 := by
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, quadraticProduct_one]
  · simp [correctedQuadraticProduct, h, quadraticProduct_one,
      localQuadratic_one]

theorem correctedQuadraticProduct_mul
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O) :
    correctedQuadraticProduct P (x * y) =
      correctedQuadraticProduct P x * correctedQuadraticProduct P y := by
  by_cases h : quadraticProduct P (-1) = 1
  · simp [correctedQuadraticProduct, h, quadraticProduct_mul]
  · simp only [correctedQuadraticProduct, h, ite_false,
      quadraticProduct_mul, localQuadratic_mul]
    ring

private def correctedQuadraticHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : O →* ℤ where
  toFun := correctedQuadraticProduct P
  map_one' := correctedQuadraticProduct_one P
  map_mul' := correctedQuadraticProduct_mul P

theorem correctedQuadraticProduct_units
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (u : Oˣ) :
    correctedQuadraticProduct P (u : O) = 1 := by
  let hζ := IsCyclotomicExtension.zeta_spec 3 ℚ K
  let η : Oˣ := (IsPrimitiveRoot.isUnit hζ.toInteger_isPrimitiveRoot
    (by decide)).unit
  have hη : (η : O) = omega := rfl
  have hu := IsCyclotomicExtension.Rat.Three.Units.mem hζ u
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hu
  rcases hu with h | h | h | h | h | h
  · subst u
    simpa using correctedQuadraticProduct_one P
  · subst u
    simpa using correctedQuadraticProduct_neg_one P
  · subst u
    change correctedQuadraticProduct P (η : O) = 1
    rw [hη]
    exact correctedQuadraticProduct_omega P
  · subst u
    change correctedQuadraticProduct P (-(η : O)) = 1
    rw [neg_eq_neg_one_mul, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_neg_one, hη,
      correctedQuadraticProduct_omega]
    norm_num
  · subst u
    change correctedQuadraticProduct P ((η : O) ^ 2) = 1
    rw [pow_two, correctedQuadraticProduct_mul, hη,
      correctedQuadraticProduct_omega]
    norm_num
  · subst u
    change correctedQuadraticProduct P (-((η : O) ^ 2)) = 1
    rw [neg_eq_neg_one_mul, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_neg_one]
    have hpow : correctedQuadraticProduct P ((η : O) ^ 2) = 1 := by
      rw [pow_two, correctedQuadraticProduct_mul, hη,
        correctedQuadraticProduct_omega]
      norm_num
    rw [hpow]
    norm_num

theorem correctedQuadraticProduct_congr_mod_conductor
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) x =
      Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) y) :
    correctedQuadraticProduct P x = correctedQuadraticProduct P y := by
  classical
  have hmem : x - y ∈ lambdaIdeal * Finset.univ.prod P :=
    Ideal.Quotient.eq.mp h
  have hlambda : Ideal.Quotient.mk lambdaIdeal x =
      Ideal.Quotient.mk lambdaIdeal y :=
    Ideal.Quotient.eq.mpr (Ideal.mul_le_left hmem)
  have hprod : quadraticProduct P x = quadraticProduct P y := by
    unfold quadraticProduct
    apply Finset.prod_congr rfl
    intro j _
    apply localQuadratic_congr
    apply Ideal.Quotient.eq.mpr
    exact (Ideal.mul_le_right.trans
      (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j)))) hmem
  unfold correctedQuadraticProduct
  split_ifs <;> simp [hprod, localQuadratic_congr lambdaIdeal x y hlambda]

theorem correctedQuadraticProduct_one_of_congruent
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O)
    (h : x - 1 ∈ lambdaIdeal * Finset.univ.prod P) :
    correctedQuadraticProduct P x = 1 := by
  have hres : Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) x =
      Ideal.Quotient.mk (lambdaIdeal * Finset.univ.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr h
  exact (correctedQuadraticProduct_congr_mod_conductor P x 1 hres).trans
    (correctedQuadraticProduct_one P)

noncomputable def correctedAssociatesHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : Associates O →* ℤ where
  toFun := Quotient.lift (correctedQuadraticProduct P) (by
    intro a b hab
    obtain ⟨u, hu⟩ := hab
    rw [← hu, correctedQuadraticProduct_mul,
      correctedQuadraticProduct_units, mul_one])
  map_one' := by
    change correctedQuadraticProduct P 1 = 1
    exact correctedQuadraticProduct_one P
  map_mul' := by
    intro x y
    obtain ⟨a, rfl⟩ := Associates.mk_surjective x
    obtain ⟨b, rfl⟩ := Associates.mk_surjective y
    change correctedQuadraticProduct P (a * b) =
      correctedQuadraticProduct P a * correctedQuadraticProduct P b
    exact correctedQuadraticProduct_mul P a b

private noncomputable def idealGeneratorClass (I : Ideal O) : Associates O :=
  (Ideal.associatesMulEquivIsPrincipal O).symm
    ⟨I, IsPrincipalIdealRing.principal I⟩

private theorem idealGeneratorClass_one : idealGeneratorClass (1 : Ideal O) = 1 := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]

private theorem idealGeneratorClass_mul (I J : Ideal O) :
    idealGeneratorClass (I * J) = idealGeneratorClass I * idealGeneratorClass J := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]
  apply Subtype.ext
  rfl

private theorem idealGeneratorClass_span (x : O) :
    idealGeneratorClass (Ideal.span {x}) = Associates.mk x := by
  apply (Ideal.associatesMulEquivIsPrincipal O).injective
  simp [idealGeneratorClass]
  apply Subtype.ext
  rfl

noncomputable def correctedIdealHom
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] : Ideal O →* ℤ where
  toFun I := correctedAssociatesHom P (idealGeneratorClass I)
  map_one' := by
    rw [idealGeneratorClass_one, map_one]
  map_mul' := by
    intro I J
    rw [idealGeneratorClass_mul, map_mul]

theorem correctedIdealHom_span
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    correctedIdealHom P (Ideal.span {x}) =
      correctedQuadraticProduct P x := by
  simp [correctedIdealHom, idealGeneratorClass_span, correctedAssociatesHom]
  rfl

theorem finiteQuadratic_not_factor_without_prime
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ¬ ∃ f : ((j : {j : ι // j ≠ i₀}) → O ⧸ P j.1) → ℤ,
      ∀ x : O,
        (∏ j : ι, localQuadratic (P j) x) =
          f (fun j => Ideal.Quotient.mk (P j.1) x) := by
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  have hsame :
      (fun j : {j : ι // j ≠ i₀} => Ideal.Quotient.mk (P j.1) x) =
      (fun j : {j : ι // j ≠ i₀} => Ideal.Quotient.mk (P j.1) (1 : O)) := by
    funext j
    simpa using hres j.1 j.2
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg, hsame] at hx
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := hx.trans h1.symm
  norm_num at absurd

theorem finiteQuadratic_not_factor_omit_prime_ideal
    {ι : Type*} [Fintype ι] [DecidableEq ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2) (i₀ : ι) :
    ¬ ∃ f : (O ⧸ (Finset.univ.erase i₀).prod P) → ℤ,
      ∀ x : O,
        (∏ j : ι, localQuadratic (P j) x) =
          f (Ideal.Quotient.mk ((Finset.univ.erase i₀).prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  let s : Finset ι := Finset.univ.erase i₀
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprod : s.prod P = ⨅ j ∈ s, P j := by
    exact Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hmem : x - 1 ∈ s.prod P := by
    rw [hprod]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := (Finset.mem_erase.mp hj).1
    exact Ideal.Quotient.eq.mp (hres j hjne)
  have hsame : Ideal.Quotient.mk (s.prod P) x =
      Ideal.Quotient.mk (s.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr hmem
  have hx := hf x
  have h1 := hf (1 : O)
  rw [hneg] at hx
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (s.prod P) x) := by simpa [s] using hx
      _ = f (Ideal.Quotient.mk (s.prod P) (1 : O)) := by rw [hsame]
      _ = 1 := by simpa [s] using h1.symm
  norm_num at absurd

theorem finiteQuadratic_congr_mod_product
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x y : O)
    (h : Ideal.Quotient.mk (Finset.univ.prod P) x =
      Ideal.Quotient.mk (Finset.univ.prod P) y) :
    (∏ j : ι, localQuadratic (P j) x) =
      ∏ j : ι, localQuadratic (P j) y := by
  classical
  have hmem : x - y ∈ Finset.univ.prod P := Ideal.Quotient.eq.mp h
  apply Finset.prod_congr rfl
  intro j _
  apply localQuadratic_congr
  apply Ideal.Quotient.eq.mpr
  exact (Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_univ j))) hmem

private def finiteQuadraticOnQuotient
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (z : O ⧸ Finset.univ.prod P) : ℤ :=
  ∏ j : ι, localQuadratic (P j) (Quotient.out z)

theorem finiteQuadraticOnQuotient_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] (x : O) :
    finiteQuadraticOnQuotient P
        (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ j : ι, localQuadratic (P j) x := by
  classical
  unfold finiteQuadraticOnQuotient
  apply finiteQuadratic_congr_mod_product P
  exact Quotient.out_eq _

theorem finiteQuadratic_not_factor_subproduct
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ s.prod P) → ℤ,
      ∀ x : O,
        finiteQuadraticOnQuotient P
            (Ideal.Quotient.mk (Finset.univ.prod P) x) =
          f (Ideal.Quotient.mk (s.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprod : s.prod P = ⨅ j ∈ s, P j :=
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hmem : x - 1 ∈ s.prod P := by
    rw [hprod]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := by
      intro he
      subst j
      exact hi₀ hj
    exact Ideal.Quotient.eq.mp (hres j hjne)
  have hsame : Ideal.Quotient.mk (s.prod P) x =
      Ideal.Quotient.mk (s.prod P) (1 : O) :=
    Ideal.Quotient.eq.mpr hmem
  have hx := hf x
  have h1 := hf (1 : O)
  rw [finiteQuadraticOnQuotient_mk, hneg] at hx
  rw [finiteQuadraticOnQuotient_mk] at h1
  have hp1 : (∏ j : ι, localQuadratic (P j) (1 : O)) = 1 := by
    simp [localQuadratic_one]
  rw [hp1] at h1
  have absurd : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (s.prod P) x) := hx
      _ = f (Ideal.Quotient.mk (s.prod P) (1 : O)) := by rw [hsame]
      _ = 1 := h1.symm
  norm_num at absurd

private noncomputable def squarefreeCRT
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    (O ⧸ Finset.univ.prod P) ≃+* ((i : ι) → O ⧸ P i) := by
  classical
  have hpairU : ((Finset.univ : Finset ι) : Set ι).Pairwise
      (Function.onFun IsCoprime P) := by
    intro i hi j hj hij
    exact hpair hij
  have hprod : Finset.univ.prod P = ⨅ i, P i := by
    simpa using Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairU
  exact (Ideal.quotEquivOfEq hprod).trans
    (Ideal.quotientInfRingEquivPiQuotient P hpair)

private theorem squarefreeCRT_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    squarefreeCRT P hpair (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      fun i => Ideal.Quotient.mk (P i) x := by
  classical
  funext i
  simp only [squarefreeCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  change (Ideal.quotientInfToPiQuotient P
    (Ideal.Quotient.mk (⨅ i, P i) x)) i = Ideal.Quotient.mk (P i) x
  rfl

private noncomputable def localResidueChar (P : Ideal O) [P.IsMaximal] :
    MulChar (O ⧸ P) ℤ := by
  classical
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  letI : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  exact quadraticChar (O ⧸ P)

private theorem localResidueChar_zero_iff (P : Ideal O) [P.IsMaximal]
    (z : O ⧸ P) : localResidueChar P z = 0 ↔ z = 0 := by
  classical
  let : Field (O ⧸ P) := Ideal.Quotient.field P
  let : Fintype (O ⧸ P) := Fintype.ofFinite (O ⧸ P)
  change quadraticChar (O ⧸ P) z = 0 ↔ z = 0
  exact quadraticChar_eq_zero_iff

private noncomputable def squarefreePiChar
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal] :
    MulChar ((i : ι) → O ⧸ P i) ℤ where
  toFun z := ∏ i : ι, localResidueChar (P i) (z i)
  map_one' := by
    classical
    simp
  map_mul' := by
    classical
    intro x y
    simp only [Pi.mul_apply, map_mul, Finset.prod_mul_distrib]
  map_nonunit' := by
    classical
    intro z hz
    by_contra hprod
    have hnonzero (i : ι) : localResidueChar (P i) (z i) ≠ 0 := by
      intro hzero
      exact hprod (Finset.prod_eq_zero (Finset.mem_univ i) hzero)
    have hunit_i (i : ι) : IsUnit (z i) := by
      let : Field (O ⧸ P i) := Ideal.Quotient.field (P i)
      exact isUnit_iff_ne_zero.mpr
        ((localResidueChar_zero_iff (P i) (z i)).not.mp (hnonzero i))
    exact hz (Pi.isUnit_iff.mpr hunit_i)

noncomputable def squarefreeQuotientChar
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    MulChar (O ⧸ Finset.univ.prod P) ℤ where
  toFun z := squarefreePiChar P (squarefreeCRT P hpair z)
  map_one' := by
    simp
  map_mul' := by
    intro x y
    simp
  map_nonunit' := by
    intro z hz
    apply (squarefreePiChar P).map_nonunit
    intro hu
    have hzunit : IsUnit z := by
      simpa using hu.map (squarefreeCRT P hpair).symm.toRingHom
    exact hz hzunit

theorem squarefreeQuotientChar_mk
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) (x : O) :
    squarefreeQuotientChar P hpair
        (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      ∏ i : ι, localQuadratic (P i) x := by
  classical
  simp only [squarefreeQuotientChar, MulChar.coe_mk, MonoidHom.coe_mk,
    OneHom.coe_mk, squarefreeCRT_mk, squarefreePiChar]
  apply Finset.prod_congr rfl
  intro i _
  rfl

theorem squarefreeQuotientChar_primitive
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ s.prod P) → ℤ,
      ∀ x : O,
        squarefreeQuotientChar P hpair
            (Ideal.Quotient.mk (Finset.univ.prod P) x) =
          f (Ideal.Quotient.mk (s.prod P) x) := by
  intro hf
  apply finiteQuadratic_not_factor_subproduct P hpair hodd s i₀ hi₀
  obtain ⟨f, hf⟩ := hf
  refine ⟨f, ?_⟩
  intro x
  simpa only [finiteQuadraticOnQuotient_mk, squarefreeQuotientChar_mk] using hf x

theorem squarefreeQuotientChar_isQuadratic
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    (squarefreeQuotientChar P hpair).IsQuadratic := by
  classical
  intro z
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
  rw [squarefreeQuotientChar_mk]
  apply finite_prod_trichotomy
  intro i _
  exact localQuadratic_trichotomy (P i) x

theorem squarefreeQuotientChar_order_two
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P)) :
    squarefreeQuotientChar P hpair ^ 2 = 1 :=
  (squarefreeQuotientChar_isQuadratic P hpair).sq_eq_one

theorem correctedQuadraticProduct_not_factor_without_lambda
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hcop : IsCoprime lambdaIdeal (Finset.univ.prod P))
    (hneed : quadraticProduct P (-1) ≠ 1) :
    ¬ ∃ f : (O ⧸ Finset.univ.prod P) → ℤ,
      ∀ x : O,
        correctedQuadraticProduct P x =
          f (Ideal.Quotient.mk (Finset.univ.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hlambda, hP⟩ := crt_pair lambdaIdeal (Finset.univ.prod P) hcop
    (Ideal.Quotient.mk lambdaIdeal (-1 : O))
    (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O))
  have hraw : quadraticProduct P x = 1 := by
    change (∏ i : ι, localQuadratic (P i) x) = 1
    rw [finiteQuadratic_congr_mod_product P x 1 hP]
    simp [localQuadratic_one]
  have hlocal : localQuadratic lambdaIdeal x = -1 := by
    rw [localQuadratic_congr lambdaIdeal x (-1) hlambda]
    exact lambdaQuadratic_neg_one
  have hx : correctedQuadraticProduct P x = -1 := by
    simp [correctedQuadraticProduct, hneed, hraw, hlocal]
  have h1 : correctedQuadraticProduct P (1 : O) = 1 :=
    correctedQuadraticProduct_one P
  have hEq : f (Ideal.Quotient.mk (Finset.univ.prod P) x) =
      f (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O)) :=
    congrArg f hP
  have : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (Finset.univ.prod P) x) :=
        hx.symm.trans (hf x)
      _ = f (Ideal.Quotient.mk (Finset.univ.prod P) (1 : O)) := hEq
      _ = 1 := (hf 1).symm.trans h1
  norm_num at this

theorem lambdaQuadratic_sq_one_of_not_mem (x : O)
    (hx : x ∉ lambdaIdeal) :
    localQuadratic lambdaIdeal x ^ 2 = 1 := by
  rcases localQuadratic_trichotomy lambdaIdeal x with hzero | hone | hminus
  · exact False.elim (hx ((localQuadratic_zero_iff lambdaIdeal x).mp hzero))
  · simp [hone]
  · simp [hminus]

theorem correctedQuadraticProduct_pair_cancel
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (P : ι → Ideal O) (Q : κ → Ideal O)
    [∀ i, (P i).IsMaximal] [∀ j, (Q j).IsMaximal]
    (hsame : quadraticProduct P (-1) = quadraticProduct Q (-1))
    (x : O) (hx : x ∉ lambdaIdeal) :
    correctedQuadraticProduct P x * correctedQuadraticProduct Q x =
      quadraticProduct P x * quadraticProduct Q x := by
  by_cases hP : quadraticProduct P (-1) = 1
  · have hQ : quadraticProduct Q (-1) = 1 := hsame.symm.trans hP
    simp [correctedQuadraticProduct, hP, hQ]
  · have hQ : quadraticProduct Q (-1) ≠ 1 := by
      intro h
      exact hP (hsame.trans h)
    simp only [correctedQuadraticProduct, hP, hQ, ite_false]
    have hlamSq := lambdaQuadratic_sq_one_of_not_mem x hx
    calc
      quadraticProduct P x * localQuadratic lambdaIdeal x *
          (quadraticProduct Q x * localQuadratic lambdaIdeal x) =
        (quadraticProduct P x * quadraticProduct Q x) *
          localQuadratic lambdaIdeal x ^ 2 := by ring
      _ = quadraticProduct P x * quadraticProduct Q x := by
        rw [hlamSq, mul_one]

theorem correctedQuadraticProduct_not_factor_without_prime
    {ι : Type*} [Fintype ι] (P : ι → Ideal O)
    [∀ i, (P i).IsMaximal]
    (hpair : Pairwise (Function.onFun IsCoprime P))
    (hodd : ∀ i, ringChar (O ⧸ P i) ≠ 2)
    (hcop : IsCoprime lambdaIdeal (Finset.univ.prod P))
    (s : Finset ι) (i₀ : ι) (hi₀ : i₀ ∉ s) :
    ¬ ∃ f : (O ⧸ lambdaIdeal * s.prod P) → ℤ,
      ∀ x : O,
        correctedQuadraticProduct P x =
          f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) x) := by
  classical
  rintro ⟨f, hf⟩
  obtain ⟨x, hres, hneg⟩ := finiteQuadratic_detects_prime P hpair hodd i₀
  obtain ⟨y, hlam, hfull⟩ := crt_pair lambdaIdeal (Finset.univ.prod P) hcop
    (Ideal.Quotient.mk lambdaIdeal (1 : O))
    (Ideal.Quotient.mk (Finset.univ.prod P) x)
  have hraw : quadraticProduct P y = -1 := by
    change (∏ j : ι, localQuadratic (P j) y) = -1
    rw [finiteQuadratic_congr_mod_product P y x hfull]
    exact hneg
  have hlocal : localQuadratic lambdaIdeal y = 1 := by
    rw [localQuadratic_congr lambdaIdeal y 1 hlam]
    exact localQuadratic_one lambdaIdeal
  have hy : correctedQuadraticProduct P y = -1 := by
    by_cases hsign : quadraticProduct P (-1) = 1
    · simp [correctedQuadraticProduct, hsign, hraw]
    · simp [correctedQuadraticProduct, hsign, hraw, hlocal]
  have hcopS : IsCoprime lambdaIdeal (s.prod P) := by
    apply IsCoprime.prod_right
    intro j hj
    exact (IsCoprime.prod_right_iff.mp hcop) j (Finset.mem_univ j)
  have hpairS : (s : Set ι).Pairwise (Function.onFun IsCoprime P) := by
    intro j hj k hk hjk
    exact hpair hjk
  have hprodS : s.prod P = ⨅ j ∈ s, P j :=
    Ideal.prod_eq_iInf_of_pairwise_isCoprime hpairS
  have hs : y - 1 ∈ s.prod P := by
    rw [hprodS]
    simp only [Submodule.mem_iInf]
    intro j hj
    have hjne : j ≠ i₀ := by
      intro he
      subst j
      exact hi₀ hj
    have hPj : Ideal.Quotient.mk (P j) y =
        Ideal.Quotient.mk (P j) x := by
      apply Ideal.Quotient.eq.mpr
      exact (Ideal.prod_le_inf.trans
        (Finset.inf_le (Finset.mem_univ j))) (Ideal.Quotient.eq.mp hfull)
    exact Ideal.Quotient.eq.mp (hPj.trans (hres j hjne))
  have hmod : Ideal.Quotient.mk (lambdaIdeal * s.prod P) y =
      Ideal.Quotient.mk (lambdaIdeal * s.prod P) (1 : O) := by
    apply Ideal.Quotient.eq.mpr
    rw [Ideal.mul_eq_inf_of_isCoprime hcopS]
    exact ⟨Ideal.Quotient.eq.mp hlam, hs⟩
  have : (-1 : ℤ) = 1 := by
    calc
      (-1 : ℤ) = f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) y) :=
        hy.symm.trans (hf y)
      _ = f (Ideal.Quotient.mk (lambdaIdeal * s.prod P) (1 : O)) :=
        congrArg f hmod
      _ = 1 := (hf 1).symm.trans (correctedQuadraticProduct_one P)
  norm_num at this

end ActualEisensteinSieve

end

end OAI
end OAIOriginalModule0002

/-! Original module: OAI.NumberTheory.DirichletL.CubicDyadicDecay
Source SHA256: 1a6ab6ccc62d7bd902ea5728dcf49d01093595ebf908875f34a0163378ad4293
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0003









namespace OAI

namespace SevenEighths.CubicDyadicDecay
open scoped BigOperators
noncomputable section

def decayConstant (α : ℝ) : ℝ :=
  (2 : ℝ)^α / ((2 : ℝ)^α - 1) + (1 - (2 : ℝ)^(α - 3))⁻¹

lemma dyadic_rpow (α : ℝ) (j : ℕ) :
    ((2 : ℝ)^j)^α = ((2 : ℝ)^α)^j := by
  rw [← Real.rpow_natCast_mul (by norm_num), mul_comm,
    Real.rpow_mul_natCast (by norm_num)]

lemma decay_le_low (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤ ((2 : ℝ)^α)^j := by
  rw [← dyadic_rpow]
  exact div_le_self (by positivity) (one_le_pow₀ (by
    have : 0 ≤ t * (2 : ℝ)^j := by positivity
    linarith))

lemma decay_le_high (t α : ℝ) (ht : 0 < t) (j : ℕ) :
    ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3 ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α - 3))^j := by
  have hk : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ((2 : ℝ)^j)^α / (t * (2 : ℝ)^j)^3 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity)
        (pow_le_pow_left₀ (by positivity) (by linarith) 3)
    _ = _ := by
      rw [← dyadic_rpow, Real.rpow_sub hk, Real.rpow_neg ht.le, mul_pow]
      simp only [Real.rpow_ofNat]
      ring

lemma decay_summable (t α : ℝ) (ht : 0 < t) (hα : α < 3) :
    Summable (fun j : ℕ => ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) := by
  have hr : (2 : ℝ)^(α - 3) < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  exact ((summable_geometric_of_lt_one (by positivity) hr).mul_left (t^(-3 : ℝ))).of_nonneg_of_le
    (fun j => by positivity) (decay_le_high t α ht)

lemma decayConstant_pos (α : ℝ) (hα : 0 < α) (hα3 : α < 3) :
    0 < decayConstant α := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α - 3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  unfold decayConstant
  positivity

lemma geometric_prefix_le (q : ℝ) (hq : 1 < q) (k : ℕ) :
    (∑ j ∈ Finset.range k, q^j) ≤ q^k / (q - 1) := by
  rw [geom_sum_eq (ne_of_gt hq)]
  exact div_le_div_of_nonneg_right (by linarith) (by linarith)

lemma decay_tail_le (t α : ℝ) (ht : 0 < t) (hα3 : α < 3) (k : ℕ) :
    (∑' j : ℕ, ((2 : ℝ)^(j+k))^α / (1 + t * (2 : ℝ)^(j+k))^3) ≤
      t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k * (1 - (2 : ℝ)^(α-3))⁻¹ := by
  have hr0 : 0 ≤ (2 : ℝ)^(α-3) := by positivity
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hs := summable_geometric_of_lt_one hr0 hr
  calc
    _ ≤ ∑' j : ℕ, t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^(j+k) := by
      apply (decay_summable t α ht hα3).comp_injective (add_left_injective k) |>.tsum_le_tsum
        (fun j => decay_le_high t α ht (j+k))
      exact (hs.comp_injective (add_left_injective k)).mul_left _
    _ = _ := by
      simp_rw [pow_add]
      rw [tsum_mul_left, tsum_mul_right, tsum_geometric_of_lt_one hr0 hr]
      ring

theorem dyadic_decay_bound (t α : ℝ) (ht : 0 < t) (hα : 0 < α) (hα3 : α < 3) :
    (∑' j : ℕ, ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
      decayConstant α * t^(-α) := by
  have hq : 1 < (2 : ℝ)^α := Real.one_lt_rpow (by norm_num) hα
  have hr : (2 : ℝ)^(α-3) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hden : 0 < (1 - (2 : ℝ)^(α-3))⁻¹ := inv_pos.mpr (by linarith)
  by_cases ht1 : 1 ≤ t
  · have hp : t^(-3 : ℝ) ≤ t^(-α) :=
      Real.rpow_le_rpow_of_exponent_le ht1 (by linarith)
    have hh := decay_tail_le t α ht hα3 0
    simp only [Nat.add_zero, pow_zero, mul_one] at hh
    apply hh.trans
    unfold decayConstant
    nlinarith [mul_nonneg (div_nonneg (by positivity : 0 ≤ (2 : ℝ)^α)
      (by linarith : 0 ≤ (2 : ℝ)^α - 1)) (by positivity : 0 ≤ t^(-α)),
      mul_le_mul_of_nonneg_right hp hden.le]
  · have hit : 1 ≤ t⁻¹ := (one_le_inv₀ ht).mpr (le_of_not_ge ht1)
    obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near hit (by norm_num : (1 : ℝ) < 2)
    let k := n+1
    have hk0 : 0 < (2 : ℝ)^k := by positivity
    have hk : t⁻¹ ≤ (2 : ℝ)^k := le_of_lt hn'
    have hk' : (2 : ℝ)^k ≤ 2*t⁻¹ := by
      dsimp [k]
      rw [pow_succ]
      nlinarith
    have hlow : (∑ j ∈ Finset.range k,
        ((2 : ℝ)^j)^α / (1 + t * (2 : ℝ)^j)^3) ≤
        (2 : ℝ)^α / ((2 : ℝ)^α - 1) * t^(-α) := by
      calc
        _ ≤ ∑ j ∈ Finset.range k, ((2 : ℝ)^α)^j :=
          Finset.sum_le_sum (fun j hj => decay_le_low t α ht j)
        _ ≤ ((2 : ℝ)^α)^k / ((2 : ℝ)^α - 1) := geometric_prefix_le _ hq k
        _ ≤ (2*t⁻¹)^α / ((2 : ℝ)^α - 1) := by
          rw [← dyadic_rpow]
          exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hk0.le hk' hα.le)
            (by linarith)
        _ = _ := by
          rw [Real.mul_rpow (by norm_num) (inv_nonneg.mpr ht.le),
            ← Real.rpow_neg_eq_inv_rpow]
          ring
    have hhigh : t^(-3 : ℝ) * ((2 : ℝ)^(α-3))^k ≤ t^(-α) := by
      rw [← dyadic_rpow]
      calc
        _ ≤ t^(-3 : ℝ) * (t⁻¹)^(α-3) :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos (inv_pos.mpr ht)
            hk (by linarith)) (by positivity)
        _ = _ := by
          rw [← Real.rpow_neg_eq_inv_rpow, ← Real.rpow_add ht]
          congr 1
          ring
    rw [← (decay_summable t α ht hα3).sum_add_tsum_nat_add k]
    have htail := (decay_tail_le t α ht hα3 k).trans
      (mul_le_mul_of_nonneg_right hhigh hden.le)
    unfold decayConstant
    nlinarith

theorem two_power_majorant (B : ℝ → ℝ) (C P Q t α β : ℝ)
    (hC : 0 ≤ C) (hP : 0 ≤ P) (hQ : 0 ≤ Q) (ht : 0 < t)
    (hα : 0 < α) (hα3 : α < 3) (hβ : 0 < β) (hβ3 : β < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ C * (P*K^α + Q*K^β)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1 + t*(2 : ℝ)^j)^3) ≤
      C * (P*decayConstant α*t^(-α) + Q*decayConstant β*t^(-β)) := by
  let f (γ : ℝ) (j : ℕ) := ((2 : ℝ)^j)^γ / (1+t*(2 : ℝ)^j)^3
  have hsα : Summable (f α) := decay_summable t α ht hα3
  have hsβ : Summable (f β) := decay_summable t β ht hβ3
  have hs : Summable (fun j => C*(P*f α j+Q*f β j)) :=
    ((hsα.mul_left P).add (hsβ.mul_left Q)).mul_left C
  have hle (j : ℕ) : B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3 ≤
      C*(P*f α j+Q*f β j) := by
    have hi := div_le_div_of_nonneg_right (hB ((2 : ℝ)^j)
      (one_le_pow₀ (by norm_num))) (by positivity : 0 ≤ (1+t*(2 : ℝ)^j)^3)
    dsimp [f]
    convert hi using 1
    ring
  have hsum := hs.of_nonneg_of_le
    (fun j => div_nonneg (hB0 _ (one_le_pow₀ (by norm_num))) (by positivity)) hle
  refine ⟨hsum, (hsum.tsum_le_tsum hle hs).trans ?_⟩
  rw [tsum_mul_left, (hsα.mul_left P).tsum_add (hsβ.mul_left Q), tsum_mul_left,
    tsum_mul_left]
  apply mul_le_mul_of_nonneg_left _ hC
  have h₁ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t α ht hα hα3) hP
  have h₂ := mul_le_mul_of_nonneg_left (dyadic_decay_bound t β ht hβ hβ3) hQ
  dsimp [f] at *
  nlinarith

theorem sieve_growth_majorant (B : ℝ → ℝ) (A N t δ ξ : ℝ)
    (hA : 0 ≤ A) (hN : 0 < N) (ht : 0 < t)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    Summable (fun j : ℕ => B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ∧
    (∑' j : ℕ, B ((2 : ℝ)^j) / (1+t*(2 : ℝ)^j)^3) ≤
      A*N^δ * (N*decayConstant (1/3+δ)*t^(-(1/3+δ)) +
        decayConstant (ξ+δ)*t^(-(ξ+δ))) := by
  have hh := two_power_majorant B (A*N^δ) N 1 t (1/3+δ) (ξ+δ)
    (by positivity) hN.le (by norm_num) ht hα hα3 hβ hβ3 hB0
  simp only [one_mul] at hh
  apply hh
  intro K hK
  have hK0 : 0 < K := lt_of_lt_of_le (by norm_num) hK
  apply (hB K hK).trans_eq
  rw [Real.mul_rpow hK0.le hN.le, Real.rpow_add hK0, Real.rpow_add hK0]
  ring

lemma poisson_scale_identity (M N α : ℝ) (hM : 0 < M) (hN : 0 < N) :
    M/N * (M/N^2)^(-α) = M^(1-α) * N^(2*α-1) := by
  rw [Real.div_rpow hM.le (sq_nonneg N), Real.rpow_neg hM.le,
    Real.rpow_neg (sq_nonneg N), div_inv_eq_mul,
    ← Real.rpow_natCast_mul hN.le 2 α, Real.rpow_sub hM,
    Real.rpow_sub hN, Real.rpow_one, Real.rpow_one]
  norm_num
  ring

lemma poisson_small_power_identity (M N δ β : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^δ * (M/N) * (M/N^2)^(-(β+δ)) =
      N^(3*δ)*M^(-δ)*M^(1-β)*N^(2*β-1) := by
  rw [mul_assoc, poisson_scale_identity M N (β+δ) hM hN]
  calc
    _ = M^(1-(β+δ)) * (N^δ*N^(2*(β+δ)-1)) := by ring
    _ = M^(-δ+(1-β)) * N^(3*δ+(2*β-1)) := by
      rw [← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring
    _ = _ := by rw [Real.rpow_add hM, Real.rpow_add hN]; ring

theorem sieve_poisson_bound (B : ℝ → ℝ) (A M N δ ξ : ℝ)
    (hA : 0 ≤ A) (hM : 0 < M) (hN : 0 < N)
    (hα : 0 < 1/3+δ) (hα3 : 1/3+δ < 3)
    (hβ : 0 < ξ+δ) (hβ3 : ξ+δ < 3)
    (hB0 : ∀ K, 1 ≤ K → 0 ≤ B K)
    (hB : ∀ K, 1 ≤ K → B K ≤ A*(K*N)^δ*(N*K^(1/3 : ℝ)+K^ξ)) :
    (M/N) * (∑' j : ℕ, B ((2 : ℝ)^j) / (1+M*(2 : ℝ)^j/N^2)^3) ≤
      A*N^(3*δ)*M^(-δ) *
        (decayConstant (1/3+δ)*(M*N)^(2/3 : ℝ) +
          decayConstant (ξ+δ)*M^(1-ξ)*N^(2*ξ-1)) := by
  have ht : 0 < M/N^2 := by positivity
  have hh := (sieve_growth_majorant B A N (M/N^2) δ ξ hA hN ht
    hα hα3 hβ hβ3 hB0 hB).2
  have hden : (fun j : ℕ => B ((2 : ℝ)^j)/(1+(M/N^2)*(2 : ℝ)^j)^3) =
      (fun j : ℕ => B ((2 : ℝ)^j)/(1+M*(2 : ℝ)^j/N^2)^3) := by
    funext j
    congr 2
    ring
  rw [hden] at hh
  apply (mul_le_mul_of_nonneg_left hh (div_pos hM hN).le).trans_eq
  have hid₁ := poisson_small_power_identity M N δ (1/3) hM hN
  have hid₂ := poisson_small_power_identity M N δ ξ hM hN
  have hmix : N * M^(1-(1/3 : ℝ)) * N^(2*(1/3 : ℝ)-1) =
      (M*N)^(2/3 : ℝ) := by
    norm_num
    rw [Real.mul_rpow hM.le hN.le]
    have hn' : N * N^(- (1/3 : ℝ)) = N^(2/3 : ℝ) := by
      calc
        _ = N^(1 : ℝ) * N^(-(1/3 : ℝ)) := by rw [Real.rpow_one]
        _ = _ := by rw [← Real.rpow_add hN]; norm_num
    nlinarith [congrArg (fun x => M^(2/3 : ℝ)*x) hn']
  calc
    _ = A*N*decayConstant (1/3+δ)*(N^δ*(M/N)*(M/N^2)^(-(1/3+δ))) +
        A*decayConstant (ξ+δ)*(N^δ*(M/N)*(M/N^2)^(-(ξ+δ))) := by ring
    _ = _ := by
      rw [hid₁, hid₂]
      have he := congrArg (fun x => A*N^(3*δ)*M^(-δ)*decayConstant (1/3+δ)*x) hmix
      nlinarith [he]

lemma descent_factor_le_one (e d u v : ℝ) (he : 1 ≤ e) (hed : e ≤ d)
    (hv : v ≤ 0) (huv : u+v ≤ 0) : e^u*d^v ≤ 1 := by
  have hd : 1 ≤ d := he.trans hed
  by_cases hu : 0 ≤ u
  · calc
      _ ≤ d^u*d^v := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by linarith) hed hu) (by positivity)
      _ = d^(u+v) := (Real.rpow_add (by linarith : 0 < d) u v).symm
      _ ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hd huv
  · exact (mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos he (le_of_not_ge hu))
      (Real.rpow_le_one_of_one_le_of_nonpos hd hv) (by positivity) (by norm_num)).trans_eq
      (one_mul 1)

lemma monomial_descendant_le (M N e d u v : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hv : 0 ≤ v) (huv : 0 ≤ u+v) :
    (M/e)^u*(N/d)^v ≤ M^u*N^v := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  have hg := descent_factor_le_one e d (-u) (-v) he hed (by linarith) (by linarith)
  calc
    _ = (M^u*N^v)*(e^(-u)*d^(-v)) := by
      rw [Real.div_rpow hM.le he0.le, Real.div_rpow hN.le hd0.le,
        Real.rpow_neg he0.le, Real.rpow_neg hd0.le]
      ring
    _ ≤ (M^u*N^v)*1 := mul_le_mul_of_nonneg_left hg (by positivity)
    _ = _ := mul_one _

lemma mixed_monomial_identity (M N δ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) =
      M^(2/3-δ)*N^(2/3+3*δ) := by
  rw [Real.mul_rpow hM.le hN.le]
  calc
    _ = (M^(-δ)*M^(2/3 : ℝ))*(N^(3*δ)*N^(2/3 : ℝ)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma secondary_monomial_identity (M N δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N) :
    N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) =
      M^(1-ξ-δ)*N^(2*ξ-1+3*δ) := by
  calc
    _ = (M^(-δ)*M^(1-ξ))*(N^(3*δ)*N^(2*ξ-1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hM, ← Real.rpow_add hN]
      congr 1 <;> congr 1 <;> ring

lemma mixed_descendant_le (M N e d δ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*((M/e)*(N/d))^(2/3 : ℝ) ≤
      N^(3*δ)*M^(-δ)*(M*N)^(2/3 : ℝ) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [mixed_monomial_identity (M/e) (N/d) δ (div_pos hM he0) (div_pos hN hd0),
    mixed_monomial_identity M N δ hM hN]
  exact monomial_descendant_le M N e d (2/3-δ) (2/3+3*δ) hM hN he hed
    (by linarith) (by linarith)

lemma secondary_descendant_le (M N e d δ ξ : ℝ) (hM : 0 < M) (hN : 0 < N)
    (he : 1 ≤ e) (hed : e ≤ d) (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) :
    (N/d)^(3*δ)*(M/e)^(-δ)*(M/e)^(1-ξ)*(N/d)^(2*ξ-1) ≤
      N^(3*δ)*M^(-δ)*M^(1-ξ)*N^(2*ξ-1) := by
  have he0 : 0 < e := by linarith
  have hd0 : 0 < d := by linarith
  rw [secondary_monomial_identity (M/e) (N/d) δ ξ (div_pos hM he0) (div_pos hN hd0),
    secondary_monomial_identity M N δ ξ hM hN]
  exact monomial_descendant_le M N e d (1-ξ-δ) (2*ξ-1+3*δ) hM hN he hed
    (by linarith) (by linarith)

theorem poisson_envelope_descendant_le (M N e d δ ξ P Q : ℝ)
    (hM : 0 < M) (hN : 0 < N) (he : 1 ≤ e) (hed : e ≤ d)
    (hδ : 0 ≤ δ) (hξ : 1 ≤ ξ) (hP : 0 ≤ P) (hQ : 0 ≤ Q) :
    (N/d)^(3*δ)*(M/e)^(-δ) *
        (P*((M/e)*(N/d))^(2/3 : ℝ) + Q*(M/e)^(1-ξ)*(N/d)^(2*ξ-1)) ≤
      N^(3*δ)*M^(-δ) * (P*(M*N)^(2/3 : ℝ)+Q*M^(1-ξ)*N^(2*ξ-1)) := by
  have hm := mul_le_mul_of_nonneg_left (mixed_descendant_le M N e d δ hM hN he hed hδ) hP
  have hs := mul_le_mul_of_nonneg_left
    (secondary_descendant_le M N e d δ ξ hM hN he hed hδ hξ) hQ
  nlinarith [hm, hs]

end
end SevenEighths.CubicDyadicDecay

end OAI
end OAIOriginalModule0003

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Algebra
Source SHA256: 1bbf98bbbd1c4ebc573dd6c53013e518d0d0c97897116bcd4eb96affdde07d38
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0004







namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_inv_eq_square (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) :
    χ⁻¹ = χ ^ 2 := by
  calc
    χ⁻¹ = χ⁻¹ * χ ^ 3 := by rw [hχ, mul_one]
    _ = χ ^ 2 := by group

theorem cubic_square_eq_star (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 2 = star (χ x) := by
  rw [MulChar.star_apply', cubic_inv_eq_square χ hχ, MulChar.pow_apply' _ (by decide)]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

omit [Finite Rˣ] in
theorem cubic_cube_eq_mask (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ (x ^ 3) = if IsUnit x then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ]
  by_cases hx : IsUnit x
  · rw [ite_eq_left hx, MulChar.one_apply hx]
  · rw [ite_eq_right hx, MulChar.map_nonunit _ hx]

theorem cubic_row_decomposition (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1)
    (a b c : R) :
    χ (a * b ^ 2 * c ^ 3) =
      χ a * star (χ b) * (if IsUnit c then 1 else 0) := by
  rw [map_mul, map_mul, map_pow, cubic_square_eq_star χ hχ,
    cubic_cube_eq_mask χ hχ]

omit [Finite Rˣ] in
theorem cubic_norm_le_one (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have hc : χ x ^ 3 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ, MulChar.one_apply hx]
    exact (Complex.norm_eq_one_of_pow_eq_one hc (by decide)).le
  · rw [MulChar.map_nonunit _ hx, norm_zero]
    exact zero_le_one

theorem row_decomposition_sum {ι M : Type*} [CommMonoid M]
    (S : Finset ι) (coef : ι → ℂ) (ρ : ι → M →* R)
    (χ : ι → MulChar R ℂ) (hχ : ∀ n ∈ S, χ n ^ 3 = 1)
    (a b c : M) :
    (∑ n ∈ S, coef n * χ n (ρ n (a * b ^ 2 * c ^ 3))) =
      ∑ n ∈ S,
        (coef n * star (χ n (ρ n b)) *
          (if IsUnit (ρ n c) then 1 else 0)) * χ n (ρ n a) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  have hmap : ρ n (a * b ^ 2 * c ^ 3) =
      ρ n a * (ρ n b) ^ 2 * (ρ n c) ^ 3 := by simp only [map_mul, map_pow]
  rw [hmap, cubic_row_decomposition (χ n) (hχ n hn)]
  ring

omit [Finite Rˣ] in
theorem extracted_coefficients_energy_le {ι : Type*}
    (S : Finset ι) (coef : ι → ℂ) (χ : ι → MulChar R ℂ)
    (hχ : ∀ n ∈ S, χ n ^ 3 = 1) (b c : ι → R) :
    (∑ n ∈ S, ‖coef n * star (χ n (b n)) *
      (if IsUnit (c n) then (1 : ℂ) else 0)‖ ^ 2) ≤
      ∑ n ∈ S, ‖coef n‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : IsUnit (c n)
  · simp only [ite_eq_left hc, mul_one, norm_mul, norm_star]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_right (norm_nonneg _) (cubic_norm_le_one (χ n) (hχ n hn) _)
  · simp only [ite_eq_right hc, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0004

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Factorization
Source SHA256: fbdf1b9b8d00a6babd8cc925a9c65b069ae80c4471135981b8b1147e4ccb6a16
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0005




namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p

def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p

def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)

theorem count_mod_three (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  have h := Nat.mod_add_div k 3
  have hlt := Nat.mod_lt k (by decide : 0 < 3)
  split_ifs <;> omega

omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree

omit [Subsingleton Mˣ] in
theorem firstPart_squarefree (x : M) : Squarefree (firstPart x) :=
  residual_squarefree x 1

omit [Subsingleton Mˣ] in
theorem secondPart_squarefree (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2

omit [Subsingleton Mˣ] in
theorem residual_parts_isRelPrime (x : M) : IsRelPrime (firstPart x) (secondPart x) := by
  unfold firstPart secondPart
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  apply (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp'.1)).isRelPrime_iff_not_dvd.mpr
  intro hd
  have heq := normalizedFactors_eq_of_dvd x p (Multiset.mem_toFinset.mp hp'.1)
    q (Multiset.mem_toFinset.mp hq'.1) hd
  subst q
  omega

theorem cubic_factorization (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hp : (∏ p ∈ (normalizedFactors x).toFinset,
      p ^ (normalizedFactors x).count p) = x := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp (prod_normalizedFactors hx)
  have hper (p : M) : p ^ (normalizedFactors x).count p =
      (if (normalizedFactors x).count p % 3 = 1 then p else 1) *
      (if (normalizedFactors x).count p % 3 = 2 then p else 1) ^ 2 *
      (p ^ ((normalizedFactors x).count p / 3)) ^ 3 := by
    conv_lhs => rw [count_mod_three ((normalizedFactors x).count p)]
    rw [pow_add, pow_add, Nat.mul_comm 3, pow_mul]
    split_ifs <;> simp [pow_mul]
  calc
    x = ∏ p ∈ (normalizedFactors x).toFinset,
        p ^ (normalizedFactors x).count p := hp.symm
    _ = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
      simp_rw [hper]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [firstPart, secondPart, cubePart, Finset.prod_filter]

theorem extraction_injective_on_nonzero :
    Set.InjOn (fun x : M => (firstPart x, secondPart x, cubePart x)) {x | x ≠ 0} := by
  intro x hx y hy h
  have h1 := congrArg (fun t : M × M × M => t.1) h
  have h2 := congrArg (fun t : M × M × M => t.2.1) h
  have h3 := congrArg (fun t : M × M × M => t.2.2) h
  dsimp only at h1 h2 h3
  rw [cubic_factorization x hx, cubic_factorization y hy, h1, h2, h3]

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0005

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Operator
Source SHA256: 45c1fea54b94c93894139673096df9080057485c2e6a1ea319a7d76e16d49612
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0006



namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def operator (A : Matrix m n ℂ) : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ m :=
  A.toEuclideanLin.toContinuousLinearMap

omit [DecidableEq m] in
@[simp] theorem operator_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) (i : m) :
    operator A x i = ∑ j, A i j * x j := rfl

def squaredNorm (A : Matrix m n ℂ) : ℝ := ‖operator A‖ ^ 2

def conjugateVector (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun j => star (x j))

omit [Fintype n] [DecidableEq n] in
@[simp] theorem conjugateVector_apply (x : EuclideanSpace ℂ n) (j : n) :
    conjugateVector x j = star (x j) := rfl

omit [DecidableEq n] in
@[simp] theorem norm_conjugateVector (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector_apply, norm_star]

omit [DecidableEq m] in
theorem operator_conjugate_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq m] in
theorem operator_conjugate_norm_le (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector] using (operator A).le_opNorm (conjugateVector x)

omit [DecidableEq m] in
theorem operator_conjugate_norm (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  apply le_antisymm (operator_conjugate_norm_le A)
  simpa only [star_star] using operator_conjugate_norm_le (fun i j => star (A i j))

theorem operator_conjTranspose_norm (A : Matrix m n ℂ) :
    ‖operator A.conjTranspose‖ = ‖operator A‖ := by
  have heq : operator A.conjTranspose = (operator A).adjoint := by
    unfold operator
    rw [Matrix.toEuclideanLin_conjTranspose_eq_adjoint, LinearMap.adjoint_toContinuousLinearMap]
  rw [heq]
  exact ContinuousLinearMap.adjoint.norm_map _

theorem squaredNorm_transpose (A : Matrix m n ℂ) :
    squaredNorm A.transpose = squaredNorm A := by
  unfold squaredNorm
  have h := operator_conjugate_norm A.transpose
  change ‖operator A.conjTranspose‖ = ‖operator A.transpose‖ at h
  rw [operator_conjTranspose_norm] at h
  exact congrArg (fun x : ℝ => x ^ 2) h.symm

theorem squaredNorm_reciprocity (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (hrecip : ∀ i j, A i j = B j i) : squaredNorm A = squaredNorm B := by
  have h : A = B.transpose := by ext i j; exact hrecip i j
  rw [h, squaredNorm_transpose]

omit [DecidableEq m] in
theorem energy_le_squaredNorm (A : Matrix m n ℂ) (c : n → ℂ) :
    (∑ i, ‖∑ j, A i j * c j‖ ^ 2) ≤ squaredNorm A * ∑ j, ‖c j‖ ^ 2 := by
  let x : EuclideanSpace ℂ n := WithLp.toLp 2 c
  have h := (operator A).le_opNorm x
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  simpa only [squaredNorm, mul_pow, EuclideanSpace.norm_sq_eq, operator_apply, x] using hs

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0006

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.Blocks
Source SHA256: 3b1eabe72ead4d84320af63d0a587e8f70a8107b92a4f47639649f7418d8c89d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0007



namespace OAI

namespace SevenEighths.CubicSieve
open scoped BigOperators
noncomputable section

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]

theorem squaredNorm_nonneg (A : Matrix a n ℂ) : 0 ≤ squaredNorm A := sq_nonneg _

theorem masked_energy_le (A : Matrix a n ℂ) (coef phase : n → ℂ)
    (hphase : ∀ j, ‖phase j‖ ≤ 1) :
    (∑ i, ‖∑ j, A i j * (coef j * phase j)‖ ^ 2) ≤
      squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
  apply (energy_le_squaredNorm A (fun j => coef j * phase j)).trans
  apply mul_le_mul_of_nonneg_left _ (squaredNorm_nonneg A)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase j)

theorem rectangular_block_energy_le
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef mask : n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ j, ‖mask j‖ ≤ 1) :
    (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
      min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  have hleft :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card b : ℝ) * squaredNorm A) * ∑ j, ‖coef j‖ ^ 2 := by
    calc
      _ ≤ ∑ k : b, squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h := masked_energy_le A coef (fun j => star (B k j) * mask j) (by
          intro j
          rw [norm_mul, norm_star]
          exact (mul_le_mul_of_nonneg_right (hB k j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by simp [mul_assoc]
  have hright :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : a, squaredNorm (fun k j => star (B k j)) * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := masked_energy_le (fun k j => star (B k j)) coef
          (fun j => A i j * mask j) (by
            intro j
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        have hn : squaredNorm (fun k j => star (B k j)) = squaredNorm B := by
          unfold squaredNorm
          rw [operator_conjugate_norm]
        rw [hn]
        simp [mul_assoc]
  rcases le_total ((Fintype.card b : ℝ) * squaredNorm A)
      ((Fintype.card a : ℝ) * squaredNorm B) with h | h
  · rw [min_eq_left h]
    exact hleft
  · rw [min_eq_right h]
    exact hright

theorem cube_family_block_energy_le {c : Type*} [Fintype c]
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef : n → ℂ) (mask : c → n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ l j, ‖mask l j‖ ≤ 1) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask l j‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm A)
          ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  calc
    _ ≤ ∑ l : c, min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact rectangular_block_energy_le A B coef (mask l) hA hB (hmask l)
    _ = _ := by simp [mul_assoc]

end
end SevenEighths.CubicSieve

end OAI
end OAIOriginalModule0007

/-! Original module: OAI.NumberTheory.DirichletL.Descent.Basic
Source SHA256: 1378e578d6059a8499e4619e162d1ca7ea94e5b08cf1f80b94a5dfe580983cf6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0008





namespace OAI

namespace SevenEighths.InverseMoment

def MarkedMargins (m r z c : ℝ) : Prop :=
  r + 2 * z ≤ m - c ∧ 2 * r + 8 * z ≤ 3 * m - c

def CanonicalMargins (F M Q z c : ℝ) : Prop :=
  c ≤ F - M - Q - z ∧ c ≤ 4 * F - 3 * M - 6 * z

theorem markedMargins_of_strict {m r z : ℝ}
    (h₁ : r + 2 * z < m) (h₂ : 2 * r + 8 * z < 3 * m) :
    ∃ c > 0, MarkedMargins m r z c := by
  refine ⟨min (m - r - 2 * z) (3 * m - 2 * r - 8 * z), ?_, ?_⟩
  · exact lt_min (by linarith) (by linarith)
  · constructor
    · have := min_le_left (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith
    · have := min_le_right (m - r - 2 * z) (3 * m - 2 * r - 8 * z)
      linarith

theorem markedMargins_subcollection {m r z z' c : ℝ}
    (h : MarkedMargins m r z c) (hz : z' ≤ z) :
    MarkedMargins m r z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_subcollection {F M Q z z' c : ℝ}
    (h : CanonicalMargins F M Q z c) (hz : z' ≤ z) :
    CanonicalMargins F M Q z' c := by
  obtain ⟨h₁, h₂⟩ := h
  constructor <;> linarith

theorem canonicalMargins_weaken {F M Q z c c' : ℝ}
    (h : CanonicalMargins F M Q z c) (hc : c' ≤ c) :
    CanonicalMargins F M Q z c' := by
  exact ⟨hc.trans h.1, hc.trans h.2⟩

def decrease (ell A t g theta V : ℝ) : ℝ := ell + A + t + g - theta + V

def childF (F ell A t g theta V j delta : ℝ) : ℝ :=
  F - decrease ell A t g theta V - 2 * ell + j + delta

def childM (M ell A t g theta V j eta : ℝ) : ℝ :=
  M - 2 * decrease ell A t g theta V - 2 * ell + j + eta

theorem canonical_transition (F M ell A t g theta V j : ℝ) :
    childF F ell A t g theta V j 0 - childM M ell A t g theta V j 0 =
      F - M + decrease ell A t g theta V ∧
    4 * childF F ell A t g theta V j 0 -
      3 * childM M ell A t g theta V j 0 =
      4 * F - 3 * M + 2 * (A + t + g - theta + V) + j := by
  constructor <;> unfold childF childM decrease <;> ring

theorem child_margins_sharp {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    c + delta - 5 * eta ≤
      childF F ell A t g theta V j delta -
      childM M ell A t g theta V j eta - Q' - z ∧
    c + 4 * delta - 7 * eta ≤
      4 * childF F ell A t g theta V j delta -
      3 * childM M ell A t g theta V j eta - 6 * z := by
  obtain ⟨h₁, h₂⟩ := h
  unfold childF childM decrease at *
  constructor <;> linarith

theorem child_margins {F M Q Q' z c ell A t g theta V j delta eta : ℝ}
    (h : CanonicalMargins F M Q z c)
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hV : 0 ≤ V) (hj : 0 ≤ j)
    (hgt : -2 * eta ≤ g - theta) (hdelta : 0 ≤ delta) (heta : 0 ≤ eta)
    (hQ : Q' ≤ Q + decrease ell A t g theta V + 4 * eta) :
    CanonicalMargins (childF F ell A t g theta V j delta)
      (childM M ell A t g theta V j eta) Q' z (c - 7 * eta) := by
  obtain ⟨h₁, h₂⟩ := child_margins_sharp (delta := delta) h hA ht hV hj hgt hQ
  constructor <;> linarith

theorem child_row_decrease {M ell A t g theta V j eta d : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hgt : -2 * eta ≤ g - theta)
    (hj : j ≤ 2 * ell + 3 * eta) (hterminal : d ≤ ell + V)
    (heta : eta ≤ d / 16) :
    3 * d / 2 ≤ M - childM M ell A t g theta V j eta := by
  unfold childM decrease
  linarith

theorem childF_upper {F ell A t g theta V j delta eta : ℝ}
    (hA : 0 ≤ A) (ht : 0 ≤ t) (hell : 0 ≤ ell) (hV : 0 ≤ V)
    (hgt : -2 * eta ≤ g - theta) (hj : j ≤ 2 * ell + 3 * eta)
    (hdelta : delta ≤ 6 * eta) :
    childF F ell A t g theta V j delta ≤ F + 11 * eta := by
  unfold childF decrease
  linarith

theorem clipping_bounds {N eta : ℝ} (heta : 0 ≤ eta) (hN : -6 * eta ≤ N) :
    0 ≤ max 0 N - N ∧ max 0 N - N ≤ 6 * eta := by
  constructor
  · exact sub_nonneg.mpr (le_max_right 0 N)
  · rcases le_total 0 N with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; linarith

theorem step_energy_exponent {F Fc kappa lambda count delta eta tau pi eps : ℝ}
    (hid : kappa + lambda + count + 2 * Fc = F)
    (hdelta : delta ≤ 6 * eta) :
    kappa + lambda + count + 2 * (Fc + delta) +
      (9 / 2 + 18 + 11 / 2) * eta + tau + pi + eps ≤
      F + 40 * eta + tau + pi + eps := by
  linarith

def initialF (r z G P delta : ℝ) : ℝ := r + z - 2 * G - P + delta

def initialM (m r z G P eta tau : ℝ) : ℝ :=
  2 * (r + z - 2 * G) - m - 2 * P + 6 * eta + tau

theorem initial_margins_sharp {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta) :
    c₁ + delta - 9 * eta - tau ≤
      initialF r z G P delta - initialM m r z G P eta tau - Q - (z - G) ∧
    c₂ + 4 * delta - 22 * eta - 3 * tau ≤
      4 * initialF r z G P delta - 3 * initialM m r z G P eta tau -
        6 * (z - G) := by
  unfold initialF initialM
  constructor <;> linarith

theorem initial_margins {m r z G P delta eta tau Q c₁ c₂ : ℝ}
    (h₁ : r + 2 * z ≤ m - c₁) (h₂ : 2 * r + 8 * z ≤ 3 * m - c₂)
    (hG : 0 ≤ G) (hP : -2 * eta ≤ P) (hQ : Q ≤ P + G + 3 * eta)
    (hc : 0 ≤ min c₁ c₂) (hdelta : 0 ≤ delta) (heta : eta ≤ min c₁ c₂ / 100)
    (htau : tau ≤ min c₁ c₂ / 100) :
    CanonicalMargins (initialF r z G P delta)
      (initialM m r z G P eta tau) Q (z - G) (3 * min c₁ c₂ / 4) := by
  obtain ⟨ha, hb⟩ := initial_margins_sharp (delta := delta) (tau := tau) h₁ h₂ hG hP hQ
  have hc₁ := min_le_left c₁ c₂
  have hc₂ := min_le_right c₁ c₂
  constructor <;> linarith

theorem initial_prefactor_identity (m r z G P : ℝ) :
    (m - 2 * (r + z - 2 * G) + P) + P +
      2 * initialF r z G P 0 = m := by
  unfold initialF
  ring

theorem initial_energy_exponent {m delta eta pi eps : ℝ}
    (hdelta : delta ≤ 3 * eta) :
    m + 3 * eta + 2 * eta + 2 * delta + pi + eps ≤
      m + 11 * eta + pi + eps := by
  linarith

theorem total_step_loss {D eta tau pi eps : ℝ}
    (h₁ : D * eta ≤ eps / 160) (h₂ : D * tau ≤ eps / 4)
    (h₃ : D * pi ≤ eps / 4) :
    D * (40 * eta + tau + pi) ≤ 3 * eps / 4 := by
  nlinarith

theorem depth_margin {c D h eta : ℝ} (heta : 0 ≤ eta) (hh : h ≤ D)
    (hbudget : D * eta ≤ c / 14) : c / 2 ≤ c - 7 * h * eta := by
  have := mul_le_mul_of_nonneg_right hh heta
  nlinarith

end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0008

/-! Original module: OAI.NumberTheory.DirichletL.Descent.Fibers
Source SHA256: 38ac7b73def855c0a02500fc65fb8160265733a04e2a77a864b4b7c1351ee187
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0009





namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

def weightedEnergy {ι : Type*} (s : Finset ι) (w : ι → ℝ) (f : ι → ℂ) : ℝ :=
  ∑ i ∈ s, w i * ‖f i‖ ^ 2

theorem weightedEnergy_nonneg {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) : 0 ≤ weightedEnergy s w f := by
  exact Finset.sum_nonneg fun i hi => mul_nonneg (hw i hi) (sq_nonneg _)

theorem weighted_cauchy {ι : Type*} (s : Finset ι) (w : ι → ℝ)
    (f g : ι → ℂ) (hw : ∀ i ∈ s, 0 ≤ w i) :
    ‖∑ i ∈ s, (w i : ℂ) * f i * star (g i)‖ ≤
      Real.sqrt (weightedEnergy s w f) * Real.sqrt (weightedEnergy s w g) := by
  have hf : ∑ i ∈ s, (Real.sqrt (w i) * ‖f i‖) ^ 2 = weightedEnergy s w f := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  have hg : ∑ i ∈ s, (Real.sqrt (w i) * ‖g i‖) ^ 2 = weightedEnergy s w g := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [mul_pow, Real.sq_sqrt (hw i hi)]
  calc
    ‖∑ i ∈ s, (w i : ℂ) * f i * star (g i)‖ ≤
        ∑ i ∈ s, ‖(w i : ℂ) * f i * star (g i)‖ := norm_sum_le _ _
    _ = ∑ i ∈ s, (Real.sqrt (w i) * ‖f i‖) * (Real.sqrt (w i) * ‖g i‖) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hw i hi)]
      calc
        w i * ‖f i‖ * ‖g i‖ =
            (Real.sqrt (w i) * Real.sqrt (w i)) * ‖f i‖ * ‖g i‖ := by
          rw [Real.mul_self_sqrt (hw i hi)]
        _ = _ := by ring
    _ ≤ Real.sqrt (weightedEnergy s w f) * Real.sqrt (weightedEnergy s w g) := by
      simpa only [hf, hg] using Real.sum_mul_le_sqrt_mul_sqrt s
        (fun i => Real.sqrt (w i) * ‖f i‖) (fun i => Real.sqrt (w i) * ‖g i‖)

theorem fiber_energy_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D E : κ → ℝ) (hp : ∀ i ∈ s, p i ∈ t)
    (hE : ∀ j ∈ t, 0 ≤ E j)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ∑ i ∈ s, w i * E (p i) ≤ ∑ j ∈ t, D j * E j := by
  calc
    ∑ i ∈ s, w i * E (p i) =
        ∑ j ∈ t, ∑ i ∈ s with p i = j, w i * E (p i) :=
      (Finset.sum_fiberwise_of_maps_to hp _).symm
    _ = ∑ j ∈ t, (∑ i ∈ s with p i = j, w i) * E j := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [(Finset.mem_filter.mp hi).2]
    _ ≤ ∑ j ∈ t, D j * E j :=
      Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hD j hj) (hE j hj)

theorem weightedEnergy_fiber_bound {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    weightedEnergy s w (f ∘ p) ≤ weightedEnergy t D f := by
  exact fiber_energy_bound s t p w D (fun j => ‖f j‖ ^ 2) hp
    (fun j _ => sq_nonneg _) hD

theorem weighted_cauchy_fiber {ι κ : Type*} [DecidableEq κ]
    (s : Finset ι) (t : Finset κ) (p : ι → κ) (w : ι → ℝ)
    (D : κ → ℝ) (f g : κ → ℂ) (hp : ∀ i ∈ s, p i ∈ t)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hD : ∀ j ∈ t, ∑ i ∈ s with p i = j, w i ≤ D j) :
    ‖∑ i ∈ s, (w i : ℂ) * f (p i) * star (g (p i))‖ ≤
      Real.sqrt (weightedEnergy t D f) * Real.sqrt (weightedEnergy t D g) := by
  apply (weighted_cauchy s w (f ∘ p) (g ∘ p) hw).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D f hp hD))
    (Real.sqrt_le_sqrt (weightedEnergy_fiber_bound s t p w D g hp hD))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem finite_expansion_energy {κ ι : Type*} [DecidableEq ι]
    (rows : Finset κ) (terms : Finset ι) (active : κ → Finset ι)
    (w F : κ → ι → ℂ) (C : ℝ)
    (hsub : ∀ k ∈ rows, active k ⊆ terms)
    (hw : ∀ k ∈ rows, ∀ i ∈ active k, ‖w k i‖ ≤ 1)
    (hcard : ∀ k ∈ rows, ((active k).card : ℝ) ≤ C) :
    (∑ k ∈ rows, ‖∑ i ∈ active k, w k i * F k i‖ ^ 2) ≤
      C * ∑ i ∈ terms, ∑ k ∈ rows, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
  have hlocal (k : κ) (hk : k ∈ rows) :
      ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        C * ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
    have hb : ‖∑ i ∈ active k, w k i * F k i‖ ^ 2 ≤
        ((active k).card : ℝ) * ∑ i ∈ active k, ‖w k i * F k i‖ ^ 2 := by
      calc
        _ ≤ (∑ i ∈ active k, ‖w k i * F k i‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ _ := by
          simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
            Finset.sum_mul_sq_le_sq_mul_sq (active k) (fun _ => (1 : ℝ))
              (fun i => ‖w k i * F k i‖)
    have hsum : (∑ i ∈ active k, ‖w k i * F k i‖ ^ 2) ≤
        ∑ i ∈ active k, ‖F k i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i hi
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hw k hk i hi)
    exact hb.trans (mul_le_mul (hcard k hk) hsum
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (le_trans (Nat.cast_nonneg _) (hcard k hk)))
  calc
    _ ≤ ∑ k ∈ rows, C * ∑ i ∈ active k, ‖F k i‖ ^ 2 :=
      Finset.sum_le_sum hlocal
    _ = C * ∑ k ∈ rows, ∑ i ∈ active k, ‖F k i‖ ^ 2 := by rw [Finset.mul_sum]
    _ = C * ∑ k ∈ rows, ∑ i ∈ terms, if i ∈ active k then ‖F k i‖ ^ 2 else 0 := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      rw [← Finset.sum_filter]
      congr 1
      ext i
      simp only [Finset.mem_filter]
      exact ⟨fun hi => ⟨hsub k hk hi, hi⟩, And.right⟩
    _ = _ := by rw [Finset.sum_comm]

end

end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0009

/-! Original module: OAI.NumberTheory.DirichletL.Descent.LocalReflection
Source SHA256: 119edaab53aa2758c20702d14fef80aebe43c68072589e430d931dc1f9ca5afc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0010




namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators Classical

noncomputable section

variable {F : Type*} [Field F] [Fintype F]

def zeroMark (x : F) : ℂ := if x = 0 then 1 else 0

def localFourier (f : F → ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ t : F, f t * ψ (-(h * t))

theorem localFourier_zeroMark (ψ : AddChar F ℂ) (h : F) :
    localFourier zeroMark ψ h = 1 := by
  simp [localFourier, zeroMark]

theorem localFourier_trivial_nonzero (ψ : AddChar F ℂ)
    (hψ : ψ.IsPrimitive) (h : F) (hh : h ≠ 0) :
    localFourier (fun t => (1 : MulChar F ℂ) t) ψ h = -1 := by
  have he := gaussSum_one_left (hψ (neg_ne_zero.mpr hh))
  simpa only [gaussSum, AddChar.mulShift_apply, neg_mul, localFourier] using he

omit [Fintype F] in
theorem zeroMark_complement (x : F) :
    zeroMark x = 1 - (1 : MulChar F ℂ) x := by
  by_cases hx : x = 0
  · simp [zeroMark, hx, MulChar.map_zero]
  · rw [zeroMark, ite_eq_right hx, MulChar.one_apply (isUnit_iff_ne_zero.mpr hx)]
    ring

def localReflectionActive (f : F → ℂ) (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (σ ε : Fˣ) (x : F) : ℂ :=
  (Fintype.card F : ℂ)⁻¹ * ∑ h : Fˣ,
    localFourier f ψ h * ((χ⁻¹) ^ 2) (σ * h) *
      ψ (((ε : F) * x) * ((h⁻¹ : Fˣ) : F))

theorem marked_active_eq_neg_trivial (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive (fun t => (1 : MulChar F ℂ) t) χ ψ σ ε x := by
  unfold localReflectionActive
  rw [← mul_neg, ← Finset.sum_neg_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  rw [localFourier_zeroMark, localFourier_trivial_nonzero ψ hψ h (Units.ne_zero h)]
  ring

theorem marked_inactive_coefficient (ψ : AddChar F ℂ) :
    (Fintype.card F : ℂ)⁻¹ * localFourier zeroMark ψ 0 =
      (Fintype.card F : ℂ)⁻¹ := by
  rw [localFourier_zeroMark, mul_one]

end

end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0010

/-! Original module: OAI.NumberTheory.DirichletL.Descent.Marks
Source SHA256: c532c5c180a77984acb6aaae8b602846bcf41222276cfe6c0125b335bba30a64
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0011




namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators

noncomputable section

variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def primeSlot (L : Finset ι) (a : ι → ℂ) (A : Finset ι) : ℂ :=
  ∑ p ∈ L, if p ∈ A then a p else 0

def primeMark (I : Finset σ) (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : ℂ := ∏ i ∈ I, primeSlot (L i) (a i) A

omit [DecidableEq σ] in
@[simp] theorem primeMark_empty (L : σ → Finset ι) (a : σ → ι → ℂ)
    (A : Finset ι) : primeMark ∅ L a A = 1 := by
  simp [primeMark]

theorem primeMark_eq_tuple_sum (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ p ∈ I.pi L,
      ∏ i ∈ I.attach, if p i.1 i.2 ∈ A then a i.1 (p i.1 i.2) else 0 := by
  exact Finset.prod_sum I L (fun i p => if p ∈ A then a i p else 0)

theorem primeSlot_priority (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (A ∪ B) = primeSlot L a A + primeSlot L a (B \ A) := by
  unfold primeSlot
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hA : p ∈ A <;> by_cases hB : p ∈ B <;> simp [hA, hB]

theorem primeMark_priority (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (A ∪ B) =
      ∑ J ∈ I.powerset, primeMark J L a A * primeMark (I \ J) L a (B \ A) := by
  unfold primeMark
  simp_rw [primeSlot_priority]
  exact Finset.prod_add _ _ I

theorem primeSlot_residual_list (L A B : Finset ι) (a : ι → ℂ) :
    primeSlot L a (B \ A) = primeSlot (L \ A) a B := by
  simp only [primeSlot, Finset.sum_ite_mem]
  congr 1
  ext p
  simp only [Finset.mem_inter, Finset.mem_sdiff]
  tauto

omit [DecidableEq σ] in
theorem primeMark_residual_lists (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A B : Finset ι) :
    primeMark I L a (B \ A) = primeMark I (fun i => L i \ A) a B := by
  unfold primeMark
  apply Finset.prod_congr rfl
  intro i hi
  exact primeSlot_residual_list _ _ _ _

theorem primeSlot_norm_le (L A : Finset ι) (a : ι → ℂ)
    (ha : ∀ p ∈ L, ‖a p‖ ≤ 1) :
    ‖primeSlot L a A‖ ≤ ((L ∩ A).card : ℝ) := by
  simp only [primeSlot, Finset.sum_ite_mem]
  apply (norm_sum_le _ _).trans
  calc
    ∑ p ∈ L ∩ A, ‖a p‖ ≤ ∑ p ∈ L ∩ A, (1 : ℝ) :=
      Finset.sum_le_sum fun p hp => ha p (Finset.mem_inter.mp hp).1
    _ = _ := by simp

omit [DecidableEq σ] in
theorem primeMark_norm_le_divisor_count (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι)
    (hL : (I : Set σ).PairwiseDisjoint L)
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) :
    ‖primeMark I L a A‖ ≤ (2 : ℝ) ^ A.card := by
  have hdis : (I : Set σ).PairwiseDisjoint (fun i => L i ∩ A) := by
    intro i hi j hj hij
    exact (hL hi hj hij).mono (Finset.inter_subset_left) (Finset.inter_subset_left)
  have hcard : (∑ i ∈ I, (L i ∩ A).card) ≤ A.card := by
    rw [← Finset.card_biUnion hdis]
    apply Finset.card_le_card
    intro p hp
    obtain ⟨i, hi, hp⟩ := Finset.mem_biUnion.mp hp
    exact (Finset.mem_inter.mp hp).2
  calc
    ‖primeMark I L a A‖ = ∏ i ∈ I, ‖primeSlot (L i) (a i) A‖ := by
      exact norm_prod _ _
    _ ≤ ∏ i ∈ I, ((L i ∩ A).card : ℝ) := by
      exact Finset.prod_le_prod₀ (fun i _ => norm_nonneg _)
        (fun i hi => primeSlot_norm_le _ _ _ (ha i hi))
    _ ≤ ∏ i ∈ I, (2 : ℝ) ^ (L i ∩ A).card := by
      apply Finset.prod_le_prod₀ (fun i _ => Nat.cast_nonneg _)
      intro i hi
      exact_mod_cast (Nat.le_of_lt (L i ∩ A).card.lt_two_pow_self)
    _ = (2 : ℝ) ^ (∑ i ∈ I, (L i ∩ A).card) :=
      Finset.prod_pow_eq_pow_sum _ _ _
    _ ≤ (2 : ℝ) ^ A.card := pow_le_pow_right₀ (by norm_num) hcard

end

end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0011

/-! Original module: OAI.NumberTheory.DirichletL.Descent.Overlap
Source SHA256: a897c61cde304bad337851945d5dd1f47c75d80aaa8f2519cb65d5da31fc6166
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0012





namespace OAI

namespace SevenEighths.InverseMoment

open UniqueFactorizationMonoid

section Moebius

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem moebius_squarefree_sq {P : M} (hP : Squarefree P) :
    moebius P ^ 2 = 1 := by
  rw [hP.moebius_eq, ← pow_mul, mul_comm _ 2, pow_mul]
  norm_num

theorem moebius_overlap_recovery {n P : M} (hnP : IsRelPrime n P)
    (hP : Squarefree P) : moebius n = moebius (n * P) * moebius P := by
  rw [hnP.moebius_mul, mul_assoc, ← pow_two, moebius_squarefree_sq hP, mul_one]

theorem moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by
  have hμ : (moebius n₀ : ℂ) = (moebius (n₀ * P₀) : ℂ) * (moebius P₀ : ℂ) := by
    exact_mod_cast moebius_overlap_recovery hnP hP
  rw [hjn.moebius_mul, Int.cast_mul, map_mul, map_mul, map_mul, hμ]
  ring

theorem hybrid_mask_quotients {k P c R r : M}
    (hk : Squarefree k) (hP : Squarefree P) (hc : Squarefree c)
    (hPc : IsRelPrime P c) (hRk : R ∣ k) (hrk : r ∣ k)
    (hRP : R ∣ P) (hrc : r ∣ c) :
    ∃ k' P' c' : M,
      k = (R * r) * k' ∧ P = R * P' ∧ c = r * c' ∧
      IsRelPrime R r ∧ IsRelPrime k' (R * r) ∧
      IsRelPrime P' R ∧ IsRelPrime c' r ∧
      Squarefree k' ∧ Squarefree P' ∧ Squarefree c' := by
  have hRr : IsRelPrime R r := (hPc.of_dvd_left hRP).of_dvd_right hrc
  obtain ⟨k', hk'⟩ := hRr.mul_dvd hRk hrk
  obtain ⟨P', hP'⟩ := hRP
  obtain ⟨c', hc'⟩ := hrc
  have hks : Squarefree ((R * r) * k') := hk' ▸ hk
  have hPs : Squarefree (R * P') := hP' ▸ hP
  have hcs : Squarefree (r * c') := hc' ▸ hc
  obtain ⟨hkrel, _, hksf⟩ := squarefree_mul_iff.mp hks
  obtain ⟨hPrel, _, hPsf⟩ := squarefree_mul_iff.mp hPs
  obtain ⟨hcrel, _, hcsf⟩ := squarefree_mul_iff.mp hcs
  exact ⟨k', P', c', hk', hP', hc', hRr, hkrel.symm,
    hPrel.symm, hcrel.symm, hksf, hPsf, hcsf⟩

end Moebius

theorem inverse_eq_square_of_fourth_eq {z : ℂ} (hz : z ^ 4 = z) :
    z⁻¹ = z ^ 2 := by
  by_cases hzero : z = 0
  · simp [hzero]
  have hcube : z ^ 3 = 1 := by
    apply mul_left_cancel₀ hzero
    calc
      z * z ^ 3 = z ^ 4 := by ring
      _ = z := hz
      _ = z * 1 := by ring
  calc
    z⁻¹ = z⁻¹ * z ^ 3 := by rw [hcube, mul_one]
    _ = z ^ 2 := by field_simp

theorem inverse_cube_square_eq_sixth {z : ℂ} (h : z ^ 6 = 0 ∨ z ^ 6 = 1) :
    ((z ^ 3)⁻¹) ^ 2 = z ^ 6 := by
  rw [← inv_pow, ← pow_mul]
  norm_num
  rcases h with h | h <;> rw [h] <;> norm_num

theorem inverse_square_cube_mask {M : Type*} [Monoid M]
    (ψ : M →* ℂ) (n b : M) (h : ψ b ^ 6 = 0 ∨ ψ b ^ 6 = 1) :
    (ψ (n * b ^ 3))⁻¹ ^ 2 = (ψ n)⁻¹ ^ 2 * ψ b ^ 6 := by
  rw [map_mul, map_pow, mul_inv_rev, mul_pow, inverse_cube_square_eq_sixth h]
  ring

theorem overlap_scalar_norm_le {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖z ^ 2‖ ≤ 1 := by
  rw [norm_pow]
  simpa using pow_le_pow_left₀ (norm_nonneg z) hz 2

end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0012

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SieveComposition
Source SHA256: 6a1e1412238aec2351cc16f6ed1616a8fe3b4f9a00c6fa0934ea034b090b2e9d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0013



namespace OAI

namespace SevenEighths.InverseMoment

open scoped BigOperators
noncomputable section

theorem bounded_finset_coefficient_sum_sq {C : Type*} (s : Finset C)
    (b f : C → ℂ) (hb : ∀ c ∈ s, ‖b c‖ ≤ 1) :
    ‖∑ c ∈ s, b c * f c‖ ^ 2 ≤ (s.card : ℝ) * ∑ c ∈ s, ‖f c‖ ^ 2 := by
  classical
  have h := finite_expansion_energy ({()} : Finset Unit) s
    (fun _ => s) (fun _ => b) (fun _ => f) (s.card : ℝ)
    (by simp) (by simpa using hb) (by simp)
  simpa using h

theorem bounded_coefficient_sum_sq {C : Type*} [Fintype C]
    (b f : C → ℂ) (hb : ∀ c, ‖b c‖ ≤ 1) :
    ‖∑ c, b c * f c‖ ^ 2 ≤ (Fintype.card C : ℝ) * ∑ c, ‖f c‖ ^ 2 := by
  classical
  simpa using bounded_finset_coefficient_sum_sq Finset.univ b f (by simpa using hb)

theorem positive_triple_enlarge {M H C : Type*}
    [DecidableEq M] [DecidableEq H] [DecidableEq C]
    (pairs : Finset (M × H)) (cset : M → Finset C)
    (hs : Finset H) (mc : Finset (M × C)) (E : H → M → C → ℝ)
    (hh : ∀ p ∈ pairs, p.2 ∈ hs)
    (hm : ∀ p ∈ pairs, ∀ c ∈ cset p.1, (p.1, c) ∈ mc)
    (hE : ∀ h m c, 0 ≤ E h m c) :
    (∑ p ∈ pairs, ∑ c ∈ cset p.1, E p.2 p.1 c) ≤
      ∑ h ∈ hs, ∑ u ∈ mc, E h u.1 u.2 := by
  let f : (Σ _p : M × H, C) → H × (M × C) := fun p => (p.1.2, (p.1.1, p.2))
  have hf : Function.Injective f := by
    have hi : Function.LeftInverse
        (fun u : H × (M × C) => (⟨(u.2.1, u.1), u.2.2⟩ : Σ _p : M × H, C)) f := by
      rintro ⟨⟨m, h⟩, c⟩
      rfl
    exact hi.injective
  have hmapped : ((pairs.sigma (fun p => cset p.1)).image f) ⊆ hs ×ˢ mc := by
    intro u hu
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hu
    have hp' := Finset.mem_sigma.mp hp
    exact Finset.mem_product.mpr ⟨hh p.1 hp'.1, hm p.1 hp'.1 p.2 hp'.2⟩
  have hb := Finset.sum_le_sum_of_injOn f hf.injOn hmapped
    (f := fun p : Σ _p : M × H, C => E p.1.2 p.1.1 p.2)
    (g := fun u : H × (M × C) => E u.1 u.2.1 u.2.2)
    (by intros; exact le_rfl) (by intro u _ _; exact hE _ _ _)
  simpa only [Finset.sum_sigma, Finset.sum_product] using hb

theorem column_fiber_sieve {K X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (φ : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ) (hQ : 0 ≤ Q)
    (hφ : ∀ x ∈ source, φ x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter (fun x => φ x = y)).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y * f y‖ ^ 2) ≤
        Q * ∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (φ x) * a x‖ ^ 2) ≤
      Q * D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
  let f : Y → ℂ := fun y => ∑ x ∈ source with φ x = y, a x
  have he (k : K) : (∑ x ∈ source, q k (φ x) * a x) =
      ∑ y ∈ target, q k y * f y := by
    rw [← Finset.sum_fiberwise_of_maps_to hφ]
    apply Finset.sum_congr rfl
    intro y hy
    dsimp only [f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hf := finite_expansion_energy target source
    (fun y => source.filter (fun x => φ x = y)) (fun _ _ => 1) (fun _ => a) D
    (fun _ _ => Finset.filter_subset _ _) (by simp) hfiber
  have hf' : (∑ y ∈ target, ‖f y‖ ^ 2) ≤ D * ∑ x ∈ source, ‖a x‖ ^ 2 := by
    have hrhs : (∑ x ∈ source, ∑ y ∈ target,
        if x ∈ source.filter (fun x => φ x = y) then ‖a x‖ ^ 2 else 0) =
        ∑ x ∈ source, ‖a x‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro x hx
      simp [hx, hφ x hx]
    rw [hrhs] at hf
    simpa only [one_mul, f] using hf
  simp_rw [he]
  exact (hsieve f).trans (by
    calc
      _ ≤ Q * (D * ∑ x ∈ source, ‖a x‖ ^ 2) := mul_le_mul_of_nonneg_left hf' hQ
      _ = _ := by ring)

theorem quadratic_cubic_composition
    {K M H C P : Type*} [Fintype K] [Fintype M] [Fintype H] [Fintype C] [Fintype P]
    (q : K → M → H → ℂ) (χ : M → C → P → ℂ)
    (a : H → P → ℂ) (beta : C → M → H → ℂ) (Q S : ℝ) (hQ : 0 ≤ Q)
    (hbeta : ∀ c m h, ‖beta c m h‖ ≤ 1)
    (hquadratic : ∀ f : M → H → ℂ,
      (∑ k, ‖∑ m, ∑ h, q k m h * f m h‖ ^ 2) ≤ Q * ∑ m, ∑ h, ‖f m h‖ ^ 2)
    (hcubic : ∀ u : P → ℂ,
      (∑ m, ∑ c, ‖∑ p, u p * χ m c p‖ ^ 2) ≤ S * ∑ p, ‖u p‖ ^ 2) :
    (∑ k, ‖∑ m, ∑ h, q k m h *
      (∑ c, beta c m h * (∑ p, a h p * χ m c p))‖ ^ 2) ≤
      Q * (Fintype.card C : ℝ) * S * ∑ h, ∑ p, ‖a h p‖ ^ 2 := by
  classical
  apply (hquadratic (fun m h => ∑ c, beta c m h * (∑ p, a h p * χ m c p))).trans
  have hcauchy :
      (∑ m, ∑ h, ‖∑ c, beta c m h * (∑ p, a h p * χ m c p)‖ ^ 2) ≤
      (Fintype.card C : ℝ) * ∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2 := by
    calc
      _ ≤ ∑ m, ∑ h, (Fintype.card C : ℝ) *
          ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro m _
        apply Finset.sum_le_sum
        intro h _
        exact bounded_coefficient_sum_sq _ _ (fun c => hbeta c m h)
      _ = _ := by
        simp only [← Finset.mul_sum]
        congr 1
        exact Finset.sum_comm
  have hcs : (∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2) ≤
      S * ∑ h, ∑ p, ‖a h p‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun h _ => hcubic (a h)
  calc
    _ ≤ Q * ((Fintype.card C : ℝ) *
        ∑ h, ∑ m, ∑ c, ‖∑ p, a h p * χ m c p‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hcauchy hQ
    _ ≤ Q * ((Fintype.card C : ℝ) * (S * ∑ h, ∑ p, ‖a h p‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hcs (Nat.cast_nonneg _)) hQ
    _ = _ := by ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0013

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SlotAssignments
Source SHA256: 4c986fb1a8ff7614d8dab2f75ebf583f93da473fd5aa395abbb5471ed1d771bd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0014



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {σ ι : Type*} [DecidableEq σ] [DecidableEq ι]

def slotAssignmentWeight (I : Finset σ) (a : σ → ι → ℂ)
    (q : ∀ i ∈ I, ι) : ℂ := ∏ i ∈ I.attach, a i.val (q i.val i.property)

theorem primeMark_supported_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A = ∑ q ∈ I.pi (fun i => L i ∩ A), slotAssignmentWeight I a q := by
  simp only [primeMark,primeSlot,Finset.sum_ite_mem,slotAssignmentWeight]
  exact Finset.prod_sum I (fun i => L i ∩ A) a

theorem slotAssignmentWeight_norm_le_one (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) (q : ∀ i ∈ I, ι)
    (hq : q ∈ I.pi (fun i => L i ∩ A))
    (ha : ∀ i ∈ I, ∀ p ∈ L i, ‖a i p‖ ≤ 1) : ‖slotAssignmentWeight I a q‖ ≤ 1 := by
  rw [slotAssignmentWeight,norm_prod]
  apply Finset.prod_le_one₀ (fun _ _ => norm_nonneg _)
  intro i _
  exact ha i.val i.property _ (Finset.mem_inter.mp (Finset.mem_pi.mp hq i.val i.property)).1

def indexedSlotAssignment (I : Finset σ) (q : ∀ i ∈ I, ι) : Fin I.card → ι :=
  fun j => q ((I.equivFin).symm j).val ((I.equivFin).symm j).property

omit [DecidableEq σ] [DecidableEq ι] in
theorem indexedSlotAssignment_injective (I : Finset σ) :
    Function.Injective (indexedSlotAssignment (ι:=ι) I) := by
  intro q r h
  funext i hi
  have he := congrFun h (I.equivFin ⟨i,hi⟩)
  simpa [indexedSlotAssignment] using he

theorem indexedSlotAssignment_support (I : Finset σ) (L : σ → Finset ι)
    (A : Finset ι) (q : ∀ i ∈ I, ι) (hq : q ∈ I.pi (fun i => L i ∩ A))
    (j : Fin I.card) :
    indexedSlotAssignment I q j ∈ L ((I.equivFin).symm j).val ∩ A :=
  Finset.mem_pi.mp hq _ _

theorem primeMark_indexed_assignments (I : Finset σ) (L : σ → Finset ι)
    (a : σ → ι → ℂ) (A : Finset ι) :
    primeMark I L a A =
      ∑ r ∈ (I.pi (fun i => L i ∩ A)).image (indexedSlotAssignment I),
        slotAssignmentWeight I a (fun i hi => r (I.equivFin ⟨i,hi⟩)) := by
  rw [Finset.sum_image (fun q _ r _ h => indexedSlotAssignment_injective I h)]
  simpa only [indexedSlotAssignment,Equiv.symm_apply_apply] using
    primeMark_supported_assignments I L a A

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0014

/-! Original module: OAI.NumberTheory.DirichletL.Detector
Source SHA256: b7a35ece30047890b1ae79cad9d6ef11ba15c8d377086e940cc54c0e8401ff67
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0015








namespace OAI

namespace SevenEighths.Detector

theorem exists_small_increment (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lo hi e : ℝ} (hlo : lo ≤ M 0) (hhi : M n ≤ hi)
    (hwidth : hi - lo ≤ n * e) :
    ∃ i < n, M (i + 1) - M i ≤ e := by
  by_contra h
  have hinc : ∀ i ∈ Finset.range n, e < M (i + 1) - M i := by
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, Finset.mem_range.mp hi, hle⟩)
  have hs := Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) hinc
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_sub] at hs
  linarith

theorem buffered_bin_of_rounding {x y a e : ℝ}
    (hround : a ≤ x ∧ x < a + e) (hstep : y - x ≤ e) :
    a ≤ x ∧ x < a + e ∧ y < a + 2 * e := by
  exact ⟨hround.1, hround.2, by linarith [hround.2]⟩

theorem exists_grid_rounding {base x e : ℝ} (he : 0 < e) (hx : base ≤ x) :
    ∃ k : ℕ, base + e * k ≤ x ∧ x < base + e * k + e := by
  let k := ⌊(x - base) / e⌋₊
  have hnonneg : 0 ≤ (x - base) / e := div_nonneg (sub_nonneg.mpr hx) he.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((x - base) / e)
  have hlo' := (le_div_iff₀ he).mp hlo
  have hhi' := (div_lt_iff₀ he).mp hhi
  refine ⟨k, ?_, ?_⟩ <;> dsimp [k] <;> nlinarith

theorem exists_buffered_bin (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {e : ℝ} (he : 0 < e)
    (hbound : ∀ j ≤ n, (51 / 100 : ℝ) ≤ M j ∧ M j ≤ 1)
    (hwidth : (49 / 100 : ℝ) ≤ n * e) :
    ∃ i < n, ∃ k : ℕ,
      let a : ℝ := 51 / 100 + e * k
      a ≤ 1 ∧ a ≤ M i ∧ M i < a + e ∧ M (i + 1) < a + 2 * e := by
  obtain ⟨i, hi, hstep⟩ := exists_small_increment M hn (e := e)
    (hbound 0 (Nat.zero_le _)).1 (hbound n le_rfl).2 (by linarith)
  obtain ⟨k, hklo, hkhi⟩ := exists_grid_rounding he (hbound i hi.le).1
  refine ⟨i, hi, k, ?_, hklo, hkhi, ?_⟩
  · exact hklo.trans (hbound i hi.le).2
  · linarith

theorem maximal_zero_of_floor_lt {ι : Type*} (L : ι → ℂ → ℂ)
    (zeros : Finset (ι × ℂ)) {floor M : ℝ}
    (hzero : ∀ p ∈ zeros, L p.1 p.2 = 0)
    (hmax : M ∈ insert floor (zeros.image (fun p => p.2.re)))
    (hfloor : floor < M) :
    ∃ χ ρ, (χ, ρ) ∈ zeros ∧ L χ ρ = 0 ∧ ρ.re = M := by
  classical
  rcases Finset.mem_insert.mp hmax with h | h
  · exact False.elim ((ne_of_gt hfloor) h)
  · obtain ⟨⟨χ, ρ⟩, hp, heq⟩ := Finset.mem_image.mp h
    exact ⟨χ, ρ, hp, hzero _ hp, heq⟩

theorem simultaneous_saturation {U δ r m ε A B : ℝ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hprod : U ^ (δ * (r + m) - ε) ≤ A * B)
    (hupperA : A ≤ U ^ (δ * r + ε))
    (hupperB : B ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ A ∧ U ^ (δ * m - 2 * ε) ≤ B := by
  have hU0 : 0 < U := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hBcoarse : B ≤ U ^ (δ * m + ε) := by
    apply hupperB.trans
    exact Real.rpow_le_rpow_of_exponent_le hU.le
      (by have h := mul_le_mul_of_nonneg_left (min_le_left m (1 - m)) hδ0; linarith)
  have hpupper : A * B ≤ U ^ (δ * r + ε + (δ * min m (1 - m) + ε)) := by
    rw [Real.rpow_add hU0]
    exact mul_le_mul hupperA hupperB hB (Real.rpow_nonneg hU0.le _)
  have hexp := (Real.rpow_le_rpow_left_iff hU).mp (hprod.trans hpupper)
  have hlength : m ≤ 1 / 2 + 75 * ε := by
    by_cases hm : m ≤ 1 / 2
    · linarith
    · have hmin : min m (1 - m) = 1 - m := min_eq_right (by linarith)
      rw [hmin] at hexp
      have hm0 : 0 ≤ m - 1 / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hδ hm0
      nlinarith
  have hlowerA : U ^ (δ * r - 2 * ε) ≤ A := by
    have hp : U ^ (δ * r - 2 * ε) * U ^ (δ * m + ε) ≤
        A * U ^ (δ * m + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := mul_le_mul_of_nonneg_left hBcoarse hA
    have hpos := Real.rpow_pos_of_pos hU0 (δ * m + ε)
    nlinarith
  have hlowerB : U ^ (δ * m - 2 * ε) ≤ B := by
    have hp : U ^ (δ * m - 2 * ε) * U ^ (δ * r + ε) ≤
        B * U ^ (δ * r + ε) := by
      calc
        _ = U ^ (δ * (r + m) - ε) := by rw [← Real.rpow_add hU0]; congr 1; ring
        _ ≤ A * B := hprod
        _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hupperA hB
    have hpos := Real.rpow_pos_of_pos hU0 (δ * r + ε)
    nlinarith
  exact ⟨hlength, hlowerA, hlowerB⟩

theorem inverse_length_of_saturation {r m t ε κ : ℝ}
    (hsupport : t - κ ≤ r + m) (hplain : m ≤ 1 / 2 + 75 * ε) :
    t - 1 / 2 - 75 * ε - κ ≤ r := by linarith

theorem complex_simultaneous_saturation {U δ r m ε : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hprod : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hupperM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hupperS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ ‖M‖ ^ 2 ∧
      U ^ (δ * m - 2 * ε) ≤ ‖S‖ ^ 2 := by
  apply simultaneous_saturation hU hδ hε (sq_nonneg _) (sq_nonneg _)
    _ hupperM hupperS
  simpa only [norm_mul, mul_pow] using hprod

end SevenEighths.Detector

end OAI
end OAIOriginalModule0015

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Basic
Source SHA256: 12366d70e0deb94c6a5b74b69231312bdfe9978aa92a2dad2b8626b51c863694
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0016







namespace OAI

namespace SevenEighths.Probe
noncomputable section

def principalScalar {ι : Type*} (slots : Finset ι) (Z ℓ : ℝ) (S : ι → ℝ) : ℝ :=
  (-1) ^ slots.card * Z ^ (-ℓ / 6) * ∏ i ∈ slots, S i

theorem principalScalar_ne_zero {ι : Type*} (slots : Finset ι)
    {Z ℓ : ℝ} {S : ι → ℝ} (hZ : 0 < Z)
    (hS : ∀ i ∈ slots, 0 < S i) : principalScalar slots Z ℓ S ≠ 0 := by
  unfold principalScalar
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ne_of_gt (Real.rpow_pos_of_pos hZ _))
  · exact ne_of_gt (Finset.prod_pos hS)

def normalizedProbe (I A : ℝ → ℂ) (c : ℂ) (Z : ℝ) : ℂ := I Z / (c * A Z)

theorem normalizedProbe_error (I A f : ℝ → ℂ) {c : ℂ} {Z : ℝ}
    (hc : c ≠ 0) (hA : A Z ≠ 0) :
    normalizedProbe I A c Z - f Z = (I Z - (c * A Z) * f Z) / (c * A Z) := by
  unfold normalizedProbe
  field_simp

theorem norm_div_bound {I B : ℂ} {Z C D a ε : ℝ} (hZ : 0 < Z)
    (hI : ‖I‖ ≤ C * Z ^ a) (hB : ‖B⁻¹‖ ≤ D * Z ^ ε) :
    ‖I / B‖ ≤ (C * D) * Z ^ (a + ε) := by
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add hZ]
  calc
    ‖I‖ * ‖B⁻¹‖ ≤ (C * Z ^ a) * (D * Z ^ ε) :=
      mul_le_mul hI hB (norm_nonneg _) ((norm_nonneg _).trans hI)
    _ = C * D * (Z ^ a * Z ^ ε) := by ring

theorem common_normalization_bounds (I A f : ℝ → ℂ) {c : ℂ}
    {Z C_low C_high D a b ε : ℝ} (hZ : 0 < Z)
    (hc : c ≠ 0) (hA : A Z ≠ 0)
    (hrecip : ‖(c * A Z)⁻¹‖ ≤ D * Z ^ ε)
    (hlow : ‖I Z‖ ≤ C_low * Z ^ a)
    (hhigh : ‖I Z - (c * A Z) * f Z‖ ≤ C_high * Z ^ b) :
    ‖normalizedProbe I A c Z‖ ≤ (C_low * D) * Z ^ (a + ε) ∧
    ‖normalizedProbe I A c Z - f Z‖ ≤ (C_high * D) * Z ^ (b + ε) := by
  constructor
  · exact norm_div_bound hZ hlow hrecip
  · rw [normalizedProbe_error I A f hc hA]
    exact norm_div_bound hZ hhigh hrecip

end
end SevenEighths.Probe

end OAI
end OAIOriginalModule0016

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Compensation
Source SHA256: db4b2b2ca1c5cfc9d23fefb08b30e1411891d1007462492211abb4140e4a71d2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0017






namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbeCompensation

def tupleOperation {α : Type*} [CommMonoid α] {K : ℕ}
    (p : Fin K → α) (q : α → ℝ) (η : α → ℂ)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) : ℂ :=
  ∑ J ∈ (Finset.univ : Finset (Fin K)).powerset,
    (-1 : ℂ) ^ J.card * ((q (∏ i ∈ J, p i) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) *
      star (η (∏ i ∈ Finset.univ \ J, p i)) *
      F (∏ i ∈ Finset.univ \ J, p i)
        (X / q (∏ i ∈ J, p i)) (Y / q (∏ i ∈ J, p i))
        (Z * q (∏ i ∈ Finset.univ \ J, p i))

theorem tupleOperation_zero {α : Type*} [CommMonoid α]
    (p : Fin 0 → α) (q : α → ℝ) (η : α → ℂ)
    (hq : q 1 = 1) (hη : η 1 = 1)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) :
    tupleOperation p q η F X Y Z = F 1 X Y Z := by
  simp [tupleOperation, hq, hη]

theorem tupleOperation_one {α : Type*} [CommMonoid α]
    (p : Fin 1 → α) (q : α → ℝ) (η : α → ℂ)
    (hq : q 1 = 1) (hη : η 1 = 1)
    (F : α → ℝ → ℝ → ℝ → ℂ) (X Y Z : ℝ) :
    tupleOperation p q η F X Y Z =
      star (η (p 0)) * F (p 0) X Y (Z * q (p 0)) -
      ((q (p 0) ^ (-(3 / 2 : ℝ)) : ℝ) : ℂ) * F 1 (X / q (p 0)) (Y / q (p 0)) Z := by
  have hp : (Finset.univ : Finset (Fin 1)).powerset = {∅, {0}} := by decide
  simp only [tupleOperation, hp]
  simp [hq, hη]
  ring

end SevenEighths.ProbeCompensation
end

end OAI
end OAIOriginalModule0017

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Euler
Source SHA256: 1bd3365ab3804e359606f209ce9d95853c118cb69f5d7379a7073ef1e02d6bd3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0018





namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

def markedFactor (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ((R * (1 - qInv) - K * V ^ a) / (1 - V) + J) / (1 - R)

def markedTableSeries (R V qInv K J : ℂ) (a : ℕ) : ℂ :=
  ∑' r : ℕ, R ^ r *
    ((∑' m : ℕ, (R * (1 - qInv) * V ^ m - K * V ^ (m + a))) + J)

theorem marked_table_resummation (R V qInv K J : ℂ) (a : ℕ)
    (hR : ‖R‖ < 1) (hV : ‖V‖ < 1) :
    markedTableSeries R V qInv K J a = markedFactor R V qInv K J a := by
  have hgeo := hasSum_geometric_of_norm_lt_one hV
  have hfirst := hgeo.mul_left (R * (1 - qInv))
  have hsecond : HasSum (fun m : ℕ => K * V ^ (m + a))
      (K * V ^ a * (1 - V)⁻¹) := by
    convert hgeo.mul_left (K * V ^ a) using 1
    funext m
    rw [pow_add]
    ring
  have hin := (hfirst.sub hsecond).tsum_eq
  unfold markedTableSeries
  rw [hin, tsum_mul_right, tsum_geometric_of_norm_lt_one hR]
  unfold markedFactor
  simp only [div_eq_mul_inv]
  ring

theorem unramified_marked_error (R V qInv K W D : ℂ)
    (hR : 1 - R ≠ 0) (hV : 1 - V ≠ 0) :
    markedFactor R V qInv K (-D + W * R) 1 + D =
      (R * ((1 - qInv) + (1 - V) * (W - D)) - K * V) /
        ((1 - R) * (1 - V)) := by
  unfold markedFactor
  field_simp
  ring

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule0018

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Gauss
Source SHA256: 703401fb77716560cd0f33774271bd867e0f23853c5b255c7543bdb86f7dd14e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0019





namespace OAI

namespace SevenEighths.ProbeGauss
open scoped BigOperators Classical
noncomputable section

def frequencyGauss {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) : ℂ :=
  ∑ v : F, ξ v * ψ (h * v)

theorem frequencyGauss_eq_shift {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    frequencyGauss ξ ψ h = gaussSum ξ (ψ.mulShift h) := rfl

theorem frequencyGauss_nonzero {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) {h : F} (hh : h ≠ 0) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  exact gaussSum_mulShift_eq ξ ψ (Units.mk0 h hh)

theorem frequencyGauss_zero_nonprincipal {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) :
    frequencyGauss ξ ψ 0 = 0 := by
  simpa [frequencyGauss] using MulChar.sum_eq_zero_of_ne_one hξ

theorem frequencyGauss_nonprincipal {F : Type*} [Field F] [Fintype F]
    (ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (hξ : ξ ≠ 1) (h : F) :
    frequencyGauss ξ ψ h = ξ⁻¹ h * gaussSum ξ ψ := by
  by_cases hh : h = 0
  · subst h
    rw [frequencyGauss_zero_nonprincipal ξ ψ hξ, MulChar.map_zero, zero_mul]
  · exact frequencyGauss_nonzero ξ ψ hh

theorem frequencyGauss_principal {F : Type*} [Field F] [Fintype F]
    (ψ : AddChar F ℂ) (hψ : ψ ≠ 1) (h : F) :
    frequencyGauss 1 ψ h = if h = 0 then (Nat.card Fˣ : ℂ) else -1 := by
  classical
  by_cases hh : h = 0
  · subst h
    simpa [frequencyGauss, Nat.card_eq_fintype_card] using
      (MulChar.sum_one_eq_card_units (R := F) (R' := ℂ))
  · rw [ite_eq_right hh, frequencyGauss_nonzero _ ψ hh, inv_one,
      MulChar.one_apply (isUnit_iff_ne_zero.mpr hh), one_mul]
    exact gaussSum_one_left hψ

theorem gauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    gaussSum χ ψ * gaussSum χ⁻¹ ψ = χ (-1) * (Fintype.card F : ℂ) := by
  rw [← mul_gaussSum_inv_eq_gaussSum χ⁻¹, mul_left_comm,
    gaussSum_mul_gaussSum_eq_card hχ hψ, MulChar.inv_apply', inv_neg_one]

def normalizedGauss {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) : ℂ :=
  gaussSum χ ψ / (Real.sqrt (Fintype.card F) : ℂ)

theorem normalizedGauss_inverse_pair {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    normalizedGauss χ ψ * normalizedGauss χ⁻¹ ψ = χ (-1) := by
  have hq : (Fintype.card F : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hs : (Real.sqrt (Fintype.card F) : ℂ) ^ 2 = (Fintype.card F : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card F) : (0 : ℝ) ≤ _)
  unfold normalizedGauss
  rw [div_mul_div_comm, ← pow_two, hs, gauss_inverse_pair χ ψ hχ hψ]
  exact mul_div_cancel_right₀ _ hq

theorem finite_gauss_convolution {F : Type*} [Field F] [Fintype F]
    (χ ξ : MulChar F ℂ) (ψ : AddChar F ℂ) (h : F) :
    (∑ d : F, χ d * frequencyGauss ξ ψ (h - d)) =
      χ⁻¹ (-1) * gaussSum χ ψ * frequencyGauss (ξ * χ⁻¹) ψ h := by
  classical
  have hfreq (v : F) :
      ξ v * (∑ d : F, χ d * ψ (-(v * d))) =
        χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v) := by
    by_cases hv : v = 0
    · subst v
      simp [MulChar.map_zero]
    · have hn : -v ≠ 0 := neg_ne_zero.mpr hv
      have he := gaussSum_mulShift_eq χ ψ (Units.mk0 (-v) hn)
      simp only [gaussSum, AddChar.mulShift_apply, Units.val_mk0] at he
      have hinv : χ⁻¹ (-v) = χ⁻¹ (-1) * χ⁻¹ v := by rw [← map_mul]; congr 1; ring
      rw [hinv] at he
      have he' : (∑ d : F, χ d * ψ (-(v * d))) =
          (χ⁻¹ (-1) * χ⁻¹ v) * gaussSum χ ψ := by
        simpa only [neg_mul, gaussSum] using he
      rw [he']
      ring
  unfold frequencyGauss
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    (∑ v : F, ∑ d : F, χ d * (ξ v * ψ ((h - d) * v))) =
        ∑ v : F, ψ (h * v) * (ξ v * ∑ d : F, χ d * ψ (-(v * d))) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show (h - d) * v = h * v + -(v * d) by ring, ψ.map_add_eq_mul]
      ring
    _ = ∑ v : F, ψ (h * v) *
        (χ⁻¹ (-1) * gaussSum χ ψ * (ξ v * χ⁻¹ v)) := by simp_rw [hfreq]
    _ = ∑ v : F, χ⁻¹ (-1) * gaussSum χ ψ * ((ξ * χ⁻¹) v * ψ (h * v)) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [MulChar.mul_apply]
      ring

end
end SevenEighths.ProbeGauss

end OAI
end OAIOriginalModule0019

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Local
Source SHA256: c24d3484b46dc6fb5dab01bd154b0a9b666750565ebf1af7dd12631ad9a55003
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0020





namespace OAI

namespace SevenEighths.ProbeLocal
noncomputable section

def localFactor (V W Pstar : ℂ) : ℂ := 1 / (1 - V) + W / (1 - W) + Pstar

def localCorrection (V W D Pstar : ℂ) : ℂ :=
  localFactor V W Pstar * ((1 - V) * (1 - W)) / (1 - D)

def continuedCorrection (V W D Pstar : ℂ) : ℂ :=
  (1 - V * W + (1 - V) * (1 - W) * Pstar) / (1 - D)

theorem continuedCorrection_eq_raw (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar = localCorrection V W D Pstar := by
  unfold continuedCorrection localCorrection localFactor
  field_simp
  ring

def compensatedReplacement (V W D Pstar B q : ℂ) : ℂ :=
  ((B - q) * (1 - V) * (1 - W) * Pstar - q * (1 - V * W)) / (1 - D)

theorem correction_defect (V W D Pstar : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0) :
    localCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold localCorrection localFactor
  field_simp
  ring

theorem compensatedReplacement_eq_raw (V W D Pstar B q : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hP : localFactor V W Pstar ≠ 0) :
    compensatedReplacement V W D Pstar B q =
      localCorrection V W D Pstar * (B * Pstar / localFactor V W Pstar - q) := by
  unfold localCorrection compensatedReplacement
  field_simp
  unfold localFactor
  field_simp
  ring

theorem compensatedReplacement_ramified (V Pstar B q : ℂ) (hV : 1 - V ≠ 0) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * localCorrection V 0 0 Pstar := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  ring

theorem normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hW : 1 - W ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        localCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement localCorrection localFactor
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continuedCorrection_defect (V W D Pstar : ℂ) (hD : 1 - D ≠ 0) :
    continuedCorrection V W D Pstar - 1 =
      (D * (V + W - V * W) - V * W +
        (1 - V) * (1 - W) * (Pstar + D)) / (1 - D) := by
  unfold continuedCorrection
  field_simp
  ring

theorem continued_normalized_cancellation (V W D Pstar B q vInv : ℂ)
    (hV : 1 - V ≠ 0) (hD : 1 - D ≠ 0)
    (hBD : B * D = vInv) (hvW : vInv * W = q) :
    compensatedReplacement V W D Pstar B q +
        continuedCorrection V W D Pstar * vInv =
      (1 - V) * (1 - W) / (1 - D) *
        ((vInv - q) * (V / (1 - V) - D) +
          (B + vInv - q) * (Pstar + D)) := by
  unfold compensatedReplacement continuedCorrection
  field_simp
  linear_combination -(1 - V) * (1 - W) * hBD + (1 - V) * hvW

theorem continued_ramified_compensation (V Pstar B q : ℂ) :
    compensatedReplacement V 0 0 Pstar B q =
      B * (1 - V) * Pstar - q * continuedCorrection V 0 0 Pstar := by
  simp only [compensatedReplacement, continuedCorrection, mul_zero, sub_zero,
    mul_one, div_one]
  ring

end
end SevenEighths.ProbeLocal

end OAI
end OAIOriginalModule0020

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CorrectionBounds
Source SHA256: 6531ff6a758f9cbda74d5be18ac98ce0e65e9a4d1a9dae7008add6d372029c7e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0021





namespace OAI

noncomputable section
namespace SevenEighths.ProbeLocal

lemma one_sub_ne_zero_of_norm_le_half (a : ℂ) (ha : ‖a‖ ≤ 1/2) : 1 - a ≠ 0 := by
  intro h
  have : a = 1 := by linear_combination -h
  rw [this, norm_one] at ha
  norm_num at ha

