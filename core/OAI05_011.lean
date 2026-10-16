
end SevenEighths.ProbeRow
end

end OAI
end OAIOriginalModule1214

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalAnalytic
Source SHA256: 2c333bbf6a0252156005ca3654c53172e3352d3776dcd01356a623fceaca3fd7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1215



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ProbeRow CubicEisenstein CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem CalibrationData.residueMonoid_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.residueMonoid a‖ ≤ 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one C.residue (Ideal.Quotient.mk _ a)

theorem CalibrationData.Xi_norm_le_one (C : CalibrationData) (a : O) :
    ‖C.Xi a‖ ≤ 1 := by
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans
    (idealRowHom_norm _ _)

theorem CalibrationData.Xi_norm_one (C : CalibrationData) (a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    ‖C.Xi a‖ = 1 := by
  let : Finite (O ⧸ Ideal.span {C.generator}) :=
    ConcreteTraceCRT.finite_quotient_span C.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {C.generator}) := Fintype.ofFinite _
  have hu := (CubicEisenstein.isUnit_quotient_span_iff C.generator a).mpr hcop
  have hξ : ‖C.residueMonoid a‖ = 1 := by
    exact (FiniteRayExpansion.norm_char_unit C.residue hu.unit)
  have hc : IsCoprime (Ideal.span {a} : Ideal O) (Ideal.span {C.generator}) :=
    (Ideal.isCoprime_span_singleton_iff a C.generator).mpr hcop.symm
  have h6 := idealRowHom_sixth_mask C.generator (Ideal.span {a}) ha
  rw [idealRowHom_argument_pow _ _ _ ha, ite_eq_left hc] at h6
  change ‖C.residueMonoid a * idealRowHom C.generator (Ideal.span {a})‖ = 1
  rw [norm_mul, hξ, Complex.norm_eq_one_of_pow_eq_one h6 (by decide : (6 : ℕ) ≠ 0), mul_one]

theorem calibrated_rowCoefficient_apply (η : HeckeFamily.Character) (C : CalibrationData)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hcop : IsCoprime C.generator a) :
    rowCoefficient η C.Xi s hs m a = HeckeFamily.elementCoeff η a * (C.Xi a)⁻¹ *
      sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  rowCoefficient_apply_unit η C.Xi s hs m a (C.Xi_norm_one a ha hcop)

theorem physicalRow_integrable (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Ideal O) (s : O) (hs : Supported (Ideal.span {s})) (m : O)
    (Z : ℝ) (hZ : 0 < Z) :
    Integrable (fun y : ℝ => (Z : ℂ) ^ ((4 : ℂ) + y * Complex.I) *
      Complex.exp (((4 : ℂ) + y * Complex.I) ^ 2) *
      spectralRow C.excluded D (rowCoefficient η C.Xi s hs m) ((4 : ℂ) + y * Complex.I)) := by
  exact spectralRow_vertical_integrable C.excluded D (rowCoefficient η C.Xi s hs m)
    (fun a => rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m a)
    4 (by norm_num) Z hZ

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1215

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CalibrationSupport
Source SHA256: 3de800afc83570e01c6583d5fe4847b3e63887d3b9f936dd824cff5e314fe224
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1216



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve ProbeRow
local notation "O" => ActualEisensteinCubic.O

theorem calibrationForSet_coprime_iff (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (a : O) : IsCoprime (calibrationForSet S hS).generator a ↔ ∀ P ∈ S, a ∉ P := by
  rw [← Ideal.isCoprime_span_singleton_iff, calibrationForSet_span, IsCoprime.prod_left_iff]
  constructor
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mp (h P hP)
  · intro h P hP
    let : P.IsMaximal := hS P hP
    exact (SixthPowerAverage.prime_coprime_span_iff P a).mpr (h P hP)

theorem calibrationForSet_coprime_of_excluded (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, P.IsMaximal) (a : O)
    (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    IsCoprime (calibrationForSet S hS).generator a := by
  apply (calibrationForSet_coprime_iff S hS a).mpr
  intro P hP ha
  apply hmask P hP
  exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

theorem source_rowCoefficient_apply (η : HeckeFamily.Character)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, P.IsMaximal)
    (s : O) (hs : Supported (Ideal.span {s})) (m a : O)
    (ha : Supported (Ideal.span {a})) (hmask : ∀ P ∈ S, ¬P ∣ Ideal.span {a}) :
    rowCoefficient η (calibrationForSet S hS).Xi s hs m a =
      HeckeFamily.elementCoeff η a * ((calibrationForSet S hS).Xi a)⁻¹ *
        sexticReciprocityPhase a s * idealRowHom m (Ideal.span {a}) :=
  calibrated_rowCoefficient_apply η (calibrationForSet S hS) s hs m a ha
    (calibrationForSet_coprime_of_excluded S hS a hmask)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1216

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowPeriod
Source SHA256: 9e62cdb96eff842e0f59876b6f968677ff352ac07c27d875fcb0cc9f069c9ace
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1217



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def calibrationRowModulus (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : Id :=
  1*Ideal.span {B}*Ideal.span {(72:O)}*Ideal.span {D.numeratorGood}

def periodicCalibrationXi (C : CalibrationData) (B : O) (D : GoodMaskRowData B 1 C.generator) : O→*ℂ :=
  C.residueMonoid*actualPeriodicRow 1 B D.numeratorUnit D.numeratorLambda D.numeratorTwo
    D.numeratorGood D.numeratorSupported

lemma calibrationRowModulus_ne_zero (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : calibrationRowModulus C B D≠0 := by
  unfold calibrationRowModulus
  apply mul_ne_zero
  · apply mul_ne_zero
    · exact mul_ne_zero one_ne_zero (Ideal.span_singleton_eq_bot.not.mpr hB)
    · apply Ideal.span_singleton_eq_bot.not.mpr
      norm_num
  · exact D.numeratorSupported.1

lemma periodicCalibrationXi_norm (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (a : O) : ‖periodicCalibrationXi C B D a‖≤1 := by
  rw [periodicCalibrationXi,MonoidHom.mul_apply,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (C.residueMonoid_norm_le_one a)).trans (actualPeriodicRow_norm 1 (fun _=>by simp) B D.numeratorUnit D.numeratorLambda D.numeratorTwo
      D.numeratorGood D.numeratorSupported a)

lemma periodicCalibrationXi_periodic (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) :
    FactorsModulo (Ideal.span {C.generator}*calibrationRowModulus C B D) (periodicCalibrationXi C B D) := by
  have hp := actualPeriodicRow_periodic (1:O→*ℂ) 1 (fun _ _ _=>rfl)
    B D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
  intro x y hxy
  change C.residueMonoid x*_ = C.residueMonoid y*_
  congr 1
  · apply congrArg C.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left hxy)
  · exact hp x y (Ideal.mul_le_right hxy)

lemma periodicCalibrationXi_eq_primary (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    periodicCalibrationXi C B D n=C.Xi n := by
  have he := rowTwist_eq_actualPeriodicRow_primary (1:O→*ℂ) B 1 C.generator hBL hB2
    D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported
    D.numeratorPrimary D.numeratorFactor n hpn
  rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn] at he
  have hmask : coprimalityMask B n=(1:ℂ) := by
    change (if IsCoprime B n then (1:ℂ) else 0)=1
    rw [ite_eq_left hc]
  simp only [MonoidHom.one_apply,hmask,one_mul,one_pow] at he
  change C.residueMonoid n*_ = C.residueMonoid n*idealRowHom C.generator (Ideal.span {n})
  rw [←he]

def lowPeriodicBase (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) : O→*ℂ :=
  rayMonoid χ*targetMonoid η*conjugateMonoid (periodicCalibrationXi C B D)*reciprocityPhaseMonoid s hs

def lowBaseModulus (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) : Id :=
  η.modulus*(Ideal.span {C.generator}*calibrationRowModulus C B D)*Ideal.span {(4:O)}

lemma lowBaseModulus_ne_zero (η : HeckeFamily.Character) (C : CalibrationData) (B : O) (hB : B≠0)
    (D : GoodMaskRowData B 1 C.generator) : lowBaseModulus η C B D≠0 := by
  unfold lowBaseModulus
  apply mul_ne_zero
  · exact mul_ne_zero η.modulus_ne_bot (mul_ne_zero (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero)
      (calibrationRowModulus_ne_zero C B hB D))
  · apply Ideal.span_singleton_eq_bot.not.mpr
    norm_num

lemma lowPeriodicBase_periodic (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) :
    FactorsModulo (lowBaseModulus η C B D) (lowPeriodicBase η C B D s hs χ) := by
  intro x y hxy
  have h4 : (4:O)∣x-y := Ideal.mem_span_singleton.mp (Ideal.mul_le_right hxy)
  have hη : targetMonoid η x=targetMonoid η y := by
    apply congrArg η.residue
    exact Ideal.Quotient.eq.mpr (Ideal.mul_le_left (Ideal.mul_le_left hxy))
  have hc := periodicCalibrationXi_periodic C B D x y (Ideal.mul_le_right (Ideal.mul_le_left hxy))
  change ((rayMonoid χ x*targetMonoid η x)*star (periodicCalibrationXi C B D x))*
      sexticReciprocityPhase s x=
    ((rayMonoid χ y*targetMonoid η y)*star (periodicCalibrationXi C B D y))*sexticReciprocityPhase s y
  rw [hη,hc,sexticReciprocityPhase_congr_right s x y h4]
  have hr : rayMonoid χ x=rayMonoid χ y := rayCharacter_eq_of_mod_four χ x y h4
  rw [hr]

lemma lowPeriodicBase_norm (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (a : O) : ‖lowPeriodicBase η C B D s hs χ a‖≤1 := by
  have hr : ‖rayMonoid χ a‖≤1 := FiniteRayExpansion.norm_char_le_one χ _
  change ‖((rayMonoid χ a*targetMonoid η a)*star (periodicCalibrationXi C B D a))*sexticReciprocityPhase s a‖≤1
  simp only [norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) ((mul_le_of_le_one_left (norm_nonneg _) hr).trans (targetMonoid_norm_le_one η a))).trans (periodicCalibrationXi_norm C B D a))).trans (sexticReciprocityPhase_norm s a)

lemma lowPeriodicBase_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter)
    (n : O) (hn : Supported (Ideal.span {n})) (hpn : λ₀^2∣n-1) (hc : IsCoprime B n) :
    lowPeriodicBase η C B D s hs χ n=(rayMonoid χ*physicalRowBase η C.Xi s hs) n := by
  change ((rayMonoid χ n*targetMonoid η n)*star (periodicCalibrationXi C B D n))*sexticReciprocityPhase s n=
    rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)
  rw [periodicCalibrationXi_eq_primary C B D hBL hB2 n hn hpn hc]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1217

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowPuncture
Source SHA256: de069c3f87d4ae0f8d6813ea1d47707b9ab9d0b8380ea8625a3cc0caa04b294d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1218



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic CanonicalCoefficientClass ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma calibration_generator_dvd (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (a : O) (ha : Ideal.span {a}∈S) : a∣(calibrationForSet S hS).generator := by
  apply Ideal.span_singleton_dvd_span_singleton_iff_dvd.mp
  rw [calibrationForSet_span]
  exact Finset.dvd_prod_of_mem (fun P : Id=>P) ha

lemma calibration_generator_bad (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S) :
    λ₀∣(calibrationForSet S hS).generator ∧ (2:O)∣(calibrationForSet S hS).generator := by
  constructor
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inl rfl
  · apply calibration_generator_dvd S hS
    apply hbad
    simp only [fixedBadPrimes,Finset.mem_insert,Finset.mem_singleton]
    exact Or.inr trivial

lemma supported_of_coprime_bad (B n : O) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (hc : IsCoprime B n) : Supported (Ideal.span {n}) := by
  apply supported_span_iff n |>.mpr
  constructor
  · exact PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mp
      (hc.of_isCoprime_of_dvd_left hBL)
  · have h2 : IsCoprime (-2:O) n := (hc.of_isCoprime_of_dvd_left hB2).neg_left
    have hn := negative_two_prime.irreducible.coprime_iff_not_dvd.mp h2
    simpa only [neg_dvd] using hn

lemma lowPeriodicBase_zero_of_not_coprime (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (s : O) (hs : Supported (Ideal.span {s}))
    (χ : RayCharacter) (n : O) (hc : ¬IsCoprime B n) : lowPeriodicBase η C B D s hs χ n=0 := by
  have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
  change ((rayMonoid χ n*targetMonoid η n)*star (C.residueMonoid n*
      ((((1:O→*ℂ) n*coprimalityMask B n)*
        numeratorBadTwist D.numeratorUnit D.numeratorLambda D.numeratorTwo D.numeratorGood D.numeratorSupported n)*
        movingNumeratorRow D.numeratorGood D.numeratorSupported n)))*sexticReciprocityPhase s n=0
  rw [hm]
  simp only [mul_zero,zero_mul,star_zero]

lemma lowPeriodicRow_eq_primary (η : HeckeFamily.Character) (C : CalibrationData) (B : O)
    (D : GoodMaskRowData B 1 C.generator) (hBL : λ₀∣B) (hB2 : (2:O)∣B)
    (s : O) (hs : Supported (Ideal.span {s})) (χ : RayCharacter) (z n : O) (hpn : λ₀^2∣n-1) :
    rowTwist (lowPeriodicBase η C B D s hs χ) B 1 z n=
      (coprimalityMask B*(rayMonoid χ*rowCoefficient η C.Xi s hs z)) n := by
  by_cases hc : IsCoprime B n
  · have hn := supported_of_coprime_bad B n hBL hB2 hc
    have hm : coprimalityMask B n=(1:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=1;rw [ite_eq_left hc]
    rw [rowTwist_extract_sixth_mask _ _ _ _ _ hn,lowPeriodicBase_eq_primary η C B D hBL hB2 s hs χ n hn hpn hc]
    simp only [MonoidHom.mul_apply,hm,mul_one,one_pow,one_mul]
    change (rayMonoid χ n*((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n))*
      idealRowHom z (Ideal.span {n})=rayMonoid χ n*
        (((targetMonoid η n*star (C.Xi n))*sexticReciprocityPhase s n)*idealRowHom z (Ideal.span {n}))
    ring
  · have hm : coprimalityMask B n=(0:ℂ) := by change (if IsCoprime B n then (1:ℂ) else 0)=0;rw [ite_eq_right hc]
    change lowPeriodicBase η C B D s hs χ n*idealRowHom (B^6*1^4*z) (Ideal.span {n})=
      coprimalityMask B n*(rayMonoid χ n*rowCoefficient η C.Xi s hs z n)
    rw [lowPeriodicBase_zero_of_not_coprime η C B D s hs χ n hc,hm,zero_mul,zero_mul]

lemma calibration_coprime_iff_excluded_span (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (a : O) :
    IsCoprime (calibrationForSet S hS).generator a ↔ ∀P∈S,¬P∣Ideal.span {a} := by
  rw [calibrationForSet_coprime_iff]
  constructor
  · intro h P hP hd
    exact h P hP (Ideal.dvd_iff_le.mp hd (Ideal.subset_span (by simp)))
  · intro h P hP ha
    apply h P hP
    exact Ideal.dvd_iff_le.mpr (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr ha))

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1218

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowCompletion
Source SHA256: 15bd6e1af491221e8db627e922ea01f2bc69a8e3cce3d24b72ea1366483ee71d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1219


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalRowCompletion CanonicalQuadraticSieve CompletedGauss
open RayFourExpansion InitialMeanSquare SecondPassArithmetic ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma summand_zero_completedIndex (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id)
    (h : completedIndex I J=0) : summand Ψ W X I J=0 := by
  have hprod : primaryGenerator I*primaryGenerator J^3=0 := h
  rcases mul_eq_zero.mp hprod with hI|hJ
  · simp only [summand,columnWeight,squarefreeGaussCoefficient,hI,ne_eq,not_true_eq_false,
      and_false,dite_false,zero_mul,zero_div]
  · have hj : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3*
        Ψ (primaryGenerator J)^3/(Ideal.absNorm J:ℂ)=0
      simp only [hj,FiniteGaussPhase.angularFactor,map_zero,norm_zero,Complex.ofReal_zero,
        div_zero,star_zero,zero_pow (by decide : (3:ℕ)≠0),zero_mul,zero_div]
    simp only [summand,hc,mul_zero,zero_mul]

lemma markedSummand_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (X : ℝ) (I J : Id) :
    markedSummand S D Ψ W X I J=
      summand (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X I J*
        (if D∣I*J^3 then (1:ℂ) else 0) := by
  rw [summand_mul_fixed_twist]
  change completedMask S D I J*summand Ψ W X I J=
    coprimalityMask (calibrationForSet S hS).generator (completedIndex I J)*summand Ψ W X I J*
      (if D∣I*J^3 then (1:ℂ) else 0)
  by_cases hA : completedIndex I J=0
  · rw [summand_zero_completedIndex Ψ W X I J hA]
    simp only [mul_zero,zero_mul]
  · have he := calibration_coprime_iff_excluded_span S hS (completedIndex I J)
    rw [completedIndex_eq_primaryGenerator] at he hA
    rw [(primaryGenerator_spec (I*J^3) hA).1] at he
    change _=(if IsCoprime (calibrationForSet S hS).generator (completedIndex I J) then (1:ℂ) else 0)*_ * _
    rw [completedIndex_eq_primaryGenerator,he]
    unfold completedMask
    by_cases hd : D∣I*J^3 <;> by_cases hx : ∀P∈S,¬P∣I*J^3 <;>
      simp only [hd,hx,and_self,and_false,true_and,false_and,ite_true,ite_false,mul_one,mul_zero,zero_mul] ; simp_all

lemma markedCompletedT_eq_punctured (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : Id) (Ψ : O→*ℂ) (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X) :
    ProbeCompleted.markedCompletedT S D Ψ W X=
      InverseMoment.markedCompletedT (coprimalityMask (calibrationForSet S hS).generator*Ψ) W X
        (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [InverseMoment.markedCompletedT_eq_tsum _ W hW X hX]
  unfold ProbeCompleted.markedCompletedT
  apply tsum_congr
  intro p
  exact markedSummand_eq_punctured S hS D Ψ W X p.1 p.2

lemma inverseMarkedCompletedT_congr_primary (Ψ Φ : O→*ℂ)
    (h : ∀n : O,ConcretePrimeRowBridge.goodLambda^2∣n-1→Ψ n=Φ n)
    (W : ℝ→ℂ) (X : ℝ) (d : Id→ℂ) :
    InverseMoment.markedCompletedT Ψ W X d=InverseMoment.markedCompletedT Φ W X d := by
  unfold InverseMoment.markedCompletedT
  apply tsum_congr
  intro I
  apply tsum_congr
  intro J
  rw [summand,summand,columnWeight_congr_primary Ψ Φ h,cubeWeight_congr_primary Ψ Φ h]

def calibrationLowData (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) :
    GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator :=
  goodMaskRowData _ 1 _ (calibrationForSet S hS).generator_ne_zero one_ne_zero
    (calibrationForSet S hS).generator_ne_zero

theorem correctedPhysicalRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X)
    (E : GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) W X=
      ∑χ : RayCharacter,correctionCoeff χ*InverseMoment.markedCompletedT
        (rowTwist (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator E s hs χ)
          (calibrationForSet S hS).generator 1 z) W X (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ _
  rw [markedCompletedT_eq_punctured S hS D _ W hW X hX]
  congr 1
  apply inverseMarkedCompletedT_congr_primary
  intro n hn
  exact (lowPeriodicRow_eq_primary η (calibrationForSet S hS) (calibrationForSet S hS).generator E
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2 s hs χ z n hn).symm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1219

/-! Original module: OAI.NumberTheory.DirichletL.Detector.RowInterchange
Source SHA256: a2cce044bfc064c73bcca39bc04ee79052b64909904c30773b36648c2eca7fff
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1220


namespace OAI

noncomputable section
open scoped BigOperators Classical
open MeasureTheory
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O

theorem spectralSummand_norm_eq_of_re (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (s t : ℂ) (h : s.re = t.re) (I J : Ideal O) :
    ‖spectralSummand S D Ψ s I J‖ = ‖spectralSummand S D Ψ t I J‖ := by
  have h3 : (3 * s).re = (3 * t).re := by simp [Complex.mul_re, h]
  simp only [spectralSummand, norm_mul, fullIdealWeight_norm_eq_of_re _ _ h,
    fullIdealWeight_norm_eq_of_re _ _ h3]

def mellinSummand (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (p : Ideal O × Ideal O) (y : ℝ) : ℂ :=
  (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) * Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
    spectralSummand S D Ψ ((σ : ℂ) + y * Complex.I) p.1 p.2

theorem mellinSummand_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) (y : ℝ) :
    ‖mellinSummand S D Ψ σ Z p y‖ =
      (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖) *
        Real.exp (-1 * y ^ 2) := by
  unfold mellinSummand
  rw [norm_mul, verticalKernel_norm Z hZ σ y,
    spectralSummand_norm_eq_of_re S D Ψ _ (σ : ℂ) (by simp)]
  ring

theorem mellinSummand_integrable (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    Integrable (mellinSummand S D Ψ σ Z p) := by
  have hc : Continuous (fun y : ℝ => (σ : ℂ) + y * Complex.I) := by fun_prop
  have ht : Continuous (fun y : ℝ => spectralSummand S D Ψ
      ((σ : ℂ) + y * Complex.I) p.1 p.2) :=
    continuous_const.mul ((fullIdealWeight_continuous p.1).comp hc |>.mul
      ((fullIdealWeight_continuous p.2).comp (continuous_const.mul hc)))
  have hk := (hc.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hZ.ne'))).mul ((hc.pow 2).cexp)
  apply ((integrable_exp_neg_mul_sq (b := 1) (by norm_num)).const_mul
    (Z ^ σ * Real.exp (σ ^ 2) * ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖)).mono'
    (hk.mul ht).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun y => (mellinSummand_norm S D Ψ σ Z hZ p y).le)

theorem mellinSummand_integral_norm (S : Finset (Ideal O)) (D : Ideal O) (Ψ : O →* ℂ)
    (σ Z : ℝ) (hZ : 0 < Z) (p : Ideal O × Ideal O) :
    (∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) =
      ‖spectralSummand S D Ψ (σ : ℂ) p.1 p.2‖ *
        (Z ^ σ * Real.exp (σ ^ 2) * ∫ y : ℝ, Real.exp (-1 * y ^ 2)) := by
  simp only [mellinSummand_norm S D Ψ σ Z hZ, integral_const_mul]
  ring

theorem spectralRow_integral_eq_tsum (S : Finset (Ideal O)) (D : Ideal O)
    (Ψ : O →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (σ : ℝ) (hσ : 1 < σ)
    (Z : ℝ) (hZ : 0 < Z) :
    (∫ y : ℝ, (Z : ℂ) ^ ((σ : ℂ) + y * Complex.I) *
      Complex.exp (((σ : ℂ) + y * Complex.I) ^ 2) *
      spectralRow S D Ψ ((σ : ℂ) + y * Complex.I)) =
      ∑' p, ∫ y : ℝ, mellinSummand S D Ψ σ Z p y := by
  let : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
  let : Countable (Ideal O) := ConcretePrimeRowBridge.idealGenerator_injective.countable
  have hs : Summable (fun p => ∫ y : ℝ, ‖mellinSummand S D Ψ σ Z p y‖) := by
    simp only [mellinSummand_integral_norm S D Ψ σ Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (σ : ℂ) hσ).norm.mul_right _
  rw [integral_tsum_of_summable_integral_norm
    (fun p => mellinSummand_integrable S D Ψ σ Z hZ p) hs]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro y
  simp only [mellinSummand, tsum_mul_left, spectralRow]

end SevenEighths.ProbeRow
end

end OAI
end OAIOriginalModule1220

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianMellin
Source SHA256: 0526d85d63bcee8a85cb945c231af1263839ca0808c6d714132d0781b2618a04
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1221



namespace OAI

noncomputable section
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianMellinProfile (y : ℝ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-(Complex.log (y:ℂ))^2/4)

lemma gaussianMellin_integral (y : ℝ) (hy : 0<y) (σ : ℝ) :
    (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      (Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log (y:ℂ))^2/4) := by
  have hi (v : ℝ) :
      (y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2)=
      Complex.exp ((-1:ℂ)*(v:ℂ)^2+
        (Complex.I*(2*(σ:ℂ)-Complex.log (y:ℂ)))*(v:ℂ)+
        ((σ:ℂ)^2-Complex.log (y:ℂ)*(σ:ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),←Complex.exp_add]
    congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring
  simp_rw [hi]
  rw [integral_cexp_quadratic (by norm_num : (-1:ℂ).re<0)]
  congr 1
  · norm_num
  · congr 1
    ring_nf
    simp only [Complex.I_sq]
    ring

lemma gaussianMellin_inversion (y : ℝ) (hy : 0<y) (σ : ℝ) :
    ((1/(2*Real.pi):ℝ):ℂ)*
      (∫v : ℝ,(y:ℂ)^(-((σ:ℂ)+v*Complex.I))*Complex.exp (((σ:ℂ)+v*Complex.I)^2))=
      gaussianMellinProfile y := by
  rw [gaussianMellin_integral y hy σ]
  exact mul_assoc _ _ _ |>.symm

lemma gaussian_completed_norm_power (a b Z : ℝ) (ha : 0<a) (hb : 0<b) (hZ : 0<Z) (t : ℂ) :
    (Z:ℂ)^t*((a:ℂ)^(-t)*(b:ℂ)^(-(3*t)))=((a*b^3/Z:ℝ):ℂ)^(-t) := by
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos ha (pow_pos hb 3)).le hZ.le]
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le (pow_pos hb 3).le]
  have hp : ((b^3:ℝ):ℂ)^(-t)=(b:ℂ)^((3:ℂ)*(-t)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hb.le (3:ℝ) (-t)).symm
  rw [hp,Complex.cpow_neg (Z:ℂ),div_inv_eq_mul]
  rw [show (3:ℂ)*(-t)= -(3*t) by ring]
  ring

lemma gaussianMellinProfile_norm (y : ℝ) (hy : 0<y) :
    ‖gaussianMellinProfile y‖=
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (-(Real.log y)^2/4) := by
  unfold gaussianMellinProfile
  rw [norm_mul,Complex.norm_exp,←Complex.ofReal_log hy.le]
  congr 2
  simp [←Complex.ofReal_pow]

lemma gaussianMellinProfile_power_bound (y : ℝ) (hy : 0<y) (a : ℝ) :
    ‖gaussianMellinProfile y‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (a^2)*y^(-a) := by
  rw [gaussianMellinProfile_norm y hy,Real.rpow_def_of_pos hy]
  rw [mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log y/2-a)]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1221

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianCompletion
Source SHA256: 5ee7ec8c1869fcce035ad7aa2b0dffefa706cc1d5d42e4385f3330d1149ceeb1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1222



namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss CubicEisenstein
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedProfile (y : ℝ) : ℂ := gaussianMellinProfile y/(Real.sqrt y:ℂ)

lemma gaussianCompleted_Vstar (y : ℝ) (hy : 0<y) :
    Vstar gaussianCompletedProfile y=gaussianMellinProfile y := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianCompletedProfile]
  field_simp

lemma gaussian_mellinSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (σ Z : ℝ) (hZ : 0<Z) (I J : Id) :
    ((1/(2*Real.pi):ℝ):ℂ)*(∫v : ℝ,mellinSummand S D Ψ σ Z (I,J) v)=
      correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [mellinSummand,spectralSummand,fullIdealWeight,correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hq : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z :=
    div_pos (mul_pos hi (pow_pos hj 3)) hZ
  have hp (v : ℝ) : mellinSummand S D Ψ σ Z (I,J) v=
      (((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z:ℝ):ℂ)^(-((σ:ℂ)+v*Complex.I))*
      Complex.exp (((σ:ℂ)+v*Complex.I)^2)*
      (completedMask S D I J*completedCorrection I J*
        (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J) := by
    unfold mellinSummand spectralSummand fullIdealWeight
    simp only [ite_eq_right hI,ite_eq_right hJ]
    rw [←gaussian_completed_norm_power _ _ Z hi hj hZ]
    push_cast
    ring
  simp_rw [hp]
  rw [integral_mul_const,←mul_assoc,gaussianMellin_inversion _ hq σ]
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianCompleted_Vstar _ hq]
  ring

lemma gaussian_correctedSummand_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    Summable (fun p : Id×Id=>correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2) := by
  have hs : Summable (fun p : Id×Id=>∫v : ℝ,‖mellinSummand S D Ψ 2 Z p v‖) := by
    simp only [mellinSummand_integral_norm S D Ψ 2 Z hZ]
    exact (spectralRow_summable S D Ψ hΨ (2:ℂ) (by norm_num)).norm.mul_right _
  have hi : Summable (fun p : Id×Id=>∫v : ℝ,mellinSummand S D Ψ 2 Z p v) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun _=>norm_nonneg _) (fun p=>norm_integral_le_integral_norm _) hs
  have hh := hi.mul_left (((1/(2*Real.pi):ℝ):ℂ))
  simpa only [gaussian_mellinSummand S D Ψ 2 Z hZ] using hh

theorem spectralRow_eq_gaussianCompleted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (σ : ℝ) (hσ : 1<σ) (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral σ (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow S D Ψ t)=
      correctedCompletedT S D Ψ gaussianCompletedProfile Z := by
  rw [verticalIntegral,spectralRow_integral_eq_tsum S D Ψ hΨ σ hσ Z hZ,←tsum_mul_left]
  unfold correctedCompletedT
  apply tsum_congr
  intro p
  exact gaussian_mellinSummand S D Ψ σ Z hZ p.1 p.2

theorem markedPhysicalProbe_eq_gaussian (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (X Y Z : ℝ) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      (Y:ℂ)⁻¹*∑'s : {I : Id // CanonicalQuadraticSieve.Supported I},
        if ∀P∈C.excluded,¬P∣s.val then
          let a := primaryGenerator s.val
          let ha := CanonicalQuadraticSieve.supported_primaryGenerator_ne_zero s.val s.property
          let has := (CanonicalQuadraticSieve.supported_span_primaryGenerator_iff s.val).mpr s.property
          let q : ℝ := Ideal.absNorm s.val
          W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator s.val/
            (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
          ∑'m : O,C.residueMonoid m*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)*
            W0 (elementNorm m/(elementNorm C.generator*q*X))*
            correctedCompletedT C.excluded D (rowCoefficient η C.Xi a has m)
              gaussianCompletedProfile Z
        else 0 := by
  unfold markedPhysicalProbe
  congr 1
  apply tsum_congr
  intro s
  split_ifs with h
  · dsimp only
    congr 1
    apply tsum_congr
    intro m
    rw [spectralRow_eq_gaussianCompleted _ _ _
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m) 4 (by norm_num) Z hZ]
  · rfl

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1222

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianPartition
Source SHA256: e8c07b6a103deb0f0e65277c1a06b5035a36482560d9ac5c6389eaf4c783277b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1223



namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
namespace SevenEighths.ProbePhysical
open DyadicTransfer

def gaussianCutoff (y : ℝ) : ℂ := (Real.smoothTransition (2-y):ℂ)
def gaussianAnnulus (y : ℝ) : ℂ := annularCutoff gaussianCutoff y

lemma gaussianCutoff_small (y : ℝ) (hy : y≤1) : gaussianCutoff y=1 := by
  simp only [gaussianCutoff,Real.smoothTransition.one_of_one_le (by linarith : 1≤2-y),Complex.ofReal_one]
lemma gaussianCutoff_large (y : ℝ) (hy : 2≤y) : gaussianCutoff y=0 := by
  simp only [gaussianCutoff,Real.smoothTransition.zero_of_nonpos (by linarith : 2-y≤0),Complex.ofReal_zero]
lemma gaussianAnnulus_small (y : ℝ) (hy : y≤1/2) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_le_half gaussianCutoff gaussianCutoff_small hy
lemma gaussianAnnulus_large (y : ℝ) (hy : 2≤y) : gaussianAnnulus y=0 :=
  annularCutoff_eq_zero_of_two_le gaussianCutoff gaussianCutoff_large hy
lemma gaussianAnnulus_contDiff : ContDiff ℝ ∞ gaussianAnnulus := by
  unfold gaussianAnnulus annularCutoff gaussianCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).sub
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))
lemma gaussianAnnulus_compact : HasCompactSupport gaussianAnnulus := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianAnnulus y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianAnnulus_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianAnnulus_large y (le_of_lt (lt_of_not_ge h)))

lemma gaussianAnnulus_nonneg (y : ℝ) : 0≤(gaussianAnnulus y).re := by
  by_cases hy : y≤1/2
  · rw [gaussianAnnulus_small y hy]; simp
  · change 0≤Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)
    exact sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))
lemma gaussianAnnulus_norm (y : ℝ) : ‖gaussianAnnulus y‖=(gaussianAnnulus y).re := by
  have h : gaussianAnnulus y=((gaussianAnnulus y).re:ℂ) := by
    simp [gaussianAnnulus,annularCutoff,gaussianCutoff]
  rw [h,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (gaussianAnnulus_nonneg y)]
  rfl

lemma gaussianAnnulus_support_scales (x : ℝ) (K : ℕ)
    (hlo : (2:ℝ)^K≤x) (hhi : x<(2:ℝ)^(K+1)) (j : ℕ) (hj : j∉({K,K+1}:Finset ℕ)) :
    gaussianAnnulus (x/(2:ℝ)^j)=0 := by
  have hp : (0:ℝ)<2^j := by positivity
  have hj' : j≠K ∧ j≠K+1 := by simpa using hj
  by_cases hlt : j<K
  · apply gaussianAnnulus_large
    apply (le_div_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show j+1≤K by omega)
    rw [pow_succ] at h
    linarith
  · apply gaussianAnnulus_small
    apply (div_le_iff₀ hp).mpr
    have h := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) (show K+2≤j by omega)
    have he : (2:ℝ)^(K+2)=2*((2:ℝ)^(K+1)) := by rw [pow_succ]; ring
    rw [he] at h
    linarith

lemma gaussianAnnulus_partition (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j)) 1 := by
  obtain ⟨K,hlo,hhi⟩ := exists_nat_pow_near hx (by norm_num : (1:ℝ)<2)
  have h : HasSum (fun j : ℕ=>gaussianAnnulus (x/(2:ℝ)^j))
      (∑j∈({K,K+1}:Finset ℕ),gaussianAnnulus (x/(2:ℝ)^j)) :=
    hasSum_sum_of_ne_finset_zero (gaussianAnnulus_support_scales x K hlo hhi)
  convert h using 1
  rw [Finset.sum_pair (by omega : K≠K+1)]
  unfold gaussianAnnulus annularCutoff
  have he : 2*(x/(2:ℝ)^(K+1))=x/(2:ℝ)^K := by rw [pow_succ]; field_simp
  have hh : 2≤2*(x/(2:ℝ)^K) := by
    have hq : 1≤x/(2:ℝ)^K := (one_le_div (by positivity)).mpr hlo
    linarith
  rw [he,gaussianCutoff_small _ ((div_le_one (by positivity)).mpr hhi.le),
    gaussianCutoff_large _ hh]
  ring

lemma gaussianAnnulus_partition_norm (x : ℝ) (hx : 1≤x) :
    HasSum (fun j : ℕ=>‖gaussianAnnulus (x/(2:ℝ)^j)‖) 1 := by
  simpa only [gaussianAnnulus_norm,Complex.one_re] using
    Complex.hasSum_re (gaussianAnnulus_partition x hx)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1223

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianWindows
Source SHA256: 045f00d06e64c005c0d37031c3842152d959fea2609ce4cb2f4916f7485f8f50
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1224


namespace OAI

noncomputable section
open scoped Classical Topology ContDiff
open Filter
namespace SevenEighths.ProbePhysical
open CompletedGauss

lemma gaussianMellinProfile_real (y : ℝ) (hy : 0<y) :
    gaussianMellinProfile y=
      ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
        (Real.exp (-(Real.log y)^2/4):ℂ) := by
  unfold gaussianMellinProfile
  rw [←Complex.ofReal_log hy.le]
  congr 1
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring

def gaussianDyadicProfile (Z : ℝ) (j : ℕ) (y : ℝ) : ℂ :=
  gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z)/(Real.sqrt y:ℂ)

lemma gaussianDyadicProfile_small (Z : ℝ) (j : ℕ) (y : ℝ) (hy : y≤1/2) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_small y hy,zero_mul,zero_div]
lemma gaussianDyadicProfile_large (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 2≤y) :
    gaussianDyadicProfile Z j y=0 := by
  simp only [gaussianDyadicProfile,gaussianAnnulus_large y hy,zero_mul,zero_div]

lemma gaussianDyadicProfile_compact (Z : ℝ) (j : ℕ) : HasCompactSupport (gaussianDyadicProfile Z j) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianDyadicProfile Z j y≠0 at hy
  constructor
  · by_contra h
    exact hy (gaussianDyadicProfile_small Z j y (le_of_lt (lt_of_not_ge h)))
  · by_contra h
    exact hy (gaussianDyadicProfile_large Z j y (le_of_lt (lt_of_not_ge h)))

lemma gaussianDyadicProfile_contDiff (Z : ℝ) (hZ : 0<Z) (j : ℕ) :
    ContDiff ℝ ∞ (gaussianDyadicProfile Z j) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have he : gaussianDyadicProfile Z j =ᶠ[𝓝 y]
        (fun x : ℝ=>gaussianAnnulus x*
          (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
            (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))/(Real.sqrt x:ℂ)) := by
      filter_upwards [eventually_gt_nhds hy] with x hx
      rw [gaussianDyadicProfile,gaussianMellinProfile_real _ (div_pos (mul_pos (by positivity) hx) hZ)]
    apply ContDiffAt.congr_of_eventuallyEq _ he
    have hq : (2:ℝ)^j*y/Z≠0 := ne_of_gt (div_pos (mul_pos (by positivity) hy) hZ)
    have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have ha := gaussianAnnulus_contDiff.contDiffAt (x:=y)
    have hl : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.log ((2:ℝ)^j*x/Z)) y :=
      (show ContDiffAt ℝ ∞ (fun x : ℝ=>(2:ℝ)^j*x/Z) y by fun_prop).log hq
    have hg : ContDiffAt ℝ ∞ (fun x : ℝ=>Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4)) y :=
      ((hl.pow 2).neg.div_const 4).exp
    have hgC := Complex.ofRealCLM.contDiff.contDiffAt.comp y hg
    have hsR : ContDiffAt ℝ ∞ Real.sqrt y := Real.contDiffAt_sqrt hy.ne'
    have ht : ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianAnnulus x*
        (((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
          (Real.exp (-(Real.log ((2:ℝ)^j*x/Z))^2/4):ℂ))) y :=
      ha.mul (contDiffAt_const.mul hgC)
    have hsc : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y hsR
    simpa only [div_eq_mul_inv] using ht.mul (hsc.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianDyadicProfile_small Z j x hx.le

lemma gaussianDyadicProfile_Vstar (Z : ℝ) (j : ℕ) (y : ℝ) (hy : 0<y) :
    Vstar (gaussianDyadicProfile Z j) y=
      gaussianAnnulus y*gaussianMellinProfile ((2:ℝ)^j*y/Z) := by
  have h : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
  simp only [Vstar,gaussianDyadicProfile]
  field_simp

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1224

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianDecomposition
Source SHA256: 494752f7dcd2e0916be5e4d3c7a64c24e5551a9bc5a5f278200e46f068ebf389
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1225


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma annular_reassembly_summable {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    Summable (fun q : α×ℕ=>gaussianAnnulus (N q.1/(2:ℝ)^q.2)*a q.1) := by
  have hs (p : α) : HasSum (fun j : ℕ=>‖gaussianAnnulus (N p/(2:ℝ)^j)*a p‖) ‖a p‖ := by
    by_cases hp : a p=0
    · simp only [hp,mul_zero,norm_zero]
      exact hasSum_zero
    · simpa only [norm_mul,one_mul] using (gaussianAnnulus_partition_norm (N p) (hN p hp)).mul_right ‖a p‖
  apply Summable.of_norm
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  exact ⟨fun p=>(hs p).summable,by simpa only [fun p=>(hs p).tsum_eq] using ha.norm⟩

lemma annular_reassembly {α : Type*} (a : α→ℂ) (N : α→ℝ)
    (ha : Summable a) (hN : ∀p,a p≠0→1≤N p) :
    (∑'j : ℕ,∑'p : α,gaussianAnnulus (N p/(2:ℝ)^j)*a p)=∑'p,a p := by
  rw [Summable.tsum_comm (f:=fun p : α=>fun j : ℕ=>gaussianAnnulus (N p/(2:ℝ)^j)*a p)
    (annular_reassembly_summable a N ha hN)]
  apply tsum_congr
  intro p
  by_cases hp : a p=0
  · simp [hp]
  · simpa only [one_mul] using ((gaussianAnnulus_partition (N p) (hN p hp)).mul_right (a p)).tsum_eq

lemma gaussian_dyadic_correctedSummand (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        correctedSummand S D Ψ gaussianCompletedProfile Z I J := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN := mul_pos hi (pow_pos hj 3)
  unfold correctedSummand markedSummand summand
  rw [gaussianDyadicProfile_Vstar _ _ _ (div_pos hN (by positivity)),
    gaussianCompleted_Vstar _ (div_pos hN hZ)]
  have he : (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/Z=
      (Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/Z := by
    field_simp
  rw [he]
  ring

lemma gaussian_correctedSummand_norm_ge_one (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (I J : Id)
    (h : correctedSummand S D Ψ gaussianCompletedProfile Z I J≠0) :
    1≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := by
  have hI : I≠0 := by intro he; subst I; simp [correctedSummand,markedSummand,summand] at h
  have hJ : J≠0 := by intro he; subst J; simp [correctedSummand,markedSummand,summand] at h
  have hi : 1≤Ideal.absNorm I := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : 1≤Ideal.absNorm J := Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  exact_mod_cast one_le_mul_of_one_le_of_one_le hi (one_le_pow₀ hj)

theorem correctedGaussian_eq_tsum_dyadic (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    correctedCompletedT S D Ψ gaussianCompletedProfile Z=
      ∑'j : ℕ,correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) := by
  unfold correctedCompletedT
  simp_rw [gaussian_dyadic_correctedSummand S D Ψ Z hZ]
  exact (annular_reassembly _ _ (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).symm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1225

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianLow
Source SHA256: 3a37f28e065cc4c54fbd92e44a08cf0dd03ac6ae1cebc0bba46203be74721bd6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1226



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianDyadicSchwartz (Z : ℝ) (hZ : 0<Z) (j : ℕ) : SchwartzMap ℝ ℂ :=
  (gaussianDyadicProfile_compact Z j).toSchwartzMap (gaussianDyadicProfile_contDiff Z hZ j)

theorem physicalSpectralRow_eq_dyadic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (Z : ℝ) (hZ : 0<Z) :
    verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*
      spectralRow S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z) t)=
      ∑'j : ℕ,∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (gaussianDyadicSchwartz Z hZ j) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  have hΨ := rowCoefficient_norm_le_one η (calibrationForSet S hS).Xi
    (calibrationForSet S hS).Xi_norm_le_one s hs z
  rw [spectralRow_eq_gaussianCompleted _ _ _ hΨ 4 (by norm_num) Z hZ,
    correctedGaussian_eq_tsum_dyadic _ _ _ hΨ Z hZ]
  apply tsum_congr
  intro j
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D
    (gaussianDyadicProfile Z j) (gaussianDyadicProfile_compact Z j) ((2:ℝ)^j)
    (by positivity) (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1226

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianDerivative
Source SHA256: e822dd45a58f81ae149643bd4749a53a2e52cee9d70dd83397415ac8e522cf6d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1227





namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianLog (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*Complex.exp (-(Complex.log z)^2/4)

lemma gaussianLog_ofReal (y : ℝ) : gaussianLog (y:ℂ)=gaussianMellinProfile y := rfl

lemma gaussianLog_power_bound (z : ℂ) (hz : z≠0) (a : ℝ) :
    ‖gaussianLog z‖≤
      ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*
        Real.exp (Real.pi^2/4+a^2)*‖z‖^(-a) := by
  have hre : (-(Complex.log z)^2/4).re=
      ((Complex.log z).im^2-(Real.log ‖z‖)^2)/4 := by
    simp [pow_two,Complex.mul_re,Complex.log_re]
  have hp : (Complex.log z).im^2≤Real.pi^2 := by
    have h1 := Complex.log_im_le_pi z
    have h2 := Complex.neg_pi_lt_log_im z
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (show 0≤Real.pi+(Complex.log z).im by linarith)]
  unfold gaussianLog
  rw [norm_mul,Complex.norm_exp,hre,Real.rpow_def_of_pos (norm_pos_iff.mpr hz),
    mul_assoc,←Real.exp_add]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  nlinarith [sq_nonneg (Real.log ‖z‖/2-a)]

lemma iteratedDeriv_restrict_positive (f : ℂ→ℂ)
    (hf : ∀x : ℝ,0<x→AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) (hx : 0<x) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : Set.EqOn (deriv (fun y : ℝ=>f (y:ℂ))) (fun y : ℝ=>deriv f (y:ℂ)) (Set.Ioi 0) := by
      intro y hy
      exact (hf y hy).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he.iteratedDeriv_of_isOpen isOpen_Ioi n hx]
    exact ih (deriv f) (fun y hy=>(hf y hy).deriv)

lemma gaussianLog_analytic (z : ℂ) (hz : 0<z.re) : AnalyticAt ℂ gaussianLog z := by
  have hl := analyticAt_clog (Complex.mem_slitPlane_iff.mpr (Or.inl hz))
  unfold gaussianLog
  exact analyticAt_const.mul (((hl.pow 2).neg.div_const (c:=4)).cexp)

lemma gaussianLog_scaled_analytic (r : ℝ) (hr : 0<r) (z : ℂ) (hz : 0<z.re) :
    AnalyticAt ℂ (fun w : ℂ=>gaussianLog ((r:ℂ)*w)) z := by
  have h : 0<((r:ℂ)*z).re := by simpa using mul_pos hr hz
  exact (gaussianLog_analytic _ h).comp (analyticAt_const.mul analyticAt_id)

lemma gaussianLog_scaled_disk_bound (a : ℝ) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0<r→∀y∈Set.Icc (1/2:ℝ) 2,
      ∀z∈Metric.closedBall (y:ℂ) (1/4),‖gaussianLog ((r:ℂ)*z)‖≤C*r^(-a) := by
  have hc : ContinuousOn (fun t : ℝ=>t^(-a)) (Set.Icc (1/4:ℝ) (9/4)) := by
    intro t ht
    exact (continuousAt_id.rpow_const (Or.inl (show t≠0 by linarith [ht.1]))).continuousWithinAt
  obtain ⟨B,hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  have hBpos : 0<B := by
    have hh := hB 1 (by norm_num : (1:ℝ)∈Set.Icc (1/4:ℝ) (9/4))
    norm_num at hh
    linarith
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖*Real.exp (Real.pi^2/4+a^2)
  have hcn : 0≤c := mul_nonneg (norm_nonneg _) (Real.exp_pos _).le
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro r hr y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hyr : ‖(y:ℂ)‖=y := by rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith [hy.1])]
  have hu := norm_sub_norm_le z (y:ℂ)
  have hl := norm_sub_norm_le (y:ℂ) z
  rw [hyr] at hu hl
  rw [norm_sub_rev] at hl
  have hzn : ‖z‖∈Set.Icc (1/4:ℝ) (9/4) := ⟨by linarith [hy.1],by linarith [hy.2]⟩
  have hz0 : z≠0 := norm_pos_iff.mp (by linarith [hzn.1])
  have hrz : (r:ℂ)*z≠0 := mul_ne_zero (Complex.ofReal_ne_zero.mpr hr.ne') hz0
  have hb : ‖z‖^(-a)≤B := (le_abs_self _).trans (hB ‖z‖ hzn)
  have hh := gaussianLog_power_bound ((r:ℂ)*z) hrz a
  have hnorm : ‖(r:ℂ)*z‖=r*‖z‖ := by rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hr]
  rw [hnorm,Real.mul_rpow hr.le (norm_nonneg _)] at hh
  calc
    _ ≤ c*(r^(-a)*‖z‖^(-a)) := hh
    _ ≤ c*(r^(-a)*B) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hb (by positivity)) hcn
    _ ≤ (c+1)*B*r^(-a) := by nlinarith [mul_nonneg hBpos.le (Real.rpow_pos_of_pos hr (-a)).le]

lemma gaussianLog_scaled_derivative_bound (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀r : ℝ,0<r→∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (fun x : ℝ=>gaussianMellinProfile (r*x)) y‖≤C*r^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLog_scaled_disk_bound a
  refine ⟨(n.factorial:ℝ)*B/(1/4:ℝ)^n,by positivity,?_⟩
  intro r hr y hy
  have hf : ∀x : ℝ,0<x→AnalyticAt ℂ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (x:ℂ) :=
    fun x hx=>gaussianLog_scaled_analytic r hr (x:ℂ) hx
  have he : (fun x : ℝ=>gaussianMellinProfile (r*x))=
      (fun x : ℝ=>gaussianLog ((r:ℂ)*(x:ℂ))) := by
    funext x
    rw [←Complex.ofReal_mul,gaussianLog_ofReal]
  rw [he,iteratedDeriv_restrict_positive _ hf n y (by linarith [hy.1])]
  have hd : DiffContOnCl ℂ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (Metric.ball (y:ℂ) (1/4)) := by
    apply DifferentiableOn.diffContOnCl_ball (U:={z : ℂ|0<z.re})
      (fun z hz=>(gaussianLog_scaled_analytic r hr z hz).differentiableAt.differentiableWithinAt)
    intro z hz
    have hn : ‖z-(y:ℂ)‖≤1/4 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
    have ha := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hn
    simp only [Complex.sub_re,Complex.ofReal_re,abs_le] at ha
    change 0<z.re
    linarith [hy.1]
  have hh := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1/4) hd
    (fun z hz=>hbound r hr y hy z (Metric.sphere_subset_closedBall hz))
  exact hh.trans_eq (by ring)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1227

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianSeminorm
Source SHA256: f355f3fe007d6f1f3bb535ca92e0e37e996ffc214669ae3f33cb1a8f2d11b25a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1228


namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open Filter Set
namespace SevenEighths.ProbePhysical

def gaussianFixedWindow (y : ℝ) : ℂ := gaussianAnnulus y/(Real.sqrt y:ℂ)
lemma gaussianFixedWindow_small (y : ℝ) (hy : y≤1/2) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_small y hy,zero_div]
lemma gaussianFixedWindow_large (y : ℝ) (hy : 2≤y) : gaussianFixedWindow y=0 := by
  simp only [gaussianFixedWindow,gaussianAnnulus_large y hy,zero_div]
lemma gaussianFixedWindow_compact : HasCompactSupport gaussianFixedWindow := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a:=(1/2:ℝ)) (b:=2))
  intro y hy
  change gaussianFixedWindow y≠0 at hy
  constructor
  · by_contra h; exact hy (gaussianFixedWindow_small y (le_of_lt (lt_of_not_ge h)))
  · by_contra h; exact hy (gaussianFixedWindow_large y (le_of_lt (lt_of_not_ge h)))
lemma gaussianFixedWindow_contDiff : ContDiff ℝ ∞ gaussianFixedWindow := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : 0<y
  · have hs : (Real.sqrt y:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hy).ne'
    have hf : ContDiffAt ℝ ∞ (fun x : ℝ=>(Real.sqrt x:ℂ)) y :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp y (Real.contDiffAt_sqrt hy.ne')
    unfold gaussianFixedWindow
    simp only [div_eq_mul_inv]
    exact gaussianAnnulus_contDiff.contDiffAt.mul (hf.fun_inv hs)
  · apply contDiffAt_const.congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds (show y<(1/2:ℝ) by linarith)] with x hx
    exact gaussianFixedWindow_small x hx.le

def gaussianFixedSchwartz : SchwartzMap ℝ ℂ := gaussianFixedWindow_compact.toSchwartzMap gaussianFixedWindow_contDiff

lemma gaussianProfile_scaled_smooth (r : ℝ) (hr : 0<r) (y : ℝ) (hy : 0<y) :
    ContDiffAt ℝ ∞ (fun x : ℝ=>gaussianMellinProfile (r*x)) y := by
  have hf : ContDiffAt ℂ ∞ (fun z : ℂ=>gaussianLog ((r:ℂ)*z)) (y:ℂ) :=
    (gaussianLog_scaled_analytic r hr (y:ℂ) hy).contDiffAt
  have hh := (hf.restrict_scalars ℝ).comp y Complex.ofRealCLM.contDiff.contDiffAt
  simpa only [Function.comp_def,Complex.ofRealCLM_apply,←Complex.ofReal_mul,gaussianLog_ofReal] using hh

lemma gaussianDyadicProfile_factor (Z : ℝ) (j : ℕ) :
    gaussianDyadicProfile Z j=(fun y : ℝ=>gaussianFixedWindow y*
      gaussianMellinProfile (((2:ℝ)^j/Z)*y)) := by
  funext y
  unfold gaussianDyadicProfile gaussianFixedWindow
  rw [show (2:ℝ)^j*y/Z=((2:ℝ)^j/Z)*y by ring]
  ring

lemma gaussianDyadicProfile_derivative_outside (Z : ℝ) (j n : ℕ) (y : ℝ)
    (hy : y∉Set.Icc (1/2:ℝ) 2) : iteratedDeriv n (gaussianDyadicProfile Z j) y=0 := by
  have he : gaussianDyadicProfile Z j=ᶠ[𝓝 y](fun _=>0) := by
    simp only [Set.mem_Icc,not_and_or,not_le] at hy
    rcases hy with hy|hy
    · filter_upwards [eventually_lt_nhds hy] with x hx
      exact gaussianDyadicProfile_small Z j x hx.le
    · filter_upwards [eventually_gt_nhds hy] with x hx
      exact gaussianDyadicProfile_large Z j x hx.le
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianDyadicProfile_derivative_uniform (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→∀j : ℕ,∀y∈Set.Icc (1/2:ℝ) 2,
      ‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤C*(((2:ℝ)^j/Z)^(-a)) := by
  choose B hB hbound using fun i : ℕ=>gaussianLog_scaled_derivative_bound a i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i gaussianFixedSchwartz
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := by exact apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro Z hZ j y hy
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  have hy0 : 0<y := by linarith [hy.1]
  rw [gaussianDyadicProfile_factor,iteratedDeriv_fun_mul
    (gaussianFixedWindow_contDiff.contDiffAt.of_le (by simp))
    ((gaussianProfile_scaled_smooth _ hr y hy0).of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i gaussianFixedWindow y*
        iteratedDeriv (n-i) (fun x : ℝ=>gaussianMellinProfile (((2:ℝ)^j/Z)*x)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*(((2:ℝ)^j/Z)^(-a))) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hfixed : ‖iteratedDeriv i gaussianFixedWindow y‖≤A i := by
        have hh := SchwartzMap.le_seminorm' ℝ 0 i gaussianFixedSchwartz y
        simp only [pow_zero,one_mul] at hh
        exact hh
      exact mul_le_mul (mul_le_mul_of_nonneg_left hfixed (Nat.cast_nonneg _))
        (hbound _ _ hr y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*(((2:ℝ)^j/Z)^(-a)) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*(((2:ℝ)^j/Z)^(-a)) := by nlinarith [Real.rpow_pos_of_pos hr (-a)]

theorem gaussianDyadicSchwartz_seminorm (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      SchwartzMap.seminorm ℝ k n (gaussianDyadicSchwartz Z hZ j)≤C*(((2:ℝ)^j/Z)^(-a)) := by
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicProfile_derivative_uniform a n
  refine ⟨(2:ℝ)^k*B,by positivity,?_⟩
  intro Z hZ j
  have hr : 0<(2:ℝ)^j/Z := div_pos (by positivity) hZ
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  change |y|^k*‖iteratedDeriv n (gaussianDyadicProfile Z j) y‖≤_
  by_cases hy : y∈Set.Icc (1/2:ℝ) 2
  · have habs : |y|≤2 := by rw [abs_of_nonneg (by linarith [hy.1])]; exact hy.2
    calc
      _ ≤ (2:ℝ)^k*(B*(((2:ℝ)^j/Z)^(-a))) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) habs k) (hbound Z hZ j y hy)
          (norm_nonneg _) (by positivity)
      _ = _ := by ring
  · rw [gaussianDyadicProfile_derivative_outside Z j n y hy,norm_zero,mul_zero]
    positivity

theorem gaussianDyadicSchwartz_finite_seminorm (a : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*(((2:ℝ)^j/Z)^(-a)) := by
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1,by norm_num,?_⟩
    intro Z hZ j
    simp only [Finset.sup_empty,one_mul]
    change 0≤(((2:ℝ)^j/Z)^(-a))
    exact Real.rpow_nonneg (by positivity) _
  | @insert p S hp ih =>
    obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_seminorm a p.1 p.2
    obtain ⟨C,hC,hrest⟩ := ih
    refine ⟨B+C,by positivity,?_⟩
    intro Z hZ j
    rw [Finset.sup_insert,Seminorm.sup_apply]
    apply max_le
    · exact (hbound Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])
    · exact (hrest Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-a)])

theorem gaussianDyadicSchwartz_two_sided (A : ℝ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C*min (((2:ℝ)^j/Z)^A) (((2:ℝ)^j/Z)^(-A)) := by
  obtain ⟨B,hB,hlo⟩ := gaussianDyadicSchwartz_finite_seminorm (-A) S
  obtain ⟨C,hC,hhi⟩ := gaussianDyadicSchwartz_finite_seminorm A S
  refine ⟨B+C,by positivity,?_⟩
  intro Z hZ j
  rw [mul_min_of_nonneg _ _ (by positivity : 0≤B+C)]
  apply le_min
  · have hh := hlo Z hZ j
    rw [neg_neg] at hh
    exact hh.trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) A])
  · exact (hhi Z hZ j).trans (by nlinarith [Real.rpow_nonneg (by positivity : 0≤(2:ℝ)^j/Z) (-A)])

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1228

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianSummation
Source SHA256: 8cbdf3603586c4d8f8da6f22fcbbcc8d4521d19b7977da4a2db8c7b5e537e196
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1229


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbePhysical

lemma gaussianDyadicSchwartz_polynomial_decay (N : ℕ) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,∀j : ℕ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
        C/(1+(2:ℝ)^j/Z)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianDyadicSchwartz_finite_seminorm 0 S
  obtain ⟨C,hC,hdecay⟩ := gaussianDyadicSchwartz_finite_seminorm (N:ℝ) S
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro Z hZ j
  let r := (2:ℝ)^j/Z
  have hr : 0<r := div_pos (by positivity) hZ
  have hden : 0<(1+r)^N := pow_pos (by linarith) _
  change _≤(B+C)*(2:ℝ)^N/(1+r)^N
  by_cases hr1 : r≤1
  · have hh := hzero Z hZ j
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay Z hZ j
    change _≤C*r^(-(N:ℝ)) at hh
    rw [Real.rpow_neg hr.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+r)^N≤(2*r)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hi : 0≤C*(r^N)⁻¹ := by positivity
    have hm := mul_le_mul_of_nonneg_left hp hi
    rw [mul_pow] at hm
    have hn : r^N≠0 := ne_of_gt (pow_pos hr _)
    have he : (C*(r^N)⁻¹)*((2:ℝ)^N*r^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianDyadicSchwartz_summed (s : ℝ) (hs : 0<s) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,∀hZ : 0<Z,
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*
        S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianDyadicSchwartz_polynomial_decay N S
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound Z hZ j) (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (gaussianDyadicSchwartz Z hZ j) := by positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1229

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianFlow
Source SHA256: 86398c70748f960142fac626a425eed4d91623fd4b8a894746c1916126ebf975
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1230


namespace OAI

noncomputable section
open scoped Classical ContDiff Topology
open Filter Set Metric
namespace SevenEighths.ProbePhysical

def gaussianFlow (R : ℝ) (z : ℂ) : ℂ :=
  ((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)*
    Complex.exp (-((Real.log R:ℂ)+z)^2/4)
lemma gaussianFlow_analytic (R : ℝ) (z : ℂ) : AnalyticAt ℂ (gaussianFlow R) z := by
  unfold gaussianFlow
  fun_prop
lemma gaussianFlow_real (R : ℝ) (hR : 0<R) (s : ℝ) :
    gaussianFlow R (s:ℂ)=gaussianMellinProfile (R*Real.exp s) := by
  unfold gaussianFlow gaussianMellinProfile
  rw [←Complex.ofReal_log (mul_pos hR (Real.exp_pos _)).le,Real.log_mul hR.ne' (Real.exp_pos _).ne',Real.log_exp,
    Complex.ofReal_add]

lemma iteratedDeriv_restrict_real (f : ℂ→ℂ)
    (hf : ∀x : ℝ,AnalyticAt ℂ f (x:ℂ)) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (fun y : ℝ=>f (y:ℂ)) x=iteratedDeriv n f (x:ℂ) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iteratedDeriv_succ',iteratedDeriv_succ']
    have he : deriv (fun y : ℝ=>f (y:ℂ))=(fun y : ℝ=>deriv f (y:ℂ)) := by
      funext y
      exact (hf y).differentiableAt.hasDerivAt.comp_ofReal.deriv
    rw [he]
    exact ih (deriv f) (fun y=>(hf y).deriv)

lemma gaussianFlow_disk_bound (a L : ℝ) (_hL : 0≤L) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ∀z∈Metric.closedBall (y:ℂ) 1,‖gaussianFlow R z‖≤C*R^(-a) := by
  let c := ‖((1/(2*Real.pi):ℝ):ℂ)*(Real.pi:ℂ)^(1/2:ℂ)‖
  let B := Real.exp (a^2+1/4+|a| *(L+1))
  have hc : 0≤c := norm_nonneg _
  have hB : 0<B := Real.exp_pos _
  refine ⟨(c+1)*B,by positivity,?_⟩
  intro R hR y hy z hz
  have hd : ‖z-(y:ℂ)‖≤1 := by simpa only [Metric.mem_closedBall,dist_eq_norm] using hz
  have hzr := (Complex.abs_re_le_norm (z-(y:ℂ))).trans hd
  have hzi := (Complex.abs_im_le_norm (z-(y:ℂ))).trans hd
  simp only [Complex.sub_re,Complex.sub_im,Complex.ofReal_re,Complex.ofReal_im,sub_zero] at hzr hzi
  have hre : |z.re|≤L+1 := by
    have h := abs_add_le (z.re-y) y
    have he : z.re-y+y=z.re := by ring
    rw [he] at h
    linarith
  have hsq : z.im^2≤1 := by nlinarith [(abs_le.mp hzi).1,(abs_le.mp hzi).2]
  have hmul : -(a*z.re)≤|a| *(L+1) := by
    calc
      _ ≤ |a*z.re| := neg_le_abs _
      _ = |a| *|z.re| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hre (abs_nonneg _)
  have he : (-((Real.log R:ℂ)+z)^2/4).re=(z.im^2-(Real.log R+z.re)^2)/4 := by
    simp [pow_two,Complex.mul_re]
  unfold gaussianFlow
  rw [norm_mul,Complex.norm_exp,he]
  have hb : Real.exp ((z.im^2-(Real.log R+z.re)^2)/4)≤B*R^(-a) := by
    rw [Real.rpow_def_of_pos hR,←Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [sq_nonneg ((Real.log R+z.re)/2-a)]
  calc
    _ ≤ c*(B*R^(-a)) := mul_le_mul_of_nonneg_left hb hc
    _ ≤ (c+1)*B*R^(-a) := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]

lemma gaussianFlow_derivative_bound (a L : ℝ) (hL : 0≤L) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianFlow_disk_bound a L hL
  refine ⟨(n.factorial:ℝ)*B,by positivity,?_⟩
  intro R hR y hy
  rw [iteratedDeriv_restrict_real _ (fun x=>gaussianFlow_analytic R (x:ℂ)) n y]
  have hf : Differentiable ℂ (gaussianFlow R) := fun z=>(gaussianFlow_analytic R z).differentiableAt
  have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n
    (by norm_num : (0:ℝ)<1) hf.diffContOnCl
    (fun z hz=>hbound R hR y hy z (Metric.sphere_subset_closedBall hz))
  simpa only [one_pow,div_one,mul_assoc] using h

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1230

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianLogWindow
Source SHA256: e508f509619ab460fd408a82752c3d2694af63fcc8e6a5ec01d9b31910945d02
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1231


namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open Filter Set MeasureTheory
namespace SevenEighths.ProbePhysical

lemma gaussianFlow_real_smooth (R : ℝ) : ContDiff ℝ ∞ (fun s : ℝ=>gaussianFlow R (s:ℂ)) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have hf : ContDiffAt ℂ ∞ (gaussianFlow R) (s:ℂ) := (gaussianFlow_analytic R _).contDiffAt
  exact (hf.restrict_scalars ℝ).comp s Complex.ofRealCLM.contDiff.contDiffAt

def gaussianLogWindow (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  (hV.mul_right (f':=fun s : ℝ=>gaussianFlow R (s:ℂ))).toSchwartzMap
    (V.smooth'.mul (gaussianFlow_real_smooth R))
@[simp] lemma gaussianLogWindow_apply (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R s : ℝ) : gaussianLogWindow V hV R s=V s*gaussianFlow R (s:ℂ) := rfl

lemma gaussianLogWindow_derivative_outside (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hbox : ∀s,V s≠0→|s|≤L) (R y : ℝ) (hy : L < |y|) (n : ℕ) :
    iteratedDeriv n (gaussianLogWindow V hV R) y=0 := by
  have he : (gaussianLogWindow V hV R:ℝ→ℂ)=ᶠ[𝓝 y](fun _=>0) := by
    have hu : {x : ℝ | L < |x|}∈𝓝 y := (isOpen_lt continuous_const continuous_abs).mem_nhds hy
    filter_upwards [hu] with x hx
    have hv : V x=0 := by by_contra h; exact (not_lt_of_ge (hbox x h)) hx
    simp only [gaussianLogWindow_apply,hv,zero_mul]
  rw [he.iteratedDeriv_eq n]
  simp

lemma gaussianLogWindow_derivative_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (a : ℝ) (n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→∀y : ℝ,|y|≤L→
      ‖iteratedDeriv n (gaussianLogWindow V hV R) y‖≤C*R^(-a) := by
  choose B hB hbound using fun i : ℕ=>gaussianFlow_derivative_bound a L hL i
  let A (i : ℕ) := SchwartzMap.seminorm ℝ 0 i V
  let C := ∑i∈Finset.range (n+1),(n.choose i:ℝ)*A i*B (n-i)
  have hA (i : ℕ) : 0≤A i := apply_nonneg _ _
  have hC : 0≤C := Finset.sum_nonneg (fun i _=>mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hA i)) (hB _).le)
  refine ⟨C+1,by positivity,?_⟩
  intro R hR y hy
  change ‖iteratedDeriv n (fun s : ℝ=>V s*gaussianFlow R (s:ℂ)) y‖≤_
  rw [iteratedDeriv_fun_mul (f:=(V:ℝ→ℂ)) (g:=fun s : ℝ=>gaussianFlow R (s:ℂ))
    (V.smooth'.contDiffAt.of_le (by simp))
    ((gaussianFlow_real_smooth R).contDiffAt.of_le (by simp))]
  calc
    _ ≤ ∑i∈Finset.range (n+1),‖(n.choose i:ℂ)*iteratedDeriv i V y*
        iteratedDeriv (n-i) (fun s : ℝ=>gaussianFlow R (s:ℂ)) y‖ := norm_sum_le _ _
    _ ≤ ∑i∈Finset.range (n+1),((n.choose i:ℝ)*A i)*(B (n-i)*R^(-a)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul,norm_mul,Complex.norm_natCast]
      have hv : ‖iteratedDeriv i V y‖≤A i := by
        simpa only [pow_zero,one_mul] using SchwartzMap.le_seminorm' ℝ 0 i V y
      exact mul_le_mul (mul_le_mul_of_nonneg_left hv (Nat.cast_nonneg _))
        (hbound _ R hR y hy) (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hA i))
    _ = C*R^(-a) := by simp only [C,Finset.sum_mul]; apply Finset.sum_congr rfl; intros; ring
    _ ≤ (C+1)*R^(-a) := by nlinarith [Real.rpow_pos_of_pos hR (-a)]

theorem gaussianLogWindow_seminorm (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      SchwartzMap.seminorm ℝ k n (gaussianLogWindow V hV R)≤C*R^(-a) := by
  obtain ⟨B,hB,hbound⟩ := gaussianLogWindow_derivative_bound V hV L hL a n
  refine ⟨(1+L^k)*B,by positivity,?_⟩
  intro R hR
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro y
  by_cases hy : |y|≤L
  · calc
      _ ≤ L^k*(B*R^(-a)) := mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) hy k)
        (hbound R hR y hy) (norm_nonneg _) (pow_nonneg hL _)
      _ ≤ _ := by nlinarith [mul_pos hB (Real.rpow_pos_of_pos hR (-a))]
  · rw [gaussianLogWindow_derivative_outside V hV L hbox R y (lt_of_not_ge hy) n,norm_zero,mul_zero]
    positivity

theorem gaussianLogWindow_fourier_moment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (L : ℝ) (hL : 0≤L) (hbox : ∀s,V s≠0→|s|≤L) (a : ℝ) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
      (∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤C*R^(-a) := by
  let p := (MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower
  let K := J+p
  choose B hB hb using fun q : ℕ×ℕ=>gaussianLogWindow_seminorm V hV L hL hbox a q.1 q.2
  let C := (∑i∈Finset.range (K+1),(B (0,i)+B (p,i)))+1
  have hC : 0<C := by
    have hh : 0≤∑i∈Finset.range (K+1),(B (0,i)+B (p,i)) :=
      Finset.sum_nonneg (fun i _=>add_nonneg (hB _).le (hB _).le)
    dsimp only [C]; linarith
  let D := (2:ℝ)^J*(FourierBridge.coefficientMomentBound 0 C+FourierBridge.coefficientMomentBound J C)
  have hD : 0≤D := mul_nonneg (by positivity)
    (add_nonneg (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le)
      (FourierBridge.coefficientMomentBound_nonneg _ _ hC.le))
  refine ⟨D+1,by positivity,?_⟩
  intro R hR
  have hcancel : R^a*R^(-a)=1 := by rw [←Real.rpow_add hR]; simp
  have hsource (i : ℕ) (hi : i≤J+(MeasureTheory.volume : MeasureTheory.Measure ℝ).integrablePower) :
      R^a*(SchwartzMap.seminorm ℝ 0 i (gaussianLogWindow V hV R)+
        SchwartzMap.seminorm ℝ p i (gaussianLogWindow V hV R))≤C := by
    have hbi : B (0,i)+B (p,i)≤C := by
      have hh := Finset.single_le_sum (s:=Finset.range (K+1)) (a:=i)
        (f:=fun i=>B (0,i)+B (p,i))
        (fun i _=>add_nonneg (hB _).le (hB _).le) (Finset.mem_range.mpr (by dsimp only [K,p]; omega))
      dsimp only [C]; linarith
    calc
      _ ≤ R^a*(B (0,i)*R^(-a)+B (p,i)*R^(-a)) :=
        mul_le_mul_of_nonneg_left (add_le_add (hb (0,i) R hR) (hb (p,i) R hR)) (by positivity)
      _ = B (0,i)+B (p,i) := by rw [←add_mul]; calc
        _=(B (0,i)+B (p,i))*(R^a*R^(-a)) := by ring
        _=_ := by rw [hcancel,mul_one]
      _ ≤ C := hbi
  have hh := FourierBridge.uniform_fourier_one_plus_moment (gaussianLogWindow V hV R) J
    (R^a) C (by positivity) hC.le hsource
  change R^a*(∫t : ℝ,(1+‖t‖)^J*‖(𝓕 (gaussianLogWindow V hV R)) t‖)≤D at hh
  have hp := mul_le_mul_of_nonneg_left hh (Real.rpow_pos_of_pos hR (-a)).le
  have hc' : R^(-a)*R^a=1 := by rw [mul_comm,hcancel]
  rw [←mul_assoc,hc',one_mul] at hp
  exact hp.trans (by nlinarith [Real.rpow_pos_of_pos hR (-a)])

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1231

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianCoupled
Source SHA256: 21a6117120a386823e2f596b2b5e2e52e7cf4ffebddffac10de8ed320ba9cb5e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1232


namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge LocalLogFourier
namespace SevenEighths.ProbePhysical

def gaussianJointDensity (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) : SchwartzMap ℝ ℂ :=
  𝓕 (gaussianLogWindow V hV R)

lemma gaussianProfile_positive_smooth : ContDiffOn ℝ ∞ gaussianMellinProfile (Set.Ioi 0) := by
  intro y hy
  have hh := (gaussianProfile_scaled_smooth 1 (by norm_num) y hy).contDiffWithinAt (s:=Set.Ioi 0)
  simpa only [one_mul] using hh

lemma gaussianLogWindow_eq_positive (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (R : ℝ) (hR : 0<R) : gaussianLogWindow V hV R=
      positiveLogProfile V gaussianMellinProfile R hV V.smooth' gaussianProfile_positive_smooth hR := by
  ext s
  simp only [gaussianLogWindow_apply,positiveLogProfile_apply,gaussianFlow_real R hR]

theorem gaussian_coupled_separation {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a y : ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (R : ℝ) (hR : 0<R)
    (hactive : (∏i,W i (y i))≠0→V (∑i,a i*y i)=1) :
    (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
      ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t := by
  have hh := coupled_positive_log_separation W gaussianMellinProfile V R a y hV V.smooth'
    gaussianProfile_positive_smooth hR hactive
  rw [←gaussianLogWindow_eq_positive V hV R hR] at hh
  exact hh

theorem gaussian_coupled_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (a M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i y≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀y : ι→ℝ,
        (∏i,W i (y i))*gaussianMellinProfile (R*Real.exp (∑i,a i*y i))=
          ∫t : ℝ,(∏i,W i (y i)*logPhase t (a i*y i))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let T := ∑i,|a i| *M i
  have hT : 0≤T := Finset.sum_nonneg (fun i _=>mul_nonneg (abs_nonneg _) (hM i))
  obtain ⟨φ,hφc,hφs,hφone,hφsupp,_⟩ := FourierBridge.exists_complex_smooth_cutoff T hT
  let V : SchwartzMap ℝ ℂ := hφc.toSchwartzMap hφs
  have hV : HasCompactSupport (V:ℝ→ℂ) := hφc
  have hbox : ∀s,V s≠0→|s|≤T+1 := by
    intro s hs
    have hh := hφsupp (subset_tsupport φ hs)
    exact abs_le.mpr hh
  refine ⟨V,hV,?_,?_⟩
  · intro R hR y
    apply gaussian_coupled_separation W a y V hV R hR
    exact FourierBridge.coupled_cutoff_active W φ a y M hwindow (by simpa only [T] using hφone)
  · intro A J
    obtain ⟨C,hC,hbound⟩ := gaussianLogWindow_fourier_moment V hV (T+1) (by linarith) hbox A J
    refine ⟨C,hC,?_⟩
    intro R hR
    exact ⟨JointLogSeparation.weighted_schwartz_integrable (gaussianJointDensity V hV R) J,hbound R hR⟩

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1232

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianSlots
Source SHA256: fcf0dc45845a9cde9f15d3277b659811a20223d23b6277a193a42efc1dca1a09
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1233


namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap FourierTransform
open MeasureTheory Filter Set FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical

def gaussianSlotWindow {ι : Type*} (W : ι→ℝ→ℂ) : Option ι→ℝ→ℂ
  | none => fun y=>gaussianAnnulus (Real.exp y)
  | some i => fun y=>W i (Real.exp y)
def gaussianSlotSlope {ι : Type*} : Option ι→ℝ
  | none => 1
  | some _ => -1
def gaussianSlotPoint {ι : Type*} (x : ℝ) (q : ι→ℝ) : Option ι→ℝ
  | none => Real.log x
  | some i => Real.log (q i)

lemma gaussianSlot_argument {ι : Type*} [Fintype ι] (x : ℝ) (hx : 0<x) (q : ι→ℝ) (hq : ∀i,0<q i) :
    Real.exp (∑i : Option ι,gaussianSlotSlope i*gaussianSlotPoint x q i)=x/(∏i,q i) := by
  simp only [Fintype.sum_option,gaussianSlotSlope,gaussianSlotPoint,one_mul,neg_one_mul]
  rw [Real.exp_add,Real.exp_sum,Real.exp_log hx]
  simp_rw [Real.exp_neg,Real.exp_log (hq _)]
  rw [Finset.prod_inv_distrib]
  rfl

lemma logPhase_neg_argument (t y : ℝ) : logPhase t (-y)=logPhase (-t) y := by
  unfold logPhase
  congr 1
  push_cast
  ring

lemma gaussianSlot_product {ι : Type*} [Fintype ι] (W : ι→ℝ→ℂ)
    (x : ℝ) (hx : 0<x) (q : ι→ℝ) (hq : ∀i,0<q i) (t : ℝ) :
    (∏i : Option ι,gaussianSlotWindow W i (gaussianSlotPoint x q i)*
      logPhase t (gaussianSlotSlope i*gaussianSlotPoint x q i))=
      gaussianAnnulus x*logPhase t (Real.log x)*
        ∏i,W i (q i)*logPhase (-t) (Real.log (q i)) := by
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,gaussianSlotSlope,
    one_mul,neg_one_mul,Real.exp_log hx,logPhase_neg_argument]
  simp_rw [Real.exp_log (hq _)]

lemma gaussianFixedWindow_Vstar_twist (t x : ℝ) (hx : 0<x) :
    Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x=
      gaussianAnnulus x*logPhase t (Real.log x) := by
  have hs : (Real.sqrt x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hx).ne'
  unfold Vstar CompletedHeight.normTwistedSource gaussianFixedWindow
  field_simp

lemma gaussianAnnulus_log_support (y : ℝ) (hy : gaussianAnnulus (Real.exp y)≠0) :
    |y|≤|Real.log (1/2)|+|Real.log 2|+1 := by
  have hlo : (1/2:ℝ)<Real.exp y := by
    by_contra h; exact hy (gaussianAnnulus_small _ (le_of_not_gt h))
  have hhi : Real.exp y<2 := by
    by_contra h; exact hy (gaussianAnnulus_large _ (le_of_not_gt h))
  have hl : Real.log (1/2)≤y := by simpa using Real.log_le_log (by norm_num : (0:ℝ)<1/2) hlo.le
  have hh : y≤Real.log 2 := by simpa using Real.log_le_log (Real.exp_pos y) hhi.le
  rw [abs_le]
  constructor
  · have := neg_abs_le (Real.log (1/2)); have := abs_nonneg (Real.log 2); linarith
  · have := le_abs_self (Real.log 2); have := abs_nonneg (Real.log (1/2)); linarith

theorem gaussian_selected_slot_family {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
        gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
          ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
            (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t) ∧
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) := by
  let M' : Option ι→ℝ := fun o=>match o with
    | none => |Real.log (1/2)|+|Real.log 2|+1
    | some i => M i
  have hM' : ∀o,0≤M' o := by intro o; cases o with
    | none => dsimp [M']; positivity
    | some i => exact hM i
  have hW : ∀o y,gaussianSlotWindow W o y≠0→|y|≤M' o := by
    intro o y
    cases o with
    | none => exact gaussianAnnulus_log_support y
    | some i => exact hwindow i y
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_coupled_family (gaussianSlotWindow W) gaussianSlotSlope M' hM' hW
  refine ⟨V,hV,?_,hbound⟩
  intro R hR x hx q hq
  have hh := hsep R hR (gaussianSlotPoint x q)
  rw [gaussianSlot_argument x hx q hq] at hh
  simp only [Fintype.prod_option,gaussianSlotWindow,gaussianSlotPoint,Real.exp_log hx] at hh
  simp_rw [Real.exp_log (hq _)] at hh
  rw [show R*(x/∏i,q i)=R*x/(∏i,q i) by ring] at hh
  rw [hh]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [gaussianFixedWindow_Vstar_twist t x hx]
  simp only [gaussianSlotSlope,one_mul,neg_one_mul,logPhase_neg_argument]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1233

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianCompletedSlots
Source SHA256: afa8f31c3a5d01b230b9f22547aa35057827a844f272753b395931d3b6efc006
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1234



namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma correctedSummand_normTwisted (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (W : ℝ→ℂ) (T t : ℝ) (I J : Id) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource W t) T I J=
      logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T))*
        correctedSummand S D Ψ W T I J := by
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
    CompletedHeight.normTwistedSource
  ring

lemma correctedSummand_fixed_finite (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T : ℝ) (hT : 0<T) :
    (Function.support (fun p : Id×Id=>correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2)).Finite := by
  apply (completedT_finite_support Ψ gaussianFixedWindow gaussianFixedWindow_compact T hT).subset
  intro p hp hz
  exact hp (by simp only [correctedSummand,markedSummand,hz,mul_zero])

lemma gaussian_slot_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ) (x : ℝ) (c : ℂ) :
    Integrable (fun t : ℝ=>logPhase t x*c*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  have hh : Integrable (fun t : ℝ=>b t*(logPhase t x*c*
      ∏i,W i (q i)*logPhase (-t) (Real.log (q i)))) := by
    apply b.integrable.mul_bdd (c:=‖c‖*∏i,‖W i (q i)‖)
    · apply Continuous.aestronglyMeasurable
      apply Continuous.mul ((logPhase_continuous_left x).mul_const c)
      apply continuous_finsetProd
      intro i hi
      exact ((logPhase_continuous_left (Real.log (q i))).comp continuous_neg).const_mul _
    · apply Filter.Eventually.of_forall
      intro t
      simp only [norm_mul,norm_prod,logPhase_norm,mul_one,one_mul,le_refl]
  simpa only [mul_comm (b _) _] using hh

lemma gaussian_selected_summand {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0<Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0<q i) (I J : Id) :
    (∏i,W i (q i))*correctedSummand S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) I J=
      ∫t : ℝ,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) I J*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  by_cases hI : I=0
  · subst I
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  by_cases hJ : J=0
  · subst J
    simp [correctedSummand,markedSummand,CompletedGauss.summand]
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hT : (0:ℝ)<2^j := by positivity
  have hN := div_pos (mul_pos hi (pow_pos hj 3)) hT
  have hprod : 0<∏i,q i := Finset.prod_pos (fun i _=>hq i)
  have hh := hsep ((2:ℝ)^j/Z) (div_pos hT hZ) _ hN q hq
  have he : (2:ℝ)^j/Z*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(∏i,q i)=
      (2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i) := by ring
  rw [he] at hh
  unfold correctedSummand markedSummand CompletedGauss.summand
  rw [gaussianDyadicProfile_Vstar _ _ _ hN]
  let c : ℂ := completedCorrection I J*completedMask S D I J*
    (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I):ℂ))*cubeWeight Ψ J
  calc
    _ = c*(gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
      (∏i,W i (q i))*gaussianMellinProfile
        ((2:ℝ)^j*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)/(Z*∏i,q i))) := by dsimp [c]; ring
    _ = c*∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t)
      ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j)*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp [c]
      ring

lemma correctedSummand_gaussian_factor (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (Z : ℝ) (j : ℕ) (I J : Id) :
    correctedSummand S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j) I J=
      gaussianMellinProfile (((2:ℝ)^j/Z)*((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/(2:ℝ)^j))*
        correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) I J := by
  rw [gaussianDyadicProfile_factor]
  unfold correctedSummand markedSummand CompletedGauss.summand Vstar
  ring

lemma gaussian_selected_completed_integrable {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (q : ι→ℝ) (b : SchwartzMap ℝ ℂ)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (T : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*b t) := by
  let hf := correctedSummand_fixed_finite S D Ψ T hT
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow T p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  simp_rw [hr,Finset.sum_mul]
  apply integrable_finsetSum
  intro p hp
  simp_rw [correctedSummand_normTwisted]
  exact gaussian_slot_integrable W q b _ _

theorem gaussian_selected_completed {ι : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (S : Finset Id) (D : Id) (Ψ : O→*ℂ) (Z : ℝ) (hZ : 0<Z) (j : ℕ)
    (q : ι→ℝ) (hq : ∀i,0<q i) :
    (∏i,W i (q i))*correctedCompletedT S D Ψ
      (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∫t : ℝ,correctedCompletedT S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  let hf := correctedSummand_fixed_finite S D Ψ ((2:ℝ)^j) (by positivity)
  have hz (p : Id×Id) (hp : p∉hf.toFinset) :
      correctedSummand S D Ψ gaussianFixedWindow ((2:ℝ)^j) p.1 p.2=0 := by
    simpa only [Set.Finite.mem_toFinset,Function.mem_support,not_not] using hp
  have hl : correctedCompletedT S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ (gaussianDyadicProfile (Z*∏i,q i) j) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_gaussian_factor,hz p hp,mul_zero])
  have hr (t : ℝ) : correctedCompletedT S D Ψ
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑p∈hf.toFinset,correctedSummand S D Ψ
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2 := by
    exact tsum_eq_sum (fun p hp=>by rw [correctedSummand_normTwisted,hz p hp,mul_zero])
  have hi (p : Id×Id) : Integrable (fun t : ℝ=>
      correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j) p.1 p.2*
        (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simp_rw [correctedSummand_normTwisted]
    exact gaussian_slot_integrable W q _ _ _
  rw [hl,Finset.mul_sum]
  simp_rw [hr,Finset.sum_mul]
  rw [integral_finsetSum _ (fun p _=>hi p)]
  apply Finset.sum_congr rfl
  intro p hp
  exact gaussian_selected_summand W V hV hsep S D Ψ Z hZ j q hq p.1 p.2

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1234

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianTuple
Source SHA256: d25b42be81da032dedf63954f8cc203f9fedefc1c14e3fad6753216c475c7a7d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1235



namespace OAI

noncomputable section
open scoped Classical ContDiff Topology SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussian_selected_tuple_sum {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (Z : ℝ) (hZ : 0<Z) (j : ℕ) (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
      ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hi (k : α) : Integrable (fun t : ℝ=>a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
    simpa only [mul_assoc] using (gaussian_selected_completed_integrable W (q k) _ S (D k) (Ψ k) _ (by positivity)).const_mul _
  simp_rw [Finset.sum_mul]
  rw [integral_finsetSum _ (fun k _=>hi k)]
  apply Finset.sum_congr rfl
  intro k hk
  have hh := gaussian_selected_completed W V hV hsep S (D k) (Ψ k) Z hZ j (q k) (hq k hk)
  calc
    _ = a k*((∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) := by ring
    _ = a k*∫t : ℝ,correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
      (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))*
        gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by rw [hh]
    _ = _ := by
      rw [←integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun t=>by dsimp only; ring)

lemma gaussian_selected_scale {ι : Type*} [Fintype ι]
    (Z : ℝ) (P Q : ι→ℝ) (hP : ∀i,0<P i) :
    (Z*∏i,P i)*(∏i,Q i/P i)=Z*∏i,Q i := by
  rw [Finset.prod_div_distrib]
  have hp : (∏i,P i)≠0 := ne_of_gt (Finset.prod_pos (fun i _=>hP i))
  field_simp

theorem gaussian_selected_tuple_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀A : ℝ,∀J : ℕ,∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→
        Integrable (fun t : ℝ=>(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖) ∧
        (∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖)≤C*R^(-A)) ∧
      (∀F : Finset α,∀a : α→ℂ,∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
        ∀Z : ℝ,0<Z→∀j : ℕ,∀q : α→ι→ℝ,(∀k∈F,∀i,0<q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
          (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j))=
          ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
            (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,hbound⟩ := gaussian_selected_slot_family W M hM hwindow
  exact ⟨V,hV,hbound,fun F a S D Ψ Z hZ j q hq=>
    gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq⟩

lemma gaussianFixedWindow_twist_compact (t : ℝ) :
    HasCompactSupport (CompletedHeight.normTwistedSource gaussianFixedWindow t) := by
  exact gaussianFixedWindow_compact.mul_left

theorem gaussian_twisted_physical_row_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id) (j : ℕ) (t : ℝ) :
    correctedCompletedT S D (rowCoefficient η (calibrationForSet S hS).Xi s hs z)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (CanonicalRowCompletion.rowTwist
            (lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
              (calibrationLowData S hS) s hs χ)
            (calibrationForSet S hS).generator 1 z)
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)
          (fun A=>if D∣A then (1:ℂ) else 0) := by
  exact correctedPhysicalRow_eq_periodic_inverse η S hS hbad s hs z D _
    (gaussianFixedWindow_twist_compact t) _ (by positivity) (calibrationLowData S hS)

lemma correctedGaussian_dyadic_summable (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (Z : ℝ) (hZ : 0<Z) :
    Summable (fun j : ℕ=>correctedCompletedT S D Ψ (gaussianDyadicProfile Z j) ((2:ℝ)^j)) := by
  have hh := (annular_reassembly_summable
    (fun p : Id×Id=>correctedSummand S D Ψ gaussianCompletedProfile Z p.1 p.2)
    (fun p : Id×Id=>(Ideal.absNorm p.1:ℝ)*(Ideal.absNorm p.2:ℝ)^3)
    (gaussian_correctedSummand_summable S D Ψ hΨ Z hZ)
    (fun p=>gaussian_correctedSummand_norm_ge_one S D Ψ Z p.1 p.2)).prod_symm.prod
  simpa only [correctedCompletedT,gaussian_dyadic_correctedSummand S D Ψ Z hZ,Prod.swap] using hh

theorem gaussian_selected_tuple_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (hΨ : ∀k∈F,∀n,‖Ψ k n‖≤1) (Z : ℝ) (hZ : 0<Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      gaussianCompletedProfile (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j)*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  have hp (k : α) (hk : k∈F) : 0<Z*∏i,q k i :=
    mul_pos hZ (Finset.prod_pos (fun i _=>hq k hk i))
  have hd (k : α) (hk : k∈F) : Summable (fun j : ℕ=>a k*(∏i,W i (q k i))*
      correctedCompletedT S (D k) (Ψ k) (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j)) :=
    (correctedGaussian_dyadic_summable S (D k) (Ψ k) (hΨ k hk) _ (hp k hk)).mul_left _
  calc
    _ = ∑k∈F,∑'j : ℕ,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [correctedGaussian_eq_tsum_dyadic S (D k) (Ψ k) (hΨ k hk) _ (hp k hk),tsum_mul_left]
    _ = ∑'j : ℕ,∑k∈F,a k*(∏i,W i (q k i))*correctedCompletedT S (D k) (Ψ k)
      (gaussianDyadicProfile (Z*∏i,q k i) j) ((2:ℝ)^j) := (Summable.tsum_finsetSum hd).symm
    _ = _ := by
      apply tsum_congr
      intro j
      exact gaussian_selected_tuple_sum W V hV hsep F a S D Ψ Z hZ j q hq

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1235

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianCrude
Source SHA256: c8ea9217ae1dce3d0b1900b7fedea2def02235c209737da880ffc8ff61e1aa59
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1236


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CubicEisenstein FourierBridge
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gaussianAnnulus_norm_le_one (y : ℝ) : ‖gaussianAnnulus y‖≤1 := by
  rw [gaussianAnnulus_norm]
  change Real.smoothTransition (2-y)-Real.smoothTransition (2-2*y)≤1
  linarith [Real.smoothTransition.le_one (2-y),Real.smoothTransition.nonneg (2-2*y)]

lemma gaussianAnnulus_scaled_square (N T : ℝ) (hN : 0<N) (hT : 0<T) :
    N^2*‖gaussianAnnulus (N/T)‖≤4*T^2 := by
  by_cases hz : gaussianAnnulus (N/T)=0
  · rw [hz,norm_zero,mul_zero]
    positivity
  have hn : N/T<2 := by
    by_contra hh
    exact hz (gaussianAnnulus_large _ (le_of_not_gt hh))
  have hn' : N<2*T := (div_lt_iff₀ hT).mp hn
  calc
    _ ≤ N^2 := mul_le_of_le_one_right (sq_nonneg _) (gaussianAnnulus_norm_le_one _)
    _ ≤ _ := by nlinarith

lemma gaussianFixedWindow_spectral_identity (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (T t : ℝ) (hT : 0<T) (I J : Id) (hI : I≠0) (hJ : J≠0) :
    correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J=
      spectralSummand S D Ψ 2 I J*
        ((((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3:ℝ):ℂ)^2*
          (gaussianAnnulus ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)*
            logPhase t (Real.log ((Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3/T)))) := by
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hic : (Ideal.absNorm I:ℂ)≠0 := by exact_mod_cast hi.ne'
  have hjc : (Ideal.absNorm J:ℂ)≠0 := by exact_mod_cast hj.ne'
  unfold correctedSummand markedSummand CompletedGauss.summand spectralSummand fullIdealWeight
  rw [gaussianFixedWindow_Vstar_twist t _ (div_pos (mul_pos hi (pow_pos hj 3)) hT)]
  simp only [ite_eq_right hI,ite_eq_right hJ]
  norm_num only [show (3:ℂ)*2=6 by norm_num,Complex.cpow_neg,Complex.cpow_ofNat]
  push_cast
  field_simp

lemma gaussianFixedWindow_summand_crude (S : Finset Id) (D : Id) (Ψ : O→*ℂ)
    (hΨ : ∀n,‖Ψ n‖≤1) (T t : ℝ) (hT : 0<T) (I J : Id) :
    ‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T I J‖≤
      4*T^2*rowMajorant 2 (I,J) := by
  by_cases hI : I=0
  · subst I
    simp only [correctedSummand,markedSummand,summand_zero_left,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  by_cases hJ : J=0
  · subst J
    simp only [correctedSummand,markedSummand,summand_zero_right,mul_zero,norm_zero]
    unfold rowMajorant
    positivity
  have hi : (0:ℝ)<Ideal.absNorm I := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hj : (0:ℝ)<Ideal.absNorm J := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hJ)
  have hN : 0<(Ideal.absNorm I:ℝ)*(Ideal.absNorm J:ℝ)^3 := mul_pos hi (pow_pos hj 3)
  rw [gaussianFixedWindow_spectral_identity S D Ψ T t hT I J hI hJ,
    norm_mul,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hN,
    norm_mul,logPhase_norm,mul_one]
  have hs : ‖spectralSummand S D Ψ 2 I J‖≤rowMajorant 2 (I,J) := by
    simpa only [Complex.ofReal_ofNat,Complex.ofReal_zero,zero_mul,add_zero] using
      spectralSummand_vertical_bound S D Ψ hΨ 2 0 (I,J)
  have hn := gaussianAnnulus_scaled_square _ T hN hT
  exact (mul_le_mul hs hn (by positivity) (by unfold rowMajorant;positivity)).trans_eq (by ring)

theorem gaussianFixedWindow_completed_crude :
    ∃C : ℝ,0<C ∧ ∀S : Finset Id,∀D : Id,∀Ψ : O→*ℂ,
      (∀n,‖Ψ n‖≤1)→∀T t : ℝ,0<T→
      ‖correctedCompletedT S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T‖≤C*T^2 := by
  let M : ℝ := ∑'p : Id×Id,rowMajorant 2 p
  have hM : 0≤M := tsum_nonneg (fun p=>by unfold rowMajorant;positivity)
  refine ⟨4*M+1,by positivity,?_⟩
  intro S D Ψ hΨ T t hT
  have hs := correctedSummand_summable S D Ψ _ (gaussianFixedWindow_twist_compact t) T hT
  change ‖∑'p : Id×Id,correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖≤_
  calc
    _ ≤ ∑'p : Id×Id,‖correctedSummand S D Ψ (CompletedHeight.normTwistedSource gaussianFixedWindow t) T p.1 p.2‖ := norm_tsum_le_tsum_norm hs.norm
    _ ≤ ∑'p : Id×Id,4*T^2*rowMajorant 2 p := hs.norm.tsum_le_tsum
      (fun p=>gaussianFixedWindow_summand_crude S D Ψ hΨ T t hT p.1 p.2)
      ((rowMajorant_summable 2 (by norm_num)).mul_left (4*T^2))
    _ = (4*M)*T^2 := by rw [tsum_mul_left];dsimp only [M];ring
    _ ≤ _ := by nlinarith [sq_nonneg T]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1236

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianDensityBudget
Source SHA256: 42ee10381da1a2003fe309f4b7773c4908bc625eff31f9c23392f82836ba9730
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1237


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianJointMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : ℝ :=
  ∫t : ℝ,(1+‖t‖)^J*‖gaussianJointDensity V hV R t‖

lemma gaussianJointMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (R : ℝ) : 0≤gaussianJointMoment V hV J R := by
  apply integral_nonneg
  intro t
  positivity

lemma gaussianJointMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianJointMoment V hV J R≤C*R^(-A) := by
  obtain ⟨L,hL,hbox⟩ := hV.isBounded.exists_pos_norm_le
  have hb : ∀s,V s≠0→|s|≤L := by
    intro s hs
    simpa only [Real.norm_eq_abs] using hbox s (subset_tsupport V hs)
  exact gaussianLogWindow_fourier_moment V hV L hL.le hb A J

lemma gaussianJointMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianJointMoment V hV J R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianJointMoment_power_bound V hV J 0
  obtain ⟨C,hC,hdecay⟩ := gaussianJointMoment_power_bound V hV J (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianJointMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianJointMoment_polynomial_decay V hV J N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianJointMoment_nonneg V hV J _)
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1237

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianTailBudget
Source SHA256: 38f614d4aa36aff2966a4143f0fd73876902f38004d643acf22d3a41716f071b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1238


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical

def gaussianWeightedMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) : ℝ := R^k*gaussianJointMoment V hV J R

lemma gaussianWeightedMoment_nonneg (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k R : ℝ) (hR : 0≤R) : 0≤gaussianWeightedMoment V hV J k R := by
  unfold gaussianWeightedMoment
  exact mul_nonneg (Real.rpow_nonneg hR _) (gaussianJointMoment_nonneg V hV J R)

lemma gaussianWeightedMoment_power_bound (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (k A : ℝ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianWeightedMoment V hV J k R≤C*R^(-A) := by
  obtain ⟨C,hC,hb⟩ := gaussianJointMoment_power_bound V hV J (A+k)
  refine ⟨C,hC,?_⟩
  intro R hR
  have hh := mul_le_mul_of_nonneg_left (hb R hR) (Real.rpow_nonneg hR.le k)
  change R^k*gaussianJointMoment V hV J R≤_
  calc
    _ ≤ R^k*(C*R^(-(A+k))) := hh
    _ = C*R^(-A) := by
      rw [←mul_assoc,mul_comm (R^k) C,mul_assoc,←Real.rpow_add hR]
      congr 2
      ring

lemma gaussianWeightedMoment_polynomial_decay (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k : ℝ) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀R : ℝ,0<R→gaussianWeightedMoment V hV J k R≤C/(1+R)^N := by
  obtain ⟨B,hB,hzero⟩ := gaussianWeightedMoment_power_bound V hV J k 0
  obtain ⟨C,hC,hdecay⟩ := gaussianWeightedMoment_power_bound V hV J k (N:ℝ)
  refine ⟨(B+C)*(2:ℝ)^N,by positivity,?_⟩
  intro R hR
  have hden : 0<(1+R)^N := pow_pos (by linarith) _
  by_cases hr1 : R≤1
  · have hh := hzero R hR
    simp only [neg_zero,Real.rpow_zero,mul_one] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2:ℝ)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hb := mul_le_mul_of_nonneg_left hp hB.le
    nlinarith [mul_nonneg hC.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)]
  · have hh := hdecay R hR
    rw [Real.rpow_neg hR.le,Real.rpow_natCast] at hh
    apply hh.trans
    apply (le_div_iff₀ hden).mpr
    have hp : (1+R)^N≤(2*R)^N := pow_le_pow_left₀ (by linarith) (by linarith) _
    have hm := mul_le_mul_of_nonneg_left hp (show 0≤C*(R^N)⁻¹ by positivity)
    rw [mul_pow] at hm
    have hn : R^N≠0 := ne_of_gt (pow_pos hR _)
    have he : (C*(R^N)⁻¹)*((2:ℝ)^N*R^N)=C*(2:ℝ)^N := by field_simp
    rw [he] at hm
    exact hm.trans (by nlinarith [mul_nonneg hB.le (pow_nonneg (by norm_num : (0:ℝ)≤2) N)])

theorem gaussianWeightedMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J : ℕ) (k s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z : ℝ,0<Z→
      Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)) ∧
      (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z))≤C*Z^s := by
  obtain ⟨N,hN⟩ := exists_nat_gt s
  obtain ⟨B,hB,hbound⟩ := gaussianWeightedMoment_polynomial_decay V hV J k N
  obtain ⟨C,hC,hkernel⟩ := CompletedDyadic.kernel_sum_bound s (N:ℝ) hs hN
  refine ⟨B*C,by positivity,?_⟩
  intro Z hZ
  obtain ⟨hks,hkt⟩ := hkernel Z⁻¹ (inv_pos.mpr hZ)
  have hb (j : ℕ) : ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z)≤
      B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := by
    have hh := mul_le_mul_of_nonneg_left (hbound ((2:ℝ)^j/Z) (div_pos (by positivity) hZ))
      (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s)
    simpa only [CompletedDyadic.kernelTerm,Real.rpow_natCast,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm] using hh
  have hnon (j : ℕ) : 0≤((2:ℝ)^j)^s*gaussianWeightedMoment V hV J k ((2:ℝ)^j/Z) :=
    mul_nonneg (Real.rpow_nonneg (by positivity : (0:ℝ)≤2^j) s) (gaussianWeightedMoment_nonneg V hV J k _ (by positivity))
  have hsum := Summable.of_nonneg_of_le hnon hb (hks.mul_left B)
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,B*CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := hsum.tsum_le_tsum hb (hks.mul_left B)
    _ = B*∑'j : ℕ,CompletedDyadic.kernelTerm Z⁻¹ s (N:ℝ) j := tsum_mul_left
    _ ≤ B*(C*(Z⁻¹)^(-s)) := mul_le_mul_of_nonneg_left hkt hB.le
    _ = (B*C)*Z^s := by rw [Real.inv_rpow hZ.le,Real.rpow_neg hZ.le,inv_inv]; ring

def gaussianRemoteMoment (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (J : ℕ) (s Z A : ℝ) (j : ℕ) : ℝ :=
  if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
    ((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)
  else 0

theorem gaussianRemoteMoment_summed (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (J N : ℕ) (s : ℝ) (hs : 0<s) :
    ∃C : ℝ,0<C ∧ ∀Z A : ℝ,0<Z→1≤A→
      Summable (gaussianRemoteMoment V hV J s Z A) ∧
      (∑'j : ℕ,gaussianRemoteMoment V hV J s Z A j)≤C*Z^s/A^N := by
  obtain ⟨Cm,hCm,hm⟩ := gaussianWeightedMoment_summed V hV J (-(N:ℝ)) s hs
  obtain ⟨Cp,hCp,hp⟩ := gaussianWeightedMoment_summed V hV J (N:ℝ) s hs
  refine ⟨Cm+Cp,by positivity,?_⟩
  intro Z A hZ hA
  have hAp : 0<A := lt_of_lt_of_le zero_lt_one hA
  have hAN : 0<A^N := pow_pos hAp N
  obtain ⟨hsm,htm⟩ := hm Z hZ
  obtain ⟨hsp,htp⟩ := hp Z hZ
  let U : ℕ→ℝ := fun j=>
    (((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z)+
      ((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z))/A^N
  have hU : Summable U := (hsm.add hsp).div_const _
  have hnon (j : ℕ) : 0≤gaussianRemoteMoment V hV J s Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · exact mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianJointMoment_nonneg V hV J _)
    · rfl
  have hb (j : ℕ) : gaussianRemoteMoment V hV J s Z A j≤U j := by
    let R := (2:ℝ)^j/Z
    have hR : 0<R := div_pos (by positivity) hZ
    have hM : 0≤gaussianJointMoment V hV J R := gaussianJointMoment_nonneg V hV J R
    unfold gaussianRemoteMoment
    split_ifs with hj
    · have he : A^N≤R^(-(N:ℝ))+R^(N:ℝ) := by
        rcases hj with hlo|hhi
        · have hra : R*A≤1 := (le_div_iff₀ hAp).mp (by simpa only [one_div,R] using hlo)
          have hh := pow_le_pow_left₀ (by positivity : 0≤R*A) hra N
          rw [mul_pow,one_pow] at hh
          have hi : A^N≤R^(-(N:ℝ)) := by
            rw [Real.rpow_neg hR.le,Real.rpow_natCast]
            rw [←one_div]
            exact (le_div_iff₀ (pow_pos hR N)).mpr (by simpa only [mul_comm] using hh)
          exact hi.trans (le_add_of_nonneg_right (Real.rpow_nonneg hR.le _))
        · have hi : A^N≤R^(N:ℝ) := by
            rw [Real.rpow_natCast]
            exact pow_le_pow_left₀ hAp.le hhi N
          exact hi.trans (le_add_of_nonneg_left (Real.rpow_nonneg hR.le _))
      change ((2:ℝ)^j)^s*gaussianJointMoment V hV J R≤_
      dsimp only [U]
      apply (le_div_iff₀ hAN).mpr
      calc
        _ ≤ (((2:ℝ)^j)^s*gaussianJointMoment V hV J R)*(R^(-(N:ℝ))+R^(N:ℝ)) :=
          mul_le_mul_of_nonneg_left he (mul_nonneg (Real.rpow_nonneg (by positivity) _) hM)
        _ = _ := by unfold gaussianWeightedMoment;dsimp only [R];ring
    · dsimp only [U]
      apply div_nonneg _ hAN.le
      exact add_nonneg
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
        (mul_nonneg (Real.rpow_nonneg (by positivity) _) (gaussianWeightedMoment_nonneg V hV J _ _ hR.le))
  have hsum := Summable.of_nonneg_of_le hnon hb hU
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,U j := hsum.tsum_le_tsum hb hU
    _ = ((∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (-(N:ℝ)) ((2:ℝ)^j/Z))+
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianWeightedMoment V hV J (N:ℝ) ((2:ℝ)^j/Z)))/A^N := by
      dsimp only [U]
      rw [tsum_div_const,hsm.tsum_add hsp]
    _ ≤ (Cm*Z^s+Cp*Z^s)/A^N := div_le_div_of_nonneg_right (add_le_add htm htp) hAN.le
    _ = _ := by ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1238

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianRemoteRows
Source SHA256: 322034af461135599f4966ed12fbf265b0d20babfc24582a2fa3071095767dc6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1239



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianCompletedFamilyIntegral {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
    (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianCompletedFamilyMass {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*∏i,‖W i (q k i)‖

lemma gaussianCompletedFamilyMass_nonneg {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (W : ι→ℝ→ℂ) (q : α→ι→ℝ) :
    0≤gaussianCompletedFamilyMass F a W q := by
  unfold gaussianCompletedFamilyMass
  positivity

lemma gaussianCompletedFamily_integrable {α ι : Type*} [Fintype ι]
    (F : Finset α) (a : α→ℂ) (S : Finset Id) (D : α→Id) (Ψ : α→O→*ℂ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (hT : 0<T) :
    Integrable (fun t : ℝ=>(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
      (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t) := by
  have hh := integrable_finsetSum F (fun k _=>(gaussian_selected_completed_integrable W (q k)
    (gaussianJointDensity V hV (T/Z)) S (D k) (Ψ k) T hT).const_mul (a k))
  simpa only [Finset.sum_mul,mul_assoc] using hh

theorem gaussianCompletedFamily_crude :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀V : SchwartzMap ℝ ℂ,∀hV : HasCompactSupport (V:ℝ→ℂ),∀T Z : ℝ,0<T→
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV T Z‖≤
        C*T^2*gaussianCompletedFamilyMass F a W q*gaussianJointMoment V hV 0 (T/Z) := by
  obtain ⟨C,hC,hb⟩ := gaussianFixedWindow_completed_crude
  refine ⟨C,hC,?_⟩
  intro α ι _ F a S D Ψ hΨ W q V hV T Z hT
  have hf := gaussianCompletedFamily_integrable F a S D Ψ W q V hV T Z hT
  have hp (t : ℝ) :
      ‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖≤
      (C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    calc
      _ ≤ ∑k∈F,‖a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i)))‖ := norm_sum_le _ _
      _ ≤ ∑k∈F,‖a k‖*(C*T^2)*(∏i,‖W i (q k i)‖) := by
        apply Finset.sum_le_sum
        intro k hk
        simp only [norm_mul,norm_prod,logPhase_norm,mul_one]
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hb S (D k) (Ψ k) (hΨ k hk) T t hT) (norm_nonneg _))
          (Finset.prod_nonneg (fun _ _=>norm_nonneg _))
      _ = _ := by unfold gaussianCompletedFamilyMass;rw [Finset.mul_sum];congr 1;funext k;ring
  calc
    _ ≤ ∫t : ℝ,‖(∑k∈F,a k*correctedCompletedT S (D k) (Ψ k)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫t : ℝ,(C*T^2*gaussianCompletedFamilyMass F a W q)*‖gaussianJointDensity V hV (T/Z) t‖ :=
      integral_mono hf.norm ((gaussianJointDensity V hV (T/Z)).integrable.norm.const_mul _) hp
    _ = _ := by simp only [integral_const_mul,gaussianJointMoment,pow_zero,one_mul]

theorem gaussianCompletedFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{α ι : Type*} [Fintype ι],∀F : Finset α,∀a : α→ℂ,
      ∀S : Finset Id,∀D : α→Id,∀Ψ : α→O→*ℂ,
      (∀k∈F,∀n,‖Ψ k n‖≤1)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C*gaussianCompletedFamilyMass F a W q*Z^2/A^N := by
  obtain ⟨Cr,hCr,hr⟩ := gaussianCompletedFamily_crude
  obtain ⟨Cg,hCg,hg⟩ := gaussianRemoteMoment_summed V hV 0 N 2 (by norm_num)
  refine ⟨Cr*Cg,by positivity,?_⟩
  intro α ι _ F a S D Ψ hΨ W q Z A hZ hA
  obtain ⟨hs,ht⟩ := hg Z A hZ hA
  let M := gaussianCompletedFamilyMass F a W q
  have hM : 0≤M := gaussianCompletedFamilyMass_nonneg F a W q
  have hb (j : ℕ) :
      (if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0)≤
      (Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := by
    unfold gaussianRemoteMoment
    split_ifs
    · simpa only [M,Real.rpow_two,mul_assoc,mul_comm,mul_left_comm] using
        hr F a S D Ψ hΨ W q V hV ((2:ℝ)^j) Z (by positivity)
    · simp
  have hnon (j : ℕ) : 0≤(if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
      ‖gaussianCompletedFamilyIntegral F a S D Ψ W q V hV ((2:ℝ)^j) Z‖ else 0) := by split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnon hb (hs.mul_left (Cr*M))
  refine ⟨hsum,?_⟩
  calc
    _ ≤ ∑'j : ℕ,(Cr*M)*gaussianRemoteMoment V hV 0 2 Z A j := hsum.tsum_le_tsum hb (hs.mul_left (Cr*M))
    _ = (Cr*M)*∑'j : ℕ,gaussianRemoteMoment V hV 0 2 Z A j := tsum_mul_left
    _ ≤ (Cr*M)*(Cg*Z^(2:ℝ)/A^N) := mul_le_mul_of_nonneg_left ht (mul_nonneg hCr.le hM)
    _ = _ := by rw [Real.rpow_two];dsimp only [M];ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1239

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SpectralSeparation
Source SHA256: ac9a787c061cb47ad79a18ceb178d2bc9275b89093ae0a1fe431fc9b9c8f347d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1240



namespace OAI

noncomputable section
namespace SevenEighths.ProbeRow
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion CanonicalQuadraticSieve
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O

def baseRowCoefficient (η : HeckeFamily.Character) (Xi : O →* ℂ)
    (s : O) (hs : Supported (Ideal.span {s})) : O →* ℂ :=
  targetMonoid η * InitialMeanSquare.conjugateMonoid Xi * reciprocityPhaseMonoid s hs

lemma spectralSummand_mul_fixed_twist (S : Finset (Ideal O)) (D I J : Ideal O)
    (φ Ψ : O →* ℂ) (t : ℂ) :
    spectralSummand S D (φ*Ψ) t I J =
      φ (completedIndex I J) * spectralSummand S D Ψ t I J := by
  have hc (η : O →* ℂ) : cubeWeight η J =
      star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        η (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ) := rfl
  unfold spectralSummand
  rw [hc, hc]
  simp only [columnWeight, MonoidHom.mul_apply, map_mul, map_pow, mul_pow, completedIndex]
  ring

theorem spectralSummand_row_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (Xi : O →* ℂ) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    spectralSummand S D (rowCoefficient η Xi s hs m) t I J =
      idealRowHom m (Ideal.span {completedIndex I J}) *
        spectralSummand S D (baseRowCoefficient η Xi s hs) t I J := by
  have hr : rowCoefficient η Xi s hs m =
      ((idealRowHom m).toMonoidHom.comp principalIdealHom.toMonoidHom) *
        baseRowCoefficient η Xi s hs := by
    change _ * _ = _ * _
    exact mul_comm _ _
  rw [hr, spectralSummand_mul_fixed_twist]
  rfl

theorem calibrated_spectralSummand_separation (S : Finset (Ideal O)) (D I J : Ideal O)
    (η : HeckeFamily.Character) (C : ProbePhysical.CalibrationData) (s : O)
    (hs : Supported (Ideal.span {s})) (m : O) (t : ℂ) :
    C.residueMonoid m * spectralSummand S D (rowCoefficient η C.Xi s hs m) t I J =
      ProbePhysical.calibratedNumerator C (completedIndex I J) m *
        spectralSummand S D (baseRowCoefficient η C.Xi s hs) t I J := by
  rw [spectralSummand_row_separation]
  unfold ProbePhysical.calibratedNumerator
  ring

theorem spectralSummand_zero_completedIndex (S : Finset (Ideal O)) (D I J : Ideal O)
    (Ψ : O →* ℂ) (t : ℂ) (hz : completedIndex I J=0) :
    spectralSummand S D Ψ t I J=0 := by
  rcases mul_eq_zero.mp hz with hI | hJ
  · have hg : squarefreeGaussCoefficient I=0 := by
      unfold squarefreeGaussCoefficient
      rw [dite_eq_right (by simp [hI])]
    simp only [spectralSummand, columnWeight, hg, zero_mul, zero_div, mul_zero]
  · have hJ' : primaryGenerator J=0 := (pow_eq_zero_iff (by decide : 3≠0)).mp hJ
    have hc : cubeWeight Ψ J=0 := by
      change star (FiniteGaussPhase.angularFactor (primaryGenerator J))^3 *
        Ψ (primaryGenerator J)^3 / (Ideal.absNorm J:ℂ)=0
      simp [hJ', FiniteGaussPhase.angularFactor]
    simp only [spectralSummand, hc, mul_zero, zero_mul]

end SevenEighths.ProbeRow
end

end OAI
end OAIOriginalModule1240

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SpectralWeights
Source SHA256: 58508eda082dfdc1fd9df3cad1e204adacc1edb8bc0bd15b959ab8e3cd37602b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1241


namespace OAI

noncomputable section
namespace SevenEighths.ProbeEuler

lemma signed_diagonal_phase (omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    omega^(((e+3*l)*k:ℕ):ℤ) * omega^(-((e*l+l.choose 2:ℕ):ℤ)) =
      omega^((e+3*l)*k+e*l+l.choose 2) := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  have hi : omega⁻¹=omega := by
    apply inv_eq_of_mul_eq_one_left
    simpa only [pow_two] using ho
  rw [zpow_neg, zpow_natCast, zpow_natCast, ← inv_pow, hi, ← pow_add]
  congr 1
  omega

lemma source_signed_phase (C omega : ℂ) (ho : omega^2=1) (e l k : ℕ) :
    C^l * omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) =
      localCubePhase C omega e l k := by
  have hn : omega≠0 := by intro h; simp [h] at ho
  rw [sub_eq_add_neg, zpow_add₀ hn, signed_diagonal_phase omega ho]
  rfl

lemma spectral_power_split (Q : ℝ) (hQ : 0<Q) (x w z : ℂ) (e l k m : ℕ) :
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ)) =
      ((Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ))^e *
      (((Q:ℂ)^(-x))^3/(Q:ℂ))^l * ((Q:ℂ)^(-w))^k * ((Q:ℂ)^(-6*z))^m := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  have h1 : (Q:ℂ)^(-x)/(Q:ℂ)^(1/2:ℂ) = (Q:ℂ)^(-x-(1/2:ℂ)) :=
    (Complex.cpow_sub _ _ hn).symm
  have h3 : ((Q:ℂ)^(-x))^3/(Q:ℂ) = (Q:ℂ)^(-1-3*x) := by
    rw [← Complex.cpow_nat_mul (Q:ℂ) 3 (-x)]
    calc
      _ = (Q:ℂ)^(3*(-x)) / (Q:ℂ)^(1:ℂ) := by rw [Complex.cpow_one]; norm_num
      _ = (Q:ℂ)^(3*(-x)-1) := (Complex.cpow_sub _ _ hn).symm
      _ = _ := by congr 1; ring
  rw [h1, h3, ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_mul_nat, ← Complex.cpow_mul_nat,
    ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn, ← Complex.cpow_add _ _ hn]
  congr 1
  ring

lemma cpow_half_eq_sqrt (Q : ℝ) (hQ : 0≤Q) :
    (Q:ℂ)^(1/2:ℂ) = (Real.sqrt Q:ℂ) := by
  rw [Real.sqrt_eq_rpow]
  simpa using (Complex.ofReal_cpow hQ (1/2:ℝ)).symm

def sourceWeightedScalar (Q : ℝ) (eta a gamma1 C omega x w z scalar : ℂ)
    (e l k m : ℕ) : ℂ :=
  (-1:ℂ)^e * gamma1^(-(e:ℤ)) * eta^e * (a*C)^l *
    omega^((((e+3*l)*k:ℕ):ℤ)-(e*l+l.choose 2:ℕ)) * scalar *
    (Q:ℂ)^(-(x+1/2)*(e:ℂ)-(1+3*x)*(l:ℂ)-w*(k:ℂ)-6*z*(m:ℂ))

theorem sourceWeightedScalar_eq (Q : ℝ) (hQ : 0<Q)
    (eta a gamma1 G1 C omega x w z scalar : ℂ) (hG : G1=gamma1*(Real.sqrt Q:ℂ))
    (ho : omega^2=1) (e l k m : ℕ) :
    sourceWeightedScalar Q eta a gamma1 C omega x w z scalar e l k m =
      weightedScalar Q eta a G1 C omega ((Q:ℂ)^(-x)) ((Q:ℂ)^(-w))
        ((Q:ℂ)^(-6*z)) scalar e l k m := by
  unfold sourceWeightedScalar weightedScalar
  rw [spectral_power_split Q hQ, cpow_half_eq_sqrt Q hQ.le]
  rw [zpow_neg, zpow_natCast]
  have hphase := source_signed_phase 1 omega ho e l k
  simp only [localCubePhase, one_pow, one_mul] at hphase
  unfold localCubePhase
  rw [hphase, mul_pow a C, hG]
  simp only [mul_pow, div_pow]

  ring

open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ProbePrimePower
local notation "O" => ActualEisensteinCubic.O

lemma firstGauss_eq_gamma_sqrt (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p}) :
    primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      localGamma p hp.ne_zero hg 1 *
        (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  have hs : (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr hQ).ne'
  unfold localGamma
  rw [pow_one, ProbePhase.normalizedTraceGauss_eq_normalizedGauss]
  simp only [ProbeGauss.normalizedGauss, ← Nat.card_eq_fintype_card]
  change _ = (gaussSum _ _ / (Real.sqrt (Ideal.absNorm (Ideal.span {p})):ℂ)) * _
  rw [div_mul_cancel₀ _ hs]
  simp only [primeGauss, map_one, one_mul, tsum_fintype, gaussSum]

theorem sourceWeightedScalar_actual (p : O) (hp : Prime p)
    [(Ideal.span {p} : Ideal O).IsMaximal] (hg : goodLambda ∉ Ideal.span {p})
    (eta a x w z scalar : ℂ) (e l k m : ℕ) :
    sourceWeightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (localGamma p hp.ne_zero hg 1) (star (localGamma p hp.ne_zero hg 3))
      (actualSextic (Ideal.span {p}) hg (-1)) x w z scalar e l k m =
    weightedScalar (Ideal.absNorm (Ideal.span {p})) eta a
      (primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1)
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-x)) ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-w))
      ((Ideal.absNorm (Ideal.span {p}):ℂ)^(-6*z)) scalar e l k m := by
  have hQ : 0 < (Ideal.absNorm (Ideal.span {p}):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  simpa only [Complex.ofReal_natCast] using
    sourceWeightedScalar_eq _ hQ eta a (localGamma p hp.ne_zero hg 1) _
      (star (localGamma p hp.ne_zero hg 3)) (actualSextic (Ideal.span {p}) hg (-1))
      x w z scalar (firstGauss_eq_gamma_sqrt p hp hg)
      (actualSextic_neg_one_sq _ hg) e l k m

end SevenEighths.ProbeEuler
end

end OAI
end OAIOriginalModule1241

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalNorms
Source SHA256: f317b273df7e141d619230f721fff8b7a88703a486fe25695f51213956d58bb6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1242



namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma elementNorm_mul (a b : ActualEisensteinCubic.O) :
    elementNorm (a*b)=elementNorm a*elementNorm b := by
  simp only [elementNorm,←Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

lemma elementNorm_pow (a : ActualEisensteinCubic.O) (n : ℕ) :
    elementNorm (a^n)=elementNorm a^n := by
  simp only [elementNorm,←Ideal.span_singleton_pow,map_pow,Nat.cast_pow]

lemma physical_radial_argument (B A s H : ActualEisensteinCubic.O) (X : ℝ)
    (hB : elementNorm B≠0) (hs : elementNorm s≠0) :
    (elementNorm B*elementNorm s*X)*elementNorm H/elementNorm ((B*A)*s)=
      X*elementNorm H/elementNorm A := by
  simp only [elementNorm_mul]
  field_simp

lemma physical_poisson_prefactor (B A S X : ℝ) (hB : 0<B) (hA : 0<A) (hS : 0<S) (hX : 0<X) :
    (Real.sqrt (B*S*X):ℂ)⁻¹*(Real.sqrt S:ℂ)⁻¹*((B*S*X/(B*A):ℝ):ℂ)=
      (Real.sqrt X:ℂ)/(Real.sqrt B:ℂ)/(A:ℂ) := by
  have hBc : (B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hB.ne'
  have hAc : (A:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hA.ne'
  have hSb : (Real.sqrt B:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hB).ne'
  have hSs : (Real.sqrt S:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hS).ne'
  have hSx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  rw [Real.sqrt_mul (mul_pos hB hS).le,Real.sqrt_mul hB.le]
  simp only [Complex.ofReal_mul,Complex.ofReal_div]
  field_simp
  have hb : (Real.sqrt B:ℂ)^2=(B:ℂ) := by exact_mod_cast Real.sq_sqrt hB.le
  have hs : (Real.sqrt S:ℂ)^2=(S:ℂ) := by exact_mod_cast Real.sq_sqrt hS.le
  have hx : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  rw [hs,hx]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1242

/-! Original module: OAI.NumberTheory.DirichletL.Detector.MellinPowers
Source SHA256: bd852004a4eba595d9ffcaa5363d1b4dcb5c69bd77b48f33538b56f6815903fa
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1243


namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical
open ProbeEuler

lemma sourceNormPower_identity (I J H X : ℝ) (hI : 0<I) (hJ : 0<J) (hH : 0<H) (hX : 0<X)
    (t z : ℂ) :
    ((I*J^3:ℝ):ℂ)⁻¹*((X*H/(I*J^3):ℝ):ℂ)^(-z)*
      ((I:ℂ)^(-t)*(J:ℂ)^(-3*t)) /
      ((Real.sqrt I:ℂ)*(J:ℂ)) * (Real.sqrt X:ℂ) =
      (X:ℂ)^(1/2-z)*(H:ℂ)^(-z)*
        (I:ℂ)^(-(t+1-z)-1/2)*(J:ℂ)^(-(1+3*(t+1-z))) := by
  have hi : (I:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hI.ne'
  have hj : (J:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hJ.ne'
  have hh : (H:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hH.ne'
  have hx : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  rw [←cpow_half_eq_sqrt I hI.le,←cpow_half_eq_sqrt X hX.le]
  rw [Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg (mul_pos hX hH).le (mul_pos hI (pow_pos hJ 3)).le]
  simp only [Complex.ofReal_mul,Complex.ofReal_pow]
  rw [Complex.mul_cpow_ofReal_nonneg hX.le hH.le]
  have hmul : ((I:ℂ)*(J:ℂ)^3)^(-z)=(I:ℂ)^(-z)*((J:ℂ)^3)^(-z) := by
    simpa only [Complex.ofReal_pow] using Complex.mul_cpow_ofReal_nonneg hI.le (pow_pos hJ 3).le (-z)
  rw [hmul]
  have hp : ((J:ℂ)^3)^(-z)=(J:ℂ)^((3:ℂ)*(-z)) := by
    simpa only [Real.rpow_ofNat,Real.rpow_natCast,Complex.ofReal_pow,Complex.cpow_ofNat,Complex.ofReal_ofNat] using
      (Complex.cpow_mul_ofReal_nonneg hJ.le (3:ℝ) (-z)).symm
  rw [hp]
  rw [show (J:ℂ)^3=(J:ℂ)^(3:ℂ) by simp]
  have hir : (I:ℂ)=Complex.exp (Complex.log (I:ℂ)) := (Complex.exp_log hi).symm
  have hjr : (J:ℂ)=Complex.exp (Complex.log (J:ℂ)) := (Complex.exp_log hj).symm
  simp only [Complex.cpow_def_of_ne_zero hi,Complex.cpow_def_of_ne_zero hj,
    Complex.cpow_def_of_ne_zero hh,Complex.cpow_def_of_ne_zero hx,div_eq_mul_inv,
    mul_inv_rev,←Complex.exp_neg,←Complex.exp_add]
  rw [hir,hjr]
  simp only [←Complex.exp_neg,←Complex.exp_add]
  rw [Complex.exp_log hi,Complex.exp_log hj]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1243

/-! Original module: OAI.NumberTheory.DirichletL.Detector.Windows
Source SHA256: 58089460ec680f566d0d79bde77d495de6e98633b7a6ed230ae6cc035f977ba8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1244


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem elementWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun m : O => W (elementNorm m / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (ShortDraftLatticeCount.rowNormBall M).finite_toSet.subset
  intro m hm
  apply ShortDraftLatticeCount.mem_rowNormBall_of_absNorm_le
  have hnorm : elementNorm m ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hm)
  unfold elementNorm at hnorm
  exact_mod_cast hnorm.trans hM.le

theorem idealWindow_finite_support (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) :
    (Function.support (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R))).Finite := by
  obtain ⟨B, hB, hbound⟩ := compact_window_bound W hW
  obtain ⟨M, hM⟩ := exists_nat_gt (B * R)
  apply (Ideal.finite_setOfPred_absNorm_le M).subset
  intro I hI
  have hnorm : (Ideal.absNorm I : ℝ) ≤ B * R := (div_le_iff₀ hR).mp (hbound _ hI)
  exact_mod_cast hnorm.trans hM.le

theorem elementWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : O → ℂ) :
    Summable (fun m : O => W (elementNorm m / R) * F m) := by
  apply summable_of_hasFiniteSupport
  apply (elementWindow_finite_support W hW R hR).subset
  intro m hm hzero
  exact hm (by simp only [hzero, zero_mul])

theorem idealWindow_mul_summable (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (R : ℝ) (hR : 0 < R) (F : Ideal O → ℂ) :
    Summable (fun I : Ideal O => W ((Ideal.absNorm I : ℝ) / R) * F I) := by
  apply summable_of_hasFiniteSupport
  apply (idealWindow_finite_support W hW R hR).subset
  intro I hI hzero
  exact hI (by simp only [hzero, zero_mul])

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1244

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalReopen
Source SHA256: 17b2815b48db16c5534bda27e55a568e738290c5b4ce0ea24832c9e63287e376
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1245




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbePhysical
open ActualEisensteinCubic CompletedGauss ProbeCompleted ProbeRow CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O

lemma supportedElement_ne_zero (s : O) (hs : Supported (Ideal.span {s})) : s≠0 := by
  intro h
  apply hs.1
  simp [h]

lemma finite_support_tsum_comm {α β : Type*} (f : α → β → ℂ) (S : Finset α)
    (hz : ∀ a, a∉S → ∀ b, f a b=0) (hs : ∀ a∈S, Summable (f a)) :
    (∑' a, ∑' b, f a b) = ∑' b, ∑' a, f a b := by
  calc
    _ = ∑ a∈S, ∑' b, f a b := tsum_eq_sum (fun a ha => by simp only [hz a ha, tsum_zero])
    _ = ∑' b, ∑ a∈S, f a b := (Summable.tsum_finsetSum hs).symm
    _ = _ := by
      apply tsum_congr
      intro b
      exact (tsum_eq_sum (fun a ha => hz a ha b)).symm

theorem physical_spectral_reopen (η : HeckeFamily.Character) (C : CalibrationData)
    (S : Finset (Ideal O)) (D : Ideal O) (s : O)
    (hs : Supported (Ideal.span {s})) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (K : ℝ) (hK : 0<K) (t : ℂ) (ht : 1<t.re) :
    (∑' m : O, C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) *
      W (elementNorm m/K) * spectralRow S D (rowCoefficient η C.Xi s hs m) t) =
    ∑' p : Ideal O × Ideal O, spectralSummand S D (baseRowCoefficient η C.Xi s hs) t p.1 p.2 *
      ∑' m : O, calibratedNumerator C (completedIndex p.1 p.2) m *
        sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) := by
  let F (m : O) (p : Ideal O × Ideal O) : ℂ :=
    C.residueMonoid m * sexticGauss s (supportedElement_ne_zero s hs) (-m) * W (elementNorm m/K) *
      spectralSummand S D (rowCoefficient η C.Xi s hs m) t p.1 p.2
  have hfin := elementWindow_finite_support W hW K hK
  have hzero : ∀ m, m∉hfin.toFinset → ∀ p, F m p=0 := by
    intro m hm p
    have hz : W (elementNorm m/K)=0 := by simpa only [Set.Finite.mem_toFinset, Function.mem_support, not_not] using hm
    simp only [F, hz, mul_zero, zero_mul]
  have hsum (m : O) : Summable (F m) :=
    (spectralRow_summable S D (rowCoefficient η C.Xi s hs m)
      (rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one s hs m) t ht).mul_left _
  have he := finite_support_tsum_comm F hfin.toFinset hzero (fun m _ => hsum m)
  calc
    _ = ∑' m : O, ∑' p : Ideal O × Ideal O, F m p := by
      simp only [F, spectralRow, tsum_mul_left]
    _ = ∑' p : Ideal O × Ideal O, ∑' m : O, F m p := he
    _ = _ := by
      apply tsum_congr
      intro p
      rw [← tsum_mul_left]
      apply tsum_congr
      intro m
      unfold F
      rw [spectralSummand_row_separation]
      unfold calibratedNumerator
      ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1245

/-! Original module: OAI.NumberTheory.DirichletL.Detector.PhysicalRows
Source SHA256: 58b97cbec9cc8b7c8fdb1feaffd1b91f62e1e247bcbb57aa865750dad2c456c8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1246



namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CanonicalQuadraticSieve CompletedGauss
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRowIndex := {I : Id // Supported I}×O

def physicalRowMonoid (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) : O→*ℂ :=
  rowCoefficient η C.Xi (primaryGenerator r.1.val)
    ((supported_span_primaryGenerator_iff r.1.val).mpr r.1.property) r.2

def physicalRowWeight (C : CalibrationData) (W0 W1 : ℝ→ℂ) (X Y : ℝ) (r : PhysicalRowIndex) : ℂ :=
  if ∀P∈C.excluded,¬P∣r.1.val then
    let a := primaryGenerator r.1.val
    let ha := supported_primaryGenerator_ne_zero r.1.val r.1.property
    let q : ℝ := Ideal.absNorm r.1.val
    (Y:ℂ)⁻¹*W1 (q/Y)*CanonicalRowCompletion.idealRowHom C.generator r.1.val/
      (C.tau*C.residueMonoid a*(Real.sqrt (elementNorm C.generator*q*X):ℂ))*
      C.residueMonoid r.2*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-r.2)*
        W0 (elementNorm r.2/(elementNorm C.generator*q*X))
  else 0

lemma physicalRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (r : PhysicalRowIndex) (n : O) : ‖physicalRowMonoid η C r n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ r.2 n

lemma physicalRowWeight_outer_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (h : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowWeight_inner_zero (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex)
    (h : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))=0) :
    physicalRowWeight C W0 W1 X Y r=0 := by
  unfold physicalRowWeight
  split_ifs <;> simp [h]

lemma physicalRowScale_pos (C : CalibrationData) (X : ℝ) (hX : 0<X)
    (s : {I : Id // Supported I}) : 0<elementNorm C.generator*(Ideal.absNorm s.val:ℝ)*X := by
  have hc : 0<elementNorm C.generator := by
    unfold elementNorm
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr C.generator_ne_zero))
  have hs : (0:ℝ)<Ideal.absNorm s.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr s.property.1)
  positivity

theorem physicalRowWeight_finite_support (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) :
    (Function.support (physicalRowWeight C W0 W1 X Y)).Finite := by
  have ho := (idealWindow_finite_support W1 hW1 Y hY).preimage
    (f:=fun s : {I : Id // Supported I}=>s.val) Subtype.val_injective.injOn
  apply Set.Finite.of_finite_fibers Prod.fst
  · apply ho.subset
    rintro s ⟨r,hr,rfl⟩
    exact fun hz=>hr (physicalRowWeight_outer_zero C W0 W1 X Y r hz)
  · intro s hs
    have hm := elementWindow_finite_support W0 hW0 _ (physicalRowScale_pos C X hX s)
    apply ((Set.finite_singleton s).prod hm).subset
    intro r hr
    have he : r.1=s := hr.2
    refine ⟨he,?_⟩
    intro hz
    apply hr.1
    apply physicalRowWeight_inner_zero C W0 W1 X Y r
    simpa only [he] using hz

lemma physicalRowWeight_mul_summable (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y : ℝ) (hX : 0<X) (hY : 0<Y) (F : PhysicalRowIndex→ℂ) :
    Summable (fun r=>physicalRowWeight C W0 W1 X Y r*F r) := by
  apply summable_of_hasFiniteSupport
  apply (physicalRowWeight_finite_support C W0 W1 hW0 hW1 X Y hX hY).subset
  intro r hr hz
  exact hr (by dsimp only; rw [hz,zero_mul])

theorem markedPhysicalProbe_eq_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t) := by
  have hf := physicalRowWeight_mul_summable C W0 W1 hW0 hW1 X Y hX hY
    (fun r=>verticalIntegral 4 (fun t=>(Z:ℂ)^t*Complex.exp (t^2)*spectralRow C.excluded D (physicalRowMonoid η C r) t))
  rw [hf.tsum_prod]
  unfold markedPhysicalProbe
  rw [←tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hc : ∀P∈C.excluded,¬P∣s.val
  · simp only [physicalRowWeight,physicalRowMonoid]
    try dsimp only
    simp only [ite_eq_left hc]
    rw [←tsum_mul_left,←tsum_mul_left]
    apply tsum_congr
    intro m
    ring
  · simp only [physicalRowWeight]
    try dsimp only
    simp only [ite_eq_right hc,zero_mul,mul_zero,tsum_zero]

theorem markedPhysicalProbe_eq_gaussian_rows (η : HeckeFamily.Character) (C : CalibrationData)
    (D : Id) (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    markedPhysicalProbe η C D W0 W1 X Y Z=
      ∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 X Y r*
        correctedCompletedT C.excluded D (physicalRowMonoid η C r) gaussianCompletedProfile Z := by
  rw [markedPhysicalProbe_eq_rows η C D W0 W1 hW0 hW1 X Y Z hX hY]
  apply tsum_congr
  intro r
  rw [spectralRow_eq_gaussianCompleted _ _ _ (physicalRowMonoid_norm η C r) 4 (by norm_num) Z hZ]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1246

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTuple
Source SHA256: 2cb103c746aab311d4047d6e06950828d709e7564a34d0f7f56e52d193725d3b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1247



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalRows_common_finset {α : Type*} (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (X Y : α→ℝ) (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) :
    ∃R : Finset PhysicalRowIndex,∀k∈F,∀r,r∉R→physicalRowWeight C W0 W1 (X k) (Y k) r=0 := by
  have hf (k : {k // k∈F}) := physicalRowWeight_finite_support C W0 W1 hW0 hW1
    (X k.val) (Y k.val) (hX k.val k.property) (hY k.val k.property)
  let R := F.attach.biUnion (fun k=>(hf k).toFinset)
  refine ⟨R,?_⟩
  intro k hk r hr
  by_contra hn
  apply hr
  exact Finset.mem_biUnion.mpr ⟨⟨k,hk⟩,by simp,by simpa only [Set.Finite.mem_toFinset,Function.mem_support] using hn⟩

theorem physical_selected_gaussian_reassembly {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : ι→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (hX : ∀k∈F,0<X k) (hY : ∀k∈F,0<Y k) (Z : ℝ) (hZ : 0<Z)
    (q : α→ι→ℝ) (hq : ∀k∈F,∀i,0<q k i) :
    (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
      (X k) (Y k) (Z*∏i,q k i))=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
        (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
          correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
            (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
        (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
          gaussianJointDensity V hV ((2:ℝ)^j/Z) t := by
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hs (k : α) (hk : k∈F) (f : PhysicalRowIndex→ℂ) :
      (∑'r,physicalRowWeight C W0 W1 (X k) (Y k) r*f r)=
      ∑r∈R,physicalRowWeight C W0 W1 (X k) (Y k) r*f r :=
    tsum_eq_sum (fun r hr=>by rw [hR k hk r hr,zero_mul])
  let A (p : α×PhysicalRowIndex) := a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2
  have hh := gaussian_selected_tuple_reassembly W V hV hsep (F×ˢR) A C.excluded
    (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) Z hZ (fun p=>q p.1)
    (fun p hp=>hq p.1 (Finset.mem_product.mp hp).1)
  calc
    _ = ∑p∈F×ˢR,A p*(∏i,W i (q p.1 i))*correctedCompletedT C.excluded (D p.1)
      (physicalRowMonoid η C p.2) gaussianCompletedProfile (Z*∏i,q p.1 i) := by
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro k hk
        rw [markedPhysicalProbe_eq_gaussian_rows η C (D k) W0 W1 hW0 hW1
          (X k) (Y k) _ (hX k hk) (hY k hk) (mul_pos hZ (Finset.prod_pos (fun i _=>hq k hk i))),hs k hk]
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r hr
        dsimp [A]
        ring
    _ = _ := hh
    _ = _ := by
      apply tsum_congr
      intro j
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro t
      dsimp only
      congr 1
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hs k hk,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro r hr
      dsimp [A]
      ring

theorem physical_selected_gaussian_family {ι α : Type*} [Fintype ι]
    (W : ι→ℝ→ℂ) (M : ι→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : SchwartzMap ℝ ℂ,∃hV : HasCompactSupport (V:ℝ→ℂ),
      (∀J : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧ ∀Z : ℝ,0<Z→
        Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z)) ∧
        (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment V hV J ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
        (∀k∈F,0<X k)→(∀k∈F,0<Y k)→∀Z : ℝ,0<Z→
        ∀q : α→ι→ℝ,(∀k∈F,∀i,0<q k i)→
        (∑k∈F,a k*(∏i,W i (q k i))*markedPhysicalProbe η C (D k) W0 W1
          (X k) (Y k) (Z*∏i,q k i))=
          ∑'j : ℕ,∫t : ℝ,(∑k∈F,a k*
            (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
              correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
                (CompletedHeight.normTwistedSource gaussianFixedWindow t) ((2:ℝ)^j))*
            (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*
              gaussianJointDensity V hV ((2:ℝ)^j/Z) t) := by
  obtain ⟨V,hV,hsep,_⟩ := gaussian_selected_slot_family W M hM hwindow
  refine ⟨V,hV,fun J s hs=>gaussianJointMoment_summed V hV J s hs,?_⟩
  intro η C W0 W1 hW0 hW1 F a D X Y hX hY Z hZ q hq
  exact physical_selected_gaussian_reassembly W V hV hsep η C W0 W1 hW0 hW1
    F a D X Y hX hY Z hZ q hq

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1247

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianCompensation
Source SHA256: 72d7f4fe4219cb5ee7aa82b97b468d6605cd7c40ebb2479fb38d37c9e909456d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1248



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma physicalElementNorm_pos (a : O) (ha : a≠0) : 0<elementNorm a := by
  unfold elementNorm
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr ha))

lemma elementNorm_slotProduct {K : ℕ} (p : Fin K→O) (J : Finset (Fin K)) :
    elementNorm (slotProduct p J)=∏i∈J,elementNorm (p i) := by
  induction J using Finset.induction_on with
  | empty => simp [slotProduct,elementNorm_one]
  | @insert i J hi ih => simpa only [slotProduct,Finset.prod_insert hi,elementNorm_mul] using congrArg (fun x=>elementNorm (p i)*x) ih

lemma slotProduct_nonzero {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    slotProduct p J≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)

lemma slotProduct_norm_pos {K : ℕ} (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K)) :
    0<elementNorm (slotProduct p J) := physicalElementNorm_pos _ (slotProduct_nonzero p hp J)

def compensationSubsetCoefficient {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (HeckeFamily.elementCoeff η (slotProduct p (Finset.univ\J)))

def compensationSubsetProbe {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y Z : ℝ) : ℂ :=
  compensationSubsetCoefficient η p J*
    markedPhysicalProbe η C (Ideal.span {slotProduct p (Finset.univ\J)}) W0 W1
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

lemma compensatedTuple_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) :
    compensatedTuple η C W0 W1 p X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,compensationSubsetProbe η C W0 W1 p J X Y Z := rfl

lemma compensatedPhysicalProbe_eq_subsets {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (slotPrimes : Fin K→Finset O)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (X Y Z : ℝ) :
    compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
      ∑J∈(Finset.univ : Finset (Fin K)).powerset,
        ∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
          (∏i,W i (elementNorm (p i).val/P i))*
            compensationSubsetProbe η C W0 W1 (fun i=>(p i).val) J X Y Z := by
  unfold compensatedPhysicalProbe
  simp_rw [compensatedTuple_eq_subsets,Finset.mul_sum]
  exact Finset.sum_comm

theorem compensationSubsetProbe_eq_gaussian_rows {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (p : Fin K→O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    compensationSubsetProbe η C W0 W1 p J X Y Z=
      compensationSubsetCoefficient η p J*
        ∑'r : PhysicalRowIndex,
          physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
            correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
              (physicalRowMonoid η C r) gaussianCompletedProfile
                (Z*elementNorm (slotProduct p (Finset.univ\J))) := by
  unfold compensationSubsetProbe
  rw [markedPhysicalProbe_eq_gaussian_rows η C _ W0 W1 hW0 hW1 _ _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J))
    (mul_pos hZ (slotProduct_norm_pos p hp _))]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1248

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianPhysicalTail
Source SHA256: c0c2845cc3dd4fe5e30ffdb06c43a73adde64a170386060bcac5b51465095a32
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1249



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory CompletedGauss FourierBridge
namespace SevenEighths.ProbePhysical
open ProbeCompleted
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def gaussianPhysicalFamilyIntegral {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) : ℂ :=
  ∫t : ℝ,(∑k∈F,a k*
    (∑'r : PhysicalRowIndex,physicalRowWeight C W0 W1 (X k) (Y k) r*
      correctedCompletedT C.excluded (D k) (physicalRowMonoid η C r)
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) T)*
    (∏i,W i (q k i)*logPhase (-t) (Real.log (q k i))))*gaussianJointDensity V hV (T/Z) t

def gaussianPhysicalFamilyMass {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) : ℝ :=
  ∑k∈F,‖a k‖*(∏i,‖W i (q k i)‖)*∑'r : PhysicalRowIndex,‖physicalRowWeight C W0 W1 (X k) (Y k) r‖

lemma gaussianPhysicalFamily_mass_eq {α ι : Type*} [Fintype ι]
    (C : CalibrationData) (W0 W1 : ℝ→ℂ) (F : Finset α) (a : α→ℂ) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianCompletedFamilyMass (F×ˢR)
      (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2) W (fun p=>q p.1)=
      gaussianPhysicalFamilyMass C W0 W1 F a X Y W q := by
  unfold gaussianCompletedFamilyMass gaussianPhysicalFamilyMass
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,norm_zero]),Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [norm_mul]
  ring

lemma gaussianPhysicalFamily_integral_eq {α ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (F : Finset α) (a : α→ℂ) (D : α→Id) (X Y : α→ℝ)
    (W : ι→ℝ→ℂ) (q : α→ι→ℝ) (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (T Z : ℝ) (R : Finset PhysicalRowIndex)
    (hR : ∀k∈F,∀r∉R,physicalRowWeight C W0 W1 (X k) (Y k) r=0) :
    gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV T Z=
      gaussianCompletedFamilyIntegral (F×ˢR)
        (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
        C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2) W (fun p=>q p.1) V hV T Z := by
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  congr 1
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro k hk
  rw [tsum_eq_sum (s:=R) (fun r hr=>by rw [hR k hk r hr,zero_mul]),Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  ring

theorem gaussianPhysicalFamily_remote (V : SchwartzMap ℝ ℂ)
    (hV : HasCompactSupport (V:ℝ→ℂ)) (N : ℕ) :
    ∃C0 : ℝ,0<C0 ∧ ∀{α ι : Type*} [Fintype ι],
      ∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
      HasCompactSupport W0→HasCompactSupport W1→
      ∀F : Finset α,∀a : α→ℂ,∀D : α→Id,∀X Y : α→ℝ,
      (∀k∈F,0<X k)→(∀k∈F,0<Y k)→∀W : ι→ℝ→ℂ,∀q : α→ι→ℝ,
      ∀Z A : ℝ,0<Z→1≤A→
      Summable (fun j : ℕ=>if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0) ∧
      (∑'j : ℕ,if (2:ℝ)^j/Z≤A⁻¹ ∨ A≤(2:ℝ)^j/Z then
        ‖gaussianPhysicalFamilyIntegral η C W0 W1 F a D X Y W q V hV ((2:ℝ)^j) Z‖ else 0)≤
          C0*gaussianPhysicalFamilyMass C W0 W1 F a X Y W q*Z^2/A^N := by
  obtain ⟨C0,hC0,hb⟩ := gaussianCompletedFamily_remote V hV N
  refine ⟨C0,hC0,?_⟩
  intro α ι _ η C W0 W1 hW0 hW1 F a D X Y hX hY W q Z A hZ hA
  obtain ⟨R,hR⟩ := physicalRows_common_finset C W0 W1 hW0 hW1 F X Y hX hY
  have hh := hb (F×ˢR) (fun p=>a p.1*physicalRowWeight C W0 W1 (X p.1) (Y p.1) p.2)
    C.excluded (fun p=>D p.1) (fun p=>physicalRowMonoid η C p.2)
    (fun p _=>physicalRowMonoid_norm η C p.2) W (fun p=>q p.1) Z A hZ hA
  rw [gaussianPhysicalFamily_mass_eq C W0 W1 F a X Y W q R hR] at hh
  simpa only [gaussianPhysicalFamily_integral_eq η C W0 W1 F a D X Y W q V hV _ Z R hR] using hh

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1249

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianSubset
Source SHA256: d3c66c1fe25820ac61ff34641cf84a5384851709462d1ad1a55b0237ed0f5a3a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1250


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory FourierBridge CompletedGauss
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev SelectedSlot {K : ℕ} (J : Finset (Fin K)) := ↥(Finset.univ\J)

def compensationSubsetWeight {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  compensationSubsetCoefficient η p J*(∏i∈J,W i (elementNorm (p i)/P i))

def selectedSlotFactor {K : ℕ} (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (p : Fin K→O) (J : Finset (Fin K)) (t : ℝ) : ℂ :=
  ∏i : SelectedSlot J,W i.val (elementNorm (p i.val)/P i.val)*
    logPhase (-t) (Real.log (elementNorm (p i.val)/P i.val))

def compensationRowTest {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K)) (X Y T t : ℝ) : ℂ :=
  ∑'r : PhysicalRowIndex,
    physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
      correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
        (physicalRowMonoid η C r) (CompletedHeight.normTwistedSource gaussianFixedWindow t) T

lemma gaussian_slot_window_split {K : ℕ} (W : Fin K→ℝ→ℂ) (q : Fin K→ℝ) (J : Finset (Fin K)) :
    (∏i,W i (q i))=(∏i∈J,W i (q i))*(∏i : SelectedSlot J,W i.val (q i.val)) := by
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=>W i (q i))]
  have hh := Finset.prod_sdiff (Finset.subset_univ J) (f:=fun i=>W i (q i))
  simpa only [mul_comm] using hh.symm

lemma gaussian_compensation_scale {K : ℕ} (P : Fin K→ℝ) (hP : ∀i,0<P i)
    (p : Fin K→O) (J : Finset (Fin K)) (Z : ℝ) :
    (Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p i.val)/P i.val)=
      Z*elementNorm (slotProduct p (Finset.univ\J)) := by
  rw [←Finset.prod_coe_sort (Finset.univ\J) P]
  rw [gaussian_selected_scale Z (fun i : SelectedSlot J=>P i.val)
    (fun i : SelectedSlot J=>elementNorm (p i.val)) (fun i=>hP i.val)]
  rw [Finset.prod_coe_sort (Finset.univ\J) (fun i=>elementNorm (p i)),elementNorm_slotProduct]

theorem compensation_subset_common {K : ℕ} {α : Type*}
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (V : SchwartzMap ℝ ℂ) (hV : HasCompactSupport (V:ℝ→ℂ))
    (hsep : ∀R : ℝ,0<R→∀x : ℝ,0<x→∀q : SelectedSlot J→ℝ,(∀i,0<q i)→
      gaussianAnnulus x*(∏i,W i.val (q i))*gaussianMellinProfile (R*x/(∏i,q i))=
        ∫t : ℝ,Vstar (CompletedHeight.normTwistedSource gaussianFixedWindow t) x*
          (∏i,W i.val (q i)*logPhase (-t) (Real.log (q i)))*gaussianJointDensity V hV R t)
    (η : HeckeFamily.Character) (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (hW0 : HasCompactSupport W0) (hW1 : HasCompactSupport W1)
    (F : Finset α) (p : α→Fin K→O) (hp : ∀k∈F,∀i,p k i≠0)
    (P : Fin K→ℝ) (hP : ∀i,0<P i) (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∑k∈F,(∏i,W i (elementNorm (p k i)/P i))*compensationSubsetProbe η C W0 W1 (p k) J X Y Z)=
      ∑'j : ℕ,∫t : ℝ,(∑k∈F,compensationSubsetWeight η W P (p k) J*
        compensationRowTest η C W0 W1 (p k) J X Y ((2:ℝ)^j) t*
          selectedSlotFactor W P (p k) J t)*
            gaussianJointDensity V hV ((2:ℝ)^j/(Z*∏i∈Finset.univ\J,P i)) t := by
  have hbase : 0<Z*∏i∈Finset.univ\J,P i := mul_pos hZ (Finset.prod_pos (fun i _=>hP i))
  have hh := physical_selected_gaussian_reassembly
    (fun i : SelectedSlot J=>W i.val) V hV hsep η C W0 W1 hW0 hW1 F
    (fun k=>compensationSubsetWeight η W P (p k) J)
    (fun k=>Ideal.span {slotProduct (p k) (Finset.univ\J)})
    (fun k=>X/elementNorm (slotProduct (p k) J)) (fun k=>Y/elementNorm (slotProduct (p k) J))
    (fun k hk=>div_pos hX (slotProduct_norm_pos (p k) (hp k hk) J))
    (fun k hk=>div_pos hY (slotProduct_norm_pos (p k) (hp k hk) J))
    (Z*∏i∈Finset.univ\J,P i) hbase
    (fun k (i : SelectedSlot J)=>elementNorm (p k i.val)/P i.val)
    (fun k hk i=>div_pos (physicalElementNorm_pos _ (hp k hk i.val)) (hP i.val))
  calc
    _ = ∑k∈F,compensationSubsetWeight η W P (p k) J*
      (∏i : SelectedSlot J,W i.val (elementNorm (p k i.val)/P i.val))*
        markedPhysicalProbe η C (Ideal.span {slotProduct (p k) (Finset.univ\J)}) W0 W1
          (X/elementNorm (slotProduct (p k) J)) (Y/elementNorm (slotProduct (p k) J))
          ((Z*∏i∈Finset.univ\J,P i)*(∏i : SelectedSlot J,elementNorm (p k i.val)/P i.val)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [gaussian_compensation_scale P hP (p k) J Z,gaussian_slot_window_split W (fun i=>elementNorm (p k i)/P i) J]
      unfold compensationSubsetProbe compensationSubsetWeight
      ring
    _ = _ := hh

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1250

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GaussianCommon
Source SHA256: ecacb550c8a12fca88c7df98e7c086808338979f56058cdba850d6fc00ad41a4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1251


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
open MeasureTheory
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem compensatedPhysicalProbe_common_gaussian {K : ℕ}
    (W : Fin K→ℝ→ℂ) (M : Fin K→ℝ) (hM : ∀i,0≤M i)
    (hwindow : ∀i y,W i (Real.exp y)≠0→|y|≤M i) :
    ∃V : Finset (Fin K)→SchwartzMap ℝ ℂ,
    ∃hV : ∀A,HasCompactSupport (V A:ℝ→ℂ),
      (∀N : ℕ,∀s : ℝ,0<s→∃B : ℝ,0<B ∧
        ∀A : Finset (Fin K),∀Z : ℝ,0<Z→
          Summable (fun j : ℕ=>((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z)) ∧
          (∑'j : ℕ,((2:ℝ)^j)^s*gaussianJointMoment (V A) (hV A) N ((2:ℝ)^j/Z))≤B*Z^s) ∧
      (∀η : HeckeFamily.Character,∀C : CalibrationData,∀W0 W1 : ℝ→ℂ,
        HasCompactSupport W0→HasCompactSupport W1→
        ∀slotPrimes : Fin K→Finset O,(∀i a,a∈slotPrimes i→a≠0)→
        ∀P : Fin K→ℝ,(∀i,0<P i)→∀X Y Z : ℝ,0<X→0<Y→0<Z→
          compensatedPhysicalProbe η C W0 W1 slotPrimes W P X Y Z=
          ∑A∈(Finset.univ : Finset (Fin K)).powerset,
            ∑'j : ℕ,∫t : ℝ,
              (∑p : ((i : Fin K)→{a : O // a∈slotPrimes i}),
                compensationSubsetWeight η W P (fun i=>(p i).val) A*
                  compensationRowTest η C W0 W1 (fun i=>(p i).val) A X Y ((2:ℝ)^j) t*
                    selectedSlotFactor W P (fun i=>(p i).val) A t)*
                      gaussianJointDensity (V A) (hV A) ((2:ℝ)^j/(Z*∏i∈Finset.univ\A,P i)) t) := by
  choose V hV hsep hbound using fun A : Finset (Fin K)=>
    gaussian_selected_slot_family (fun i : SelectedSlot A=>W i.val)
      (fun i : SelectedSlot A=>M i.val) (fun i=>hM i.val) (fun i=>hwindow i.val)
  refine ⟨V,hV,?_,?_⟩
  · intro N s hs
    choose B hB hb using fun A : Finset (Fin K)=>gaussianJointMoment_summed (V A) (hV A) N s hs
    let B0 := (∑A∈(Finset.univ : Finset (Fin K)).powerset,B A)+1
    have hB0 : 0<B0 := by
      have hh : 0≤∑A∈(Finset.univ : Finset (Fin K)).powerset,B A :=
        Finset.sum_nonneg (fun A _=>(hB A).le)
      dsimp only [B0]
      linarith
    refine ⟨B0,hB0,?_⟩
    intro A Z hZ
    obtain ⟨hsm,hbd⟩ := hb A Z hZ
    refine ⟨hsm,hbd.trans ?_⟩
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hZ.le s)
    have hm : A∈(Finset.univ : Finset (Fin K)).powerset := Finset.mem_powerset.mpr (Finset.subset_univ A)
    have hh := Finset.single_le_sum (fun A _=>(hB A).le) hm
    dsimp only [B0]
    linarith
  · intro η C W0 W1 hW0 hW1 slotPrimes hp P hP X Y Z hX hY hZ
    rw [compensatedPhysicalProbe_eq_subsets]
    apply Finset.sum_congr rfl
    intro A hA
    exact compensation_subset_common A W (V A) (hV A) (hsep A) η C W0 W1 hW0 hW1 Finset.univ
      (fun p : ((i : Fin K)→{a : O // a∈slotPrimes i})=>fun i=>(p i).val)
      (fun p _ i=>hp i (p i).val (p i).property) P hP X Y Z hX hY hZ

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1251

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowRay
Source SHA256: 4e5d316148776753dba3766095833f0565ad90d02c1ac31adf41dc10f9e718f4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1252


namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbePhysical
open ProbeCompleted ProbeRow CompletedGauss CanonicalQuadraticSieve CanonicalRowCompletion
open RayFourExpansion CanonicalCoefficientClass
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

abbrev PhysicalRayElement := {s : O // Supported (Ideal.span {s})}

def physicalRay (s : O) : RayRing := Ideal.Quotient.mk (Ideal.span {(4:O)}) s

def physicalRayRepresentative (σ : RayRing) : PhysicalRayElement :=
  if h : ∃s : PhysicalRayElement,physicalRay s.val=σ then Classical.choose h
  else ⟨1,by
    simp [Supported,Ideal.span_singleton_one,←Ideal.one_eq_top]
    change (1:Id)≠0
    exact one_ne_zero⟩

lemma physicalRayRepresentative_spec (s : PhysicalRayElement) :
    physicalRay (physicalRayRepresentative (physicalRay s.val)).val=physicalRay s.val := by
  have hh : ∃r : PhysicalRayElement,physicalRay r.val=physicalRay s.val := ⟨s,rfl⟩
  simp only [physicalRayRepresentative,dite_eq_left hh]
  exact Classical.choose_spec hh

lemma rowCoefficient_congr_ray (η : HeckeFamily.Character) (Xi : O→*ℂ)
    (s r : PhysicalRayElement) (h : physicalRay s.val=physicalRay r.val) (m : O) :
    rowCoefficient η Xi s.val s.property m=rowCoefficient η Xi r.val r.property m := by
  apply MonoidHom.ext
  intro n
  rw [rowCoefficient_apply,rowCoefficient_apply]
  have hd : (4:O)∣s.val-r.val := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp h)
  have he : sexticReciprocityPhase s.val n=sexticReciprocityPhase r.val n := by
    unfold sexticReciprocityPhase
    rw [QuadraticGaussRay.residue_eq_of_four_dvd_sub s.val r.val hd]
  rw [he]

def physicalRayRowMonoid (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m : O) : O→*ℂ :=
  rowCoefficient η C.Xi (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m

def physicalIdealRay (s : {I : Id // Supported I}) : RayRing := physicalRay (primaryGenerator s.val)

lemma physicalRowMonoid_eq_ray (η : HeckeFamily.Character) (C : CalibrationData) (r : PhysicalRowIndex) :
    physicalRowMonoid η C r=physicalRayRowMonoid η C (physicalIdealRay r.1) r.2 := by
  let s : PhysicalRayElement :=
    ⟨primaryGenerator r.1.val,(supported_span_primaryGenerator_iff r.1.val).mpr r.1.property⟩
  exact rowCoefficient_congr_ray η C.Xi s (physicalRayRepresentative (physicalRay s.val))
    (physicalRayRepresentative_spec s).symm r.2

lemma physicalRayRowMonoid_norm (η : HeckeFamily.Character) (C : CalibrationData)
    (σ : RayRing) (m n : O) : ‖physicalRayRowMonoid η C σ m n‖≤1 :=
  rowCoefficient_norm_le_one η C.Xi C.Xi_norm_le_one _ _ m n

def physicalRayPeriodicBase (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) (σ : RayRing) (χ : RayCharacter) : O→*ℂ :=
  lowPeriodicBase η (calibrationForSet S hS) (calibrationForSet S hS).generator
    (calibrationLowData S hS) (physicalRayRepresentative σ).val
      (physicalRayRepresentative σ).property χ

theorem physicalRayPeriodicBase_uniform (η : HeckeFamily.Character) (S : Finset Id)
    (hS : ∀P∈S,P.IsMaximal) :
    ∃L : Id,L≠0 ∧ ∀σ : RayRing,∀χ : RayCharacter,
      FactorsModulo L (physicalRayPeriodicBase η S hS σ χ) ∧
      ∀n : O,‖physicalRayPeriodicBase η S hS σ χ n‖≤1 := by
  refine ⟨lowBaseModulus η (calibrationForSet S hS) (calibrationForSet S hS).generator (calibrationLowData S hS),
    lowBaseModulus_ne_zero η _ _ (calibrationForSet S hS).generator_ne_zero _,?_⟩
  intro σ χ
  exact ⟨lowPeriodicBase_periodic η _ _ _ _ _ χ,lowPeriodicBase_norm η _ _ _ _ _ χ⟩

theorem physicalRayRow_eq_periodic_inverse (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (σ : RayRing) (m : O) (D : Id) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (T : ℝ) (hT : 0<T) :
    correctedCompletedT S D (physicalRayRowMonoid η (calibrationForSet S hS) σ m) W T=
      ∑χ : RayCharacter,correctionCoeff χ*
        InverseMoment.markedCompletedT
          (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator 1 m)
          W T (fun A=>if D∣A then (1:ℂ) else 0) :=
  correctedPhysicalRow_eq_periodic_inverse η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D W hW T hT
      (calibrationLowData S hS)

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1252

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowCutoff
Source SHA256: 18c6ab998cde0bd7761495a80b36fe77f0becc2a4d3b7b00b36a7e1e626baf0c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1253



namespace OAI

noncomputable section
open scoped Classical ContDiff
namespace SevenEighths.ProbePhysical
local notation "O" => ActualEisensteinCubic.O

def lowOuterCutoff (a b x : ℝ) : ℂ :=
  (Real.smoothTransition (2*x/a-1):ℂ)*(Real.smoothTransition (2-x/b):ℂ)

lemma lowOuterCutoff_small (a b : ℝ) (ha : 0<a) (x : ℝ) (hx : x≤a/2) :
    lowOuterCutoff a b x=0 := by
  have h : 2*x/a-1≤0 := by
    have hh : 2*x/a≤1 := (div_le_iff₀ ha).mpr (by linarith)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,zero_mul]

lemma lowOuterCutoff_large (a b : ℝ) (hb : 0<b) (x : ℝ) (hx : 2*b≤x) :
    lowOuterCutoff a b x=0 := by
  have h : 2-x/b≤0 := by
    have hh : 2≤x/b := (le_div_iff₀ hb).mpr hx
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.zero_of_nonpos h,Complex.ofReal_zero,mul_zero]

lemma lowOuterCutoff_one (a b : ℝ) (ha : 0<a) (hb : 0<b) (x : ℝ) (hlo : a≤x) (hhi : x≤b) :
    lowOuterCutoff a b x=1 := by
  have hl : 1≤2*x/a-1 := by
    have hh : 2≤2*x/a := (le_div_iff₀ ha).mpr (by linarith)
    linarith
  have hr : 1≤2-x/b := by
    have hh : x/b≤1 := (div_le_iff₀ hb).mpr (by simpa using hhi)
    linarith
  simp only [lowOuterCutoff,Real.smoothTransition.one_of_one_le hl,
    Real.smoothTransition.one_of_one_le hr,Complex.ofReal_one,mul_one]

lemma lowOuterCutoff_smooth (a b : ℝ) : ContDiff ℝ ∞ (lowOuterCutoff a b) := by
  unfold lowOuterCutoff
  exact (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop))).mul
    (Complex.ofRealCLM.contDiff.comp (Real.smoothTransition.contDiff.comp (by fun_prop)))

lemma lowOuterCutoff_support (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Function.support (lowOuterCutoff a b)⊆Set.Icc (a/2) (2*b) := by
  intro x hx
  constructor
  · by_contra hh
    exact hx (lowOuterCutoff_small a b ha x (le_of_lt (lt_of_not_ge hh)))
  · by_contra hh
    exact hx (lowOuterCutoff_large a b hb x (le_of_lt (lt_of_not_ge hh)))

lemma lowOuterCutoff_compact (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    HasCompactSupport (lowOuterCutoff a b) :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc (lowOuterCutoff_support a b ha hb)

lemma physical_ratio_factor (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y) :
    m/(B*X*Y)=(q/Y)*(m/(B*q*X)) := by
  field_simp

lemma physical_window_cutoff_one (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (B q X Y m : ℝ) (hq : 0<q) (hY : 0<Y)
    (h0 : W0 (m/(B*q*X))≠0) (h1 : W1 (q/Y)≠0) :
    lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (m/(B*X*Y))=1 := by
  have h0b := hW0 h0
  have h1b := hW1 h1
  apply lowOuterCutoff_one _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.1 h1b.1 ha1.le (le_trans ha0.le h0b.1)
    simpa only [mul_comm] using hh
  · rw [physical_ratio_factor B q X Y m hq hY]
    have hh := mul_le_mul h0b.2 h1b.2 (le_trans ha1.le h1b.1) (le_trans ha0.le (h0b.1.trans h0b.2))
    have hd : (q/Y)*(m/(B*q*X))≤b0*b1 := by simpa only [mul_comm] using hh
    exact hd.trans (le_max_right _ _)

theorem physicalRowWeight_insert_cutoff (C : CalibrationData) (W0 W1 : ℝ→ℂ)
    (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (X Y : ℝ) (hY : 0<Y) (r : PhysicalRowIndex) :
    physicalRowWeight C W0 W1 X Y r=
      lowOuterCutoff (a0*a1) (max 1 (b0*b1)) (elementNorm r.2/(elementNorm C.generator*X*Y))*
        physicalRowWeight C W0 W1 X Y r := by
  by_cases hz : physicalRowWeight C W0 W1 X Y r=0
  · simp only [hz,mul_zero]
  have h0 : W0 (elementNorm r.2/(elementNorm C.generator*(Ideal.absNorm r.1.val:ℝ)*X))≠0 :=
    fun h=>hz (physicalRowWeight_inner_zero C W0 W1 X Y r h)
  have h1 : W1 ((Ideal.absNorm r.1.val:ℝ)/Y)≠0 :=
    fun h=>hz (physicalRowWeight_outer_zero C W0 W1 X Y r h)
  have hq : (0:ℝ)<Ideal.absNorm r.1.val := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr r.1.property.1)
  rw [physical_window_cutoff_one W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (elementNorm C.generator) (Ideal.absNorm r.1.val) X Y (elementNorm r.2) hq hY h0 h1,one_mul]

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1253

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowMellin
Source SHA256: bef0d8a8c81e1b17beab5e079039a72c6d8c866aba61a5d068be095ee5ce3c27
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1254



namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical

lemma low_mellin_phase_norm (a v : ℝ) (ha : 0<a) :
    ‖(a:ℂ)^((v:ℂ)*Complex.I)‖=1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos ha]
  simp

lemma low_mellin_ratio_integrable (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    Integrable (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*
      mellin W ((v:ℂ)*Complex.I)) := by
  have hm : Integrable (fun v : ℝ=>mellin W ((v:ℂ)*Complex.I)) := by
    have hh := compactMellin_vertical_integrable W a0 b0 ha0 hW hWs 0
    change Integrable (fun v : ℝ=>mellin W ((0:ℂ)+v*Complex.I)) at hh
    simpa using hh
  have hc : Continuous (fun v : ℝ=>(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)) :=
    (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr ha.ne'))).mul
      (Continuous.const_cpow (by fun_prop) (Or.inl (Complex.ofReal_ne_zero.mpr hb.ne')))
  have hp : ∀v : ℝ,‖(a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)‖≤1 := by
    intro v
    rw [norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos ha,Complex.norm_cpow_eq_rpow_re_of_pos hb]
    simp
  simpa only [mul_comm] using hm.mul_bdd hc.aestronglyMeasurable (Filter.Eventually.of_forall hp)

lemma low_mellin_ratio (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (a b : ℝ) (ha : 0<a) (hb : 0<b) :
    W (a/b)=(1/(2*Real.pi):ℂ)*∫v : ℝ,
      (a:ℂ)^(-((v:ℂ)*Complex.I))*(b:ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  rw [compactMellin_inversion W a0 b0 ha0 hW hWs 0 _ (div_pos ha hb)]
  congr 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  rw [Complex.ofReal_zero,zero_add,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg ha.le hb.le]
  simp only [div_eq_mul_inv,←Complex.cpow_neg,neg_neg]

lemma low_sqrt_ratio (B q X Y : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) :
    (Real.sqrt (B*q*X):ℂ)⁻¹=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*((q/Y:ℝ):ℂ)^(-(1/2:ℂ)) := by
  have hQ : 0<B*X*Y := by positivity
  have hb : 0<q/Y := div_pos hq hY
  have he : B*q*X=(B*X*Y)*(q/Y) := by field_simp
  rw [he,Real.sqrt_mul hQ.le,Complex.ofReal_mul,Complex.cpow_neg,ProbeEuler.cpow_half_eq_sqrt _ hb.le]
  simp only [mul_inv_rev,mul_comm]

theorem physical_radial_low_mellin (W : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW : Function.support W⊆Set.Icc a0 b0) (hWs : ContDiff ℝ ∞ W)
    (B q X Y m : ℝ) (hB : 0<B) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hm : 0<m) :
    (Real.sqrt (B*q*X):ℂ)⁻¹*W (m/(B*q*X))=
      (Real.sqrt (B*X*Y):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
          ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I) := by
  have hQ : 0<B*X*Y := by positivity
  have ha : 0<m/(B*X*Y) := div_pos hm hQ
  have hb : 0<q/Y := div_pos hq hY
  have hbc : ((q/Y:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hb.ne'
  have he : m/(B*q*X)=(m/(B*X*Y))/(q/Y) := by field_simp
  rw [he,low_mellin_ratio W a0 b0 ha0 hW hWs _ _ ha hb,low_sqrt_ratio B q X Y hB hq hX hY]
  simp_rw [Complex.cpow_add _ _ hbc]
  rw [show (fun v : ℝ=>((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*
    (((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I))*mellin W ((v:ℂ)*Complex.I))=
    (fun v : ℝ=>((q/Y:ℝ):ℂ)^(-(1/2:ℂ))*
      (((m/(B*X*Y):ℝ):ℂ)^(-((v:ℂ)*Complex.I))*((q/Y:ℝ):ℂ)^((v:ℂ)*Complex.I)*mellin W ((v:ℂ)*Complex.I))) by funext v; ring]
  rw [integral_const_mul]
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1254

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowRowMellin
Source SHA256: 485c4c24852590e61653d2639d777d7e65f90627b937d93e26ce5bf722019799
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1255


namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory CompletedGauss
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def lowAdditiveCoefficient (C : CalibrationData) (W1 : ℝ→ℂ) (Y : ℝ)
    (s : {I : Id // Supported I}) (m : O) (v : ℝ) : ℂ :=
  if ∀P∈C.excluded,¬P∣s.val then
    let a := primaryGenerator s.val
    let ha := supported_primaryGenerator_ne_zero s.val s.property
    let q : ℝ := Ideal.absNorm s.val
    (Y:ℂ)⁻¹*W1 (q/Y)*idealRowHom C.generator s.val/(C.tau*C.residueMonoid a)*
      ((q/Y:ℝ):ℂ)^(-(1/2:ℂ)+(v:ℂ)*Complex.I)*(Real.sqrt q:ℂ)⁻¹*sexticGauss a ha (-m)
  else 0

def lowPhysicalScale (C : CalibrationData) (X Y : ℝ) : ℝ := elementNorm C.generator*X*Y

def lowRowMellinIntegrand (C : CalibrationData) (W0 W1 Ω : ℝ→ℂ)
    (X Y : ℝ) (r : PhysicalRowIndex) (v : ℝ) : ℂ :=
  mellin W0 ((v:ℂ)*Complex.I)*Ω (elementNorm r.2/lowPhysicalScale C X Y)*C.residueMonoid r.2*
