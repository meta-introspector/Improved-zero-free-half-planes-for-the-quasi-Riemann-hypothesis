  field_simp

theorem initial_invariant_bound (Z H B F R c : ℝ)
    (hZ : 0<Z) (hH : 0<H) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z H B*R/(columnScale Z B F*F)≤c*(Z/H) := by
  rw [initial_invariant_identity Z H B F R hZ.ne' hB.ne' hF.ne']
  have hh : R/B≤c := (div_le_iff₀ hB).mpr hR
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left hh (div_nonneg hZ.le hH.le)

theorem initial_invariant_power_general (Z B F R c σ : ℝ)
    (hZ : 0<Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z (Z^(1+σ)) B*R/(columnScale Z B F*F)≤c*Z^(-σ) := by
  have he : Z/Z^(1+σ)=Z^(-σ) := by
    calc
      _ = Z^((1:ℝ)-(1+σ)) := by rw [Real.rpow_sub hZ,Real.rpow_one]
      _ = _ := by congr 1; ring
  simpa only [he] using initial_invariant_bound Z (Z^(1+σ)) B F R c
    hZ (Real.rpow_pos_of_pos hZ _) hB hF hR

theorem initial_invariant_power (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) :
    rowScale Z (Z^((11:ℝ)/10)) B*R/(columnScale Z B F*F)≤c*Z^(-(1:ℝ)/10) := by
  have hZ0 : 0<Z := by linarith
  have he : Z/(Z^((11:ℝ)/10))=Z^(-(1:ℝ)/10) := by
    calc
      _ = Z^((1:ℝ)-(11:ℝ)/10) := by rw [Real.rpow_sub hZ0,Real.rpow_one]
      _ = _ := by norm_num
  simpa only [he] using initial_invariant_bound Z (Z^((11:ℝ)/10)) B F R c
    hZ0 (Real.rpow_pos_of_pos hZ0 _) hB hF hR

theorem initial_invariant_reserved_margin (Z B F R c : ℝ)
    (hZ : 1≤Z) (hB : 0<B) (hF : 0<F) (hR : R≤c*B) (hc : c≤Z^((1:ℝ)/20)) :
    rowScale Z (Z^((11:ℝ)/10)) B*R≤
      columnScale Z B F*F*Z^(-(1:ℝ)/20) := by
  have hZ0 : 0<Z := by linarith
  have hmass : 0<columnScale Z B F*F := by unfold columnScale; positivity
  rw [mul_comm (columnScale Z B F*F)]
  apply (div_le_iff₀ hmass).mp
  apply (initial_invariant_power Z B F R c hZ hB hF hR).trans
  calc
    c*Z^(-(1:ℝ)/10) ≤ Z^((1:ℝ)/20)*Z^(-(1:ℝ)/10) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hZ0.le _)
    _ = Z^(-(1:ℝ)/20) := by rw [←Real.rpow_add hZ0]; norm_num

theorem initial_budget_identity (Z H B : ℝ) (hZ : Z≠0) (hB : B≠0) :
    (H*B/Z^2)*B*(Z/B)*(Z/B)=H := by field_simp

end InitialMeanSquare

end

end OAI
end OAIOriginalModule0186

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicLoss
Source SHA256: eee2f4bbf9a66ec704ad90cda630861aa19783d916e37d4316a927adfc05abd3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0187


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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

theorem lifting_annular_scale_bounds (j : Fin 7) : 1≤(2:ℝ)^j.val ∧ (2:ℝ)^j.val≤64 := by
  refine ⟨one_le_pow₀ (by norm_num),?_⟩
  have hj : j.val≤6 := by omega
  have hh := pow_le_pow_right₀ (by norm_num : (1:ℝ)≤2) hj
  norm_num at hh
  exact hh

theorem HasSieveExponent.lifted_annular_selected {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (j : Fin 7) (q : ℝ), 1≤q → q≤7 →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N (N/q) a →
      annularHighEnergy ((2:ℝ)^j.val*M) N (selectedPoissonK fixedCutoffBase M N η) a ≤
        C*(M*N)^(260*η)*M*∑J,‖a J‖^2 := by
  have hc0 : 0<fixedCutoffBase := lt_of_lt_of_le (by norm_num) fixedCutoffBase_bounds.1
  obtain ⟨C,hC,hann⟩ := hexp.annular_selected_bound hα1 hα2 η hη hη1 l A hl hA
    (21952*fixedCutoffBase) (by linarith [fixedCutoffBase_bounds.1])
  refine ⟨C*64^(260*η)*64,by positivity,?_⟩
  intro M N hM hN hthreshold hK j q hq hq7 a ha
  let r : ℝ := (2:ℝ)^j.val
  have hr := lifting_annular_scale_bounds j
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hq0 : 0<q := by linarith
  have hr0 : 0<r := by dsimp [r]; positivity
  have hNq : 4≤N/q := (le_div_iff₀ hq0).mpr (by nlinarith)
  have hNqN : N/q≤N := div_le_self hN0.le hq
  have hβ : 0≤2-1/α := by
    have hfrac : 1/α≤1 := (div_le_one (by linarith : 0<α)).mpr hα1
    linarith
  have hth : (N/q)^(2-1/α)≤r*M := by
    calc
      _ ≤ N^(2-1/α) := Real.rpow_le_rpow (by positivity) hNqN hβ
      _ ≤ M := hthreshold
      _ ≤ r*M := by nlinarith [hr.1]
  let c := cutoffRescaleCoefficient fixedCutoffBase η r q
  have hc := cutoffRescaleCoefficient_bounds fixedCutoffBase η r q hc0.le hη.le hη1 hr.1 hr.2 hq hq7
  have hk := selectedPoissonK_rescale fixedCutoffBase M N η r q hM0 hN0 hr0 hq0
  have hh := hann c (r*M) (N/q) hc.1 hc.2 (by nlinarith [hr.1]) hNq hth
    (by simpa only [c,hk] using hK) (coefficientAtScale N (N/q) a)
    (coefficientAtScale_shell N (N/q) a ha)
  dsimp only [c] at hh
  rw [hk,←annularHighEnergy_coefficientAtScale (r*M) N (N/q)
    (selectedPoissonK fixedCutoffBase M N η) a (fun J hJ => (ha J hJ).2),
    ←coefficientAtScale_energy N (N/q) a (fun J hJ => (ha J hJ).2)] at hh
  have hp : ((r*M)*(N/q))^(260*η)≤64^(260*η)*(M*N)^(260*η) := by
    calc
      _ ≤ (64*(M*N))^(260*η) := by
        apply Real.rpow_le_rpow (by positivity) _ (by positivity)
        calc
          (r*M)*(N/q) ≤ (64*M)*N := by gcongr; exact hr.2
          _ = _ := by ring
      _ = _ := Real.mul_rpow (by norm_num) (by positivity)
  change annularHighEnergy (r*M) N _ a≤_
  apply hh.trans
  calc
    _ ≤ C*(64^(260*η)*(M*N)^(260*η))*(64*M)*∑J,‖a J‖^2 := by
      gcongr
      exact hr.2
    _ = _ := by ring

theorem HasSieveExponent.ball_selected_high {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (l A : ℕ) (hl : 4≤η*l) (hA : 4≤η*A) :
    ∃ C : ℝ, 0<C ∧ ∀ (M N : ℝ),
      1≤M → 28≤N → N^(2-1/α)≤M →
      1≤selectedPoissonK fixedCutoffBase M N η →
      ∀ (a : idealRange N → ℂ), CoefficientOnShell N N a →
      ballQuadraticEnergy M N a ≤
        (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+
          C*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := by
  obtain ⟨C,hC,hann⟩ := hexp.lifted_annular_selected hα1 hα2 η hη hη1 l A hl hA
  refine ⟨14*C,by positivity,?_⟩
  intro M N hM hN hthreshold hK a ha
  have hf (j : Fin 7) := hann M N hM hN hthreshold hK j 1 (by norm_num) (by norm_num)
    (liftingFreeCoefficient N a) (by simpa only [div_one] using liftingFreeCoefficient_shell N N a ha)
  have hd (j : Fin 7) := hann M N hM hN hthreshold hK j 7 (by norm_num) (by norm_num)
    (liftingDividedCoefficient N a) (liftingDividedCoefficient_shell N N a ha)
  have hsf := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hf j)
  have hsd := Finset.sum_le_sum (fun j (_ : j∈(Finset.univ : Finset (Fin 7))) => hd j)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_ofNat] at hsf hsd
  have he := liftingCoefficient_energy N a
  have hb := ballQuadraticEnergy_lifted_annuli M N (selectedPoissonK fixedCutoffBase M N η)
    (by linarith) a
  calc
    _ ≤ sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
      2*(7*(C*(M*N)^(260*η)*M*∑J,‖liftingFreeCoefficient N a J‖^2)+
        7*(C*(M*N)^(260*η)*M*∑J,‖liftingDividedCoefficient N a J‖^2)) := by linarith
    _ = _ := by
      calc
        _ = sieveNorm (selectedPoissonK fixedCutoffBase M N η) N*(∑J,‖a J‖^2)+
          (14*C)*(M*N)^(260*η)*M*((∑J,‖liftingFreeCoefficient N a J‖^2)+
            (∑J,‖liftingDividedCoefficient N a J‖^2)) := by ring
        _ = _ := by rw [he]; ring

theorem HasSieveExponent.low_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1≤α) (hα2 : α≤2) (η : ℝ) (hη : 0<η) (hη1 : η≤1)
    (c : ℝ) (hc : 4≤c) :
    ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N → N^(2-1/α)≤M → M≤N^2 →
      sieveNorm (selectedPoissonK c M N η) N≤C*(M*N)^(6*η)*M := by
  obtain ⟨C,hC,hrev⟩ := hexp.reverse η hη
  have hc0 : 0<c := by linarith
  refine ⟨C*c^η*(1+c^α),by positivity,?_⟩
  intro M N hM hN hthreshold hupper
  have hM0 : 0<M := by linarith
  have hN0 : 0<N := by linarith
  have hP : 1≤M*N := by nlinarith
  have hP0 : 0<M*N := by positivity
  have hNM := improved_threshold_ge_column α N M hα hN hthreshold
  have hNP : N≤M*N := by nlinarith
  have hK := (selectedPoisson_bounds c M N η hc hM hN hupper hη.le).2.1
  have hKP := (selectedPoisson_upper c c M N η hc le_rfl hM hN hη.le hη1).2.2
  have hprod : selectedPoissonK c M N η*N≤c*(M*N)^4 := by
    calc
      _ ≤ (c*(M*N)^3)*(M*N) := by gcongr
      _ = _ := by ring
  have hsmall : (selectedPoissonK c M N η*N)^η≤c^η*(M*N)^(4*η) := by
    calc
      _ ≤ (c*(M*N)^4)^η := Real.rpow_le_rpow (by positivity) hprod hη.le
      _ = _ := by
        rw [Real.mul_rpow hc0.le (by positivity)]
        congr 1
        rw [←Real.rpow_natCast,←Real.rpow_mul hP0.le]
        norm_num
  have hmain : (selectedPoissonK c M N η)^α≤c^α*(M*N)^(2*η)*M := by
    apply (improved_threshold_low α c η N M (by linarith) hc0 hN0 hM0 hthreshold).trans
    have hp : (M*N)^(η*α)≤(M*N)^(2*η) := Real.rpow_le_rpow_of_exponent_le hP (by nlinarith)
    exact mul_le_mul (mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hc0.le _))
      hNM hN0.le (by positivity)
  have hR : 1≤(M*N)^(2*η) := Real.one_le_rpow hP (by positivity)
  have hsum : N+(selectedPoissonK c M N η)^α≤(1+c^α)*(M*N)^(2*η)*M := by
    calc
      _ ≤ M+c^α*(M*N)^(2*η)*M := add_le_add hNM hmain
      _ ≤ (M*N)^(2*η)*M+c^α*(M*N)^(2*η)*M := by
        exact add_le_add (le_mul_of_one_le_left hM0.le hR) le_rfl
      _ = _ := by ring
  have hpowers : (M*N)^(4*η)*(M*N)^(2*η)=(M*N)^(6*η) := by
    rw [←Real.rpow_add hP0]
    congr 1
    ring
  calc
    _ ≤ C*(selectedPoissonK c M N η*N)^η*(N+(selectedPoissonK c M N η)^α) := hrev _ _ hK hN
    _ ≤ C*(c^η*(M*N)^(4*η))*((1+c^α)*(M*N)^(2*η)*M) := by gcongr
    _ = C*c^η*(1+c^α)*((M*N)^(4*η)*(M*N)^(2*η))*M := by ring
    _ = _ := by rw [hpowers]

end CanonicalQuadraticSieve

open scoped BigOperators Classical
namespace SecondPassArithmetic

theorem globalCutoffRatio_le (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M≤U^8 := by
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hden : 1≤B^2*F^2 := by nlinarith [sq_nonneg (B-1),sq_nonneg (F-1)]
  have he : H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M =
      (H*K*ell^2*(Real.exp M)^4)/(B^2*F^2) := by
    unfold globalRowScaleFloor
    field_simp

  rw [he]
  calc
    _ ≤ H*K*ell^2*(Real.exp M)^4 := div_le_self (by positivity) hden
    _ ≤ U*U*U^2*U^4 := by gcongr
    _ = U^8 := by ring

theorem globalNormCaps_polynomial (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ∀i, 0<globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i ∧
      globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H i≤27*U^22 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hF0 : 0<F := by linarith
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hratio := globalCutoffRatio_le K ell B F M H U hU hK hell hB hF hH hKU hellU hHU heU
  have hY := globalRowScaleFloor_pos K ell B F M hK hell hB0 hF0
  have hratio0 : 0≤H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M := by positivity
  have hceil : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤U^8+2 := by
    have hh := Nat.ceil_lt_add_one hratio0
    linarith
  have hpow8 : 1≤U^8 := one_le_pow₀ hU
  have hceil' : (⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1≤3*U^8 := by linarith
  have hrow : 3*(ell*Real.exp M)^2*B^2*
      ((⌈H*(ell*Real.exp M)^2/globalRowScaleFloor K ell B F M⌉₊:ℝ)+1)^2≤27*U^22 := by
    calc
      _ ≤ 3*(U^2)^2*U^2*(3*U^8)^2 := by gcongr
      _ = 27*U^22 := by ring
  have hpow2 : U^2≤27*U^22 := by
    calc
      U^2 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hpow4 : U^4≤27*U^22 := by
    calc
      U^4 ≤ U^22 := pow_le_pow_right₀ hU (by omega)
      _ ≤ 27*U^22 := by nlinarith [pow_nonneg hU0.le 22]
  have hB2 : B^2≤27*U^22 := (pow_le_pow_left₀ hB0.le hBU 2).trans hpow2
  have hLB : (ell*Real.exp M)*B^2≤27*U^22 := by
    calc
      _ ≤ U^2*U^2 := by gcongr
      _ = U^4 := by ring
      _ ≤ _ := hpow4
  intro i
  fin_cases i <;> dsimp [globalNormCaps]
  all_goals constructor
  all_goals first | positivity | exact hL.trans hpow2 | exact hB2 | exact hLB | exact hrow

theorem normLogBin_le_log_upper (x Y : ℝ) (hx : 0<x) (hxy : x≤Y) (hY : 1≤Y) :
    (normLogBin x:ℝ)≤Real.log Y := by
  have hh : (normLogBin x:ℝ)≤normLogBin Y := by exact_mod_cast normLogBin_mono hx hxy
  exact hh.trans (Nat.floor_le (Real.log_nonneg hY))

theorem globalLogBox_card_le_log (caps : Fin 10 → ℝ) (Y : ℝ) (hY : 1≤Y)
    (hcaps : ∀i,0<caps i ∧ caps i≤Y) :
    ((globalLogBox caps).card:ℝ)≤(1+Real.log Y)^10 := by
  calc
    ((globalLogBox caps).card:ℝ) = ∏i : Fin 10,((normLogBin (caps i):ℝ)+1) := by
      rw [globalLogBox_card]
      push_cast
      rfl
    _ ≤ ∏_i : Fin 10,(1+Real.log Y) := by
      apply Finset.prod_le_prod₀ (by intro i _; positivity)
      intro i _
      linarith [normLogBin_le_log_upper (caps i) Y (hcaps i).1 (hcaps i).2 hY]
    _ = (1+Real.log Y)^10 := by simp

theorem globalLogBox_card_polynomial_log (K ell B F M H U : ℝ)
    (hU : 1≤U) (hK : 0<K) (hell : 0<ell) (hB : 1≤B) (hF : 1≤F) (hH : 0≤H)
    (hKU : K≤U) (hellU : ell≤U) (hBU : B≤U) (hHU : H≤U) (heU : Real.exp M≤U) :
    ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤
      (1+Real.log 27+22*Real.log U)^10 := by
  have hU0 : 0<U := by linarith
  have hY : 1≤27*U^22 := by nlinarith [one_le_pow₀ hU (n:=22)]
  have hh := globalLogBox_card_le_log _ (27*U^22) hY
    (globalNormCaps_polynomial K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU)
  have he : 1+Real.log (27*U^22)=1+Real.log 27+22*Real.log U := by
    rw [Real.log_mul (by norm_num : (27:ℝ)≠0) (pow_ne_zero 22 hU0.ne'),Real.log_pow]
    norm_num
    ring
  rwa [he] at hh

theorem globalLogRep_le_upper (caps : Fin 10 → ℝ) (j : GlobalLogIndex)
    (hj : j∈globalLogBox caps) (i : Fin 10) (Y : ℝ)
    (hc : 0<caps i) (hcap : caps i≤Y) (hY : 1≤Y) : globalLogRep j i≤Y := by
  have hji : j i≤normLogBin (caps i) := by
    have hh := Fintype.mem_piFinset.mp hj i
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hh)
  have hjY := hji.trans (normLogBin_mono hc hcap)
  have hr : globalLogRep j i≤normLogScale (normLogBin Y) := by
    unfold globalLogRep normLogScale
    apply Real.exp_le_exp.mpr
    exact_mod_cast hjY
  exact hr.trans (normLogBin_scale_bounds Y hY).1

theorem globalBinLossScale_cancel (B : ℝ) (j : GlobalLogIndex) :
    globalBinLossScale B j = Real.exp 5*globalLogRep j 1*globalLogRep j 6*
      globalLogRep j 7*B*Real.sqrt (globalLogRep j 9) := by
  have hj := (globalLogRep_pos j 4).ne'
  have he : Real.exp 5=Real.exp 4*Real.exp 1 := by rw [←Real.exp_add]; norm_num
  rw [he]
  unfold globalBinLossScale globalPooledLabelScale
  field_simp

theorem globalBinLossScale_polynomial (ell B Y M H U : ℝ)
    (hU : 1≤U) (hell : 0<ell) (hB : 1≤B)
    (hellU : ell≤U) (hBU : B≤U) (heU : Real.exp M≤U)
    (j : GlobalLogIndex) (hj : j∈globalLogBox (globalNormCaps ell B Y M H)) :
    globalBinLossScale B j≤Real.exp 5*U^8 := by
  have hU0 : 0<U := by linarith
  have hB0 : 0<B := by linarith
  have hL0 : 0<ell*Real.exp M := by positivity
  have hL : ell*Real.exp M≤U^2 := by
    calc
      _ ≤ U*U := mul_le_mul hellU heU (Real.exp_pos M).le hU0.le
      _ = _ := by ring
  have hpow2 : 1≤U^2 := one_le_pow₀ hU
  have h1 : globalLogRep j 1≤U^2 := globalLogRep_le_upper _ j hj 1 (U^2) hL0 hL hpow2
  have h6 : globalLogRep j 6≤U^2 := globalLogRep_le_upper _ j hj 6 (U^2) hL0 hL hpow2
  have h7 : globalLogRep j 7≤U^2 := globalLogRep_le_upper _ j hj 7 (U^2) hL0 hL hpow2
  have h9 : globalLogRep j 9≤U^2 := globalLogRep_le_upper _ j hj 9 (U^2) (by simp [globalNormCaps]; positivity)
    (by simpa [globalNormCaps] using pow_le_pow_left₀ hB0.le hBU 2) hpow2
  have hsqrt : Real.sqrt (globalLogRep j 9)≤U := Real.sqrt_le_iff.mpr ⟨hU0.le,h9⟩
  rw [globalBinLossScale_cancel]
  calc
    _ ≤ Real.exp 5*U^2*U^2*U^2*U*U := by
      gcongr
      all_goals exact (globalLogRep_pos j _).le
    _ = Real.exp 5*U^8 := by ring

end SecondPassArithmetic

namespace CanonicalQuadraticSieve

theorem sieveNorm_small_columns (M N : ℝ) (hM : 1≤M) (hN : 1≤N) (hN28 : N≤28) :
    sieveNorm M N≤785*QuadraticInitialBound.initialSieveConstant*M := by
  have hceil : (⌈N⌉₊:ℝ)≤28 := by
    exact_mod_cast (Nat.ceil_le.mpr hN28 : ⌈N⌉₊≤28)
  have hs : (⌈N⌉₊:ℝ)^2≤784 := by
    nlinarith [Nat.cast_nonneg (α:=ℝ) ⌈N⌉₊]
  have hc := QuadraticInitialBound.initialSieveConstant_pos
  have hb := sieveNorm_initial M N hM hN
  have ht : M+(⌈N⌉₊:ℝ)^2≤785*M := by linarith
  calc
    _ ≤ QuadraticInitialBound.initialSieveConstant*(M+(⌈N⌉₊:ℝ)^2) := hb
    _ ≤ QuadraticInitialBound.initialSieveConstant*(785*M) := mul_le_mul_of_nonneg_left ht hc.le
    _ = _ := by ring

theorem HasSieveExponent.shell_threshold {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) :
    ∀ρ : ℝ, 0<ρ → ∃C : ℝ, 0<C ∧ ∀M N : ℝ,
      1≤M → 1≤N → N^(2-1/α)≤M →
      ∀a : idealRange N → ℂ, CoefficientOnShell N N a →
      ballQuadraticEnergy M N a≤C*(M*N)^ρ*M*∑J,‖a J‖^2 := by
  intro ρ hρ
  let η := min 1 (ρ/600)
  have hη : 0<η := lt_min (by norm_num) (by positivity)
  have hη1 : η≤1 := min_le_left _ _
  have hηρ : η≤ρ/600 := min_le_right _ _
  have h6 : 6*η≤ρ := by linarith only [hηρ,hη]
  have h260 : 260*η≤ρ := by linarith only [hηρ,hη]
  obtain ⟨l,hl⟩ := exists_nat_gt (4/η)
  have horder : 4≤η*l := by
    have hh := (div_lt_iff₀ hη).mp hl
    nlinarith only [hh]
  obtain ⟨CH,hCH,hhigh⟩ := hexp.ball_selected_high hα1 hα2 η hη hη1 l l horder horder
  obtain ⟨CL,hCL,hlow⟩ := hexp.low_threshold hα1 hα2 η hη hη1 fixedCutoffBase fixedCutoffBase_bounds.1
  let I := QuadraticInitialBound.initialSieveConstant
  have hI : 0<I := QuadraticInitialBound.initialSieveConstant_pos
  let C := 790*I+CL+CH
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro M N hM hN hthreshold a ha
  have hP : 1≤M*N := by nlinarith only [hM,hN]
  have hPρ : 1≤(M*N)^ρ := Real.one_le_rpow hP hρ.le
  have hE : 0≤∑J,‖a J‖^2 := by positivity
  have hM0 : 0≤M := le_trans zero_le_one hM
  have hscale {x y : ℝ} (hxy : x≤y) :
      x*M*∑J,‖a J‖^2 ≤ y*M*∑J,‖a J‖^2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxy hM0) hE
  have hmatrix : ballQuadraticEnergy M N a≤sieveNorm M N*∑J,‖a J‖^2 :=
    FiniteSieveOperator.energy_bound (matrix M N) a
  by_cases hlarge : N^2≤M
  · have hb := sieveNorm_large_rows M N hM hN hlarge
    calc
      _ ≤ (5*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (5*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 5*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  by_cases hsmall : N≤28
  · have hb := sieveNorm_small_columns M N hM hN hsmall
    calc
      _ ≤ (785*I*M)*∑J,‖a J‖^2 := hmatrix.trans (mul_le_mul_of_nonneg_right hb hE)
      _ = (785*I)*1*M*∑J,‖a J‖^2 := by ring
      _ ≤ _ := hscale (mul_le_mul
        (show 785*I≤C by dsimp [C]; linarith only [hI,hCL,hCH])
        hPρ zero_le_one hC.le)
  have hupper : M≤N^2 := le_of_not_ge hlarge
  have hK := (selectedPoisson_bounds fixedCutoffBase M N η fixedCutoffBase_bounds.1 hM hN hupper hη.le).2.1
  have hb := hhigh M N hM (by linarith only [hsmall]) hthreshold hK a ha
  have hlb := hlow M N hM hN hthreshold hupper
  have hp6 : (M*N)^(6*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h6
  have hp260 : (M*N)^(260*η)≤(M*N)^ρ := Real.rpow_le_rpow_of_exponent_le hP h260
  calc
    _ ≤ (sieveNorm (selectedPoissonK fixedCutoffBase M N η) N+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 := hb
    _ ≤ (CL*(M*N)^(6*η)*M+CH*(M*N)^(260*η)*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add hlb le_rfl) hE
    _ ≤ (CL*(M*N)^ρ*M+CH*(M*N)^ρ*M)*∑J,‖a J‖^2 :=
      mul_le_mul_of_nonneg_right (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp6 hCL.le) hM0)
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp260 hCH.le) hM0)) hE
    _ = (CL+CH)*(M*N)^ρ*M*∑J,‖a J‖^2 := by ring
    _ ≤ _ := hscale (mul_le_mul_of_nonneg_right
      (show CL+CH≤C by dsimp [C]; linarith only [hI])
      (Real.rpow_nonneg (by positivity) _))

theorem HasSieveExponent.improve {α : ℝ} (hexp : HasSieveExponent α)
    (hα1 : 1≤α) (hα2 : α≤2) : HasSieveExponent (2-1/α) := by
  have hα : 0<α := by linarith
  have hfrac : 1/α≤1 := (div_le_one hα).mpr hα1
  have hpos : 0≤1/α := by positivity
  apply hasSieveExponent_of_shell_threshold (2-1/α) (by linarith) (by linarith)
  exact hexp.shell_threshold hα1 hα2

open ActualEisensteinCubic CompletedGauss

theorem hasSieveExponent_one : HasSieveExponent 1 :=
  hasSieveExponent_one_of_improvement (fun _α hα hα2 h => h.improve hα.le hα2)

theorem sieveNorm_sharp :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧ ∀ M N : ℝ, 1≤M → 1≤N →
      sieveNorm M N≤C*(M*N)^ε*(M+N) := by
  simpa only [HasSieveExponent,Real.rpow_one] using hasSieveExponent_one

theorem finite_family_quadratic_large_sieve :
    ∀ ε : ℝ, 0<ε → ∃ C : ℝ, 0<C ∧
    ∀ (M N : ℝ), 1≤M → 1≤N →
    ∀ {m n : Type*} [Fintype m] [Fintype n],
    ∀ (rows : m → Ideal O) (cols : n → Ideal O),
      Function.Injective rows → Function.Injective cols →
      (∀ i, Admissible (rows i) ∧ (Ideal.absNorm (rows i):ℝ)≤M) →
      (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
    ∀ a : n → ℂ,
      (∑ i, ‖∑ j, quadraticRow (cols j) (primaryGenerator (rows i))*a j‖^2) ≤
        C*(M*N)^ε*(M+N)*∑j,‖a j‖^2 := by
  intro ε hε
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp ε hε
  refine ⟨C,hC,?_⟩
  intro M N hM hN m n _ _ rows cols hr hc hrows hcols a
  classical
  have he := FiniteSieveOperator.energy_bound
    (fun i j => quadraticRow (cols j) (primaryGenerator (rows i))) a
  have hn := family_squared_norm_le rows cols hr hc M N hrows hcols
  have hE : 0≤∑j,‖a j‖^2 := by positivity
  exact he.trans ((mul_le_mul_of_nonneg_right hn hE).trans
    (mul_le_mul_of_nonneg_right (hsharp M N hM hN) hE))

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

theorem globalLogFactor_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ U : ℝ, 1≤U →
      (1+Real.log 27+22*Real.log U)^10≤C*U^ε := by
  let deltaLoss := ε/10
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  let C0 := 1+Real.log 27+22/deltaLoss
  have hlog : 0≤Real.log 27 := Real.log_nonneg (by norm_num)
  have hC0 : 0<C0 := by dsimp [C0]; positivity
  refine ⟨C0^10,by positivity,?_⟩
  intro U hU
  have hU0 : 0<U := by linarith
  have hR : 1≤U^deltaLoss := Real.one_le_rpow hU hδ.le
  have hb : Real.log U≤U^deltaLoss/deltaLoss := Real.log_le_rpow_div hU0.le hδ
  have hs : 1+Real.log 27+22*Real.log U≤C0*U^deltaLoss := by
    calc
      _ ≤ (1+Real.log 27)*U^deltaLoss+22*(U^deltaLoss/deltaLoss) := add_le_add
        (le_mul_of_one_le_right (by linarith) hR)
        (mul_le_mul_of_nonneg_left hb (by norm_num))
      _ = C0*U^deltaLoss := by dsimp [C0]; ring
  have hs0 : 0≤1+Real.log 27+22*Real.log U := by
    have hu := Real.log_nonneg hU
    positivity
  calc
    _ ≤ (C0*U^deltaLoss)^10 := pow_le_pow_left₀ hs0 hs 10
    _ = C0^10*U^ε := by
      rw [mul_pow]
      congr 1
      rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
      dsimp [deltaLoss]
      congr 1
      ring

theorem globalLogBox_card_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      ((globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).card:ℝ)≤C*U^ε := by
  obtain ⟨C,hC,hbound⟩ := globalLogFactor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  exact (globalLogBox_card_polynomial_log K ell B F M H U hU hK hell hB hF hH
    hKU hellU hBU hHU heU).trans (hbound U hU)

theorem globalLogBox_total_loss (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U : ℝ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U →
      (∑j∈globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H),
        (globalBinLossScale B j)^η)≤C*U^(ε+8*η) := by
  obtain ⟨C,hC,hcard⟩ := globalLogBox_card_small_power ε hε
  refine ⟨C*(Real.exp 5)^η,by positivity,?_⟩
  intro K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU
  have hU0 : 0<U := by linarith
  let S := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  have hbound (j : GlobalLogIndex) (hj : j∈S) :
      (globalBinLossScale B j)^η≤(Real.exp 5)^η*U^(8*η) := by
    have hb := globalBinLossScale_polynomial ell B (globalRowScaleFloor K ell B F M) M H U
      hU hell hB hellU hBU heU j hj
    have hnonneg : 0≤globalBinLossScale B j := by
      rw [globalBinLossScale_cancel]
      have h1 := (globalLogRep_pos j 1).le
      have h6 := (globalLogRep_pos j 6).le
      have h7 := (globalLogRep_pos j 7).le
      positivity
    apply (Real.rpow_le_rpow hnonneg hb hη).trans_eq
    rw [Real.mul_rpow (Real.exp_pos _).le (by positivity)]
    congr 1
    rw [←Real.rpow_natCast,←Real.rpow_mul hU0.le]
    norm_num
  calc
    _ ≤ ∑_j∈S,((Real.exp 5)^η*U^(8*η)) := Finset.sum_le_sum hbound
    _ = (S.card:ℝ)*((Real.exp 5)^η*U^(8*η)) := by simp
    _ ≤ (C*U^ε)*((Real.exp 5)^η*U^(8*η)) :=
      mul_le_mul_of_nonneg_right (hcard K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) (by positivity)
    _ = (C*(Real.exp 5)^η)*U^(ε+8*η) := by rw [Real.rpow_add hU0]; ring

theorem globalBinLossScale_nonneg (B : ℝ) (hB : 0≤B) (j : GlobalLogIndex) :
    0≤globalBinLossScale B j := by
  rw [globalBinLossScale_cancel]
  have h1 := (globalLogRep_pos j 1).le
  have h6 := (globalLogRep_pos j 6).le
  have h7 := (globalLogRep_pos j 7).le
  positivity

theorem globalLogBox_radial_decay (ε : ℝ) (hε : 0<ε) (η : ℝ) (hη : 0≤η) :
    ∃ C : ℝ,0<C ∧ ∀ K ell B F M H U Z θ : ℝ, ∀ N : ℕ,
      1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      (∑j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        (globalBinLossScale B j)^η/
          (1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) ≤
        C*U^(ε+8*η)/Z^(θ*N) := by
  obtain ⟨C,hC,hall⟩ := globalLogBox_total_loss ε hε η hη
  refine ⟨C,hC,?_⟩
  intro K ell B F M H U Z θ N hU hK hell hB hF hH hKU hellU hBU hHU heU hZ
  let box := globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)
  let radial := fun j => globalBinRadial ell (globalPooledRowScale K ell B F j) j
  have hbase : 0<Z^θ := Real.rpow_pos_of_pos hZ _
  have hden : 0<Z^(θ*N) := Real.rpow_pos_of_pos hZ _
  have hnum (j : GlobalLogIndex) : 0≤(globalBinLossScale B j)^η :=
    Real.rpow_nonneg (globalBinLossScale_nonneg B (by linarith) j) _
  have hp (j : GlobalLogIndex) (hj : Z^θ≤radial j) :
      Z^(θ*N)≤(1+radial j)^N := by
    rw [Real.rpow_mul hZ.le,Real.rpow_natCast]
    exact pow_le_pow_left₀ hbase.le (by linarith) N
  calc
    _ ≤ ∑j∈box.filter (fun j => Z^θ≤radial j), (globalBinLossScale B j)^η/Z^(θ*N) := by
      apply Finset.sum_le_sum
      intro j hj
      exact div_le_div_of_nonneg_left (hnum j) hden (hp j (Finset.mem_filter.mp hj).2)
    _ = (∑j∈box.filter (fun j => Z^θ≤radial j),(globalBinLossScale B j)^η)/Z^(θ*N) :=
      (Finset.sum_div _ _ _).symm
    _ ≤ (∑j∈box,(globalBinLossScale B j)^η)/Z^(θ*N) := by
      apply div_le_div_of_nonneg_right _ hden.le
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j _ _ => hnum j)
    _ ≤ C*U^(ε+8*η)/Z^(θ*N) := div_le_div_of_nonneg_right
      (hall K ell B F M H U hU hK hell hB hF hH hKU hellU hBU hHU heU) hden.le

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0187

/-! Original module: OAI.NumberTheory.DirichletL.MeanSquare.TransformedColumns
Source SHA256: 5db804f219387b4af4730d4d24cf20d85ffaf40ac90cdfd725e5dbcb7410c84f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0188



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

open scoped BigOperators Classical
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open MixedCrossSeparation (columnCoefficient)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

def inputColumn (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  Ψ (∏i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*H S

def transformedColumn (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) : ℂ :=
  columnCoefficient p hp hcop hg S*Ψ (∏i∈S,p i)*
    rowCoprimeMask (fun i => Ideal.span {p i}) S (b*d)*
    star (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d)*
    finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S h*H S

omit [DecidableEq ι] in
lemma inputColumn_eq (Ψ : O→*ℂ) (b d : O) (H : Finset ι→ℂ) (S : Finset ι) :
    inputColumn p Ψ b d H S=secondInputCoefficient p hg Ψ (b*d) 1 1 H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [inputColumn,secondInputCoefficient,hr,one_pow,mul_one]

lemma transformedColumn_eq (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) (S : Finset ι) :
    transformedColumn p hp hcop hg Ψ b d h H S=
      secondPreColumn p hp hcop hg Ψ (b*d) 1 1 d h H S := by
  have hr : finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S 1=1 := by simp [finiteSquarefreeRow]
  simp only [transformedColumn,secondPreColumn,hr,one_pow,mul_one]

theorem transformedColumn_union (hpr : ∀i,lambda^2∣p i-1)
    (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ)
    (V N : Finset ι) (hVN : Disjoint V N) :
    transformedColumn p hp hcop hg Ψ b d h H (V∪N)=
      transformedColumn p hp hcop hg Ψ b d h (fun _ => 1) V *
      secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
        (fun U => H (V∪U)) N := by
  simp_rw [transformedColumn_eq p hp hcop hg]
  simpa only [mul_one,one_mul] using secondPreColumn_union p hp hcop hg hpr
    Ψ b 1 1 1 d h H V N hVN

def initialPair (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) : ℂ :=
  ∑S∈F.powerset,∑T∈F.powerset,if Disjoint S T then
    star (supportMobius (fun i => Ideal.span {p i}) S*inputColumn p Ψ₁ b d H₁ S)*
      (supportMobius (fun i => Ideal.span {p i}) T*inputColumn p Ψ₂ b d H₂ T)*
      activeGaussRowFactor p hp hinj hg T S d h else 0

lemma initialPair_eq (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      secondActualPair p hp hg hinj F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂ := by
  simp only [initialPair,secondActualPair,inputColumn_eq p hg,mul_one]

def childSum (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) : ℂ :=
  ∑N∈F.powerset,secondChildColumn p hp hcop hg Ψ b (d*∏i∈V,p i) (d*h)
    (fun U => H (V∪U)) N

lemma childSum_eq (F V : Finset ι) (Ψ : O→*ℂ) (b d h : O) (H : Finset ι→ℂ) :
    childSum p hp hcop hg F V Ψ b d h H=
      secondChildSum p hp hcop hg F V Ψ b 1 1 1 d h H := by
  rw [secondChildSum_fixed_pool]
  simp only [childSum,mul_one,one_mul]

theorem initialPair_eq_children (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (hpr : ∀i,lambda^2∣p i-1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ) (b d h : O) (H₁ H₂ : Finset ι→ℂ) :
    initialPair p hp hg hinj F Ψ₁ Ψ₂ b d h H₁ H₂=
      ∑z : SecondRayIndex,∑V∈F.powerset,
        secondTotalWeight p hp hcop hg Ψ₁ Ψ₂ b 1 1 1 d h (z,V)*
        star (childSum p hp hcop hg F V (secondRayMinus Ψ₁ z) b d h H₁)*
        childSum p hp hcop hg F V (secondRayPlus Ψ₂ z) b d (-h) H₂ := by
  simp_rw [initialPair_eq p hp hg,childSum_eq p hp hcop hg]
  exact secondActualPair_eq_children p hp hcop hg hinj hc hpr F Ψ₁ Ψ₂ b 1 1 1 d h H₁ H₂

end InitialMeanSquare

namespace CubicEisenstein

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Pointwise ENNReal

instance fullSLContinuousAction : ContinuousConstSMul (SL(2,ℂ)) HyperbolicSpace :=
  ⟨continuous_hyperbolic_action⟩

instance hyperbolicVolume_fullSupport : Measure.IsOpenPosMeasure hyperbolicVolume where
  open_pos U hU hne := by
    obtain ⟨u,hu⟩ := hne
    have hcover : (Set.univ : Set HyperbolicSpace) ⊆ ⋃g:SL(2,ℂ),g • U := by
      intro w hw
      obtain ⟨g,hg⟩ := MulAction.exists_smul_eq (SL(2,ℂ)) u w
      exact Set.mem_iUnion.mpr ⟨g,u,hu,hg⟩
    obtain ⟨seq,hseq⟩ := isLindelof_univ.indexed_countable_subcover
      (fun g : SL(2,ℂ) => g • U) (fun g => isOpenMap_smul g U hU) hcover
    intro hzero
    have hz : hyperbolicVolume (⋃n:ℕ,seq n • U)=0 := by
      apply measure_iUnion_null
      intro n
      rw [measure_smul,hzero]
    have htotal : hyperbolicVolume Set.univ=0 := measure_mono_null hseq hz
    exact hyperbolicVolume_ne_zero (Measure.measure_univ_eq_zero.mp htotal)

instance kernelQuotientVolume_fullSupport :
    Measure.IsOpenPosMeasure (integralQuotientVolume globalKubotaKernel) where
  open_pos U hU hne := by
    let quotientProjection := integralOrbitProjection globalKubotaKernel
    have hp : Measurable quotientProjection := measurable_integralOrbitProjection _
    have hpre : IsOpen (quotientProjection ⁻¹' U) := hU.preimage (continuous_integralOrbitProjection _)
    have hpren : (quotientProjection ⁻¹' U).Nonempty := by
      obtain ⟨q,hq⟩ := hne
      obtain ⟨w,rfl⟩ := Quotient.mk_surjective q
      exact ⟨w,hq⟩
    intro hzero
    have hd : hyperbolicVolume ((quotientProjection ⁻¹' U)∩hyperbolicFundamentalSet globalKubotaKernel)=0 := by
      simpa only [integralQuotientVolume,quotientProjection,Measure.map_apply (measurable_integralOrbitProjection _) hU.measurableSet,
        Measure.restrict_apply ((measurable_integralOrbitProjection _) hU.measurableSet)] using hzero
    have hinv : ∀M:globalKubotaKernel,M • (quotientProjection ⁻¹' U)=quotientProjection ⁻¹' U := by
      intro M
      ext w
      constructor
      · rintro ⟨u,hu,rfl⟩
        change quotientProjection (M • u)∈U
        change quotientProjection u∈U at hu
        rwa [show quotientProjection (M • u)=quotientProjection u from integralOrbitProjection_eq _ M u]
      · intro hw
        refine ⟨M⁻¹ • w,?_,smul_inv_smul M w⟩
        change quotientProjection (M⁻¹ • w)∈U
        rwa [show quotientProjection (M⁻¹ • w)=quotientProjection w from integralOrbitProjection_eq _ M⁻¹ w]
    have hz := globalKubotaKernel_isFundamentalDomain.measure_zero_of_invariant (quotientProjection ⁻¹' U) hinv hd
    exact hpre.measure_ne_zero _ hpren hz

lemma kernel_continuous_eq_of_ae_eq (f g : IntegralOrbitQuotient globalKubotaKernel → ℂ)
    (hf : Continuous f) (hg : Continuous g)
    (he : f =ᵐ[integralQuotientVolume globalKubotaKernel] g) : f=g :=
  (MeasureTheory.Measure.eq_of_ae_eq he hf hg)

end

open Filter MeasureTheory
open scoped BigOperators Classical Topology MatrixGroups Matrix Pointwise ENNReal

open ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O

lemma integral_upper_triangular_height (M : SL(2,O)) (hc : M 1 0=0)
    (z : ℂ) (v : ℝ) (hv : 0<v) :
    hyperbolicHeight (integralComplexMatrix M • upperPoint z v hv)=v := by
  have hdet : M 0 0*M 1 1=1 := by
    have h := M.property
    simpa only [Matrix.det_fin_two,hc,mul_zero,sub_zero] using h
  let u : Oˣ := ⟨M 1 1,M 0 0,by rw [mul_comm,hdet],hdet⟩
  have hn : ‖eisEmbedding (M 1 1)‖=1 := GaussGeneratorTransport.norm_eisEmbedding_unit u
  rw [hyperbolicHeight_action_upperPoint]
  simp only [integralComplexMatrix_apply,hc,map_zero,zero_mul,zero_add,norm_zero,
    hn,one_pow,]
  norm_num

lemma smoothCuspSeedDefect_high_zero (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ)
    (M : SL(2,O)) (z : ℂ) (v : ℝ) (hv : 0<v) (hvlarge : max b a⁻¹<v) :
    smoothCuspSeedDefect a b s (integralComplexMatrix M • upperPoint z v hv)=0 := by
  unfold smoothCuspSeedDefect cuspCutoffCorrection
  have hz : (fun r : CuspCosets => cuspCutoffTerm 1 (cuspSeedDefectProfile a b s) r
      (integralComplexMatrix M • upperPoint z v hv))=(fun _ => (0:ℂ)) := by
    funext r
    have hout : cosetHeight r (integralComplexMatrix M • upperPoint z v hv)<a ∨
        b<cosetHeight r (integralComplexMatrix M • upperPoint z v hv) := by
      induction r using Quotient.inductionOn with
      | _ N =>
        change cosetHeight (cosetOf N) _<a ∨ b<cosetHeight (cosetOf N) _
        rw [cosetHeight_cosetOf]
        change hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
          (integralComplexMatrix M • upperPoint z v hv))<a ∨
          b<hyperbolicHeight (integralComplexMatrix (N:SL(2,O)) •
            (integralComplexMatrix M • upperPoint z v hv))
        simp only [←mul_smul,←map_mul]
        by_cases hc : ((N:SL(2,O))*M) 1 0=0
        · right
          rw [integral_upper_triangular_height _ hc]
          exact (le_max_left _ _).trans_lt hvlarge
        · left
          have hh := integral_hyperbolicHeight_mul_le_one ((N:SL(2,O))*M) hc (upperPoint z v hv)
          rw [hyperbolicHeight_upperPoint] at hh
          have hav : 1<a*v := by
            have hlt : a⁻¹<v := (le_max_right _ _).trans_lt hvlarge
            have hm := mul_lt_mul_of_pos_left hlt ha
            simpa only [mul_inv_cancel₀ ha.ne'] using hm
          nlinarith
    simp [cuspCutoffTerm,cuspSeedDefectProfile_zero a b s _ hab hout]
  rw [hz,tsum_zero]

theorem kernelQuotientDefect_hasCompactSupport (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    HasCompactSupport (kernelQuotientDefect a b s) := by
  obtain ⟨S,hS⟩ := globalKubotaKernel_compact_core_cusp_cover
  obtain ⟨hcompact,hcover⟩ := hS (max b a⁻¹)
  apply HasCompactSupport.of_support_subset_isCompact hcompact
  intro q hq
  have hmem : q∈compactFordCore globalKubotaKernel S (max b a⁻¹) ∪
      ⋃r∈S,fordCuspTail globalKubotaKernel r (max b a⁻¹) := by rw [←hcover]; trivial
  rcases hmem with hcore | htail
  · exact hcore
  · exfalso
    obtain ⟨r,hr⟩ := Set.mem_iUnion.mp htail
    obtain ⟨hrS,htail⟩ := Set.mem_iUnion.mp hr
    obtain ⟨p,hp,rfl⟩ := htail
    exact hq (smoothCuspSeedDefect_high_zero a b ha hab s r⁻¹ p.1.1 p.1.2 p.2 hp.2.2)

def hyperbolicSpatialCoordinates (w : HyperbolicSpace) : SpatialCoordinates :=
  ![(hyperbolicHorizontal w).re,(hyperbolicHorizontal w).im,hyperbolicHeight w]

lemma hyperbolicSpatialCoordinates_continuous : Continuous hyperbolicSpatialCoordinates := by
  apply continuous_pi
  intro j
  fin_cases j
  · exact Complex.continuous_re.comp hyperbolicHorizontal_continuous
  · exact Complex.continuous_im.comp hyperbolicHorizontal_continuous
  · exact hyperbolicHeight_continuous

lemma hyperbolicSpatialCoordinates_positive (w : HyperbolicSpace) :
    0<hyperbolicSpatialCoordinates w 2 := hyperbolicHeight_pos w

lemma hyperbolicSpatialCoordinates_reconstruct (w : HyperbolicSpace) :
    upperPoint ((hyperbolicSpatialCoordinates w 0:ℂ)+(hyperbolicSpatialCoordinates w 1:ℂ)*Complex.I)
      (hyperbolicSpatialCoordinates w 2) (hyperbolicSpatialCoordinates_positive w)=w := by
  change upperPoint (((hyperbolicHorizontal w).re:ℂ)+((hyperbolicHorizontal w).im:ℂ)*Complex.I)
    (hyperbolicHeight w) (hyperbolicHeight_pos w)=w
  rw [Complex.re_add_im]
  exact upperCoordinates_right_inverse w

lemma smoothCuspSeedDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (smoothCuspSeedDefect a b s) := by
  have heq : smoothCuspSeedDefect a b s=
      fun w => heightPoincareField (cuspSeedDefectProfile a b s) (hyperbolicSpatialCoordinates w) := by
    funext w
    nth_rw 1 [←hyperbolicSpatialCoordinates_reconstruct w]
    exact smoothCuspSeedDefect_coordinate a b s ha hab _ (hyperbolicSpatialCoordinates_positive w)
  rw [heq,continuous_iff_continuousAt]
  intro w
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab _
    (hyperbolicSpatialCoordinates_positive w)).continuousAt.comp
      hyperbolicSpatialCoordinates_continuous.continuousAt

lemma kernelQuotientDefect_continuous (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b) :
    Continuous (kernelQuotientDefect a b s) :=
  (smoothCuspSeedDefect_continuous a b s ha hab).quotient_lift _

lemma actual_smoothCuspSeedDefect_contDiffAt (a b : ℝ) (s : ℂ) (ha : 1<a) (hab : a<b)
    (p : SpatialCoordinates) (hp : 0<p 2) :
    ContDiffAt ℝ (↑(⊤ : ℕ∞)) (smoothCuspSeedDefectField a b s) p := by
  have heq : smoothCuspSeedDefectField a b s =ᶠ[𝓝 p]
      heightPoincareField (cuspSeedDefectProfile a b s) := by
    filter_upwards [(continuous_apply 2).continuousAt.eventually_const_lt hp] with q hq
    exact smoothCuspSeedDefectField_eq a b s ha hab q hq
  exact (smoothCuspSeedDefect_contDiffAt a b s ha hab p hp).congr_of_eventuallyEq heq

end CubicEisenstein

namespace SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (firstLogDensity)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

theorem globalChildBudget_height (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
      ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*
        globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp only [globalChildBudget,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro q hq
  simp only [globalDescentWeight,norm_zero,add_zero,one_pow,mul_one]
  ring

theorem globalChildBudget_density (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε t K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side =
    firstLogDensity 0 t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  rw [globalChildBudget_height,← mul_assoc,FirstPassCubeLabels.firstLogDensity_pair_moment]

theorem globalChildBudget_integral (pool : Finset ι) (source : Finset (GlobalSecondData ι))
    (Ψ : O →* ℂ) (m : O) (windows : Fin 7 → ℝ → ℂ)
    (C ε K ell B F M H : ℝ) (A J : ℕ) (side : Bool) :
    (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε t t K ell B F M H A J side) =
    (∫ t : ℝ,firstLogDensity 0 t)*
      globalChildBudget p hp hcop hg pool source Ψ m windows C ε 0 0 K ell B F M H A J side := by
  simp_rw [globalChildBudget_density]
  exact integral_mul_const _ _

def globalFirstFiniteEnergy (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (t : ℝ) : ℝ :=
  ∑ b∈s,w b*∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2

theorem globalFirstFiniteEnergy_integrable (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (χ : RayFourExpansion.RayCharacter)
    (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    Integrable (fun t => firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t) := by
  simp only [globalFirstFiniteEnergy,Finset.mul_sum]
  apply integrable_finsetSum
  intro b hb
  apply integrable_finsetSum
  intro z hz
  have hi := firstCoreInputRow_integrable p hg (pool\(b.cube.support∪b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side χ Ψ m (FirstPassCubeLabels.normalizedColumn p
      (fun A => g (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b) A)))
    V (FirstPassCubeLabels.columnLog p (globalFirstBlockColumnScale p ell side b))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) r z
    (FirstPassCubeLabels.firstLogDensity_integrable J)
  simpa only [globalFirstCoreRow,mul_left_comm] using hi.const_mul (w b)

end SecondPassArithmetic

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve

open ActualEisensteinCubic

theorem finite_inverse_norm_sum (S : Finset (Ideal O)) (H : ℝ)
    (hS : ∀ I∈S,I≠0) (hH : ∀I∈S,(Ideal.absNorm I:ℝ)≤H) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤256*(columnDyadicLength H+1:ℝ) := by
  have hpos (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  have hbin (j : Fin (columnDyadicLength H+1)) :
      (∑I∈divisorDyadicBin S H j,1/(Ideal.absNorm I:ℝ))≤256 := by
    have hp : 0<(2:ℝ)^j.val := by positivity
    have hone : 1≤(2:ℝ)^j.val := one_le_pow₀ (by norm_num)
    have hcount : ((divisorDyadicBin S H j).card:ℝ)≤128*(2:ℝ)^j.val := by
      apply DescentFiberCost.finite_ideal_count_real _ _ hone
      · intro I hI
        exact hS I (Finset.mem_filter.mp hI).1
      · intro I hI
        obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
        have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).2
        simpa only [hj] using hb
    have hterm (I : Ideal O) (hI : I∈divisorDyadicBin S H j) :
        1/(Ideal.absNorm I:ℝ)≤2/(2:ℝ)^j.val := by
      obtain ⟨hIS,hj⟩ := Finset.mem_filter.mp hI
      have hb := (divisorDyadicLabel_bounds H I (hpos I hIS) (hH I hIS)).1
      rw [hj] at hb
      apply (div_le_div_iff₀ (by linarith [hpos I hIS]) hp).mpr
      linarith
    calc
      _ ≤ ∑_I∈divisorDyadicBin S H j,2/(2:ℝ)^j.val := Finset.sum_le_sum hterm
      _ = ((divisorDyadicBin S H j).card:ℝ)*(2/(2:ℝ)^j.val) := by simp
      _ ≤ (128*(2:ℝ)^j.val)*(2/(2:ℝ)^j.val) := by gcongr
      _ = _ := by field_simp; ring
  rw [sum_divisorDyadicBins S H]
  calc
    _ ≤ ∑j : Fin (columnDyadicLength H+1),(256:ℝ) := Finset.sum_le_sum (fun j _ => hbin j)
    _ = _ := by simp; ring

theorem ideal_reciprocal_cauchy (S : Finset (Ideal O)) (hS : ∀I∈S,I≠0)
    (v : Ideal O → ℂ) :
    ‖∑I∈S,v I‖^2≤(∑I∈S,1/(Ideal.absNorm I:ℝ))*
      (∑I∈S,(Ideal.absNorm I:ℝ)*‖v I‖^2) := by
  have hpos (I : Ideal O) (hI : I∈S) : 0<(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS I hI (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S v) 2).trans
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S
    (fun I hI => by positivity) (fun I hI => by positivity)
  intro I hI
  exact le_of_eq (by field_simp [(hpos I hI).ne'])

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

def columnSquareFiber (S : Finset (Ideal O)) (A : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => squarePart I=A)

theorem columnSquareFiber_injective (S : Finset (Ideal O)) (A : Ideal O) :
    Function.Injective (fun I : columnSquareFiber S A => squarefreePart I.val) := by
  intro I J he
  change squarefreePart I.val=squarefreePart J.val at he
  apply Subtype.ext
  have hi := (Finset.mem_filter.mp I.property).2
  have hj := (Finset.mem_filter.mp J.property).2
  calc
    I.val = A^2*squarefreePart I.val := by simpa only [hi] using (squarePart_sq_mul_squarefreePart I.val).symm
    _ = A^2*squarefreePart J.val := by rw [he]
    _ = J.val := by simpa only [hj] using squarePart_sq_mul_squarefreePart J.val

theorem columnSquareFiber_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    Admissible (squarefreePart I.val) ∧
      (Ideal.absNorm (squarefreePart I.val):ℝ)≤X/(Ideal.absNorm A:ℝ)^2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hp := (supported_square_parts I.val).mp hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A≠0 := by rw [←ha]; exact hp.1.1
  have hAn : 0<(Ideal.absNorm A:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨hp.2,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn : (Ideal.absNorm A:ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
    have hh : (Ideal.absNorm (squarePart I.val):ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
      exact_mod_cast norm_decomposition I.val
    simpa only [ha] using hh
  nlinarith

theorem columnSquareFiber_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hscale : 1≤X/(Ideal.absNorm A:ℝ)^2) :
    ((columnSquareFiber S A).card:ℝ)≤128*(X/(Ideal.absNorm A:ℝ)^2) := by
  let T := (columnSquareFiber S A).image squarefreePart
  have hcard : T.card=(columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩:columnSquareFiber S A)=(⟨J,hJ⟩:columnSquareFiber S A) :=
      columnSquareFiber_injective S A he
    exact congrArg Subtype.val hh)
  rw [←hcard]
  apply DescentFiberCost.finite_ideal_count_real T _ hscale
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).1.1
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_bounds S X hS A ⟨J,hJ⟩).2

theorem columnSquareFiber_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑k : idealRange K, ‖∑I∈columnSquareFiber S A,
      quadraticRow k.val (primaryGenerator I)*a I‖^2) ≤
      sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K *
        ∑I∈columnSquareFiber S A,‖a I‖^2 := by
  let T := columnSquareFiber S A
  let B : Matrix T (idealRange K) ℂ := fun I k => quadraticRow k.val (primaryGenerator (squarefreePart I.val))
  have hB : ‖FiniteSieveOperator.operator B‖^2≤sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K := by
    apply family_squared_norm_le (fun I : T => squarefreePart I.val) (fun k : idealRange K => k.val)
      (columnSquareFiber_injective S A) Subtype.val_injective
    · intro I
      exact columnSquareFiber_bounds S X hS A I
    · intro k
      exact mem_idealRange.mp k.property
  have hBT : B.conjTranspose=(fun k I => quadraticRow k.val (primaryGenerator (squarefreePart I.val))) := by
    ext k I
    exact canonical_quadraticRow_star k.val (mem_idealRange.mp k.property).1 _
  have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun I : T => a I.val)
  rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
  have hm (k : idealRange K) :
      ‖∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val‖^2 ≤
        ‖∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val‖^2 := by
    have hrow : (∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val)=
        idealZeroMask k.val (primaryGenerator A)*
        ∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := (Finset.mem_filter.mp I.property).2
      have hq : quadraticRow k.val (primaryGenerator I.val)=
          idealZeroMask k.val (primaryGenerator A)*quadraticRow k.val (primaryGenerator (squarefreePart I.val)) := by
        have hh := canonical_quadraticRow_primary_squarefree k.val (mem_idealRange.mp k.property).1
          (squarePart I.val) (squarefreePart I.val)
        rw [squarePart_sq_mul_squarefreePart,hi] at hh
        exact hh
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖idealZeroMask k.val (primaryGenerator A)‖^2≤1 := by
      unfold idealZeroMask
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hr (k : idealRange K) :
      (∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hr]
  rw [←Finset.sum_coe_sort T (fun I => ‖a I‖^2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))

open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

theorem columnSquareParts_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hA : A∈S.image squarePart) :
    A≠0 ∧ 1≤(Ideal.absNorm A:ℝ) ∧ (Ideal.absNorm A:ℝ)≤X ∧ 1≤X/(Ideal.absNorm A:ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hp := (supported_square_parts I).mp hi.1
  have ha : 1≤(Ideal.absNorm (squarePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.1.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hp.2.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (Ideal.absNorm (squarePart I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)=(Ideal.absNorm I:ℝ) := by
    exact_mod_cast norm_decomposition I
  refine ⟨hp.1.1,ha,by nlinarith,?_⟩
  apply (le_div_iff₀ (by positivity : 0<(Ideal.absNorm (squarePart I):ℝ)^2)).mpr
  nlinarith

theorem bounded_supported_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K X lengthScale : ℝ,
      1≤K → 1≤X → 0≤lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖≤lengthScale) →
      (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*lengthScale^2 := by
  intro ε hε
  let deltaLoss := ε/3
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := 256*(2+1/(deltaLoss*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨128*C*D^2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image squarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0<K := by linarith
  have hX0 : 0<X := by linarith
  have hP0 : 0<K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0≤R := by dsimp [R]; positivity
  have hRL : R≤D*X^deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    nlinarith
  let F : ℝ := 128*C*(K*X)^deltaLoss*(K+X)*X*lengthScale^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : idealRange K,‖∑I∈columnSquareFiber S A,
        quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0<(Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ)^2
    have hY : 1≤Y := hp.2.2.2
    have hYX : Y≤X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K≤C*(K*X)^deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K≤K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0≤Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖^2)≤128*Y*lengthScale^2 := by
      calc
        _ ≤ ∑_I∈columnSquareFiber S A,lengthScale^2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (columnSquareFiber_card S X hS A hY) (sq_nonneg _)
    have he := columnSquareFiber_energy S X K hS A a
    calc
      _ ≤ (Ideal.absNorm A:ℝ)*(sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖^2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Ideal.absNorm A:ℝ)*((C*(K*X)^deltaLoss*(K+X))*(128*Y*lengthScale^2)) := by
        gcongr
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne']
  have hsplit (k : idealRange K) :
      (∑I∈S,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarePart hI) _).symm
  have hcauchy (k : idealRange K) :
      ‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2≤
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F*R^2 := by
    calc
      _ ≤ ∑k : idealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : idealRange K,‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _ ≤ R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R^2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X)^deltaLoss*(X^deltaLoss)^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^deltaLoss*((K*X)^deltaLoss)^2 := by gcongr
      _ = (K*X)^ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _ ≤ F*(D*X^deltaLoss)^2 := by gcongr
    _ = (128*C*D^2)*((K*X)^deltaLoss*(X^deltaLoss)^2)*(K+X)*X*lengthScale^2 := by dsimp [F]; ring
    _ ≤ _ := by gcongr

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0188

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.ProductColumns
Source SHA256: abba37684c7822c666f678aea4dcf6eefc5c4216372b3be58749c7cb2ceea67c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0189


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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

def productColumnCoefficient (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ) (I : Ideal O) : ℂ :=
  ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),β p.1 p.2

theorem product_fiber_card (P : Finset (Ideal O×Ideal O)) (I : Ideal O) (hI : I≠0) :
    (P.filter (fun p => p.1*p.2=I)).card≤(idealDivisors I).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hI).mpr
    rw [←(Finset.mem_filter.mp hp).2]
    exact dvd_mul_right _ _
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hz : p.1≠0 := by intro hz; simp only [hz,zero_mul] at hp'; exact hI hp'.symm
    apply Prod.ext he
    apply mul_left_cancel₀ hz
    rw [hp',he,hq']

theorem productColumnCoefficient_norm (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ)
    (hβ : ∀n∈S,∀b∈T,‖β n b‖≤1) (I : Ideal O) (hI : I≠0) :
    ‖productColumnCoefficient S T β I‖≤(idealDivisors I).card := by
  unfold productColumnCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = ((S×ˢT).filter (fun p => p.1*p.2=I)).card := by simp
    _ ≤ _ := by exact_mod_cast product_fiber_card (S×ˢT) I hI

theorem productColumnCoefficient_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (k : Ideal O) :
    (∑n∈S,∑b∈T,quadraticRow k (primaryGenerator (n*b))*β n b)=
    ∑I∈(S×ˢT).image (fun p => p.1*p.2),quadraticRow k (primaryGenerator I)*productColumnCoefficient S T β I := by
  rw [←Finset.sum_product (f := fun p : Ideal O×Ideal O => quadraticRow k (primaryGenerator (p.1*p.2))*β p.1 p.2)]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p∈S×ˢT) => Finset.mem_image_of_mem (fun p : Ideal O×Ideal O => p.1*p.2) hp)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [productColumnCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem product_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,Supported I ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,Supported I ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hq : 0<ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_supported_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D^2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1≤X := by dsimp [X]; nlinarith
  have hX0 : 0<X := by linarith
  have hK0 : 0<K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : Supported I ∧ (Ideal.absNorm I:ℝ)≤X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨(supported_mul_iff n b).mpr ⟨(hS n hm.1).1,(hT b hm.2).1⟩,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖≤D*X^(ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (hp I hI).1.1).trans
    apply (hdiv I (hp I hI).1.1).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hp I hI).2 hq.le) hD.le
  have hb := hbound K X (D*X^(ε/4)) hK hX (by positivity) P hp (productColumnCoefficient S T β) hcoeff
  simp_rw [productColumnCoefficient_row_sum]
  apply hb.trans
  have hpow : (K*X)^(ε/2)*(X^(ε/4))^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^(ε/2)*((K*X)^(ε/4))^2 := by gcongr
      _ = _ := by
        rw [pow_two,←mul_assoc,←Real.rpow_add (by positivity : 0<K*X),←Real.rpow_add (by positivity : 0<K*X)]
        congr 1
        ring
  calc
    _ = (C*D^2)*((K*X)^(ε/2)*(X^(ε/4))^2)*(K+X)*X := by ring
    _ ≤ _ := by change _≤(C*D^2)*(K*X)^ε*(K+X)*X; gcongr

end CanonicalQuadraticSieve

namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve ConcretePrimeRowBridge

def shortCompletedSum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  ∑' H : Ideal O, if (Ideal.absNorm H:ℝ)<H₀ then
    (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
      completedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) else 0

def shortCubeRange (H₀ : ℝ) : Finset (Ideal O) :=
  (idealsUpTo ⌈H₀⌉₊).filter (fun H => (Ideal.absNorm H:ℝ)<H₀)

theorem mem_shortCubeRange (H₀ : ℝ) (H : Ideal O) :
    H∈shortCubeRange H₀ ↔ H≠0 ∧ (Ideal.absNorm H:ℝ)<H₀ := by
  rw [shortCubeRange,Finset.mem_filter,mem_idealsUpTo]
  constructor
  · rintro ⟨⟨hn,hup⟩,hH⟩
    refine ⟨?_,hH⟩
    intro hz
    have hh : Ideal.absNorm H=0 := Ideal.absNorm_eq_zero_iff.mpr hz
    omega
  · rintro ⟨hH,hn⟩
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (fun hz => hH (Ideal.absNorm_eq_zero_iff.mp hz)),
      Nat.cast_le.mp (hn.le.trans (Nat.le_ceil H₀))⟩,hn⟩

theorem shortCompletedSum_eq (Ψ : O →* ℂ) (W : ℝ → ℂ) (X H₀ : ℝ) :
    shortCompletedSum Ψ W X H₀ = ∑H∈shortCubeRange H₀,
      (UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H*
        completedT Ψ W (X/(Ideal.absNorm H:ℝ)^3) := by
  unfold shortCompletedSum
  rw [tsum_eq_sum (s:=shortCubeRange H₀)]
  · exact Finset.sum_congr rfl (fun H hH => ite_eq_left ((mem_shortCubeRange H₀ H).mp hH).2)
  · intro H hH
    by_cases hz : H=0
    · simp [hz]
    · have hn : ¬(Ideal.absNorm H:ℝ)<H₀ := fun hn => hH ((mem_shortCubeRange H₀ H).mpr ⟨hz,hn⟩)
      exact ite_eq_right hn

theorem cube_inverse_weight_norm (Ψ : O →* ℂ) (hΨ : ∀z,‖Ψ z‖≤1) (H : Ideal O) :
    ‖(UniqueFactorizationMonoid.moebius H:ℂ)*cubeWeight Ψ H‖≤1/(Ideal.absNorm H:ℝ) := by
  have hang : ‖FiniteGaussPhase.angularFactor (primaryGenerator H)‖≤1 := by
    by_cases hz : primaryGenerator H=0
    · simp [hz,FiniteGaussPhase.angularFactor]
    · exact (FiniteGaussPhase.norm_angularFactor _ hz).le
  have hw : ‖cubeWeight Ψ H‖≤1/(Ideal.absNorm H:ℝ) := by
    change ‖star (FiniteGaussPhase.angularFactor (primaryGenerator H))^3*Ψ (primaryGenerator H)^3/(Ideal.absNorm H:ℂ)‖≤_
    rw [norm_div,norm_mul,norm_pow,norm_pow,norm_star,Complex.norm_natCast]
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
    have h1 : ‖FiniteGaussPhase.angularFactor (primaryGenerator H)‖^3≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) hang 3
    have h2 : ‖Ψ (primaryGenerator H)‖^3≤1 := by
      simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hΨ _) 3
    nlinarith [pow_nonneg (norm_nonneg (Ψ (primaryGenerator H))) 3]
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one H)).trans hw

theorem short_completed_energy {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (X H₀ A : ℝ) (hA : 0≤A)
    (hcompleted : ∀H∈shortCubeRange H₀,
      (∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤A) :
    (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤
      A*(256*(columnDyadicLength H₀+1:ℝ))^2 := by
  let S := shortCubeRange H₀
  let lengthScale : ℝ := ∑H∈S,1/(Ideal.absNorm H:ℝ)
  have hS (H : Ideal O) (hH : H∈S) : H≠0 := ((mem_shortCubeRange H₀ H).mp hH).1
  have hn (H : Ideal O) (hH : H∈S) : 0<(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hS H hH (Ideal.absNorm_eq_zero_iff.mp hz))
  have hL : 0≤lengthScale := Finset.sum_nonneg (fun H hH => by positivity)
  have hb (k : κ) : ‖shortCompletedSum (Ψ k) W X H₀‖^2≤
      lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
    rw [shortCompletedSum_eq]
    apply (ideal_reciprocal_cauchy S hS _).trans
    apply mul_le_mul_of_nonneg_left _ hL
    apply Finset.sum_le_sum
    intro H hH
    rw [norm_mul]
    calc
      _ ≤ (Ideal.absNorm H:ℝ)*((1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖)^2 := by
        gcongr
        exact cube_inverse_weight_norm (Ψ k) (hΨ k) H
      _ = _ := by field_simp [(hn H hH).ne']
  have hsum : (∑k,‖shortCompletedSum (Ψ k) W X H₀‖^2)≤A*lengthScale^2 := by
    calc
      _ ≤ ∑k,lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 :=
        Finset.sum_le_sum (fun k _ => hb k)
      _ = lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro H hH
        rw [←Finset.mul_sum]
      _ ≤ lengthScale*∑H∈S,(1/(Ideal.absNorm H:ℝ))*A := by
        gcongr with H hH
        exact hcompleted H hH
      _ = A*lengthScale^2 := by rw [←Finset.sum_mul]; change lengthScale*(lengthScale*A)=A*lengthScale^2; ring
  have hbound : lengthScale≤256*(columnDyadicLength H₀+1:ℝ) :=
    finite_inverse_norm_sum S H₀ hS (fun H hH => ((mem_shortCubeRange H₀ H).mp hH).2.le)
  exact hsum.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL hbound 2) hA)

end

open ActualEisensteinCubic CanonicalQuadraticSieve

theorem short_cube_scale_algebra (z K R X F h : ℝ)
    (hz : 1≤z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F) (hFz : F≤z)
    (hh : 1≤h) (hhz : h≤z) (hmargin : K*R*z^25≤X*F) :
    1≤X/h^3 ∧ K^2*R*F*h^3/X≤K := by
  have hz0 : 0<z := by linarith
  have hF0 : 0<F := by linarith
  have hh0 : 0<h := by linarith
  have hKR : 1≤K*R := by nlinarith
  have hp4 : z^4≤z^25 := pow_le_pow_right₀ hz (by norm_num)
  have hp5 : z^5≤z^25 := pow_le_pow_right₀ hz (by norm_num)
  have hsmall : h^3*F≤z^25 := by
    calc
      _ ≤ z^3*z := by gcongr
      _ = z^4 := by ring
      _ ≤ _ := hp4
  have hcube : h^3≤X := by
    have h1 : h^3*F≤X*F := hsmall.trans ((le_mul_of_one_le_left (by positivity) hKR).trans hmargin)
    exact (mul_le_mul_iff_left₀ hF0).mp (by simpa only [mul_comm F] using h1)
  have hX : 0<X := (pow_pos hh0 3).trans_le hcube
  refine ⟨(le_div_iff₀ (pow_pos hh0 3)).mpr (by simpa using hcube),?_⟩
  have hfh : F^2*h^3≤z^25 := by
    calc
      _ ≤ z^2*z^3 := by gcongr
      _ = z^5 := by ring
      _ ≤ _ := hp5
  have hprod : K*R*F*h^3≤X := by
    have hn : K*R*(F^2*h^3)≤X*F :=
      (mul_le_mul_of_nonneg_left hfh (by positivity)).trans hmargin
    apply (mul_le_mul_iff_right₀ hF0).mp
    nlinarith
  apply (div_le_iff₀ hX).mpr
  nlinarith [mul_le_mul_of_nonneg_left hprod (show 0≤K by linarith)]

theorem short_cube_scales (Z K R X F h : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hh : 1≤h) (hhZ : h≤Z^(1/1000:ℝ))
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ))) :
    1≤X/h^3 ∧ K^2*R*F*h^3/X≤K := by
  have hZ0 : 0<Z := by linarith
  have hz : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have he : (Z^(1/1000:ℝ))^25=Z^(1/40:ℝ) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ0.le]
    norm_num
  apply short_cube_scale_algebra _ K R X F h hz hK hR hF hFZ hh hhZ
  rw [he]
  have hm := mul_le_mul_of_nonneg_right hmargin (Real.rpow_nonneg hZ0.le (1/40:ℝ))
  have hp : Z^(-(1/40:ℝ))*Z^(1/40:ℝ)=1 := by
    rw [←Real.rpow_add hZ0]
    norm_num
  calc
    _ ≤ X*F*Z^(-(1/40:ℝ))*Z^(1/40:ℝ) := hm
    _ = X*F := by rw [mul_assoc (X*F),hp,mul_one]

theorem short_completed_branch {κ : Type*} [Fintype κ]
    (Ψ : κ → O →* ℂ) (hΨ : ∀k z,‖Ψ k z‖≤1)
    (W : ℝ → ℂ) (Z K R X F A : ℝ)
    (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hA : 0≤A)
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ)))
    (hcompleted : ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
      (∑k,‖completedT (Ψ k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*R*F*(Ideal.absNorm H:ℝ)^3/X)) :
    (∑k,‖shortCompletedSum (Ψ k) W X (Z^(1/1000:ℝ))‖^2)≤
      (2*A*K)*(256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2 := by
  apply short_completed_energy Ψ hΨ W X _ (2*A*K) (by positivity)
  intro H hH
  have hs := (mem_shortCubeRange _ H).mp hH
  have hn : 1≤(Ideal.absNorm H:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hs.1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hsc := short_cube_scales Z K R X F (Ideal.absNorm H:ℝ)
    hZ hK hR hF hFZ hn hs.2.le hmargin
  apply (hcompleted H hH).trans
  nlinarith

theorem short_completed_average {κ : Type*} [Fintype κ]
    (Z K R X F A : ℝ) (hZ : 1≤Z) (hK : 1≤K) (hR : 1≤R) (hF : 1≤F)
    (hFZ : F≤Z^(1/1000:ℝ)) (hA : 0≤A)
    (hmargin : K*R≤X*F*Z^(-(1/40:ℝ)))
    (Ψ : idealRange F → κ → O →* ℂ) (hΨ : ∀f k z,‖Ψ f k z‖≤1) (W : ℝ → ℂ)
    (hcompleted : ∀f : idealRange F, ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
      (∑k,‖completedT (Ψ f k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
        A*(K+K^2*R*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X)) :
    (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)/F≤
      256*A*K*(256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2 := by
  have hZ0 : 0<Z := by linarith
  have hh : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hx := (short_cube_scales Z K R X F 1 hZ hK hR hF hFZ le_rfl hh hmargin).1
  norm_num at hx
  have hX : 0<X := by linarith
  let B := (256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ))^2
  have hb (f : idealRange F) :
      (∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)≤2*A*K*B := by
    apply short_completed_branch (Ψ f) (hΨ f) W Z K R X F A hZ hK hR hF hFZ hA hmargin
    intro H hH
    apply (hcompleted f H hH).trans
    gcongr
    exact (mem_idealRange.mp f.property).2
  have hc : ((idealRange F).card:ℝ)≤128*F := by
    apply DescentFiberCost.finite_ideal_count_real _ _ hF
    · intro I hI
      exact (mem_idealRange.mp hI).1.1
    · intro I hI
      exact (mem_idealRange.mp hI).2
  have hsum : (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)≤
      (128*F)*(2*A*K*B) := by
    calc
      _ ≤ ∑_f : idealRange F,2*A*K*B := Finset.sum_le_sum (fun f _ => hb f)
      _ = ((idealRange F).card:ℝ)*(2*A*K*B) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by dsimp [B]; positivity)
  change _≤256*A*K*B
  calc
    _ ≤ ((128*F)*(2*A*K*B))/F := div_le_div_of_nonneg_right hsum (by linarith)
    _ = _ := by field_simp; ring

theorem short_completed_normalized_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ, 0<C ∧ ∀ (Z K R X F A : ℝ),
      1≤Z → 1≤K → 1≤R → 1≤F → F≤Z^(1/1000:ℝ) → 0≤A →
      K*R≤X*F*Z^(-(1/40:ℝ)) →
      ∀ {κ : Type*} [Fintype κ],
      ∀ (Ψ : idealRange F → κ → O →* ℂ), (∀f k z,‖Ψ f k z‖≤1) →
      ∀W : ℝ → ℂ,
      (∀f : idealRange F, ∀H∈shortCubeRange (Z^(1/1000:ℝ)),
        (∑k,‖completedT (Ψ f k) W (X/(Ideal.absNorm H:ℝ)^3)‖^2)≤
          A*(K+K^2*R*(Ideal.absNorm f.val:ℝ)*(Ideal.absNorm H:ℝ)^3/X)) →
      (∑f : idealRange F,∑k,‖shortCompletedSum (Ψ f k) W X (Z^(1/1000:ℝ))‖^2)/F≤
        C*A*K*Z^ε := by
  let D := 256*(2+1/((ε/2)*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨256*D^2,by positivity,?_⟩
  intro Z K R X F A hZ hK hR hF hFZ hA hmargin κ _ Ψ hΨ W hcompleted
  have hz : 1≤Z^(1/1000:ℝ) := Real.one_le_rpow hZ (by norm_num)
  have hZ0 : 0<Z := by linarith
  have hzZ : Z^(1/1000:ℝ)≤Z := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hZ (show (1/1000:ℝ)≤1 by norm_num)
  have hl : 256*(columnDyadicLength (Z^(1/1000:ℝ))+1:ℝ)≤D*Z^(ε/2) := by
    apply (mul_le_mul_of_nonneg_left (columnDyadicLength_small_power (ε/2) (by positivity) _ hz) (by norm_num : (0:ℝ)≤256)).trans
    have hp := Real.rpow_le_rpow (by positivity : 0≤Z^(1/1000:ℝ)) hzZ (show 0≤ε/2 by positivity)
    calc
      _ = D*(Z^(1/1000:ℝ))^(ε/2) := by dsimp [D]; ring
      _ ≤ D*Z^(ε/2) := mul_le_mul_of_nonneg_left hp hD.le
  have hb := short_completed_average Z K R X F A hZ hK hR hF hFZ hA hmargin Ψ hΨ W hcompleted
  apply hb.trans
  calc
    _ ≤ 256*A*K*(D*Z^(ε/2))^2 := by gcongr
    _ = _ := by
      have hp : (Z^(ε/2))^2=Z^ε := by
        rw [pow_two,←Real.rpow_add hZ0]
        congr 1
        ring
      rw [mul_pow,hp]
      ring

end CompletedGauss

namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss QuadraticSquarefreeKernel

theorem squarefree_all_column_energy {n : Type*} [Fintype n]
    (cols : n → Ideal O) (hinj : Function.Injective cols) (X K : ℝ)
    (hcols : ∀j,Squarefree (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤X) (a : n → ℂ) :
    (∑k : idealRange K,‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2)≤
      4*sieveNorm X K*∑j,‖a j‖^2 := by
  classical
  let sector (E : fixedBadPrimes.powerset) := {j : n // badPrimeSector (cols j)=E}
  have hsector (E : fixedBadPrimes.powerset) :
      (∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2)≤
        sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
    let good : sector E → Ideal O := fun j => goodSquarefreePart (cols j.val)
    have hg : Function.Injective good := by
      intro i j hij
      apply Subtype.ext
      apply hinj
      exact goodSquarefreePart_injective_on_sector _ _ (hcols i.val).1 (hcols j.val).1
        (i.property.trans j.property.symm) hij
    have hgood (j : sector E) : Admissible (good j) ∧ (Ideal.absNorm (good j):ℝ)≤X :=
      mem_idealRange.mp (goodSquarefreePart_mem_idealRange _ (hcols j.val).1 X (hcols j.val).2)
    let B : Matrix (sector E) (idealRange K) ℂ := fun j k => quadraticRow k.val (primaryGenerator (good j))
    have hB := family_squared_norm_le good (fun k : idealRange K => k.val) hg Subtype.val_injective X K
      hgood (fun k => mem_idealRange.mp k.property)
    change ‖FiniteSieveOperator.operator B‖^2≤sieveNorm X K at hB
    have hBT : B.conjTranspose=(fun k j => quadraticRow k.val (primaryGenerator (good j))) := by
      ext k j
      exact canonical_quadraticRow_star _ (mem_idealRange.mp k.property).1 _
    have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun j : sector E => a j.val)
    rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
    have hrow (k : idealRange K) :
        (∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*
          ∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj := sector_bad_good_product (cols j.val) (hcols j.val).1 E j.property
      have hq : quadraticRow k.val (primaryGenerator (cols j.val))=
          quadraticRow k.val (primaryGenerator (sectorBadIdeal E))*quadraticRow k.val (primaryGenerator (good j)) := by
        conv_lhs => rw [←hj]
        rw [primaryGenerator_mul,canonical_quadraticRow_argument_mul _ (mem_idealRange.mp k.property).1]
      rw [hq]
      ring
    have hpoint (k : idealRange K) :
        ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2≤
          ‖∑j : sector E,quadraticRow k.val (primaryGenerator (good j))*a j.val‖^2 := by
      rw [hrow,norm_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    exact (Finset.sum_le_sum (fun k _ => hpoint k)).trans
      (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))
  have hpoint (k : idealRange K) :
      ‖∑j,quadraticRow k.val (primaryGenerator (cols j))*a j‖^2≤
        4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
    rw [←Fintype.sum_fiberwise (fun j => badPrimeSector (cols j))]
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sum_le Finset.univ (fun E : fixedBadPrimes.powerset =>
        ∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val)) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : fixedBadPrimes.powerset => (1:ℝ))
      (fun E : fixedBadPrimes.powerset => ‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖)
    have hcard : Fintype.card fixedBadPrimes.powerset=4 := by
      rw [Fintype.card_coe,fixedBadPrimes_powerset_card]
    apply hn.trans
    simpa [hcard,fixedBadPrimes_card] using hc
  calc
    _ ≤ ∑k : idealRange K,4*∑E : fixedBadPrimes.powerset,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = 4*∑E : fixedBadPrimes.powerset,∑k : idealRange K,‖∑j : sector E,quadraticRow k.val (primaryGenerator (cols j.val))*a j.val‖^2 := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ 4*∑E : fixedBadPrimes.powerset,sieveNorm X K*∑j : sector E,‖a j.val‖^2 := by
      gcongr with E
      exact hsector E
    _ = _ := by
      have he : (∑E : fixedBadPrimes.powerset,∑j : sector E,‖a j.val‖^2)=∑j,‖a j‖^2 :=
        Fintype.sum_fiberwise (fun j => badPrimeSector (cols j)) (fun j => ‖a j‖^2)
      rw [←Finset.mul_sum,he]
      ring

theorem columnSquareFiber_nonzero_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    Squarefree (squarefreePart I.val) ∧
      (Ideal.absNorm (squarefreePart I.val):ℝ)≤X/(Ideal.absNorm A:ℝ)^2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hp := squarePart_ne_zero hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A≠0 := by rw [←ha]; exact hp
  have hAn : 0<(Ideal.absNorm A:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨squarefree_squarefreePart _,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn : (Ideal.absNorm A:ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
    have hh : (Ideal.absNorm (squarePart I.val):ℝ)^2*(Ideal.absNorm (squarefreePart I.val):ℝ)=(Ideal.absNorm I.val:ℝ) := by
      exact_mod_cast norm_decomposition I.val
    simpa only [ha] using hh
  nlinarith

theorem columnSquareFiber_nonzero_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hscale : 1≤X/(Ideal.absNorm A:ℝ)^2) :
    ((columnSquareFiber S A).card:ℝ)≤128*(X/(Ideal.absNorm A:ℝ)^2) := by
  let T := (columnSquareFiber S A).image squarefreePart
  have hcard : T.card=(columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩:columnSquareFiber S A)=(⟨J,hJ⟩:columnSquareFiber S A) :=
      columnSquareFiber_injective S A he
    exact congrArg Subtype.val hh)
  rw [←hcard]
  apply DescentFiberCost.finite_ideal_count_real T _ hscale
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_nonzero_bounds S X hS A ⟨J,hJ⟩).1.ne_zero
  · intro I hI
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (columnSquareFiber_nonzero_bounds S X hS A ⟨J,hJ⟩).2

theorem columnSquareFiber_all_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑k : idealRange K, ‖∑I∈columnSquareFiber S A,
      quadraticRow k.val (primaryGenerator I)*a I‖^2) ≤
      4*sieveNorm (X/(Ideal.absNorm A:ℝ)^2) K *
        ∑I∈columnSquareFiber S A,‖a I‖^2 := by
  let T := columnSquareFiber S A
  have he := squarefree_all_column_energy
    (fun I : T => squarefreePart I.val) (columnSquareFiber_injective S A)
    (X/(Ideal.absNorm A:ℝ)^2) K (fun I => columnSquareFiber_nonzero_bounds S X hS A I)
    (fun I : T => a I.val)
  have hm (k : idealRange K) :
      ‖∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val‖^2 ≤
        ‖∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val‖^2 := by
    have hrow : (∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val)=
        idealZeroMask k.val (primaryGenerator A)*
        ∑I : T,quadraticRow k.val (primaryGenerator (squarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := (Finset.mem_filter.mp I.property).2
      have hq : quadraticRow k.val (primaryGenerator I.val)=
          idealZeroMask k.val (primaryGenerator A)*quadraticRow k.val (primaryGenerator (squarefreePart I.val)) := by
        have hh := canonical_quadraticRow_primary_squarefree k.val (mem_idealRange.mp k.property).1
          (squarePart I.val) (squarefreePart I.val)
        rw [squarePart_sq_mul_squarefreePart,hi] at hh
        exact hh
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖idealZeroMask k.val (primaryGenerator A)‖^2≤1 := by
      unfold idealZeroMask
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hr (k : idealRange K) :
      (∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑I : T,quadraticRow k.val (primaryGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hr]
  rw [←Finset.sum_coe_sort T (fun I => ‖a I‖^2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    he

theorem columnSquareParts_nonzero_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) (A : Ideal O)
    (hA : A∈S.image squarePart) :
    A≠0 ∧ 1≤(Ideal.absNorm A:ℝ) ∧ (Ideal.absNorm A:ℝ)≤X ∧ 1≤X/(Ideal.absNorm A:ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hAz := squarePart_ne_zero hi.1
  have hDz := (squarefree_squarefreePart I).ne_zero
  have ha : 1≤(Ideal.absNorm (squarePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hDz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn : (Ideal.absNorm (squarePart I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)=(Ideal.absNorm I:ℝ) := by
    exact_mod_cast norm_decomposition I
  refine ⟨hAz,ha,by nlinarith,?_⟩
  apply (le_div_iff₀ (by positivity : 0<(Ideal.absNorm (squarePart I):ℝ)^2)).mpr
  nlinarith

theorem bounded_nonzero_quadratic_norm :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K X lengthScale : ℝ,
      1≤K → 1≤X → 0≤lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖≤lengthScale) →
      (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*lengthScale^2 := by
  intro ε hε
  let deltaLoss := ε/3
  have hδ : 0<deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := 256*(2+1/(deltaLoss*Real.log 2))
  have hD : 0<D := by have hlog : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨512*C*D^2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image squarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0<K := by linarith
  have hX0 : 0<X := by linarith
  have hP0 : 0<K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_nonzero_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0≤R := by dsimp [R]; positivity
  have hRL : R≤D*X^deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    nlinarith
  let F : ℝ := 512*C*(K*X)^deltaLoss*(K+X)*X*lengthScale^2
  have hF : 0≤F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : idealRange K,‖∑I∈columnSquareFiber S A,
        quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0<(Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ)^2
    have hY : 1≤Y := hp.2.2.2
    have hYX : Y≤X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K≤C*(K*X)^deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K≤K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0≤Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖^2)≤128*Y*lengthScale^2 := by
      calc
        _ ≤ ∑_I∈columnSquareFiber S A,lengthScale^2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale^2 := by simp
        _ ≤ _ := mul_le_mul_of_nonneg_right (columnSquareFiber_nonzero_card S X hS A hY) (sq_nonneg _)
    have he := columnSquareFiber_all_energy S X K hS A a
    calc
      _ ≤ (Ideal.absNorm A:ℝ)*(4*sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖^2)) :=
        mul_le_mul_of_nonneg_left he (Nat.cast_nonneg _)
      _ ≤ (Ideal.absNorm A:ℝ)*((4*C*(K*X)^deltaLoss*(K+X))*(128*Y*lengthScale^2)) := by
        have h4 := mul_le_mul_of_nonneg_left hb (by norm_num : (0:ℝ)≤4)
        have hh := mul_le_mul h4 hea (by positivity) (by positivity)
        have hw := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg (α:=ℝ) (Ideal.absNorm A))
        convert hw using 1 ; ring
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne'] ; ring
  have hsplit (k : idealRange K) :
      (∑I∈S,quadraticRow k.val (primaryGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarePart hI) _).symm
  have hcauchy (k : idealRange K) :
      ‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2≤
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : idealRange K,‖∑I∈S,quadraticRow k.val (primaryGenerator I)*a I‖^2)≤F*R^2 := by
    calc
      _ ≤ ∑k : idealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : idealRange K,‖∑I∈columnSquareFiber S A,
          quadraticRow k.val (primaryGenerator I)*a I‖^2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _ ≤ R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R^2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X)^deltaLoss*(X^deltaLoss)^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^deltaLoss*((K*X)^deltaLoss)^2 := by gcongr
      _ = (K*X)^ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _ ≤ F*(D*X^deltaLoss)^2 := by gcongr
    _ = (512*C*D^2)*((K*X)^deltaLoss*(X^deltaLoss)^2)*(K+X)*X*lengthScale^2 := by dsimp [F]; ring
    _ ≤ _ := by gcongr

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0189

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.UniformTailBounds
Source SHA256: 7bd3ed31f80d1394b9748b805ad9b9bb915382e3af8d8593783c3beb0bc0768f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0190


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

open scoped BigOperators Classical
namespace CanonicalQuadraticSieve
open ActualEisensteinCubic CompletedGauss IdealMobiusDivisorSum

theorem product_quadratic_norm_all :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,quadraticRow k.val (primaryGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hq : 0<ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_nonzero_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D^2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1≤X := by dsimp [X]; nlinarith
  have hX0 : 0<X := by linarith
  have hK0 : 0<K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : I≠0 ∧ (Ideal.absNorm I:ℝ)≤X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨mul_ne_zero (hS n hm.1).1 (hT b hm.2).1,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖≤D*X^(ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (hp I hI).1).trans
    apply (hdiv I (hp I hI).1).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hp I hI).2 hq.le) hD.le
  have hb := hbound K X (D*X^(ε/4)) hK hX (by positivity) P hp (productColumnCoefficient S T β) hcoeff
  simp_rw [productColumnCoefficient_row_sum]
  apply hb.trans
  have hpow : (K*X)^(ε/2)*(X^(ε/4))^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^(ε/2)*((K*X)^(ε/4))^2 := by gcongr
      _ = _ := by
        rw [pow_two,←mul_assoc,←Real.rpow_add (by positivity : 0<K*X),←Real.rpow_add (by positivity : 0<K*X)]
        congr 1
        ring
  calc
    _ = (C*D^2)*((K*X)^(ε/2)*(X^(ε/4))^2)*(K+X)*X := by ring
    _ ≤ _ := by change _≤(C*D^2)*(K*X)^ε*(K+X)*X; gcongr

end CanonicalQuadraticSieve

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm)
open FirstCauchyArithmetic (supportMobius activeGaussRowFactor)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)

theorem full_uniform_secondPairRadialMode_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H →
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∑' k : {k : O // H ≤ scale * ‖eisEmbedding k‖^2},
        ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) ≤
      (Y / ‖eisEmbedding n‖) *
        ((C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 scale)^2 * (1+H)^A)) := by
  obtain ⟨s,C,hC,hbound⟩ := EisensteinSchwartzPoisson.paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
    S T e he W Y H hY hH
  dsimp only
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hnorm : 0 < ‖eisEmbedding n‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero hn)
  have hscale : 0 < scale := div_pos hY
    (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero he))) (sq_pos_of_pos hnorm))
  let tailSet : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let c := Y / ‖eisEmbedding n‖
  have hc0 : 0 ≤ c := (div_pos hY hnorm).le
  have hpnt (k : tailSet) : ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖ := by
    have ha : Y * ‖eisEmbedding k.val‖^2 / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2) =
        scale * ‖eisEmbedding k.val‖^2 := by dsimp [scale]; ring
    simp only [secondPairRadialMode, norm_mul]
    change ‖(Y : ℂ) / (‖eisEmbedding n‖ : ℂ)‖ * _ * _ ≤ _
    rw [ha, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hY, abs_of_pos hnorm]
    exact mul_le_of_le_one_right (by positivity)
      (activeGaussRowFactor_norm_le_one p hp hg hinj hc T S e k.val)
  have hmajor : Summable (fun k : tailSet =>
      c * ‖EisensteinSchwartzPoisson.paperRadialFourier W (scale * ‖eisEmbedding k.val‖^2)‖) :=
    ((EisensteinSchwartzPoisson.paperRadialFourier_lattice_summable_norm W scale hscale).subtype tailSet).mul_left c
  have hsmall : Summable (fun k : tailSet => ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑' k : tailSet, c * ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := hsmall.tsum_le_tsum hpnt hmajor
    _ = c * ∑' k : tailSet, ‖EisensteinSchwartzPoisson.paperRadialFourier W
          (scale * ‖eisEmbedding k.val‖^2)‖ := tsum_mul_left
    _ ≤ _ := mul_le_mul_of_nonneg_left (hbound W scale H hscale hH) hc0

theorem full_uniform_secondPairRadialMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (S T : Finset ι) (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ),
      0 < Y → 0 ≤ H → ∀ K : Finset O,
      let n := ∏ i : activeSupport T S, p i.val
      let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
      (∀ k : O, k ∉ K → H ≤ scale * ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, secondPairRadialMode p hp hg hinj S T e k.val W Y‖ ≤
        (Y/‖eisEmbedding n‖) *
          ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro S T e he W Y H hY hH K
  dsimp only
  intro hK
  let n := ∏ i : activeSupport T S, p i.val
  let scale := Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding n‖^2)
  let small : Set O := {k | k ∉ K}
  let large : Set O := {k | H ≤ scale * ‖eisEmbedding k‖^2}
  let f : small → large := fun k => ⟨k.val,hK k.val k.property⟩
  have hi : Function.Injective f := by
    intro a b heq
    exact Subtype.ext (congrArg (fun z : large => z.val) heq)
  have hs := secondPairRadialMode_summable_norm p hp hg hinj hc S T e he W Y hY
  calc
    _ ≤ ∑' k : small, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      norm_tsum_le_tsum_norm (hs.subtype small)
    _ ≤ ∑' k : large, ‖secondPairRadialMode p hp hg hinj S T e k.val W Y‖ :=
      (hs.subtype small).tsum_le_tsum_of_inj f hi (fun _ _ => norm_nonneg _) (fun _ => le_rfl)
        (hs.subtype large)
    _ ≤ _ := hb S T e he W Y H hY hH

theorem full_uniform_residualSecondMode_tail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
      (e : O), e ≠ 0 → ∀ (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H → ∀ K : Finset O,
      (∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T ≠ 0 →
        ∀ k : O, k ∉ K →
          H ≤ (Y / (‖eisEmbedding e‖^2 * ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) *
            ‖eisEmbedding k‖^2) →
      ‖∑' k : {k : O // k ∉ K}, residualSecondMode p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e k.val W Y‖ ≤
      residualTailCost p hg F G Ψ₁ Ψ₂ m c d H₁ H₂ e Y H A (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondPairRadialMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y H hY hH K hK
  rw [residualSecondMode_tail_eq p hp hg hinj F G Ψ₁ Ψ₂ m c d H₁ H₂ e he W Y hY K]
  unfold residualTailCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S hS
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [ite_eq_left hd, norm_mul]
    by_cases hw : residualPairWeight p hg Ψ₁ Ψ₂ m c d H₁ H₂ S T = 0
    · simp only [hw, norm_zero, zero_mul, le_refl]
    · exact mul_le_mul_of_nonneg_left (hb S T e he W Y H hY hH K (hK S hS T hT hd hw)) (norm_nonneg _)
  · simp [hd]

theorem full_uniform_secondSourceTail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (Hcol : Finset ι → ℂ)
      (W : 𝓢(ℝ, ℂ)) (Y H : ℝ), 0 < Y → 0 ≤ H →
      ∀ K : Finset ι → Finset ι → Finset O,
      (∀ G ∈ F.powerset, ∀ E : G.powerset,
        ∀ S ∈ (F\G).powerset, ∀ T ∈ (F\G).powerset, Disjoint S T →
        residualPairWeight p hg Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U)) S T ≠ 0 →
        ∀ k : O, k ∉ K G E.val →
          H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
            ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
      ∑ G ∈ F.powerset, ∑ E : G.powerset, ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_residualSecondMode_tail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F Ψ m c d Hcol W Y H hY hH K hK
  unfold secondSourceTail
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro G hG
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro E hE
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E.val
    (Finset.mem_powerset.mp E.property) Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))]
  exact hb F G Ψ Ψ m c d (fun U => Hcol (G∪U)) (fun U => Hcol (G∪U))
    (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) (primeSubsetGenerator_ne_zero _ _)
    W Y H hY hH (K G E.val) (hK G hG E)

theorem full_uniform_firstCoreSecondCutoff_tail_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
      ∑ G ∈ (F\D).powerset, ∑ E : G.powerset,
        ‖secondSourceCommonCoefficient p hg Ψ m c d G E.val‖ *
        residualTailCost p hg (F\D) G Ψ Ψ m c d (fun S => Hbase (G∪S)) (fun S => Hbase (G∪S))
          (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val) Y H A
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_secondSourceTail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F D Ψ m c d g V W negative t X Y M H hX hY hH hgM
  dsimp only
  have hcut : ∀ G ∈ (F\D).powerset, ∀ E : G.powerset,
      ∀ S ∈ ((F\D)\G).powerset, ∀ T ∈ ((F\D)\G).powerset, Disjoint S T →
      residualPairWeight p hg Ψ Ψ m c d
        (fun U => normalizedColumn p (fun R => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) R)) (G∪U))
        (fun U => normalizedColumn p (fun R => firstCoreModeProfile g V negative t
          (columnLog p (X / primeProductNorm p D) R)) (G∪U)) S T ≠ 0 →
      ∀ k : O, k ∉ firstCoreSecondCutoff p D X Y M H G E.val →
        H ≤ (Y / (‖eisEmbedding (primeSubsetGenerator (fun i => Ideal.span {p i}) E.val)‖^2 *
          ‖eisEmbedding (∏ i : activeSupport T S, p i.val)‖^2)) * ‖eisEmbedding k‖^2 := by
    intro G hG E S hS T hT hST hw k hk
    have hGS : Disjoint G S := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right
    have hGT : Disjoint G T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    obtain ⟨hs,ht⟩ := residualPairWeight_test_ne_zero p hg Ψ Ψ m c d _ _ S T hw
    exact firstCoreSecondCutoff_uniform p hp g V negative t M hgM D G E.val S T hGS hGT hST
      X Y H hX hY hs ht k hk
  have h := hb (F\D) Ψ m c d
    (normalizedColumn p (fun S => firstCoreModeProfile g V negative t
      (columnLog p (X / primeProductNorm p D) S))) W Y H hY hH
    (firstCoreSecondCutoff p D X Y M H) hcut
  simpa only [firstCoreModeProfile, residualTailCost_frequencyTwist] using h

theorem full_uniform_firstCoreSecondCutoff_tail_polynomial (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (g V W : 𝓢(ℝ, ℂ))
      (negative : Bool) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        (128*lengthScale)^4 * ((SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
          (Y*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*(1+lengthScale^3/Y)^2/(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_firstCoreSecondCutoff_tail_bound A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  dsimp only
  have hX' : 0 < X / primeProductNorm p D :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp D)
  have hgbase : ∀ u, firstCoreBaseProfile g V negative u ≠ 0 → |u| ≤ M := by
    intro u hu
    apply hgM u
    intro hz
    apply hu
    simp only [firstCoreBaseProfile_apply, hz, zero_mul]
  have hP : 0 ≤ C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W := mul_nonneg hC.le (apply_nonneg _ _)
  exact (hb F D Ψ m c d g V W negative t X Y M H hX hY hH hgM).trans
    (secondSourceTailCost_polynomial p hp hg hinj (F\D) Ψ hΨ m c d
      (firstCoreBaseProfile g V negative) M (X / primeProductNorm p D) Y H
      (1 + X / primeProductNorm p D * Real.exp M) (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) A
      hX' hY hH hP (by linarith [mul_pos hX' (Real.exp_pos M)]) (by linarith) hgbase)

theorem full_uniform_firstCoreSecondCutoff_tail_fixed_source (A : ℕ) (g V W : 𝓢(ℝ, ℂ)) (negative : Bool) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2),
    ∀ (F D : Finset ι) (Ψ : O →* ℂ) (m c d : O) (t X Y M H : ℝ),
      (∀ a, ‖Ψ a‖ ≤ 1) → 0 < X → 0 < Y → 0 ≤ H → (∀ u, g u ≠ 0 → |u| ≤ M) →
      let X' := X / primeProductNorm p D
      let lengthScale := 1 + X' * Real.exp M
      let Hmode := normalizedColumn p (fun S => firstCoreModeProfile g V negative t (columnLog p X' S))
      ‖secondSourceTail p hp hg hinj (F\D) Ψ m c d Hmode W Y (firstCoreSecondCutoff p D X Y M H)‖ ≤
        C*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^A := by
  obtain ⟨s,C,hC,hb⟩ := full_uniform_firstCoreSecondCutoff_tail_polynomial A
  let C₀ := 128^4 * (SchwartzMap.seminorm ℝ 0 0 (firstCoreBaseProfile g V negative))^2 *
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  refine ⟨1+C₀, by linarith, ?_⟩
  intro ι _ p hp _ hg hinj hc
  have hb := hb p hp hg hinj hc
  intro F D Ψ m c d t X Y M H hΨ hX hY hH hgM
  dsimp only
  have h := hb F D Ψ m c d g V W negative t X Y M H hΨ hX hY hH hgM
  apply h.trans
  calc
    _ = C₀*(1+X/primeProductNorm p D*Real.exp M)^4*Y*
        (1+(1+X/primeProductNorm p D*Real.exp M)^3/Y)^2/(1+H)^A := by dsimp [C₀]; ring
    _ ≤ _ := by gcongr; linarith

end SecondPassArithmetic

open scoped BigOperators Classical
namespace InitialMeanSquare
open IdealMobiusDivisorSum

structure ElementDatum where
  divisor : Ideal O
  shared : O
  frequency : O
  deriving DecidableEq

def elementRow (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.frequency
def elementLabel (gen : Ideal O→O) (x : ElementDatum) : O := gen x.divisor*x.shared
def elementObservation (gen : Ideal O→O) (x : ElementDatum) : O×O := (elementRow gen x,elementLabel gen x)

theorem element_divisor_injective_on_fiber (gen : Ideal O→O) (y f : O) (hy : y≠0) :
    Set.InjOn ElementDatum.divisor {x : ElementDatum | elementObservation gen x=(y,f)} := by
  intro x hx z hz hd
  have hxrow : elementRow gen x=y := congrArg Prod.fst hx
  have hzrow : elementRow gen z=y := congrArg Prod.fst hz
  have hxlabel : elementLabel gen x=f := congrArg Prod.snd hx
  have hzlabel : elementLabel gen z=f := congrArg Prod.snd hz
  have hgen : gen x.divisor≠0 := by
    intro he
    apply hy
    rw [←hxrow,elementRow,he,zero_mul]
  have hs : x.shared=z.shared := by
    apply mul_left_cancel₀ hgen
    calc
      gen x.divisor*x.shared = f := hxlabel
      _ = gen z.divisor*z.shared := hzlabel.symm
      _ = gen x.divisor*z.shared := by rw [hd]
  have hh : x.frequency=z.frequency := by
    apply mul_left_cancel₀ hgen
    calc
      gen x.divisor*x.frequency = y := hxrow
      _ = gen z.divisor*z.frequency := hzrow.symm
      _ = gen x.divisor*z.frequency := by rw [hd]
  cases x
  cases z
  simp_all

theorem element_fiber_card_le (gen : Ideal O→O) (hgen : ∀D,Ideal.span {gen D}=D)
    (s : Finset ElementDatum) (y f : O) (hy : y≠0) :
    (s.filter (fun x => elementObservation gen x=(y,f))).card≤(idealDivisors (Ideal.span {y})).card := by
  have hyI : (Ideal.span {y}:Ideal O)≠0 := by intro hz; exact hy (Ideal.span_singleton_eq_bot.mp hz)
  apply Finset.card_le_card_of_injOn ElementDatum.divisor
  · intro x hx
    change x.divisor∈idealDivisors (Ideal.span {y})
    rw [mem_idealDivisors hyI]
    have he : elementRow gen x=y := congrArg Prod.fst (Finset.mem_filter.mp hx).2
    rw [←he,elementRow,←Ideal.span_singleton_mul_span_singleton,hgen]
    exact dvd_mul_right _ _
  · intro x hx z hz he
    exact element_divisor_injective_on_fiber gen y f hy (Finset.mem_filter.mp hx).2 (Finset.mem_filter.mp hz).2 he

theorem element_weighted_energy_pushforward (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (gen : Ideal O→O), (∀D,Ideal.span {gen D}=D) →
      ∀ (s : Finset ElementDatum) (t : Finset (O×O)) (w : ElementDatum→ℂ)
        (P : O×O→ℂ) (A K : ℝ),
      0≤A → 0≤K → (∀x∈s,elementObservation gen x∈t) →
      (∀y∈t,y.1≠0) → (∀y∈t,(Ideal.absNorm (Ideal.span {y.1}):ℝ)≤K) →
      (∀x∈s,‖w x‖≤A) →
      (∑x∈s,‖w x‖*‖P (elementObservation gen x)‖^2)≤A*C*K^ε*∑y∈t,‖P y‖^2 := by
  obtain ⟨C,hC,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨C,hC,?_⟩
  intro gen hgen s t w P A K hA hK hmap ht hnorm hw
  apply (DescentWeightedCauchy.bounded_energy_pushforward s t (elementObservation gen) w P A hmap hw).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  have hyI : (Ideal.span {y.1}:Ideal O)≠0 := by intro hz; exact ht y hy (Ideal.span_singleton_eq_bot.mp hz)
  have hcard : ((s.filter (fun x => elementObservation gen x=y)).card:ℝ)≤C*K^ε := by
    calc
      _ ≤ ((idealDivisors (Ideal.span {y.1})).card:ℝ) := by
        exact_mod_cast element_fiber_card_le gen hgen s y.1 y.2 (ht y hy)
      _ ≤ C*(Ideal.absNorm (Ideal.span {y.1}):ℝ)^ε := hdiv _ hyI
      _ ≤ C*K^ε := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (hnorm y hy) hε.le) hC.le
  have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hA) (sq_nonneg ‖P y‖)
  simpa only [mul_assoc] using hh

end InitialMeanSquare

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn)
open EisensteinSchwartzPoisson (paperRadialFourier)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstDiagonalCost (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) : ℝ :=
  ∑ b∈s,‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*
    (|Y b| *‖paperRadialFourier W 0‖*
      ∑ G∈(globalFirstRawPool pool b).powerset,
        ‖secondInputCoefficient p hg Ψ (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
          (globalFirstBlockTest p g ell side b) G‖^2)

include hp in
theorem globalFirstDiagonalCost_nonneg (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g W : 𝓢(ℝ,ℂ))
    (ell : ℝ) (side : Bool) (Y : GlobalFirstData ι → ℝ) :
    0≤globalFirstDiagonalCost p hg pool s w Ψ m g W ell side Y := by
  unfold globalFirstDiagonalCost
  apply Finset.sum_nonneg
  intro b hb
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le
  positivity

omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstBlockTest_mode_norm (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (t : ℝ) (b : GlobalFirstData ι) (G : Finset ι) :
    ‖globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b G‖ =
      ‖globalFirstBlockTest p (firstCoreBaseProfile g V side) ell side b G‖ := by
  simp only [globalFirstBlockTest,normalizedColumn,norm_div,firstCoreModeProfile,
    JointLogSeparation.frequencyTwist_norm]

include hp in

theorem globalFirstSourceZero_bound
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ,ℂ)) (K ell B F M H : ℝ) (side : Bool) (t : ℝ) :
    ‖globalFirstSourceZero p hg pool s w (globalFirstConcreteCutoff p K ell B F M H side)
      Ψ m (firstCoreModeProfile g V side t) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
    globalFirstDiagonalCost p hg pool s w Ψ m (firstCoreBaseProfile g V side) W ell side
      (globalFirstPooledRow p K ell B F side) := by
  unfold globalFirstSourceZero globalFirstDiagonalCost
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp _).le]
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (norm_nonneg _)
    (inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp _).le))
  have hh := truncatedSecondZero_norm_le p hg hinj (globalFirstRawPool pool b) Ψ
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    (globalFirstBlockTest p (firstCoreModeProfile g V side t) ell side b)
    W (globalFirstPooledRow p K ell B F side b) (globalFirstConcreteCutoff p K ell B F M H side b)
    (fun G hG E hE => firstCoreSecondCutoff_zero _ _ _ _ _ _ _ _)
  apply hh.trans_eq
  congr 1
  apply Finset.sum_congr rfl
  intro G hG
  simp only [secondInputCoefficient,norm_mul,globalFirstBlockTest_mode_norm]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstTailCost (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool) : ℝ :=
  ∑ b∈s,
    let lengthScale := 1+globalFirstBlockColumnScale p ell side b/primeProductNorm p b.firstCommon*Real.exp M
    let Y := globalFirstPooledRow p K ell B F side b
    ‖w b‖*(primeProductNorm p b.firstCommon)⁻¹*lengthScale^4*Y*(1+lengthScale^3/Y)^2/(1+H)^N

include hp in
omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstTailCost_nonneg (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (K ell B F M H : ℝ) (N : ℕ) (side : Bool)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (hH : 0≤H) :
    0≤globalFirstTailCost p s w K ell B F M H N side := by
  unfold globalFirstTailCost
  apply Finset.sum_nonneg
  intro b hb
  dsimp only
  have hn := (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB hF _
  positivity
end

theorem globalFirstSourceTail_bound (N : ℕ) (g V W : 𝓢(ℝ,ℂ)) (side : Bool) :
    ∃ C : ℝ,0<C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
      (Ψ : O →* ℂ) (m : O) (K ell B F M H t : ℝ),
      (∀ a,‖Ψ a‖≤1) → 0<K → 0<ell → 0<B → 0<F → 0≤H → (∀ u,g u≠0 → |u|≤M) →
      ‖globalFirstSourceTail p hp hg hinj pool s w (globalFirstConcreteCutoff p K ell B F M H side)
        Ψ m (firstCoreModeProfile g V side t) W ell side (globalFirstPooledRow p K ell B F side)‖ ≤
      C*globalFirstTailCost p s w K ell B F M H N side := by
  obtain ⟨C,hC,hbound⟩ := full_uniform_firstCoreSecondCutoff_tail_fixed_source N g V W side
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hg hinj hc pool s w Ψ m K ell B F M H t hΨ hK hell hB hF hH hgM
  unfold globalFirstSourceTail globalFirstTailCost
  rw [Finset.mul_sum]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro b hb
  dsimp only
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (FirstPassCubeLabels.primeProductNorm_pos p hp _).le]
  have hX : 0<globalFirstBlockColumnScale p ell side b :=
    div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))
  have hY : 0<globalFirstPooledRow p K ell B F side b := globalPooledRowScale_pos K ell B F hK hell hB hF _
  have hh := hbound p hp hg hinj hc (pool\(b.cube.support∪b.common)) b.firstCommon Ψ
    (m*globalFirstBlockBadLabel p b) (globalFirstBlockLabel p b)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor)
    t (globalFirstBlockColumnScale p ell side b) (globalFirstPooledRow p K ell B F side b) M H
    hΨ hX hY hH hgM
  have hh' := mul_le_mul_of_nonneg_left hh (mul_nonneg (norm_nonneg (w b))
    (inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstCommon).le))
  apply hh'.trans_eq
  ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0190

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.CubeBlocks
Source SHA256: 5052c323e3212d3314dd39c6d79b891b7db795494aa24159352a5731bdd403ff
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0191


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

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter)

theorem globalFirstCoreRows_integrated_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Ct : ℝ),0≤C ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (s : Finset (GlobalFirstData ι))
      (w : GlobalFirstData ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (χ : RayCharacter) (r : FirstCoreIndex)
      (T : GlobalFirstData ι → Finset O),
      0≤Γ → (∀ b∈s,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈s,GlobalFirstAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈s,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈s,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side b) →
      (∀ b∈s,∀ z∈T b,z≠0) →
      let source := globalFirstSupportedPool p pool s
        (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
      let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
      let Ψmode := firstCoreTwist side χ Ψ r
      (∫ t : ℝ,firstLogDensity (2*(J+2)) t*
        globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t) ≤
      (∫ t : ℝ,firstLogDensity 0 t)*
        (globalFirstDiagonalCost p hg pool s (fun b => weight b) Ψmode m
            (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side) +
          globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side +
          Ct*globalFirstTailCost p s (fun b => weight b) K ell B F M H N side) := by
  obtain ⟨windows,C,hC,hwc,hws,hwb,hrows⟩ := globalFirstCoreRows_actual_transfer ε hε g V M hM hgM side A J
  obtain ⟨Ct,hCt,htail⟩ := globalFirstSourceTail_bound N g V rowMajorant side
  refine ⟨windows,C,Ct,hC,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool s w Γ K ell B F H Ψ m χ r T hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
  dsimp only
  let source := globalFirstSupportedPool p pool s
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  let weight := fun b => w b*globalFirstCoefficient p K ell B F side b
  let Ψmode := firstCoreTwist side χ Ψ r
  let d := globalFirstDiagonalCost p hg pool s (fun b => weight b) Ψmode m
    (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side)
  let c := globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε 0 0 K ell B F M H A J side
  let q := Ct*globalFirstTailCost p s (fun b => weight b) K ell B F M H N side
  have hΨmode : ∀ a,‖Ψmode a‖≤1 := fun a => (firstCoreTwist_norm_le side χ Ψ r a).trans (hΨ a)
  have hweight (b : GlobalFirstData ι) (hb : b∈s) : 0≤weight b :=
    mul_nonneg (hw b hb).1 (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hd : 0≤d := globalFirstDiagonalCost_nonneg p hp hg pool s _ Ψmode m _ rowMajorant ell side _
  have hq : 0≤q := mul_nonneg hCt.le (globalFirstTailCost_nonneg p hp s _ K ell B F M H N side hK hell hB hF hH)
  have hpoint (t : ℝ) : globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t ≤
      1*(d+((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*c+q) := by
    have hrow := hrows p hp hcop hg hinj hc hpr pool s w Γ K ell B F H Ψ m χ r t T
      hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
    dsimp only at hrow
    have hsmall : globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T t ≤
        ∑ b∈s,weight b*((∑ z∈T b,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t b z‖^2)+
          globalFirstCoreCorrection p g V ell side t b) := by
      apply Finset.sum_le_sum
      intro b hb
      exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right (sq_nonneg _)) (hweight b hb)
    have hz := globalFirstSourceZero_bound p hp hg hinj pool s (fun b => weight b) Ψmode m
      g V rowMajorant K ell B F M H side t
    have ht := htail p hp hg hinj hc pool s (fun b => weight b) Ψmode m K ell B F M H t
      hΨmode hK hell hB hF hH hgM
    have hupper := add_le_add (add_le_add (le_refl
      (globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*C) ε t t K ell B F M H A J side)) hz) ht
    have hfinal := hsmall.trans (hrow.trans hupper)
    rw [globalChildBudget_height] at hfinal
    simpa only [d,c,q,one_mul,add_comm,add_left_comm,add_assoc] using hfinal
  have hint := FirstPassCubeLabels.integral_pair_moment_bound J
    (globalFirstFiniteEnergy p hg pool s weight Ψ m g V ell side χ r T)
    (globalFirstFiniteEnergy_integrable p hg pool s weight Ψ m g V ell side χ r T (2*(J+2)))
    1 d c q (by norm_num) hd hq hpoint
  simpa only [mul_one] using hint

end
section

open scoped BigOperators Classical SchwartzMap
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm normalizedColumn columnLog firstLogDensity)
open RayFourExpansion (RayCharacter crossCoeff)

@[ext] structure GlobalCubeBlock (ι : Type*) where
  cube : CubeCoordinates ι
  common : Finset ι
  firstDivisor : Finset ι

namespace GlobalCubeBlock
variable {ι : Type*}
def withCommon (b : GlobalCubeBlock ι) (A : Finset ι) : GlobalFirstData ι :=
  ⟨b.cube,A,b.common,b.firstDivisor⟩
end GlobalCubeBlock

namespace GlobalFirstData
variable {ι : Type*}
def block (b : GlobalFirstData ι) : GlobalCubeBlock ι := ⟨b.cube,b.common,b.firstDivisor⟩
@[simp] theorem block_withCommon (b : GlobalCubeBlock ι) (A : Finset ι) : (b.withCommon A).block=b := rfl
@[simp] theorem withCommon_block (b : GlobalFirstData ι) : b.block.withCommon b.firstCommon=b := by cases b; rfl
end GlobalFirstData

variable {ι : Type*} [DecidableEq ι]

def globalCubePool (pool : Finset ι) (b : GlobalCubeBlock ι) : Finset ι := pool\(b.cube.support∪b.common)

def globalFirstFamilySet (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) : Finset (GlobalFirstData ι) :=
  blocks.biUnion (fun b => (globalCubePool pool b).powerset.image b.withCommon)

theorem sum_globalFirstFamilySet {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (f : GlobalFirstData ι → M) :
    ∑ d∈globalFirstFamilySet pool blocks,f d =
      ∑ b∈blocks,∑ A∈(globalCubePool pool b).powerset,f (b.withCommon A) := by
  unfold globalFirstFamilySet
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro A hA B hB he
    exact congrArg GlobalFirstData.firstCommon he
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨B,hB,he⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalFirstData.block he).symm

theorem mem_globalFirstFamilySet (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (d : GlobalFirstData ι) :
    d∈globalFirstFamilySet pool blocks ↔ d.block∈blocks ∧ d.firstCommon⊆globalCubePool pool d.block := by
  simp only [globalFirstFamilySet,Finset.mem_biUnion,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨b,hb,A,hA,rfl⟩;exact ⟨hb,hA⟩
  · rintro ⟨hb,hA⟩;exact ⟨d.block,hb,d.firstCommon,hA,d.withCommon_block⟩

variable (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalCubeColumnScale (ell : ℝ) (side : Bool) (b : GlobalCubeBlock ι) : ℝ :=
  globalFirstBlockColumnScale p ell side (b.withCommon ∅)

def globalCubeCoefficient (K ell B F : ℝ) (side : Bool) (b : GlobalCubeBlock ι) : ℝ :=
  globalFirstCoefficient p K ell B F side (b.withCommon ∅)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstCoefficient_block (K ell B F : ℝ) (side : Bool) (d : GlobalFirstData ι) :
    globalFirstCoefficient p K ell B F side d=globalCubeCoefficient p K ell B F side d.block := by
  simp [globalFirstCoefficient,globalCubeCoefficient,globalBinFirstCoefficient,globalFirstIndex,
    globalScaleIndex,globalScaleVector,globalLogRep,GlobalFirstData.append,
    GlobalCubeBlock.withCommon,GlobalFirstData.block,globalCubeActiveRoot]

def globalCubeInputFamilyEnergy (pool : Finset ι) (b : GlobalCubeBlock ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool) (J : ℕ) (T : Finset O) : ℝ :=
  firstInputFamilyEnergy p hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit side Ψ m
    (fun A => g (columnLog p (globalCubeColumnScale p ell side b) A)) V
    (globalCubeColumnScale p ell side b) (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) J T

def globalFirstFamilyWeight (w : GlobalCubeBlock ι → ℝ) (Ψ : O →* ℂ) (m : O)
    (side : Bool) (r : FirstCoreIndex) (d : GlobalFirstData ι) : ℝ :=
  w d.block*‖firstCoreOuter p hg d.cube.support
    (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit
    side Ψ m d.firstCommon r‖

theorem globalFirstFiniteEnergy_integral_sum
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℝ)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (ell : ℝ) (side : Bool)
    (χ : RayCharacter) (r : FirstCoreIndex) (T : GlobalFirstData ι → Finset O) (J : ℕ) :
    (∫ t,firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t) =
      ∑ d∈s,w d*∫ t,firstLogDensity J t*∑ z∈T d,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t d z‖^2 := by
  have hi (d : GlobalFirstData ι) : Integrable (fun t => firstLogDensity J t*
      ∑ z∈T d,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t d z‖^2) := by
    simpa only [globalFirstFiniteEnergy,Finset.sum_singleton,one_mul] using
      globalFirstFiniteEnergy_integrable p hg pool {d} (fun _ => 1) Ψ m g V ell side χ r T J
  have he (t : ℝ) : firstLogDensity J t*globalFirstFiniteEnergy p hg pool s w Ψ m g V ell side χ r T t =
      ∑ d∈s,w d*(firstLogDensity J t*∑ z∈T d,‖globalFirstCoreRow p hg pool Ψ m g V ell side χ r t d z‖^2) := by
    simp only [globalFirstFiniteEnergy,Finset.mul_sum,mul_left_comm]
  simp_rw [he]
  rw [integral_finsetSum _ (fun d hd => (hi d).const_mul (w d))]
  simp only [integral_const_mul]

theorem globalCubeInputFamilyEnergy_eq_integrated_rows
    (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (w : GlobalCubeBlock ι → ℝ)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ)) (K ell B F : ℝ) (side : Bool) (J : ℕ)
    (T : GlobalCubeBlock ι → Finset O) :
    (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F side b*
      globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side J (T b)) =
    ∑ a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑ r : FirstCoreIndex,
      ∫ t,firstLogDensity J t*globalFirstFiniteEnergy p hg pool (globalFirstFamilySet pool blocks)
        (fun d => globalFirstFamilyWeight p hg w Ψ m side r d*globalFirstCoefficient p K ell B F side d)
        Ψ m g V ell side (if side then a.1 else a.2) r (fun d => T d.block) t := by
  simp_rw [globalFirstFiniteEnergy_integral_sum, sum_globalFirstFamilySet]
  simp only [globalCubeInputFamilyEnergy,firstInputFamilyEnergy,Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  conv_lhs => arg 2; ext b; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro D hD
  rw [globalFirstCoefficient_block]
  simp only [globalFirstFamilyWeight,GlobalCubeBlock.withCommon,
    GlobalFirstData.block,globalFirstCoreRow,globalCubePool,globalCubeColumnScale,globalFirstBlockColumnScale]
  ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy)

theorem globalChild_large_radial_bound (deltaLoss : ℝ) (hδ : 0<deltaLoss) (η : ℝ) (hη : 0<η) :
    ∃ Cbox : ℝ,0<Cbox ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ)
      (C K ell B F M H U Z θ A₀ Vmax : ℝ) (N J : ℕ)
      (source : Finset (GlobalSecondData ι)) (side : Bool),
      0≤C → 1≤U → 0<K → 0<ell → 1≤B → 1≤F → 0≤H →
      K≤U → ell≤U → B≤U → H≤U → Real.exp M≤U → 0<Z →
      0≤A₀ → 0≤Vmax → (∀ t,‖V₁ t‖≤Vmax) → (∀ t,‖V₂ t‖≤Vmax) →
      (∀ t,V₁ t≠0 → |t|≤A₀) → (∀ t,V₂ t≠0 → |t|≤A₀) →
      (∀ a,‖Ψ a‖≤1) → (∀ x∈source,x.source.frequency≠0) →
      (∀ x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
      (∀ x∈source,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
      (∑ j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
          (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        ∑ ray : SecondRayIndex,∑ q∈globalBinTriples p source side j,
          globalDescentWeight C η 0 0 K ell B F (N+1) (2*J) j ray q *
          (densityChildEnergy p hp hcop hg pool (secondRayMinus Ψ ray) (secondRayPlus Ψ ray)
            (fixedTripleMask m q) (globalArithmeticTargets p source side q j) V₁ V₂
            (globalPooledColumnScale ell j) (globalPooledColumnScale ell j) (2*J) /
            (globalPooledColumnScale ell j*globalPooledLabelScale j))) ≤
      C*Cbox*(globalTerminalConstant A₀ Vmax*globalRayTripleConstant)*K*((ell*B^3)*F)*
        U^(deltaLoss+8*η)/Z^(θ*N) := by
  obtain ⟨Cbox,hCbox,hdecay⟩ := globalLogBox_radial_decay deltaLoss hδ η hη.le
  refine ⟨Cbox,hCbox,?_⟩
  intro ι _ p hp _ hcop hg hc hinj pool Ψ m V₁ V₂ C K ell B F M H U Z θ A₀ Vmax N J source side
    hC hU hK hell hB hF hH hKU hellU hBU hHU heU hZ hA₀ hVmax hV₁ hV₂ hVs₁ hVs₂ hΨ hk hb₁ hb₂
  let Q := C*(globalTerminalConstant A₀ Vmax*globalRayTripleConstant)*K*((ell*B^3)*F)
  have hQ : 0≤Q := by
    have hc0 := globalTerminalConstant_nonneg A₀ Vmax
    have hB0 := zero_lt_one.trans_le hB
    have hF0 := zero_lt_one.trans_le hF
    unfold Q globalRayTripleConstant
    positivity
  calc
    _ ≤ ∑ j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        Q*((globalBinLossScale B j)^η/(1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) := by
      apply Finset.sum_le_sum
      intro j hj
      have ht := globalRadialBin_terminal_bound_all_bins p hp hcop hg hc hinj pool Ψ hΨ m V₁ V₂
        C η 0 0 K ell B F A₀ Vmax N J hC hη hK hell hB hF hA₀ hVmax hV₁ hV₂ hVs₁ hVs₂
        source side j hk hb₁ hb₂
      apply ht.trans_eq
      simp only [norm_zero,add_zero,one_pow,mul_one,Q]
      ring
    _ = Q*(∑ j∈(globalLogBox (globalNormCaps ell B (globalRowScaleFloor K ell B F M) M H)).filter
        (fun j => Z^θ≤globalBinRadial ell (globalPooledRowScale K ell B F j) j),
        (globalBinLossScale B j)^η/(1+globalBinRadial ell (globalPooledRowScale K ell B F j) j)^N) := by
      rw [Finset.mul_sum]
    _ ≤ Q*(Cbox*U^(deltaLoss+8*η)/Z^(θ*N)) := mul_le_mul_of_nonneg_left
      (hdecay K ell B F M H U Z θ N hU hK hell hB hF hH hKU hellU hBU hHU heU hZ) hQ
    _ = _ := by dsimp [Q];ring

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap
namespace InitialMeanSquare
open ActualEisensteinCubic SecondPassArithmetic
open FirstCauchyArithmetic (supportMobius supportConjugateSum)
open ConcreteTraceCRT (eisEmbedding)

def conjugateMonoid (Ψ : O→*ℂ) : O→*ℂ where
  toFun x := star (Ψ x)
  map_one' := by simp
  map_mul' x y := by simp [map_mul]

variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

def mobiusRow (F : Finset ι) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (z : O) : ℂ :=
  ∑S∈F.powerset,supportMobius (fun i => Ideal.span {p i}) S*
    inputColumn p Ψ m 1 H S*finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S z

lemma star_mobiusRow (F : Finset ι) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (z : O) :
    star (mobiusRow p hg F Ψ m H z)=
      inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) z := by
  unfold mobiusRow inputConjugateRow supportConjugateSum
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro S hS
  have hm : star (rowCoprimeMask (fun i => Ideal.span {p i}) S m)=rowCoprimeMask (fun i => Ideal.span {p i}) S m := by
    unfold rowCoprimeMask
    split_ifs <;> simp
  simp only [star_mul,FirstCauchyArithmetic.star_supportMobius,
    inputColumn,secondInputCoefficient,conjugateMonoid,MonoidHom.coe_mk,OneHom.coe_mk,
    mul_one,hm]
  simp only [finiteSquarefreeRow,Finset.prod_const_one,one_pow,map_one,mul_one]
  ring

lemma mobiusRow_norm (F : Finset ι) (Ψ : O→*ℂ) (m : O) (H : Finset ι→ℂ) (z : O) :
    ‖mobiusRow p hg F Ψ m H z‖=
      ‖inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) z‖ := by
  rw [←star_mobiusRow p hg F Ψ m H z,norm_star]

variable (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
include hc

theorem mobiusRow_smoothed_source (F : Finset ι) (Ψ : O→*ℂ) (m : O)
    (H : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (Y : ℝ) (hY : 0<Y)
    (K : Finset ι→Finset ι→Finset O) :
    (∑'z:O,W (‖eisEmbedding z‖^2/Y)*(‖mobiusRow p hg F Ψ m H z‖^2:ℝ))=
      truncatedSecondSource p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y (fun G E => (K G E).erase 0)+
      truncatedSecondZero p hg F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K+
      secondSourceTail p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) W Y K := by
  simp_rw [mobiusRow_norm p hg]
  rw [inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F
    (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) W Y hY K]
  rw [truncatedSecondSource_eq_nonzero_add_zero p hp hg hinj]

theorem mobiusRow_finite_source (F : Finset ι) (Ψ : O→*ℂ) (m : O)
    (H : Finset ι→ℂ) (Y : ℝ) (hY : 0<Y) (T : Finset O)
    (hT : ∀z∈T,(Ideal.absNorm (Ideal.span {z}):ℝ)≤Y) (hT0 : ∀z∈T,z≠0)
    (K : Finset ι→Finset ι→Finset O) :
    (∑z∈T,‖mobiusRow p hg F Ψ m H z‖^2)≤
      ‖truncatedSecondSource p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) rowMajorant Y (fun G E => (K G E).erase 0)‖+
      (truncatedSecondZero p hg F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) rowMajorant Y K).re+
      ‖secondSourceTail p hp hg hinj F (conjugateMonoid Ψ) m 1 1
        (fun S => star (H S)) rowMajorant Y K‖-‖H ∅‖^2 := by
  have hb := finite_nonzero_row_energy_le_majorant
    (inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S))) T Y hY hT hT0
  rw [inputConjugateRow_nonzero_correction p hg F (conjugateMonoid Ψ) m 1 1
    (fun S => star (H S)) Y hY] at hb
  have he := mobiusRow_smoothed_source p hg hp hinj hc F Ψ m H rowMajorant Y hY K
  simp_rw [mobiusRow_norm p hg] at he ⊢
  change (∑'z:O,rowMajorant (‖eisEmbedding z‖^2/Y)*
    (‖inputConjugateRow p hg F (conjugateMonoid Ψ) m 1 1 (fun S => star (H S)) z‖^2:ℝ))=_ at he
  rw [he,Complex.sub_re,Complex.add_re,Complex.add_re,Complex.ofReal_re,norm_star] at hb
  exact hb.trans (by gcongr <;> exact Complex.re_le_norm _)

end InitialMeanSquare

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

def PowerfulIdeal (I : Ideal O) : Prop :=
  I≠0 ∧ ∀P∈normalizedFactors I, 2≤(normalizedFactors I).count P

theorem powerful_squarefree_dvd_squarePart (I : Ideal O) (hI : PowerfulIdeal I) :
    squarefreePart I ∣ squarePart I := by
  have ha := squarePart_ne_zero hI.1
  have hb := (squarefree_squarefreePart I).ne_zero
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hb ha).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  have he := congrArg normalizedFactors (squarePart_sq_mul_squarefreePart I)
  rw [normalizedFactors_mul (pow_ne_zero _ ha) hb,normalizedFactors_pow] at he
  have hc := congrArg (Multiset.count P) he
  simp only [Multiset.count_add,Multiset.count_nsmul] at hc
  have hsf := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hb).mp (squarefree_squarefreePart I)) P
  by_cases hzero : (normalizedFactors (squarefreePart I)).count P=0
  · omega
  · have hm : P∈normalizedFactors I := Multiset.count_pos.mp (by omega)
    have hp := hI.2 P hm
    omega

theorem powerful_exists_square_cube (I : Ideal O) (hI : PowerfulIdeal I) :
    ∃A : Ideal O, A≠0 ∧ A^2*squarefreePart I^3=I := by
  obtain ⟨A,hA⟩ := powerful_squarefree_dvd_squarePart I hI
  have ha : A≠0 := by
    intro hz
    have h := squarePart_ne_zero hI.1
    apply h
    rw [hA,hz,mul_zero]
  refine ⟨A,ha,?_⟩
  calc
    _ = (squarefreePart I*A)^2*squarefreePart I := by ring
    _ = squarePart I^2*squarefreePart I := by rw [←hA]
    _ = I := squarePart_sq_mul_squarefreePart I

def powerfulBase (I : Ideal O) : Ideal O :=
  if hI : PowerfulIdeal I then (powerful_exists_square_cube I hI).choose else 0

theorem powerfulBase_spec (I : Ideal O) (hI : PowerfulIdeal I) :
    powerfulBase I≠0 ∧ powerfulBase I^2*squarefreePart I^3=I := by
  rw [powerfulBase,dite_eq_left hI]
  exact (powerful_exists_square_cube I hI).choose_spec

theorem powerfulBase_injective_on_fiber (I J : Ideal O)
    (hI : PowerfulIdeal I) (hJ : PowerfulIdeal J)
    (hb : squarefreePart I=squarefreePart J) (ha : powerfulBase I=powerfulBase J) : I=J := by
  rw [←(powerfulBase_spec I hI).2,←(powerfulBase_spec J hJ).2,ha,hb]

theorem powerfulBase_norm_bound (I : Ideal O) (hI : PowerfulIdeal I) (X : ℝ)
    (hX : (Ideal.absNorm I:ℝ)≤X) :
    1≤(Ideal.absNorm (squarefreePart I):ℝ) ∧
    (Ideal.absNorm (squarefreePart I):ℝ)≤X ∧
    (Ideal.absNorm (powerfulBase I):ℝ)≤Real.sqrt X/(Ideal.absNorm (squarefreePart I):ℝ) := by
  have ha := (powerfulBase_spec I hI).1
  have hb := (squarefree_squarefreePart I).ne_zero
  have ha1 : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => ha (Ideal.absNorm_eq_zero_iff.mp hz))
  have hb1 : 1≤(Ideal.absNorm (squarefreePart I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hb (Ideal.absNorm_eq_zero_iff.mp hz))
  have hnorm : (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3=(Ideal.absNorm I:ℝ) := by
    have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (powerfulBase_spec I hI).2
    simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h
  have hX0 : 0≤X := (Nat.cast_nonneg _).trans hX
  have hb2 : (Ideal.absNorm (squarefreePart I):ℝ)≤(Ideal.absNorm (squarefreePart I):ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ hb1 (show (1:ℕ)≤3 by decide)
  have hab : ((Ideal.absNorm (powerfulBase I):ℝ)*(Ideal.absNorm (squarefreePart I):ℝ))^2≤X := by
    calc
      _ = (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^2 := by ring
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _)
      _ ≤ X := hnorm.trans_le hX
  have hbX : (Ideal.absNorm (squarefreePart I):ℝ)≤X := by
    calc
      _ ≤ (Ideal.absNorm (squarefreePart I):ℝ)^3 := hb2
      _ ≤ (Ideal.absNorm (powerfulBase I):ℝ)^2*(Ideal.absNorm (squarefreePart I):ℝ)^3 :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ ha1)
      _ ≤ X := hnorm.trans_le hX
  refine ⟨hb1,hbX,?_⟩
  apply (le_div_iff₀ (by linarith : 0<(Ideal.absNorm (squarefreePart I):ℝ))).mpr
  nlinarith [Real.sq_sqrt hX0,Real.sqrt_nonneg X]

end

open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel

theorem powerful_fiber_count (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X)
    (B : Ideal O) (hB : B∈S.image squarefreePart) :
    ((S.filter (fun I => squarefreePart I=B)).card:ℝ)≤128*Real.sqrt X/(Ideal.absNorm B:ℝ) := by
  obtain ⟨I,hI,hIB⟩ := Finset.mem_image.mp hB
  have hi := hS I hI
  have hnorm := powerfulBase_norm_bound I hi.1 X hi.2
  rw [hIB] at hnorm
  have hAb : 1≤(Ideal.absNorm (powerfulBase I):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => (powerfulBase_spec I hi.1).1 (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1≤Real.sqrt X/(Ideal.absNorm B:ℝ) := hAb.trans hnorm.2.2
  let T := S.filter (fun I => squarefreePart I=B)
  have hinj : Set.InjOn powerfulBase T := by
    intro J hJ lengthScale hL he
    exact powerfulBase_injective_on_fiber J lengthScale (hS J (Finset.mem_filter.mp hJ).1).1
      (hS lengthScale (Finset.mem_filter.mp hL).1).1
      ((Finset.mem_filter.mp hJ).2.trans (Finset.mem_filter.mp hL).2.symm) he
  have hcard : (T.image powerfulBase).card=T.card := Finset.card_image_iff.mpr hinj
  have hcount := DescentFiberCost.finite_ideal_count_real (T.image powerfulBase)
    (Real.sqrt X/(Ideal.absNorm B:ℝ)) hscale (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      exact (powerfulBase_spec lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1).1) (fun J hJ => by
      obtain ⟨lengthScale,hL,rfl⟩ := Finset.mem_image.mp hJ
      have hp := powerfulBase_norm_bound lengthScale (hS lengthScale (Finset.mem_filter.mp hL).1).1 X
        (hS lengthScale (Finset.mem_filter.mp hL).1).2
      simpa only [(Finset.mem_filter.mp hL).2] using hp.2.2)
  rw [hcard] at hcount
  simpa only [mul_div_assoc] using hcount

theorem powerful_ideal_count_log (S : Finset (Ideal O)) (X : ℝ) (hX : 1≤X)
    (hS : ∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) :
    (S.card:ℝ)≤32768*Real.sqrt X*(columnDyadicLength X+1:ℝ) := by
  let B := S.image squarefreePart
  have hBn (J : Ideal O) (hJ : J∈B) : J≠0 ∧ (Ideal.absNorm J:ℝ)≤X := by
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact ⟨(squarefree_squarefreePart I).ne_zero,(powerfulBase_norm_bound I (hS I hI).1 X (hS I hI).2).2.1⟩
  have he : (S.card:ℝ)=∑J∈B,((S.filter (fun I => squarefreePart I=J)).card:ℝ) := by
    calc
      _ = ∑_I∈S,(1:ℝ) := by simp
      _ = ∑J∈B,∑_I∈S.filter (fun I => squarefreePart I=J),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem squarefreePart hI) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑J∈B,128*Real.sqrt X/(Ideal.absNorm J:ℝ) := Finset.sum_le_sum (fun J hJ => powerful_fiber_count S X hS J hJ)
    _ = (128*Real.sqrt X)*∑J∈B,1/(Ideal.absNorm J:ℝ) := by rw [Finset.mul_sum]; congr 1; ext J; ring
    _ ≤ (128*Real.sqrt X)*(256*(columnDyadicLength X+1:ℝ)) :=
      mul_le_mul_of_nonneg_left (finite_inverse_norm_sum B X (fun J hJ => (hBn J hJ).1)
        (fun J hJ => (hBn J hJ).2)) (by positivity)
    _ = _ := by ring

theorem powerful_ideal_count (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ), 1≤X →
      (∀I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) →
      (S.card:ℝ)≤C*X^(1/2+ε) := by
  let C := 32768*(2+1/(ε*Real.log 2))
  have hC : 0<C := by have hl : 0<Real.log 2 := Real.log_pos (by norm_num); dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro S X hX hS
  apply (powerful_ideal_count_log S X hX hS).trans
  calc
    _ ≤ 32768*Real.sqrt X*((2+1/(ε*Real.log 2))*X^ε) :=
      mul_le_mul_of_nonneg_left (columnDyadicLength_small_power ε hε X hX) (by positivity)
    _ = C*X^(1/2+ε) := by
      rw [Real.rpow_add (by linarith : 0<X),←Real.sqrt_eq_rpow]
      dsimp [C]
      ring

end CompletedGauss

end

end OAI
end OAIOriginalModule0191

/-! Original module: OAI.NumberTheory.DirichletL.GaussSum.PowerfulParts
Source SHA256: fb9f1875a1ba3c3b2eea80943538bba741a0d2cc8e7a7d8b17d3eacaf47a712a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0192



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

open scoped BigOperators Classical
namespace CompletedGauss

section
open ActualEisensteinCubic CanonicalQuadraticSieve QuadraticSquarefreeKernel UniqueFactorizationMonoid

def rowPowerfulPart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P)).prod

def rowSimplePart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P)).prod

theorem rowPowerfulPart_ne_zero (I : Ideal O) : rowPowerfulPart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem rowSimplePart_ne_zero (I : Ideal O) : rowSimplePart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_rowPowerfulPart (I : Ideal O) :
    normalizedFactors (rowPowerfulPart I)=
      (normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_rowSimplePart (I : Ideal O) :
    normalizedFactors (rowSimplePart I)=
      (normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem rowPowerfulPart_powerful (I : Ideal O) : PowerfulIdeal (rowPowerfulPart I) := by
  refine ⟨rowPowerfulPart_ne_zero I,?_⟩
  intro P hP
  rw [normalizedFactors_rowPowerfulPart] at hP ⊢
  have hp := (Multiset.mem_filter.mp hP).2
  rw [Multiset.count_filter,ite_eq_left hp]
  exact hp

theorem rowSimplePart_squarefree (I : Ideal O) : Squarefree (rowSimplePart I) := by
  apply (squarefree_iff_nodup_normalizedFactors (rowSimplePart_ne_zero I)).mpr
  rw [normalizedFactors_rowSimplePart]
  apply Multiset.nodup_iff_count_le_one.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs <;> omega

theorem row_powerful_simple_product (I : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowSimplePart I=I := by
  rw [rowPowerfulPart,rowSimplePart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem row_powerful_simple_coprime (I : Ideal O) :
    IsCoprime (rowPowerfulPart I) (rowSimplePart I) := by
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors (rowPowerfulPart_ne_zero I)).mpr
  intro P hp hs hP
  have hp' := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (rowPowerfulPart_ne_zero I)).mpr ⟨hP,hp⟩
  have hs' := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (rowSimplePart_ne_zero I)).mpr ⟨hP,hs⟩
  rw [normalizedFactors_rowPowerfulPart] at hp'
  rw [normalizedFactors_rowSimplePart] at hs'
  exact (Multiset.mem_filter.mp hs').2 (Multiset.mem_filter.mp hp').2

theorem rowSimplePart_norm (I : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowSimplePart I):ℝ)=
      (Ideal.absNorm I:ℝ)/(Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  have hp : (Ideal.absNorm (rowPowerfulPart I):ℝ)≠0 := by
    exact_mod_cast (fun hz => rowPowerfulPart_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (eq_div_iff hp).mpr
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (row_powerful_simple_product I hI)
  simpa only [map_mul,Nat.cast_mul,mul_comm] using he

end

open ActualEisensteinCubic CanonicalQuadraticSieve UniqueFactorizationMonoid

def squarefreeMaskPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P∣R)).prod

def squarefreeResidualPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬P∣R)).prod

theorem squarefreeMaskPart_ne_zero (I R : Ideal O) : squarefreeMaskPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem squarefreeResidualPart_ne_zero (I R : Ideal O) : squarefreeResidualPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_squarefreeMaskPart (I R : Ideal O) :
    normalizedFactors (squarefreeMaskPart I R)=(normalizedFactors I).filter (fun P => P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_squarefreeResidualPart (I R : Ideal O) :
    normalizedFactors (squarefreeResidualPart I R)=(normalizedFactors I).filter (fun P => ¬P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem squarefreeMaskPart_squarefree (I R : Ideal O) (hI : Squarefree I) : Squarefree (squarefreeMaskPart I R) := by
  apply (squarefree_iff_nodup_normalizedFactors (squarefreeMaskPart_ne_zero I R)).mpr
  rw [normalizedFactors_squarefreeMaskPart]
  exact ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI).filter _

theorem squarefreeResidualPart_squarefree (I R : Ideal O) (hI : Squarefree I) : Squarefree (squarefreeResidualPart I R) := by
  apply (squarefree_iff_nodup_normalizedFactors (squarefreeResidualPart_ne_zero I R)).mpr
  rw [normalizedFactors_squarefreeResidualPart]
  exact ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI).filter _

theorem squarefree_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    squarefreeMaskPart I R*squarefreeResidualPart I R=I := by
  rw [squarefreeMaskPart,squarefreeResidualPart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem squarefreeResidualPart_coprime (I R : Ideal O) : IsCoprime (squarefreeResidualPart I R) R := by
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors (squarefreeResidualPart_ne_zero I R)).mpr
  intro P hp hr hP
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero I R)).mpr ⟨hP,hp⟩
  rw [normalizedFactors_squarefreeResidualPart] at hm
  exact (Multiset.mem_filter.mp hm).2 hr

theorem squarefreeMaskPart_dvd (I R : Ideal O) (hI : Squarefree I) : squarefreeMaskPart I R∣R := by
  by_cases hR : R=0
  · rw [hR]; exact dvd_zero _
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarefreeMaskPart_ne_zero I R) hR).mpr
  rw [normalizedFactors_squarefreeMaskPart]
  apply Multiset.le_iff_count.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs with hp
  · have hn := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI) P
    by_cases hz : (normalizedFactors I).count P=0
    · omega
    · have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero hz)
      have hr := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hR).mpr ⟨prime_of_normalized_factor P hm,hp⟩
      have hc := Multiset.count_pos.mpr hr
      omega
  · omega

def rowMaskPart (I R : Ideal O) : Ideal O := squarefreeMaskPart (rowSimplePart I) R
def rowResidualPart (I R : Ideal O) : Ideal O := squarefreeResidualPart (rowSimplePart I) R

theorem row_powerful_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowMaskPart I R*rowResidualPart I R=I := by
  rw [mul_assoc,rowMaskPart,rowResidualPart,squarefree_mask_residual_product _ _ (rowSimplePart_ne_zero I),
    row_powerful_simple_product I hI]

theorem rowMaskPart_dvd (I R : Ideal O) : rowMaskPart I R∣R :=
  squarefreeMaskPart_dvd _ _ (rowSimplePart_squarefree I)

theorem rowResidualPart_squarefree (I R : Ideal O) : Squarefree (rowResidualPart I R) :=
  squarefreeResidualPart_squarefree _ _ (rowSimplePart_squarefree I)

theorem rowResidualPart_admissible (I R : Ideal O) (hbad : ∀P∈fixedBadPrimes,P∣R) :
    Admissible (rowResidualPart I R) :=
  admissible_of_squarefree_coprime_bad _ R (rowResidualPart_squarefree I R)
    (squarefreeResidualPart_coprime (rowSimplePart I) R) hbad

theorem rowResidualPart_prime_exponent (I R P : Ideal O)
    (hP : P∈normalizedFactors (rowResidualPart I R)) :
    P∈normalizedFactors I ∧ (normalizedFactors I).count P=1 ∧ ¬P∣R := by
  rw [rowResidualPart,normalizedFactors_squarefreeResidualPart] at hP
  obtain ⟨hs,hr⟩ := Multiset.mem_filter.mp hP
  rw [normalizedFactors_rowSimplePart] at hs
  obtain ⟨hi,hcount⟩ := Multiset.mem_filter.mp hs
  exact ⟨hi,by have hp := Multiset.count_pos.mpr hi; omega,hr⟩

theorem rowResidualPart_norm (I R : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowResidualPart I R):ℝ)=(Ideal.absNorm I:ℝ)/
      ((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I R):ℝ)) := by
  have hp : (Ideal.absNorm (rowPowerfulPart I):ℝ)≠0 := by
    exact_mod_cast (fun hz => rowPowerfulPart_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm (rowMaskPart I R):ℝ)≠0 := by
    exact_mod_cast (fun hz => squarefreeMaskPart_ne_zero (rowSimplePart I) R (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (eq_div_iff (mul_ne_zero hp ht)).mpr
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (row_powerful_mask_residual_product I R hI)
  simpa only [map_mul,Nat.cast_mul,mul_comm] using he

end CompletedGauss

namespace SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff gCoeff)

def firstCoreUniformWeight (r : FirstCoreIndex) : ℝ := ‖crossCoeff r.1 r.2.1‖*‖gCoeff r.2.2‖

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def GlobalCubeAdmissible (b : GlobalCubeBlock ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor⊆b.common∪b.cube.support

theorem globalFirstFamilyWeight_bounds (blocks : Finset (GlobalCubeBlock ι))
    (w : GlobalCubeBlock ι → ℝ) (Γ : ℝ) (hw : ∀ b∈blocks,0≤w b ∧ w b≤Γ)
    (Ψ : O →* ℂ) (hΨ : ∀ a,‖Ψ a‖≤1) (m : O) (side : Bool) (r : FirstCoreIndex)
    (pool : Finset ι) (d : GlobalFirstData ι) (hd : d∈globalFirstFamilySet pool blocks) :
    0≤globalFirstFamilyWeight p hg w Ψ m side r d ∧
      globalFirstFamilyWeight p hg w Ψ m side r d≤Γ*firstCoreUniformWeight r := by
  have hw' := hw d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  constructor
  · exact mul_nonneg hw'.1 (norm_nonneg _)
  · have h1 := firstCoreOuter_norm_le p hg d.cube.support
      (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit
      side Ψ m d.firstCommon r
    have h2 := FirstPassCubeLabels.coreRayCoefficient_norm_le p
      (FirstPassCubeLabels.cubeOddSupport d.cube.support
        (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit)
      side r.1 r.2.1 r.2.2
    have hnorm : ‖firstCoreOuter p hg d.cube.support
        (fun i => d.cube.leftExponent i+d.cube.rightExponent i) d.cube.leftBit d.cube.rightBit
        side Ψ m d.firstCommon r‖≤firstCoreUniformWeight r :=
      (h1.trans (mul_le_of_le_one_right (norm_nonneg _) (hΨ _))).trans h2
    exact mul_le_mul hw'.2 hnorm (norm_nonneg _) (hw'.1.trans hw'.2)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstPooledRow_block (K ell B F : ℝ) (side : Bool) (d : GlobalFirstData ι) :
    globalFirstPooledRow p K ell B F side d=
      globalFirstPooledRow p K ell B F side (d.block.withCommon ∅) := by
  simp [globalFirstPooledRow,globalPooledRowScale,globalFirstIndex,globalLogRep,globalScaleIndex,
    globalScaleVector,GlobalFirstData.append,GlobalFirstData.block,GlobalCubeBlock.withCommon,globalCubeJNorm]

end

theorem firstCoreUniformWeight_mass : (∑ r : FirstCoreIndex,firstCoreUniformWeight r)≤512*32 := by
  simp only [firstCoreUniformWeight,Fintype.sum_prod_type]
  simp_rw [← Finset.mul_sum]
  simp_rw [← Finset.sum_mul]
  exact mul_le_mul RayFourExpansion.crossCoeff_sum_norm_le RayFourExpansion.gCoeff_sum_norm_le
    (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (by norm_num)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def globalFirstFamilyBudget (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
    (w : GlobalCubeBlock ι → ℝ) (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ,ℂ))
    (windows : Fin 7 → ℝ → ℂ) (C Ct Γ ε K ell B F M H : ℝ) (A J N : ℕ) (side : Bool) : ℝ :=
  let family := globalFirstFamilySet pool blocks
  let source := globalFirstSupportedPool p pool family
    (fun b G E => (globalFirstConcreteCutoff p K ell B F M H side b G E).erase 0) ell M side
  ∑ a : RayCharacter×RayCharacter,‖crossCoeff a.1 a.2‖*∑ r : FirstCoreIndex,
    let Ψmode := firstCoreTwist side (if side then a.1 else a.2) Ψ r
    let weight := fun d => globalFirstFamilyWeight p hg w Ψ m side r d*globalFirstCoefficient p K ell B F side d
    (∫ t : ℝ,firstLogDensity 0 t)*
      (globalFirstDiagonalCost p hg pool family (fun d => weight d) Ψmode m
          (firstCoreBaseProfile g V side) rowMajorant ell side (globalFirstPooledRow p K ell B F side) +
        globalChildBudget p hp hcop hg pool source Ψmode m windows (Γ*firstCoreUniformWeight r*C) ε 0 0 K ell B F M H A J side +
        Ct*globalFirstTailCost p family (fun d => weight d) K ell B F M H N side)

end

theorem globalCubeInputFamilyEnergy_transfer
    (ε : ℝ) (hε : 0<ε) (g V : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0≤M)
    (hgM : ∀ t,g t ≠ 0 → |t|≤M) (side : Bool) (A J N : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (C Ct : ℝ),0≤C ∧ 0<Ct ∧
      (∀ i,HasCompactSupport (windows i)) ∧ (∀ i,ContDiff ℝ ∞ (windows i)) ∧
      (∀ i t,windows i t ≠ 0 → |t|≤M+6+1) ∧
      ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (w : GlobalCubeBlock ι → ℝ) (Γ K ell B F H : ℝ)
      (Ψ : O →* ℂ) (m : O) (T : GlobalCubeBlock ι → Finset O),
      0≤Γ → (∀ b∈blocks,0≤w b ∧ w b≤Γ) → 0<K → 0<ell → 0<B → 0<F → 0≤H →
      (∀ b∈blocks,GlobalCubeAdmissible b) → (∀ a,‖Ψ a‖≤1) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F side (b.withCommon ∅)) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F side b*
        globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side (2*(J+2)) (T b)) ≤
      globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ m g V windows C Ct Γ ε K ell B F M H A J N side := by
  obtain ⟨windows,C,Ct,hC,hCt,hwc,hws,hwb,hrow⟩ := globalFirstCoreRows_integrated_transfer ε hε g V M hM hgM side A J N
  refine ⟨windows,C,Ct,hC,hCt,hwc,hws,hwb,?_⟩
  intro ι _ p hp _ hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ m T hΓ hw hK hell hB hF hH hs hΨ hb₁ hb₂ hT hT0
  rw [globalCubeInputFamilyEnergy_eq_integrated_rows]
  unfold globalFirstFamilyBudget
  dsimp only
  apply Finset.sum_le_sum
  intro a ha
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Finset.sum_le_sum
  intro r hr
  have hΓr : 0≤Γ*firstCoreUniformWeight r := mul_nonneg hΓ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  apply hrow p hp hcop hg hinj hc hpr pool (globalFirstFamilySet pool blocks)
    (globalFirstFamilyWeight p hg w Ψ m side r) (Γ*firstCoreUniformWeight r) K ell B F H Ψ m
    (if side then a.1 else a.2) r (fun d => T d.block) hΓr
    (fun d hd => globalFirstFamilyWeight_bounds p hg blocks w Γ hw Ψ hΨ m side r pool d hd)
    hK hell hB hF hH
  · intro d hd
    exact hs d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  · exact hΨ
  · intro d hd; exact hb₁ d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  · intro d hd; exact hb₂ d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1
  · intro d hd z hz
    rw [globalFirstPooledRow_block]
    exact hT d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1 z hz
  · intro d hd z hz
    exact hT0 d.block ((mem_globalFirstFamilySet pool blocks d).mp hd).1 z hz

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel columnLog)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

include hp in
omit [DecidableEq ι] [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeColumnScale_pos (ell : ℝ) (hell : 0<ell) (side : Bool) (b : GlobalCubeBlock ι) :
    0<globalCubeColumnScale p ell side b :=
  div_pos hell (mul_pos (FirstPassCubeLabels.primeProductNorm_pos p hp _) (FirstPassCubeLabels.primeProductNorm_pos p hp _))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalCubeCoefficient_side (K ell B F : ℝ) (b : GlobalCubeBlock ι) (side : Bool) :
    globalCubeCoefficient p K ell B F side b=globalCubeCoefficient p K ell B F true b := by
  simp [globalCubeCoefficient,globalFirstCoefficient,globalBinFirstCoefficient,globalFirstIndex,
    globalScaleIndex,globalScaleVector,globalLogRep,GlobalFirstData.append,GlobalCubeBlock.withCommon,globalCubeActiveRoot]

omit [∀ (i : ι), (span {p i}).IsMaximal] in
theorem globalFirstPooledRow_side (K ell B F : ℝ) (b : GlobalCubeBlock ι) (side : Bool) :
    globalFirstPooledRow p K ell B F side (b.withCommon ∅)=globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  simp [globalFirstPooledRow,globalPooledRowScale,globalFirstIndex,globalScaleIndex,globalScaleVector,
    globalLogRep,GlobalFirstData.append,GlobalCubeBlock.withCommon,globalCubeJNorm]

include hp in
theorem globalCube_first_scalar_bound (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) :
    (ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
      ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤
      globalCubeCoefficient p K ell B F true b := by
  have h := globalBin_first_coefficient_bound p hp K ell B F hK.le hell hB hF true
    ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) (by exact one_ne_zero)
  change K/(primeProductNorm p b.firstDivisor*ell*B^2*F*
    ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤ _ at h
  change _ ≤ globalCubeCoefficient p K ell B F true b at h
  convert h using 1 ; ring

def globalCubeFirstBlock (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ,ℂ)) (K ell : ℝ) : ℂ :=
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) b.common
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor
  let X₁ := globalCubeColumnScale p ell true b
  let X₂ := globalCubeColumnScale p ell false b
  ∑ x∈s,a x*actualFirstKernel p hp hcop hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit true
      (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit false
      (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S))) c (ConcretePrimeRowBridge.idealGenerator x.1))
    W V₁ V₂ X₁ X₂ (K/primeProductNorm p b.firstDivisor) d x.2

end

theorem globalCubeFirstBlock_input_transfer
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
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (K ell B F Ymax : ℝ),
      0<K → 0<ell → 0<B → 0<F →
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
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_full_uniform_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
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
  have hpref : 0≤C*Ymax^deltaLoss := mul_nonneg hC (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖globalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      (C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hL := div_pos hK (FirstPassCubeLabels.primeProductNorm_pos p hp b.firstDivisor)
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ _ hL (primeSubsetGenerator (fun i => Ideal.span {p i}) b.common)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) b.firstDivisor) (primeSubsetGenerator_ne_zero _ _)
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hsf b hb) (hs0 b hb) (hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh (inv_nonneg.mpr hden.le)
    change _ ≤ _ at hmul
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖eisEmbedding (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ globalCubeCoefficient p K ell B F true b*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖globalCubeFirstBlock p hp hcop hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,(C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = (C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = (C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ (C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end

open ActualEisensteinCubic
open FirstPassCubeLabels (primeProduct dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem globalTwoPassage_transfer
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ N₁ N₂ : ℝ)
    (hM₁ : 0≤M₁) (hM₂ : 0≤M₂) (hN₁ : 0≤N₁) (hN₂ : 0≤N₂)
    (hg₁ : ∀ t,g₁ t≠0 → |t|≤M₁) (hg₂ : ∀ t,g₂ t≠0 → |t|≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤N₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤N₂)
    (ε deltaLoss : ℝ) (hε : 0<ε) (hδ : 0<deltaLoss) (A J N : ℕ) :
    ∃ (windows₁ windows₂ : Fin 7 → ℝ → ℂ) (Cfirst C₁ Ct₁ C₂ Ct₂ : ℝ),
      0≤Cfirst ∧ 0≤C₁ ∧ 0<Ct₁ ∧ 0≤C₂ ∧ 0<Ct₂ ∧
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
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (Γ K ell B F H Ymax : ℝ),
      0≤Γ → 0<K → 0<ell → 0<B → 0<F → 0≤H → 0≤Ymax →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b ∧ w b≤Γ) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,GlobalCubeAdmissible b) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B) →
      (∀ b∈blocks,‖eisEmbedding (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,globalCubeFirstBlock p hp hcop hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      Cfirst*Ymax^deltaLoss*
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₁ m₁ g₁ V₁ windows₁ C₁ Ct₁ Γ ε K ell B F M₁ H A J N true) *
        Real.sqrt (globalFirstFamilyBudget p hp hcop hg pool blocks w Ψ₂ m₂ g₂ V₂ windows₂ C₂ Ct₂ Γ ε K ell B F M₂ H A J N false) := by
  obtain ⟨Cfirst,hCfirst,hfirst⟩ := globalCubeFirstBlock_input_transfer W V₁ V₂ N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  obtain ⟨windows₁,C₁,Ct₁,hC₁,hCt₁,hwc₁,hws₁,hwb₁,hleft⟩ := globalCubeInputFamilyEnergy_transfer ε hε g₁ V₁ M₁ hM₁ hg₁ true A J N
  obtain ⟨windows₂,C₂,Ct₂,hC₂,hCt₂,hwc₂,hws₂,hwb₂,hright⟩ := globalCubeInputFamilyEnergy_transfer ε hε g₂ V₂ M₂ hM₂ hg₂ false A J N
  refine ⟨windows₁,windows₂,Cfirst,C₁,Ct₁,C₂,Ct₂,hCfirst,hC₁,hCt₁,hC₂,hCt₂,hwc₁,hws₁,hwb₁,hwc₂,hws₂,hwb₂,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ Γ K ell B F H Ymax
    hΓ hK hell hB hF hH hYmax0 hΨ₁ hΨ₂ hw ha hadm hb₁ hb₂ hYmax hsf hs0 hmap hT0 hT
  have hf := hfirst p hp hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell B F Ymax
    hK hell hB hF hΨ₁ hΨ₂ (fun b hb => (hw b hb).1) ha hYmax hsf hs0 hmap hT0 hT
  have hl := hleft p hp hcop hg hinj hc hpr pool blocks w Γ K ell B F H Ψ₁ m₁ T hΓ hw hK hell hB hF hH hadm hΨ₁ hb₁ hb₂ hT hT0
  have hT' : ∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
      globalFirstPooledRow p K ell B F false (b.withCommon ∅) := by
    intro b hb z hz
    rw [globalFirstPooledRow_side]
