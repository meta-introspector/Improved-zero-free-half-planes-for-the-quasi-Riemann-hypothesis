      (UniqueFactorizationMonoid.moebius d : ℂ)*H d i j k else 0

def correctionRectangleMajorant (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ) : ℝ := by
  classical
  exact ∑ D ∈ S, ∑ E ∈ T, ∑ i, if P (D*E) i then
    ‖∑ j, ∑ k, originalTerm rows left right a b D E i j k * H (D*E) i j k‖ else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem signedProductDivisorSum_le_rectangles (S T : Finset (Ideal O))
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (H : Ideal O → m → n → p → ℂ)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hS : ∀ j D, D ∣ left j → D ∈ S) (hT : ∀ k E, E ∣ right k → E ∈ T) :
    ‖signedProductDivisorSum rows left right a b P H‖ ≤
      correctionRectangleMajorant S T rows left right a b P H := by
  classical
  let pairCols : n × p → Ideal O := fun x => left x.1*right x.2
  let K := columnDivisorPool pairCols
  have hpair : ∀ x, pairCols x ≠ 0 := fun x => mul_ne_zero (hleft x.1) (hright x.2)
  have hK : ∀ j k d, d ∣ left j*right k → d ∈ K :=
    fun j k d hd => mem_columnDivisorPool_of_dvd pairCols hpair (j,k) d hd
  let A : m → n → p → K → ℂ := fun i j k d => if P d.val i then
    if d.val ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d.val i j k else 0 else 0
  have he : signedProductDivisorSum rows left right a b P H =
      ∑ i, ∑ j, ∑ k, ∑ d : K, (UniqueFactorizationMonoid.moebius d.val:ℂ)*A i j k d := by
    unfold signedProductDivisorSum
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    rw [← divisorPool_filter K (left j*right k) (mul_ne_zero (hleft j) (hright k)) (hK j k),
      Finset.sum_filter, Finset.mul_sum]
    rw [Finset.sum_coe_sort K (fun d => (UniqueFactorizationMonoid.moebius d:ℂ)*
      (if P d i then if d ∣ left j*right k then originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0))]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : d ∣ left j*right k <;> by_cases hi : P d i <;>
      simp only [hd, hi, ite_true, ite_false, mul_zero] ; ring
  rw [he]
  apply (finite_principal_triangle (fun d : K => (UniqueFactorizationMonoid.moebius d.val:ℂ))
    (fun d => QuadraticInitialBound.norm_ideal_moebius_le_one d.val) A).trans
  have hp (i : m) := originalColumnSum_divisor_rectangles K S T rows left right a b i
    hleft hright hS hT P H
  have hi (i : m) : (∑ d : K, ‖∑ j, ∑ k, A i j k d‖) =
      ∑ d ∈ K, if P d i then ‖∑ j, ∑ k, if d ∣ left j*right k then
        originalTerm rows left right a b 1 1 i j k * H d i j k else 0‖ else 0 := by
    rw [Finset.sum_coe_sort K (fun d => ‖∑ j, ∑ k, if P d i then if d ∣ left j*right k then
      originalTerm rows left right a b 1 1 i j k * H d i j k else 0 else 0‖)]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : P d i <;> simp only [hd, ite_true, ite_false, Finset.sum_const_zero, norm_zero]
  simp_rw [hi]
  apply (Finset.sum_le_sum (fun i _ => hp i)).trans
  unfold correctionRectangleMajorant
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro D _
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro E _
  apply Finset.sum_le_sum
  intro i _
  by_cases hd : D*E ∈ K
  · simp only [hd, ite_true]
    exact le_rfl
  · simp only [hd, ite_false]
    positivity

theorem HasSieveExponent.small_principal_window {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (S T : Finset (Ideal O))
    (D₁ D₂ B N M F U : ℝ) (hD₁ : 1 ≤ D₁) (hD₂ : 1 ≤ D₂) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hD₁N : D₁ ≤ N) (hD₂N : D₂ ≤ N)
    (hS : ∀ D ∈ S, D₁ ≤ (Ideal.absNorm D:ℝ) ∧ (Ideal.absNorm D:ℝ) ≤ 2*D₁)
    (hT : ∀ E ∈ T, D₂ ≤ (Ideal.absNorm E:ℝ) ∧ (Ideal.absNorm E:ℝ) ≤ 2*D₂)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ D ∈ S, ∀ E ∈ T, ∀ i, P (D*E) i → (Ideal.absNorm (D*E):ℝ) ≤
      U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    correctionRectangleMajorant S T rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) ≤
      2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)) := by
  classical
  by_cases hc : D₁*D₂ ≤ (2*U)*(N*Real.sqrt (F/(M*B)))
  · apply le_trans (b := smallPrincipalCorrection S T rows left right a b M F)
    · unfold correctionRectangleMajorant smallPrincipalCorrection
      apply Finset.sum_le_sum
      intro D _
      apply Finset.sum_le_sum
      intro E _
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> first | exact le_rfl | positivity
    · exact hexp.small_principal_correction deltaLoss hδ ε hε S T D₁ D₂ B N M F (2*U)
        hD₁ hD₂ hB hN hM hF hD₁N hD₂N hS hT rows left right hr hl hri
        (fun i => ⟨(hrows i).1,(hrows i).2.2⟩) hleft hright a b hc
  · have hz : correctionRectangleMajorant S T rows left right a b P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) = 0 := by
      unfold correctionRectangleMajorant
      apply Finset.sum_eq_zero
      intro D hD
      apply Finset.sum_eq_zero
      intro E hE
      apply Finset.sum_eq_zero
      intro i _
      have hn : ¬P (D*E) i := by
        intro hp
        apply hc
        apply dual_middle_rectangle_upper M F B (Ideal.absNorm (rows i)) N D₁ D₂
          (Ideal.absNorm D) (Ideal.absNorm E) U hM hF (by linarith) (hrows i).2.1
          (by linarith) hU (by linarith) (by linarith) (hS D hD).1 (hT E hE).1
        simpa only [map_mul,Nat.cast_mul] using hP D hD E hE i hp
      simp only [hn,ite_false]
    rw [hz]
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity

theorem HasSieveExponent.small_principal_divisor_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖signedProductDivisorSum rows left right a b P
      (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2))) := by
  classical
  let S := columnDivisorPool left
  let T := columnDivisorPool right
  have hl0 : ∀ j, left j ≠ 0 := fun j => (hleft j).1.1
  have hr0 : ∀ k, right k ≠ 0 := fun k => (hright k).1.1
  have hS := columnDivisorPool_norm_bounds left hl0 N (fun j => (hleft j).2.2)
  have hT := columnDivisorPool_norm_bounds right hr0 N (fun k => (hright k).2.2)
  apply (signedProductDivisorSum_le_rectangles S T rows left right a b P _ hl0 hr0
    (mem_columnDivisorPool_of_dvd left hl0) (mem_columnDivisorPool_of_dvd right hr0)).trans
  apply divisor_dyadic_sum_le S T N _ _
  · have he := divisorEnergyFactor_nonneg ε hε N a b
    have hd := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    positivity
  · intro j k hj hk
    exact hexp.small_principal_window deltaLoss hδ ε hε (divisorDyadicBin S N j) (divisorDyadicBin T N k)
      (divisorDyadicScale j.val) (divisorDyadicScale k.val) B N M F U
      (divisorDyadicScale_ge_one _) (divisorDyadicScale_ge_one _) hB hN hM hF hU
      (divisorDyadicBin_scale_le S N hS j hj) (divisorDyadicBin_scale_le T N hT k hk)
      (divisorDyadicBin_bounds S N hS j) (divisorDyadicBin_bounds T N hT k)
      rows left right hr hl hri hrows hleft hright a b P (fun D _ E _ i hp => hP (D*E) i hp)

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

lemma source_large_cut_lower (M B b N T d : ℝ)
    (hM : 0 < M) (_hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B) (hN : 0 ≤ N) (hT : 0 < T)
    (hd : T*Real.sqrt (M/b) ≤ d) :
    Real.sqrt (M/B)*N ≤ ((4*N/T)/4)*d := by
  have hs : Real.sqrt (M/B) ≤ Real.sqrt (M/b) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hM.le hb hbB)
  have hsd : Real.sqrt (M/B) ≤ d/T := (le_div_iff₀ hT).mpr (by nlinarith)
  calc
    _ ≤ (d/T)*N := mul_le_mul_of_nonneg_right hsd hN
    _ = _ := by ring

lemma dual_large_cut_lower (M F B b N T d : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hB : 0 < B) (hb : 0 < b) (hbB : b ≤ B)
    (hN : 0 < N) (hT : 0 < T) (hd : T*(N*Real.sqrt (F/(M*b))) ≤ d) :
    Real.sqrt ((M/F)/B)*N ≤ ((4*M/(F*T))/4)*d := by
  have hs : Real.sqrt (F/(M*B)) ≤ Real.sqrt (F/(M*b)) :=
    Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hF.le (by positivity) (mul_le_mul_of_nonneg_left hbB hM.le))
  have hnd : N*Real.sqrt (F/(M*B)) ≤ d/T := by
    apply (le_div_iff₀ hT).mpr
    calc
      _ = T*(N*Real.sqrt (F/(M*B))) := by ring
      _ ≤ T*(N*Real.sqrt (F/(M*b))) := by gcongr
      _ ≤ d := hd
  rw [dual_middle_scale_identity M F B N hM hF hB hN]
  calc
    _ ≤ ((M/(F*N))*(d/T))*N := by gcongr
    _ = _ := by field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

theorem HasSieveExponent.source_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b M (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N M (4*N/T) hB hN hM (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact source_large_cut_lower M B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

theorem HasSieveExponent.dual_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖principalDivisorCorrection rows left right a b (M/F) (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      ((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*M/(F*T)+Real.sqrt (M/F)*B^(α-1/2))) := by
  apply hexp.principal_divisor_correction deltaLoss hδ ε hε B N (M/F) (4*M/(F*T)) hB hN (by positivity) (by positivity)
    rows left right hr hl hri hrows hleft hright a b
  intro d i hd
  exact dual_large_cut_lower M F B (Ideal.absNorm (rows i)) N T (Ideal.absNorm d) hM hF (by linarith)
    (by linarith [(hrows i).2.1]) (hrows i).2.2 (by linarith) hT ((hZ i).trans hd.le)

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem dual_large_principal_normalization
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0) (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0) :
    (∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
      (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
        ((Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ))):ℝ):ℂ) *
        ∑ d ∈ idealDivisors (left j*right k), if P d i then
          (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0)) =
      principalDivisorCorrection rows left right a b (M/F) P := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold principalDivisorCorrection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [←Complex.ofReal_mul, dual_principal_prefactor_identity M F (Ideal.absNorm (rows i))
    (Ideal.absNorm (left j)) (Ideal.absNorm (right k)) hM hF (hpos _ (hrows i))
      (hpos _ (hleft j)) (hpos _ (hright k)), Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : P d i
  · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
    ring
  · simp only [hd,ite_false,mul_zero]

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0163

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.LogarithmicSectors
Source SHA256: 09b2108931a41a74e14e702ee1167984548a159419a7c4138191edd98886885d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0164



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

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

variable {m n : Type*} [Fintype m] [Fintype n]

def lowPrincipalErrorSum (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    lowPrincipalError (cols j) (cols k) W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)))
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / T)
      (T * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (T ^ 4)

theorem lowPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖lowPrincipalErrorSum rows cols a W M T‖ ≤
            16384 * B * N *
              ((4 * supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ l) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := lowPrincipal_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro ε hε B N M T hB hN hM hT rows cols hr hc hrows hcols a W
  let E := (4 * supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    lowPrincipalError (cols j) (cols k) W
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)))
      (Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / T)
      (T * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ))) (T ^ 4)
  have hsc := (supportConstant_pos ε hε).le
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ E := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0 < Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hi)
    have hh := hb ε hε (cols j) (cols k) (hcols j).1 (hcols k).1 W _ _ T hX
      (show Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) / 2 ≤ Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) by linarith)
      (show Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) ≤ 2 * Real.sqrt (M / (Ideal.absNorm (rows i) : ℝ)) by linarith) hT
    change ‖error i j k‖ ≤ _ at hh
    apply hh.trans
    dsimp only [E]
    gcongr
    · exact (hcols j).2
    · exact (hcols k).2
  exact actual_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2⟩) a E hE error herr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem sqrt_product_column_shell (N i j : ℝ) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    N / 2 ≤ Real.sqrt (i * j) ∧ Real.sqrt (i * j) ≤ N := by
  have hi0 : 0 < i := by linarith
  have hj0 : 0 < j := by linarith
  have hlo : (N / 2) ^ 2 ≤ i * j := by
    simpa only [pow_two] using mul_le_mul hi.1 hj.1 (by linarith : 0 ≤ N / 2) hi0.le
  have hhi : i * j ≤ N ^ 2 := by
    simpa only [pow_two] using mul_le_mul hi.2 hj.2 hj0.le hN.le
  have hs := Real.sq_sqrt (mul_pos hi0 hj0).le
  have hp := Real.sqrt_nonneg (i * j)
  constructor <;> nlinarith

theorem dual_truncation_reference_bounds (M F b N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hb : 0 < b) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    0 < N * Real.sqrt (F / (M * b)) ∧
      (N * Real.sqrt (F / (M * b))) / 2 ≤ Real.sqrt (F * i * j / (M * b)) ∧
      Real.sqrt (F * i * j / (M * b)) ≤ 2 * (N * Real.sqrt (F / (M * b))) := by
  have hr : 0 < Real.sqrt (F / (M * b)) := Real.sqrt_pos.mpr (by positivity)
  have he : Real.sqrt (F * i * j / (M * b)) = Real.sqrt (F / (M * b)) * Real.sqrt (i * j) := by
    rw [← Real.sqrt_mul (show 0 ≤ F / (M * b) by positivity)]
    congr 1
    ring
  obtain ⟨hlo, hhi⟩ := sqrt_product_column_shell N i j hN hi hj
  refine ⟨mul_pos hN hr, ?_, ?_⟩
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hlo hr.le]
  · rw [he]
    nlinarith [mul_le_mul_of_nonneg_left hhi hr.le, mul_pos hN hr]

theorem dual_truncation_prefactor_bound (M F N i j : ℝ)
    (hM : 0 < M) (hF : 0 < F) (hN : 0 < N)
    (hi : N / 2 ≤ i ∧ i ≤ N) (hj : N / 2 ≤ j ∧ j ≤ N) :
    M / (Real.sqrt (i * j) * F) ≤ 2 * M / (F * N) := by
  obtain ⟨hlo, _⟩ := sqrt_product_column_shell N i j hN hi hj
  calc
    _ ≤ M / ((N / 2) * F) := div_le_div_of_nonneg_left hM.le (by positivity)
      (mul_le_mul_of_nonneg_right hlo hF.le)
    _ = _ := by field_simp

variable {m n : Type*} [Fintype m] [Fintype n]

def dualPrincipalErrorSum (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M F N T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))

theorem dualPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖dualPrincipalErrorSum rows cols a W M F N T‖ ≤
            16384 * B * N *
              ((2 * M / (F * N)) * ((supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primePool_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (supportConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k)) hM hF hi (by linarith) (hcols j).2 (hcols k).2
    have hh := hb ε hε (cols j * cols k) (mul_ne_zero (hcols j).1.1 (hcols k).1.1) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2.2
      · exact (hcols k).2.2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k))
        hM hF (by linarith) (hcols j).2 (hcols k).2) he (norm_nonneg _) (by positivity)
  exact actual_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2.2⟩) a _ (by positivity) error herr

end CanonicalQuadraticSieve

namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def secondSquarefreeLogSector (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    Finset (SecondExpansionData ι) :=
  (secondLogSector p D F K R X M j).filter
    (fun x => Squarefree (actualSecondLabel p B C x.divisor x.overlap v₁ v₂ ε₁ ε₂))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogSector_subset (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j ⊆ secondLogSector p D F K R X M j :=
  Finset.filter_subset _ _

def secondSquarefreeLogTargets (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    Finset (Ideal O × O) :=
  (secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j).image (fun x =>
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)))

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogTargets_subset (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex) :
    secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j ⊆
      secondLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j :=
  Finset.image_subset_image (secondSquarefreeLogSector_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j)

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogTargets_mem (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (x : SecondExpansionData ι) (hx : x ∈ secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    (secondSupportNewLabel p B v₁ v₂ ε₁ ε₂ (expansionSupportData C D x),
      secondSupportRow p (expansionSupportData C D x)) ∈
      secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

omit [∀ (i : ι), (span {p i}).IsMaximal] in
lemma secondSquarefreeLogTargets_squarefree (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (q : Ideal O × O) (hq : q ∈ secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    Squarefree q.1 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
  exact (Finset.mem_filter.mp hx).2

include hp in
lemma secondSquarefreeLogTargets_bounds (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (q : Ideal O × O) (hq : q ∈ secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    q.1 ≠ ⊥ ∧ (Ideal.absNorm q.1 : ℝ) ≤ secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j ∧
      q.2 ≠ 0 ∧ ‖eisEmbedding q.2‖^2 ≤ secondLogK j * Real.exp 1 :=
  secondLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q
    (secondSquarefreeLogTargets_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j hq)

include hp in
lemma secondSquarefreeLogSector_coordinates (B C D F R : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (x : SecondExpansionData ι)
    (hx : x ∈ secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) :
    let y := expansionSupportData C D x
    |secondSectorZ p (secondExpansionScale p X
      (primeSubsetGenerator (fun i => Ideal.span {p i}) R) y) (secondLogX p R X j) y| ≤ 2 ∧
    |secondSectorUd p (primeProductNorm p D) y| ≤ 2 ∧
    |secondSectorUe p (secondLogE j) y| ≤ 2 ∧
    |secondSectorUv p (secondLogV j) y| ≤ 2 ∧
    |secondSectorKap p (secondLogK j) y| ≤ 2 :=
  secondLogSector_coordinates p hp C D F R K X M hX j x
    (secondSquarefreeLogSector_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j hx)

end

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondExpansionSource_log_eq_squarefree
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hCB : Disjoint C B)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ : O →* ℂ) (m d : O) (z : SecondRayIndex) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ,ℂ)) (Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) d z
      (secondLogSector p D F K R X M j) H₁ H₂ W Y =
    secondExpansionSource p hp hcop hg F Ψ m (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) d z
      (secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) H₁ H₂ W Y := by
  apply secondExpansionSource_eq_squarefree p hp hcop hg B C v₁ v₂ ε₁ ε₂ hCB F Ψ m d z
  intro x hx
  have hs := secondSupportedSector_mem p F K R X M x (Finset.mem_filter.mp hx).1
  exact hs.2.1

end

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm jLabel b0Label)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open JointLogSeparation (frequencyTwist frequencyTwist_apply)
open SecondPassIntegration (densityChildEnergy)

theorem normalized_squarefree_binned_second_density_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g W : 𝓢(ℝ, ℂ)) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧
      ∀ (Y : ℝ), 0 < Y → ∀ θ : ℝ,
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X Kmax : ℝ) (K : Finset ι → Finset ι → Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X →
        (∀ G ∈ F.powerset, ∀ E ∈ G.powerset, (0 : O) ∈ K G E) →
        (∀ R ∈ F.powerset, ∀ x ∈ secondSupportedSector p F K R X M,
          ‖eisEmbedding (actualSecondRow p D x.divisor x.frequency)‖^2 ≤ Kmax) →
        let c := secondBaseLabel p B C v₁ v₂ ε₁ ε₂
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Hcol := fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S
        ‖truncatedSecondSource p hp hg hinj F Ψ m c d Hcol W Y K‖ ≤
          |Y| * ‖paperRadialFourier W 0‖ *
            (∑ G ∈ F.powerset, ‖secondInputCoefficient p hg Ψ m c d
              (fun S => normalizedColumn p (fun A => g (columnLog p X A)) S) G‖^2) +
          ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p F (X*Real.exp M),
            ∑ j ∈ secondLogBinBox (X*Real.exp M) Kmax,
            (Y * primeProductNorm p R / X^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
              (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                Ideal.absNorm (Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}))^ε) *
            (Cₛ*(1+‖θ‖)^(J+2)*(1+‖θ‖)^(J+2) /
              (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X^2))^decayOrder) *
            densityChildEnergy p hp hcop hg F (secondRayMinus Ψ z) (secondRayPlus Ψ z)
              (m * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
              (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
              (windows 5) (windows 6) (secondLogX p R X j) (secondLogX p R X j) J := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,hbound⟩ :=
    normalized_twisted_second_sector_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g g W hU hU M 2 hM (by norm_num) hgM hgM ε hε decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,?_⟩
  intro Y hY θ B C D F v₁ v₂ ε₁ ε₂ Ψ m X Kmax K hv hCB hD hΨ hX hzero hK
  dsimp only
  have hθ : ∀ t, (frequencyTwist g θ) t ≠ 0 → |t| ≤ M := by
    intro t ht
    exact hgM t (fun hz => ht (by simp only [frequencyTwist_apply,hz,mul_zero]))
  apply (truncatedSecondSource_norm_le_binned p hp hcop hg hinj hc hpr D F Ψ m
    (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
    (frequencyTwist g θ) W X Y M Kmax hX hθ K hK).trans
  apply add_le_add
  · have hd := truncatedSecondZero_norm_le p hg hinj F Ψ m
      (secondBaseLabel p B C v₁ v₂ ε₁ ε₂) (primeSubsetGenerator (fun i => Ideal.span {p i}) D)
      (fun S => normalizedColumn p (fun A => (frequencyTwist g θ) (columnLog p X A)) S) W Y K hzero
    simpa only [secondInputCoefficient_frequencyTwist_norm] using hd
  · apply Finset.sum_le_sum
    intro z hz
    apply Finset.sum_le_sum
    intro R hR
    apply Finset.sum_le_sum
    intro j hj
    rw [secondExpansionSource_log_eq_squarefree p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ hCB
      K R X M j Ψ m (primeSubsetGenerator (fun i => Ideal.span {p i}) D) z _ _ W Y]
    have hcoord := secondSquarefreeLogSector_coordinates p hp B C D F R v₁ v₂ ε₁ ε₂ K X M hX j
    have hb := hbound (primeProductNorm p D) (secondLogE j) (secondLogV j)
      (secondLogX p R X j) (secondLogK j) Y
      (FirstPassCubeLabels.primeProductNorm_pos p hp D)
      (normLogScale_pos _) (normLogScale_pos _) (secondLogX_pos p hp R X hX j)
      (normLogScale_pos _) hY θ θ B C D R F v₁ v₂ ε₁ ε₂ Ψ m z K
      (secondSquarefreeLogSector p B C D F v₁ v₂ ε₁ ε₂ K R X M j) (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      X (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)
      ((secondSquarefreeLogSector_subset p B C D F v₁ v₂ ε₁ ε₂ K R X M j).trans
        (secondLogSector_subset p D F K R X M j)) hv hCB hD hΨ hX
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))
      (fun x hx => (hcoord x hx).1) (fun x hx => (hcoord x hx).2.1)
      (fun x hx => (hcoord x hx).2.2.1) (fun x hx => (hcoord x hx).2.2.2.1)
      (fun x hx => (hcoord x hx).2.2.2.2)
      (secondSquarefreeLogTargets_mem p B C D F v₁ v₂ ε₁ ε₂ K R X M j)
      (fun q hq => (secondSquarefreeLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).1)
      (fun q hq => (secondSquarefreeLogTargets_bounds p hp B C D F v₁ v₂ ε₁ ε₂ K R X M j q hq).2.1)
    simpa only [secondBaseLabel, primeSubsetGenerator_norm_eq_productNorm,
      secondLogX_radial_scale p D R X Y hX.ne' j] using hb

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_squarefree_binned_finite_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z t : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Usupp := X' * Real.exp M
        let K := firstCoreSecondCutoff p A₀ X Y M Z
        let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2) +
          ‖firstCoreTest (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X)
            negative t A₀ ∅‖^2 ≤
        (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  have hUbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → U s = 1 := by
    intro s hs
    apply hU s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  have hMbase : ∀ s, firstCoreBaseProfile g V negative s ≠ 0 → |s| ≤ M := by
    intro s hs
    apply hgM s
    intro hz
    exact hs (by simp only [firstCoreBaseProfile_apply,hz,zero_mul])
  obtain ⟨windows,Cₐ,Cₛ,Cw,hCₐ,hCₛ,hCw,htrans⟩ :=
    normalized_squarefree_binned_second_density_transfer p hp hcop hg hinj hc hpr U hUc hUs
      (firstCoreBaseProfile g V negative) rowMajorant hUbase M hM hMbase ε hε decayOrder J
  obtain ⟨Ctail,hCtail,htail⟩ :=
    firstCoreSecondCutoff_tail_fixed_source p hp hg hinj hc tailOrder g V rowMajorant negative
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  have hX' : 0 < X / primeProductNorm p A₀ :=
    div_pos hX (FirstPassCubeLabels.primeProductNorm_pos p hp A₀)
  have hΨ' : ∀ a : O, ‖firstCoreTwist negative χ Ψ r₁ a‖ ≤ 1 :=
    fun a => (firstCoreTwist_norm_le negative χ Ψ r₁ a).trans (hΨ a)
  have hb := htrans Y hY (firstCoreModeHeight negative t) B C D (F\A₀)
    v₁ v₂ ε₁ ε₂ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂) (X / primeProductNorm p A₀)
    (firstCoreSecondRowBound p D A₀ X Y M Z) (firstCoreSecondCutoff p A₀ X Y M Z)
    hv hCB hD hΨ' hX'
    (fun G hG E hE => firstCoreSecondCutoff_zero p A₀ X Y M Z G E)
    (fun R hR x hx => firstCoreSecondCutoff_supported_row_bound p hp D A₀ (F\A₀) R
      X Y M Z hX hY hZ x hx)
  simp only [firstCoreModeHeight_norm, secondBaseLabel] at hb
  have ht := htail F A₀ (firstCoreTwist negative χ Ψ r₁)
    (m * b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) t X Y M Z hΨ' hX hY hZ hgM
  have hf := firstCoreInputRow_finite_le_truncated_tail p hp hg hinj hc F A₀ B
    (fun i => v₁ i+v₂ i) ε₁ ε₂ negative χ Ψ m g V X hX Y hY
    (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r₁ t Srows hSrows hSrows0
    (firstCoreSecondCutoff p A₀ X Y M Z)
  simp only [firstCoreModeProfile] at hf ht ⊢
  apply hf.trans
  apply mul_le_mul_of_nonneg_left
  · apply add_le_add
    · exact hb
    · exact ht
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le

end SecondPassArithmetic

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter)
open SecondPassIntegration (densityChildEnergy)

theorem firstCoreInputRow_squarefree_binned_integrated_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex)
        (X Z : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        let v := fun i => v₁ i + v₂ i
        let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
        let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
        let Ψ' := firstCoreTwist negative χ Ψ r₁
        let m' := m * b0Label p B v ε₁ ε₂
        let c' := c * jLabel p B v ε₁ ε₂
        let X' := X / primeProductNorm p A₀
        let Usupp := X' * Real.exp M
        let K := firstCoreSecondCutoff p A₀ X Y M Z
        let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
        let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity (2*(J+2)) t * (∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
          (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2)) ≤
        (∫ t : ℝ, FirstPassCubeLabels.firstLogDensity 0 t) * (primeProductNorm p A₀)⁻¹ *
          (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
              (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
            (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
              ∑ j ∈ secondLogBinBox Usupp Kmax,
              (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
                (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
                  Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
              (Cₛ /
                (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
              densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
                (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
                (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
                (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
            Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder) := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hpoint⟩ :=
    firstCoreInputRow_squarefree_binned_finite_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M hM hgM ε hε tailOrder decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  dsimp only
  let v := fun i => v₁ i+v₂ i
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let Ψ' := firstCoreTwist negative χ Ψ r₁
  let m' := m*b0Label p B v ε₁ ε₂
  let c' := c*jLabel p B v ε₁ ε₂
  let X' := X/primeProductNorm p A₀
  let Usupp := X'*Real.exp M
  let K := firstCoreSecondCutoff p A₀ X Y M Z
  let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
  let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
  let f := fun t => ∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
    (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ t z‖^2
  let diag := |Y| * ‖paperRadialFourier rowMajorant 0‖*
    (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2)
  let tail := Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder
  let childAt := fun t : ℝ => ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ*(1+‖t‖)^(J+2)*(1+‖t‖)^(J+2) /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  let child := ∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
    ∑ j ∈ secondLogBinBox Usupp Kmax,
    (Y*primeProductNorm p R/X'^2*‖secondRayCoefficient z‖*Cw*Cₐ*
      (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j*Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
    (Cₛ /
      (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
    densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
      (m'*primeSubsetGenerator (fun i => Ideal.span {p i}) R)
      (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
      (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J
  have hchild (t : ℝ) : childAt t = ((1+‖t‖)^(J+2)*(1+‖t‖)^(J+2))*child := by
    dsimp only [child, childAt]
    simp only [    Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro z hz
    apply Finset.sum_congr rfl
    intro R hR
    apply Finset.sum_congr rfl
    intro j hj
    ring
  change (∫ t, firstLogDensity (2*(J+2)) t*f t) ≤
    (∫ t, firstLogDensity 0 t)*(primeProductNorm p A₀)⁻¹*(diag+child+tail)
  apply FirstPassCubeLabels.integral_pair_moment_bound J f
  · dsimp only [f]
    simp only [Finset.mul_sum]
    apply integrable_finsetSum
    intro z hz
    exact firstCoreInputRow_integrable p hg F A₀ B v ε₁ ε₂ negative χ Ψ m
      (normalizedColumn p (fun S => g (columnLog p X S))) V (columnLog p X) c d r₁ z
      (FirstPassCubeLabels.firstLogDensity_integrable (2*(J+2)))
  · exact inv_nonneg.mpr (FirstPassCubeLabels.primeProductNorm_pos p hp A₀).le
  · dsimp [diag]
    positivity
  · dsimp [tail]
    positivity
  · intro t
    have hb := hpoint Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ χ Ψ m r₁ X Z t Srows
      hv hCB hD hΨ hX hZ hSrows hSrows0
    change f t + _ ≤ (primeProductNorm p A₀)⁻¹*(diag+childAt t+tail) at hb
    rw [hchild] at hb
    exact (le_add_of_nonneg_right (sq_nonneg _)).trans hb

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0164

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.SquarefreeTransfer
Source SHA256: 2c1f664c0434c28f32f649463f60f7f654f19de233b7f25d3a06d55b5b96cd95
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0165


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

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic
open FirstPassCubeLabels (primeProductNorm)
open ConcreteTraceCRT (eisEmbedding)
open SecondPassIntegration (densityChildEnergy childGeometricMean childEnergy)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondSquarefreeLogNormalizedEnergy (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (j : SecondLogIndex)
    (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) : ℝ :=
  densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
    (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
    (secondLogX p R X j) (secondLogX p R X j) J /
  (secondLogX p R X j * secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j)

lemma secondSquarefreeLogNormalizedEnergy_nonneg
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    0 ≤ secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  apply div_nonneg
  · apply integral_nonneg
    intro t₁
    apply integral_nonneg
    intro t₂
    apply integral_nonneg
    intro t₃
    exact mul_nonneg (JointLogSeparation.tripleLogDensity_nonneg _ _)
      (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  · exact mul_nonneg (secondLogX_pos p hp R X hX j).le
      (zero_le_one.trans (secondLogLabelBound_ge_one p hp B C v₁ v₂ ε₁ ε₂ j))

lemma secondSquarefreeLogNormalizedEnergy_empty
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X M : ℝ)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ)
    (hT : secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j = ∅) :
    secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J = 0 := by
  simp only [secondSquarefreeLogNormalizedEnergy, hT, densityChildEnergy, childGeometricMean, childEnergy,
    Finset.sum_empty, Finset.sum_const_zero, Real.sqrt_zero, mul_zero, integral_zero, zero_div]

theorem secondSquarefreeLog_normalized_cost
    (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (K : Finset ι → Finset ι → Finset O) (R : Finset ι) (X Y M : ℝ) (hX : 0 < X)
    (j : SecondLogIndex) (Ψ₁ Ψ₂ : O →* ℂ) (m : O) (V₁ V₂ : ℝ → ℂ) (J : ℕ) :
    (Y*primeProductNorm p R/X^2) *
      densityChildEnergy p hp hcop hg F Ψ₁ Ψ₂ m
        (secondSquarefreeLogTargets p B C D F v₁ v₂ ε₁ ε₂ K R X M j) V₁ V₂
        (secondLogX p R X j) (secondLogX p R X j) J =
    (Y*‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖^2*Real.exp 2/X) *
      secondSquarefreeLogNormalizedEnergy p hp hcop hg B C D F v₁ v₂ ε₁ ε₂ K R X M j Ψ₁ Ψ₂ m V₁ V₂ J := by
  unfold secondSquarefreeLogNormalizedEnergy
  rw [secondLogX_label_cost]
  have hR := (FirstPassCubeLabels.primeProductNorm_pos p hp R).ne'
  have hc := (zero_lt_one.trans_le (element_norm_ge_one _ (secondBaseLabel_ne_zero p hp B C v₁ v₂ ε₁ ε₂))).ne'
  have hcn : ‖eisEmbedding (secondBaseLabel p B C v₁ v₂ ε₁ ε₂)‖ ≠ 0 := by
    intro h; apply hc; rw [h]; norm_num
  field_simp

end SecondPassArithmetic

section

open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory
namespace SecondPassArithmetic

section
open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity)
open ConcreteTraceCRT (eisEmbedding)
open EisensteinSchwartzPoisson (paperRadialFourier)
open RayFourExpansion (RayCharacter crossCoeff)
open SecondPassIntegration (densityChildEnergy)

def firstCoreSquarefreeBudget
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (M ε : ℝ) (tailOrder decayOrder J : ℕ)
    (Y : ℝ) (A₀ B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (χ : RayCharacter) (Ψ : O →* ℂ) (m : O) (r₁ : FirstCoreIndex) (X Z : ℝ) : ℝ :=
  let v := fun i => v₁ i + v₂ i
  let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let Ψ' := firstCoreTwist negative χ Ψ r₁
  let m' := m * b0Label p B v ε₁ ε₂
  let c' := c * jLabel p B v ε₁ ε₂
  let X' := X / primeProductNorm p A₀
  let Usupp := X' * Real.exp M
  let K := firstCoreSecondCutoff p A₀ X Y M Z
  let Kmax := firstCoreSecondRowBound p D A₀ X Y M Z
  let Hbase := normalizedColumn p (fun S => firstCoreBaseProfile g V negative (columnLog p X' S))
  (primeProductNorm p A₀)⁻¹ *
    (|Y| * ‖paperRadialFourier rowMajorant 0‖ *
        (∑ G ∈ (F\A₀).powerset, ‖secondInputCoefficient p hg Ψ' m' c' d Hbase G‖^2) +
      (∑ z : SecondRayIndex, ∑ R ∈ boundedPrimeSupports p (F\A₀) Usupp,
        ∑ j ∈ secondLogBinBox Usupp Kmax,
        (Y * primeProductNorm p R / X'^2 * ‖secondRayCoefficient z‖ * Cw * Cₐ *
          (secondLogLabelBound p B C v₁ v₂ ε₁ ε₂ j *
            Ideal.absNorm (Ideal.span {b0Label p B v ε₁ ε₂}))^ε) *
        (Cₛ /
          (1+Y*secondLogK j*(primeProductNorm p R)^2/(primeProductNorm p D*X'^2))^decayOrder) *
        densityChildEnergy p hp hcop hg (F\A₀) (secondRayMinus Ψ' z) (secondRayPlus Ψ' z)
          (m' * primeSubsetGenerator (fun i => Ideal.span {p i}) R)
          (secondSquarefreeLogTargets p B C D (F\A₀) v₁ v₂ ε₁ ε₂ K R X' M j)
          (windows 5) (windows 6) (secondLogX p R X' j) (secondLogX p R X' j) J) +
      Ctail*(1+Usupp)^4*Y*(1+(1+Usupp)^3/Y)^2/(1+Z)^tailOrder)

theorem firstInputFamilyEnergy_squarefree_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (U : ℝ → ℂ) (hUc : HasCompactSupport U) (hUs : ContDiff ℝ ∞ U)
    (g V : 𝓢(ℝ, ℂ)) (negative : Bool) (hU : ∀ t, g t ≠ 0 → U t = 1)
    (M : ℝ) (hM : 0 ≤ M) (hgM : ∀ t, g t ≠ 0 → |t| ≤ M)
    (ε : ℝ) (hε : 0 < ε) (tailOrder decayOrder J : ℕ) :
    ∃ (windows : Fin 7 → ℝ → ℂ) (Cₐ Cₛ Cw Ctail : ℝ),
      0 < Cₐ ∧ 0 ≤ Cₛ ∧ 0 ≤ Cw ∧ 0 < Ctail ∧
      ∀ (Y : ℝ), 0 < Y →
      ∀ (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
        (Ψ : O →* ℂ) (m : O) (X Z : ℝ) (Srows : Finset O),
        (∀ i ∈ B, 0 < v₁ i + v₂ i) → Disjoint C B → D ⊆ C ∪ B →
        (∀ a : O, ‖Ψ a‖ ≤ 1) → 0 < X → 0 ≤ Z →
        (∀ z ∈ Srows, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
        (∀ z ∈ Srows, z ≠ 0) →
        firstInputFamilyEnergy p hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m
          (fun S => g (columnLog p X S)) V X
          (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
          (primeSubsetGenerator (fun i => Ideal.span {p i}) D) (2*(J+2)) Srows ≤
        (∫ t : ℝ, firstLogDensity 0 t) *
          ∑ a : RayCharacter × RayCharacter, ∑ A₀ ∈ F.powerset,
            ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
              ‖firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r‖ *
                firstCoreSquarefreeBudget p hp hcop hg windows Cₐ Cₛ Cw Ctail
                  g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
                  (if negative then a.1 else a.2) Ψ m r X Z := by
  obtain ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,hbound⟩ :=
    firstCoreInputRow_squarefree_binned_integrated_transfer p hp hcop hg hinj hc hpr U hUc hUs
      g V negative hU M hM hgM ε hε tailOrder decayOrder J
  refine ⟨windows,Cₐ,Cₛ,Cw,Ctail,hCₐ,hCₛ,hCw,hCtail,?_⟩
  intro Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ m X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  unfold firstInputFamilyEnergy
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a ha
  apply Finset.sum_le_sum
  intro A₀ hA₀
  apply Finset.sum_le_sum
  intro r hr
  have hb := hbound Y hY A₀ B C D F v₁ v₂ ε₁ ε₂ (if negative then a.1 else a.2)
    Ψ m r X Z Srows hv hCB hD hΨ hX hZ hSrows hSrows0
  have he : (∫ t : ℝ, firstLogDensity (2*(J+2)) t *
      ∑ z ∈ Srows, ‖firstCoreInputRow p hg F A₀ B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative
        (if negative then a.1 else a.2) Ψ m (normalizedColumn p (fun S => g (columnLog p X S)))
        V (columnLog p X) (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
        (primeSubsetGenerator (fun i => Ideal.span {p i}) D) r t z‖^2) ≤
      (∫ t : ℝ, firstLogDensity 0 t) *
        firstCoreSquarefreeBudget p hp hcop hg windows Cₐ Cₛ Cw Ctail
          g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
          (if negative then a.1 else a.2) Ψ m r X Z := by
    simpa only [firstCoreSquarefreeBudget, mul_assoc] using hb
  have hw := mul_le_mul_of_nonneg_left he (mul_nonneg (norm_nonneg (crossCoeff a.1 a.2))
    (norm_nonneg (firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r)))
  convert hw using 1 <;> (try simp only [Finset.mul_sum]) <;> ring

end

open ActualEisensteinCubic
open FirstPassCubeLabels (columnLog normalizedColumn primeProductNorm b0Label jLabel firstLogDensity
  actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)
open RayFourExpansion (RayCharacter crossCoeff)

structure SquarefreeBudgetData where
  windows : Fin 7 → ℝ → ℂ
  arithmetic : ℝ
  smooth : ℝ
  windowBound : ℝ
  tail : ℝ
  arithmetic_pos : 0 < arithmetic
  smooth_nonneg : 0 ≤ smooth
  windowBound_nonneg : 0 ≤ windowBound
  tail_pos : 0 < tail

def firstSquarefreeFamilyBudget {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (data : SquarefreeBudgetData)
    (g V : 𝓢(ℝ,ℂ)) (negative : Bool) (M ε : ℝ) (tailOrder decayOrder J : ℕ)
    (Y : ℝ) (B C D F : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (Ψ : O →* ℂ) (m : O) (X Z : ℝ) : ℝ :=
  ∑ a : RayCharacter × RayCharacter, ∑ A₀ ∈ F.powerset,
    ‖crossCoeff a.1 a.2‖ * ∑ r : FirstCoreIndex,
      ‖firstCoreOuter p hg B (fun i => v₁ i+v₂ i) ε₁ ε₂ negative Ψ m A₀ r‖ *
        firstCoreSquarefreeBudget p hp hcop hg data.windows data.arithmetic data.smooth data.windowBound data.tail
          g V negative M ε tailOrder decayOrder J Y A₀ B C D F v₁ v₂ ε₁ ε₂
          (if negative then a.1 else a.2) Ψ m r X Z

theorem first_passage_squarefree_child_transfer
    {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B C D : Finset ι) (hFB : Disjoint F B) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O)
    (hΨ₁ : ∀ a, ‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a, ‖Ψ₂ a‖ ≤ 1)
    (W g₁ g₂ V₁ V₂ : 𝓢(ℝ,ℂ))
    (U₁ U₂ : ℝ → ℂ) (hUc₁ : HasCompactSupport U₁) (hUs₁ : ContDiff ℝ ∞ U₁)
    (hUc₂ : HasCompactSupport U₂) (hUs₂ : ContDiff ℝ ∞ U₂)
    (hU₁ : ∀ t, g₁ t ≠ 0 → U₁ t=1) (hU₂ : ∀ t, g₂ t ≠ 0 → U₂ t=1)
    (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (M₁ M₂ N₁ N₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂) (hN₁ : 0 ≤ N₁) (hN₂ : 0 ≤ N₂)
    (hg₁ : ∀ t, g₁ t ≠ 0 → |t| ≤ M₁) (hg₂ : ∀ t, g₂ t ≠ 0 → |t| ≤ M₂)
    (hV₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ N₁) (hV₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ N₂)
    (ε deltaLoss : ℝ) (hε : 0 < ε) (hδ : 0 < deltaLoss) (tailOrder decayOrder J : ℕ) :
    ∃ (data₁ data₂ : SquarefreeBudgetData) (K₀ : ℝ), 0 ≤ K₀ ∧
      ∀ (lengthScale : ℝ), 0 < lengthScale → ∀ (s : Finset (Ideal O × O)) (T : Finset O)
        (w : Ideal O × O → ℂ) (M Y Z : ℝ),
      0 ≤ M → 0 < Y → 0 ≤ Z →
      (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      let c := primeSubsetGenerator (fun i => Ideal.span {p i}) C
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B (fun i => v₁ i+v₂ i) ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p X₁ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p X₂ S)))
          c (ConcretePrimeRowBridge.idealGenerator x.1)) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
  obtain ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁,hleft⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₁ hUc₁ hUs₁
      g₁ V₁ true hU₁ M₁ hM₁ hg₁ ε hε tailOrder decayOrder J
  obtain ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂,hright⟩ :=
    firstInputFamilyEnergy_squarefree_transfer p hp hcop hg hinj hc hpr U₂ hUc₂ hUs₂
      g₂ V₂ false hU₂ M₂ hM₂ hg₂ ε hε tailOrder decayOrder J
  let data₁ : SquarefreeBudgetData := ⟨windows₁,A₁,S₁,H₁,Q₁,hA₁,hS₁,hH₁,hQ₁⟩
  let data₂ : SquarefreeBudgetData := ⟨windows₂,A₂,S₂,H₂,Q₂,hA₂,hS₂,hH₂,hQ₂⟩
  obtain ⟨K₀,hK₀,hfirst⟩ := first_passage_transfer_input_family p hp hinj hcop hg hc hpr
    F B hFB (fun i => v₁ i+v₂ i) ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂
    (fun S => g₁ (columnLog p X₁ S)) (fun S => g₂ (columnLog p X₂ S))
    (fun G hG => hΨ₁ _) (fun G hG => hΨ₂ _) W V₁ V₂ X₁ X₂ hX₁ hX₂
    N₁ N₂ hN₁ hN₂ hV₁ hV₂ (2*(J+2)) deltaLoss hδ
  let I₀ : ℝ := ∫ t, firstLogDensity 0 t
  have hI₀ : 0 ≤ I₀ := integral_nonneg (FirstPassCubeLabels.firstLogDensity_nonneg 0)
  refine ⟨data₁,data₂,K₀*I₀,mul_nonneg hK₀ hI₀,?_⟩
  intro lengthScale hL s T w M Y Z hM hY hZ hs hs0 hmap hT0 hT hw
  dsimp only
  have h₁ := hleft Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z T hv hCB hD hΨ₁ hX₁ hZ hT hT0
  have h₂ := hright Y hY B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z T hv hCB hD hΨ₂ hX₂ hZ hT hT0
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z at h₁
  change _ ≤ I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
    tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z at h₂
  have hb := hfirst lengthScale hL (primeSubsetGenerator (fun i => Ideal.span {p i}) C)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) D) (primeSubsetGenerator_ne_zero _ _)
    s T w M Y hM hY.le hs hs0 hmap hT0 hT hw
  apply hb.trans
  calc
    _ ≤ (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
        (M*K₀*Y^deltaLoss) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
        Real.sqrt (I₀*firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
          tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul hI₀, Real.sqrt_mul hI₀]
      calc
        _ = (lengthScale/‖eisEmbedding (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖) *
          (M*K₀*Y^deltaLoss) * (Real.sqrt I₀)^2 *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₁ g₁ V₁ true M₁ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₁ m₁ X₁ Z) *
          Real.sqrt (firstSquarefreeFamilyBudget p hp hcop hg data₂ g₂ V₂ false M₂ ε
            tailOrder decayOrder J Y B C D F v₁ v₂ ε₁ ε₂ Ψ₂ m₂ X₂ Z) := by ring
        _ = _ := by rw [Real.sq_sqrt hI₀]; ring

end SecondPassArithmetic

namespace FirstPassCubeLabels

section
open ActualEisensteinCubic
open ConcreteTraceCRT (eisEmbedding eisEmbedding_ne_zero)

theorem actual_first_kernel_full_uniform_envelope
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
      (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ C₁ C₂ : Finset ι → ℂ,
        ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
        (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂ lengthScale hL d h hd hh
  have hR : 0 < firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h := by
    unfold firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hsep, hb⟩ := hs _ hR
  refine ⟨b, hb, ?_⟩
  intro C₁ C₂
  rw [actualFirstKernel_eq_separated p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    C₁ C₂ W V₁ V₂ X₁ X₂ hX₁ hX₂ lengthScale d h b hsep, norm_mul]
  have hi := cube_integral_norm_le_energy p hg F
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ true
      (normalizedColumn p C₁) V₁ (columnLog p X₁) t d)
    (fun t => cubeLogCoefficient p hp hcop hg B v ε₁ ε₂ false
      (normalizedColumn p C₂) V₂ (columnLog p X₂) t d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hp hcop hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => norm_cubeLogCoefficient_eq_zero p hp hcop hg B v ε₁ ε₂ false _ _ _ t d S)
    h b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
    abs_of_nonneg (norm_nonneg _)]
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left hi (div_nonneg hL.le (norm_nonneg _))

end

open ActualEisensteinCubic
open RayFourExpansion (RayCharacter crossCoeff)
open ConcreteTraceCRT (eisEmbedding)

theorem first_passage_full_uniform_transfer
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (C₁ C₂ : Finset ι → ℂ) (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T) *
        Real.sqrt (firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T) := by
  obtain ⟨H, hH, hsep⟩ := actual_first_kernel_full_uniform_envelope
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ 0 J
  obtain ⟨K, hK, hpush⟩ := first_column_energy_integral deltaLoss hδ
  refine ⟨H * K, mul_nonneg hH hK.le, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv C₁ C₂ X₁ X₂ hX₁ hX₂
  have hsep := hsep p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  let A₁ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ true C₁ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let A₂ := fun x : Ideal O × O => originalLabelColumn p hg B ε₁ ε₂ false C₂ c (ConcretePrimeRowBridge.idealGenerator x.1)
  let q := lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖
  have hq : 0 ≤ q := div_nonneg hL.le (norm_nonneg _)
  have hfam : ∀ x : Ideal O × O, ∃ b : 𝓢(ℝ, ℂ), x ∈ s →
      (∀ t : ℝ, ‖b t‖ ≤ H * firstLogDensity J t) ∧
      ‖actualFirstKernel p hp hcop hg F B v ε₁ ε₂ (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
        q * Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 b) *
          Real.sqrt (firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 b) := by
    intro x
    by_cases hx : x ∈ s
    · obtain ⟨b, hb, hk⟩ := hsep lengthScale hL d x.2 hd (hnonzero x hx)
      refine ⟨b, fun _ => ⟨?_, hk (A₁ x) (A₂ x)⟩⟩
      simpa only [pow_zero, one_mul] using hb
    · exact ⟨0, fun hx' => (hx hx').elim⟩
  choose b hb using hfam
  let E₁ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ true (A₁ x) V₁ X₁ d x.2 (b x)
  let E₂ := fun x => firstColumnEnergy p hp hcop hg F B v ε₁ ε₂ false (A₂ x) V₂ X₂ d x.2 (b x)
  let O₁ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true C₁ V₁ X₁ c d J T
  let O₂ := firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false C₂ V₂ X₂ c d J T
  let P := M * H * K * Y ^ deltaLoss
  have hP : 0 ≤ P := mul_nonneg (mul_nonneg (mul_nonneg hM hH) hK.le) (Real.rpow_nonneg hY deltaLoss)
  have hE₁ (x) : 0 ≤ E₁ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ true _ _ _ _ _ _
  have hE₂ (x) : 0 ≤ E₂ x := firstColumnEnergy_nonneg p hp hcop hg F B v ε₁ ε₂ false _ _ _ _ _ _
  have hdom : ∀ x ∈ s, ∀ t : ℝ, ‖b x t‖ ≤ H * firstLogDensity J t := fun x hx => (hb x hx).1
  have hsum₁ : (∑ x ∈ s, ‖w x‖ * E₁ x) ≤ P * O₁ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv true C₁ V₁ X₁ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hsum₂ : (∑ x ∈ s, ‖w x‖ * E₂ x) ≤ P * O₂ :=
    hpush p hp hinj hcop hg hc F B v ε₁ ε₂ hv false C₂ V₂ X₂ c d s T w b J M H Y
      hM hH hY hs hmap hT hnorm hw hdom
  have hterm (x) : ‖w x‖ * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) =
      Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x) := by
    rw [Real.sqrt_mul (norm_nonneg _), Real.sqrt_mul (norm_nonneg _)]
    calc
      _ = (Real.sqrt ‖w x‖) ^ 2 * (Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) := by
        rw [Real.sq_sqrt (norm_nonneg _)]
      _ = _ := by ring
  calc
    _ ≤ ∑ x ∈ s, ‖w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (A₁ x) (A₂ x) W V₁ V₂ X₁ X₂ lengthScale d x.2‖ := norm_sum_le _ _
    _ ≤ ∑ x ∈ s, q * (Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [norm_mul, ← hterm]
      calc
        _ ≤ ‖w x‖ * (q * Real.sqrt (E₁ x) * Real.sqrt (E₂ x)) :=
          mul_le_mul_of_nonneg_left (hb x hx).2 (norm_nonneg _)
        _ = _ := by ring
    _ = q * (∑ x ∈ s, Real.sqrt (‖w x‖ * E₁ x) * Real.sqrt (‖w x‖ * E₂ x)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ q * (Real.sqrt (∑ x ∈ s, ‖w x‖ * E₁ x) * Real.sqrt (∑ x ∈ s, ‖w x‖ * E₂ x)) :=
      mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le s
        (fun x => mul_nonneg (norm_nonneg _) (hE₁ x))
        (fun x => mul_nonneg (norm_nonneg _) (hE₂ x))) hq
    _ ≤ q * (Real.sqrt (P * O₁) * Real.sqrt (P * O₂)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.sqrt_le_sqrt hsum₁) (Real.sqrt_le_sqrt hsum₂)
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hq
    _ = _ := by
      rw [Real.sqrt_mul hP, Real.sqrt_mul hP]
      calc
        _ = q * (Real.sqrt P)^2 * Real.sqrt O₁ * Real.sqrt O₂ := by ring
        _ = _ := by rw [Real.sq_sqrt hP]; dsimp only [P]; ring

end FirstPassCubeLabels
end

open scoped BigOperators Classical SchwartzMap
namespace SecondPassArithmetic
open ActualEisensteinCubic
open FirstPassCubeLabels (actualFirstKernel originalLabelColumn cubeActiveSupport dilationLabel)
open ConcreteTraceCRT (eisEmbedding)

theorem first_passage_full_uniform_input_family
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (_hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (_hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (_hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B, 0 < v j)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (H₁ H₂ : Finset ι → ℂ)
      (_hΨ₁ : ∀ D ∈ F.powerset, ‖Ψ₁ (∏ i ∈ D, p i)‖ ≤ 1)
      (_hΨ₂ : ∀ D ∈ F.powerset, ‖Ψ₂ (∏ i ∈ D, p i)‖ ≤ 1)
      (X₁ X₂ : ℝ) (_hX₁ : 0 < X₁) (_hX₂ : 0 < X₂),
      ∀ lengthScale : ℝ, 0 < lengthScale → ∀ c d : O, d ≠ 0 →
      ∀ (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ s, Squarefree x.1) → (∀ x ∈ s, x.2 ≠ 0) →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      ‖∑ x ∈ s, w x * actualFirstKernel p hp hcop hg F B v ε₁ ε₂
        (originalLabelColumn p hg B ε₁ ε₂ true (multiplicativeCoreColumn p Ψ₁ m₁ H₁)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        (originalLabelColumn p hg B ε₁ ε₂ false (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
          c (ConcretePrimeRowBridge.idealGenerator x.1))
        W V₁ V₂ X₁ X₂ lengthScale d x.2‖ ≤
      (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
  obtain ⟨K, hK, hb⟩ := FirstPassCubeLabels.first_passage_full_uniform_transfer
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨(32 * 512) * K, mul_nonneg (by norm_num) hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ hΨ₁ hΨ₂ X₁ X₂ hX₁ hX₂
  have hb := hb p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ hv
    (multiplicativeCoreColumn p Ψ₁ m₁ H₁) (multiplicativeCoreColumn p Ψ₂ m₂ H₂)
    X₁ X₂ hX₁ hX₂
  intro lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have hf := hb lengthScale hL c d hd s T w M Y hM hY hs hnonzero hmap hT hnorm hw
  have h₁ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ true
    Ψ₁ m₁ H₁ V₁ X₁ c d J T hΨ₁
  have h₂ := firstOutputEnergy_le_input_family p hp hcop hg hc hpr F B v ε₁ ε₂ false
    Ψ₂ m₂ H₂ V₂ X₂ c d J T hΨ₂
  have hq : 0 ≤ lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ :=
    div_nonneg hL.le (norm_nonneg _)
  have hfactor : 0 ≤ M * K * Y ^ deltaLoss :=
    mul_nonneg (mul_nonneg hM hK) (Real.rpow_nonneg hY deltaLoss)
  calc
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ true
          (multiplicativeCoreColumn p Ψ₁ m₁ H₁) V₁ X₁ c d J T) *
        Real.sqrt (FirstPassCubeLabels.firstOutputEnergy p hp hcop hg F B v ε₁ ε₂ false
          (multiplicativeCoreColumn p Ψ₂ m₂ H₂) V₂ X₂ c d J T) := hf
    _ ≤ (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
        Real.sqrt ((32 * 512) * firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by
      gcongr
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 32 * 512)]
      calc
        _ = (lengthScale / ‖eisEmbedding (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) * (M * K * Y ^ deltaLoss) *
            (Real.sqrt (32 * 512)) ^ 2 *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ true Ψ₁ m₁ H₁ V₁ X₁ c d J T) *
            Real.sqrt (firstInputFamilyEnergy p hg F B v ε₁ ε₂ false Ψ₂ m₂ H₂ V₂ X₂ c d J T) := by ring
        _ = _ := by rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 32 * 512)]; ring

end SecondPassArithmetic

end

end OAI
end OAIOriginalModule0165

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.PrincipalMajorants
Source SHA256: 00d49e81128d8e6997b8f8c954b7a9d30fbd702045a062d5d02d6eb44d57711d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0166



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

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

def smallPrincipalMajorant {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ) : ℝ :=
  ((columnDyadicLength N+1:ℕ):ℝ)^2 *
    (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
      (M/F+(2*U)*Real.sqrt (M/F)*B^(α-1/2)))

lemma smallPrincipalMajorant_nonneg {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U : ℝ) (a : n → ℂ) (b : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U) :
    0 ≤ smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  positivity

lemma smallPrincipalMajorant_mono {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B' B N M F U : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB' : 0 ≤ B') (hB : B' ≤ B) (hN : 0 ≤ N) (hM : 0 ≤ M) (hF : 0 ≤ F) (hU : 0 ≤ U)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    smallPrincipalMajorant hexp deltaLoss hδ ε hε B' N M F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have ha0 : 0 ≤ α-1/2 := by linarith
  have hB0 : 0 ≤ B := hB'.trans hB
  unfold smallPrincipalMajorant
  gcongr

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedSmallPrincipalSum
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors (left j*right k), if P d i then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedSmallPrincipalSum_sector
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (P : Ideal O → m → Prop)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    unrestrictedSmallPrincipalSum rows left right a b M F P =
      signedProductDivisorSum (fun i => goodSquarefreePart (rows i)) left right
        (fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
        (fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))) P
        (fun _ _ j k => ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ)) := by
  unfold unrestrictedSmallPrincipalSum signedProductDivisorSum
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]

theorem HasSieveExponent.small_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedSmallPrincipalSum rows left right a b M F P‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedSmallPrincipalSum, Finset.univ_eq_empty, Finset.sum_empty, norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F U a b (by linarith) (by linarith) hM.le hF.le hU
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i):ℝ) = Q*(Ideal.absNorm (good i):ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul,Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B/Q)/2 ≤ (Ideal.absNorm (good i):ℝ) ∧
        (Ideal.absNorm (good i):ℝ) ≤ B/Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B/Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀):ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hPg (d : Ideal O) (i : m) (hp : P d i) : (Ideal.absNorm d:ℝ) ≤
        U*(N*Real.sqrt (F/(M*(Ideal.absNorm (good i):ℝ)))) := by
      apply (hP d i hp).trans
      have hgoodpos : 0 < (Ideal.absNorm (good i):ℝ) := by
        exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => (hg i).1.1 (Ideal.absNorm_eq_zero_iff.mp h))
      have hng : (Ideal.absNorm (good i):ℝ) ≤ (Ideal.absNorm (rows i):ℝ) :=
        Nat.cast_le.mpr (goodSquarefreePart_norm_le (rows i) (hrows i).1)
      gcongr
    rw [unrestrictedSmallPrincipalSum_sector rows left right a b M F P
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE]
    have hbnd := hexp.small_principal_divisor_sum deltaLoss hδ ε hε (B/Q) N M F U hBQ hN hM hF hU
      good left right hgr hl hri hg hleft hright a' b' P hPg
    change ‖signedProductDivisorSum good left right a' b' P _‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b
    apply hbnd.trans
    apply smallPrincipalMajorant_mono hexp hα deltaLoss hδ ε hε (B/Q) B N M F U a a' b b'
      (by positivity) (div_le_self (by linarith) hQ) (by linarith) hM.le hF.le hU
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem HasSieveExponent.unrestricted_small_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F U : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ N/2 ≤ (Ideal.absNorm (left j):ℝ) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ N/2 ≤ (Ideal.absNorm (right k):ℝ) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (P : Ideal O → m → Prop)
    (hP : ∀ d i, P d i → (Ideal.absNorm d:ℝ) ≤ U*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) :
    ‖unrestrictedSmallPrincipalSum rows left right a b M F P‖ ≤
      4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedSmallPrincipalSum rows left right a b M F P =
      ∑ E : fixedBadPrimes.powerset, unrestrictedSmallPrincipalSum
        (fun i : {i // σ i = E} => rows i.val) left right a b M F (fun d i => P d i.val) := by
    unfold unrestrictedSmallPrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedSmallPrincipalSum (fun i : {i // σ i = E} => rows i.val)
        left right a b M F (fun d i => P d i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
    hexp.small_principal_sector hα deltaLoss hδ ε hε B N M F U hB hN hM hF hU
      (fun i : {i // σ i = E} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun d i => P d i.val) (fun d i => hP d i.val)
      E (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _E : fixedBadPrimes.powerset, smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_coe, fixedBadPrimes_powerset_card]
      norm_num

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

theorem weightedDivisorCorrection_coprime_mask (G C : Ideal O)
    (hG : G ≠ 0) (hC : C ≠ 0) (hGC : IsCoprime G C) (X Z : ℝ) :
    (∑ d ∈ idealDivisors (G*C), if Z < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*((X/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
    ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      ∑ d ∈ idealDivisors C, if Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((X/(Ideal.absNorm q:ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 := by
  classical
  rw [QuadraticDivisorSplit.sum_divisors_coprime_product G C hG hC hGC]
  apply Finset.sum_congr rfl
  intro q hq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hqG := (mem_idealDivisors hG).mp hq
  have hdC := (mem_idealDivisors hC).mp hd
  have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
  have hNq : 0 < (Ideal.absNorm q:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
  have hlow : Z < (Ideal.absNorm q:ℝ)*(Ideal.absNorm d:ℝ) ↔
      Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) := by
    constructor
    · intro hz
      apply (div_lt_iff₀ hNq).mpr
      simpa only [mul_comm] using hz
    · intro hz
      simpa only [mul_comm] using (div_lt_iff₀ hNq).mp hz
  simp only [map_mul,Nat.cast_mul,hlow,(hGC.mono hqG hdC).isRelPrime.moebius_mul,Int.cast_mul]
  by_cases hp : Z/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ)
  · simp only [hp,ite_true]
    push_cast
    ring
  · simp only [hp,ite_false,mul_zero]

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def maskedPrincipalDivisorCorrection (G : Ideal O)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, originalTerm rows left right a b 1 1 i j k *
    ∑ d ∈ idealDivisors (G*(left j*right k)), if Z i < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem maskedPrincipalDivisorCorrection_eq
    (G : Ideal O) (hG : G ≠ 0)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M : ℝ) (hM : 0 ≤ M) (Z : m → ℝ)
    (hleft : ∀ j, left j ≠ 0) (hright : ∀ k, right k ≠ 0)
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k)) :
    maskedPrincipalDivisorCorrection G rows left right a b M Z =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        principalDivisorCorrection rows left right a b (M/(Ideal.absNorm q:ℝ)^2)
          (fun d i => Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ)) := by
  classical
  have ht (i : m) (j : n) (k : p) :
      (∑ d ∈ idealDivisors (G*(left j*right k)), if Z i < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*
          ((Real.sqrt (M/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        ∑ d ∈ idealDivisors (left j*right k), if Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((Real.sqrt ((M/(Ideal.absNorm q:ℝ)^2)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0 := by
    rw [weightedDivisorCorrection_coprime_mask G _ hG (mul_ne_zero (hleft j) (hright k))
      ((hGl j).mul_right (hGr k))]
    apply Finset.sum_congr rfl
    intro q hq
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
    have hNq : 0 < (Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    rw [sqrt_norm_divisor_scale M _ _ hM (Nat.cast_nonneg _) hNq]
  unfold maskedPrincipalDivisorCorrection
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ:Finset p)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ:Finset n)) (t := idealDivisors G),
    Finset.sum_comm (s := (Finset.univ:Finset m)) (t := idealDivisors G)]
  simp only [principalDivisorCorrection,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring_nf

theorem HasSieveExponent.masked_source_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε) (G : Ideal O) (hG : G ≠ 0)
    (B N M T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hT : 0 < T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Admissible (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hGl : ∀ j, IsCoprime G (left j)) (hGr : ∀ k, IsCoprime G (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)) ≤ Z i) :
    ‖maskedPrincipalDivisorCorrection G rows left right a b M Z‖ ≤
      (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
        (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
          (4*N/T+Real.sqrt M*B^(α-1/2)))) := by
  classical
  let V := ((columnDyadicLength N+1:ℕ):ℝ)^2 *
    (2*divisorEnergyFactor ε hε N a b*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
      (4*N/T+Real.sqrt M*B^(α-1/2)))
  have hqbound (q : Ideal O) (hq : q ∈ idealDivisors G) :
      ‖principalDivisorCorrection rows left right a b (M/(Ideal.absNorm q:ℝ)^2)
        (fun d i => Z i/(Ideal.absNorm q:ℝ) < (Ideal.absNorm d:ℝ))‖ ≤ V := by
    have hqG := (mem_idealDivisors hG).mp hq
    have hq0 : q ≠ 0 := by intro he; rw [he,zero_dvd_iff] at hqG; exact hG hqG
    have hq1 : 1 ≤ (Ideal.absNorm q:ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun he => hq0 (Ideal.absNorm_eq_zero_iff.mp he))
    have hqpos : 0 < (Ideal.absNorm q:ℝ) := by linarith
    have hZq (i : m) : T*Real.sqrt ((M/(Ideal.absNorm q:ℝ)^2)/(Ideal.absNorm (rows i):ℝ)) ≤
        Z i/(Ideal.absNorm q:ℝ) := by
      rw [←sqrt_norm_divisor_scale M _ _ hM.le (Nat.cast_nonneg _) hqpos]
      calc
        _ = (T*Real.sqrt (M/(Ideal.absNorm (rows i):ℝ)))/(Ideal.absNorm q:ℝ) := by ring
        _ ≤ _ := div_le_div_of_nonneg_right (hZ i) hqpos.le
    apply (hexp.source_large_principal_sum deltaLoss hδ ε hε B N (M/(Ideal.absNorm q:ℝ)^2) T
      hB hN (by positivity) hT rows left right hr hl hri hrows hleft hright a b
        (fun i => Z i/(Ideal.absNorm q:ℝ)) hZq).trans
    have he := divisorEnergyFactor_nonneg ε hε N a b
    have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
    dsimp only [V]
    gcongr
    exact div_le_self hM.le (one_le_pow₀ hq1)
  rw [maskedPrincipalDivisorCorrection_eq G hG rows left right a b M hM.le Z
    (fun j => (hleft j).1.1) (fun k => (hright k).1.1) hGl hGr]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ q ∈ idealDivisors G, V := by
      apply Finset.sum_le_sum
      intro q hq
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (QuadraticInitialBound.norm_ideal_moebius_le_one q)).trans (hqbound q hq)
    _ = _ := by simp only [Finset.sum_const,nsmul_eq_mul,V]

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson CompletedGauss
open IdealMobiusDivisorSum

lemma smallPrincipalMajorant_bad_scale {n p : Type} [Fintype n] [Fintype p]
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss)
    (ε : ℝ) (hε : 0 < ε) (B N M F U Q : ℝ) (a a' : n → ℂ) (b b' : p → ℂ)
    (hB : 0 ≤ B) (hN : 0 ≤ N) (hM : 0 < M) (hF : 0 < F) (hU : 0 ≤ U) (hQ : 1 ≤ Q)
    (ha : ∀ j, ‖a' j‖ ≤ ‖a j‖) (hb : ∀ k, ‖b' k‖ ≤ ‖b k‖) :
    (1/Q)*smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F U a' b' ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F U a b := by
  have hQp : 0 < Q := by linarith
  have he := divisorEnergyFactor_mono_coefficients ε hε N a a' b b' ha hb
  have hp : ((B/Q)*N)^deltaLoss ≤ (B*N)^deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    exact mul_le_mul_of_nonneg_right (div_le_self hB hQ) hN
  have hs := dual_bad_sector_scale M F B Q U α hM hF hB hQ hU hα
  have he0 := divisorEnergyFactor_nonneg ε hε N a' b'
  have he1 := divisorEnergyFactor_nonneg ε hε N a b
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  unfold smallPrincipalMajorant
  calc
    _ = ((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a' b'*(divisorExponentConstant hexp deltaLoss hδ*((B/Q)*N)^deltaLoss)*
        ((1/Q)*(M*Q/F+(2*U)*Real.sqrt (M*Q/F)*(B/Q)^(α-1/2)))) := by ring
    _ ≤ _ := by gcongr

lemma sqrt_sector_scale (M F Q b : ℝ) (hM : 0 < M) (hF : 0 < F) (hQ : 0 < Q) (hb : 0 < b) :
    Real.sqrt ((M/F)/(Q*b)) = (1/Q)*Real.sqrt (((M*Q)/F)/b) := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
  rw [mul_pow,Real.sq_sqrt (show 0 ≤ (M/F)/(Q*b) by positivity),
    Real.sq_sqrt (show 0 ≤ ((M*Q)/F)/b by positivity)]
  field_simp

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedLargePrincipalSum
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ := by
  classical
  exact ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ∑ d ∈ idealDivisors (left j*right k), if Z i < (Ideal.absNorm d:ℝ) then
      (UniqueFactorizationMonoid.moebius d:ℂ)*
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
lemma unrestrictedLargePrincipalSum_sector
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, Squarefree (rows i)) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k))
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) (hQ : sectorBadIdeal E ≠ 0) :
    unrestrictedLargePrincipalSum rows left right a b M F Z =
      ((1/(Ideal.absNorm (sectorBadIdeal E):ℝ):ℝ):ℂ)*
        principalDivisorCorrection (fun i => goodSquarefreePart (rows i)) left right
          (fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E)))
          (fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E)))
          ((M*(Ideal.absNorm (sectorBadIdeal E):ℝ))/F) (fun d i => Z i < (Ideal.absNorm d:ℝ)) := by
  classical
  have hQp : 0 < (Ideal.absNorm (sectorBadIdeal E):ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hQ (Ideal.absNorm_eq_zero_iff.mp h))
  unfold unrestrictedLargePrincipalSum principalDivisorCorrection
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [unrestrictedPairTerm_sector rows left right a b hrows hleft hright hray E hE i j k]
  have hn : (Ideal.absNorm (rows i):ℝ) =
      (Ideal.absNorm (sectorBadIdeal E):ℝ)*(Ideal.absNorm (goodSquarefreePart (rows i)):ℝ) := by
    have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
      (sector_bad_good_product (rows i) (hrows i) E (hE i))
    simpa only [map_mul,Nat.cast_mul] using hi.symm
  have hgpos : 0 < (Ideal.absNorm (goodSquarefreePart (rows i)):ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h =>
      (goodSquarefreePart_admissible (rows i)).1 (Ideal.absNorm_eq_zero_iff.mp h))
  rw [hn,sqrt_sector_scale M F _ _ hM hF hQp hgpos]
  apply Finset.sum_congr rfl
  intro d _
  by_cases hd : Z i < (Ideal.absNorm d:ℝ)
  · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_mul]
    ring
  · simp only [hd,ite_false,mul_zero]

theorem HasSieveExponent.large_principal_sector {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i)
    (E : fixedBadPrimes.powerset) (hE : ∀ i, badPrimeSector (rows i) = E) :
    ‖unrestrictedLargePrincipalSum rows left right a b M F Z‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  cases isEmpty_or_nonempty m with
  | inl hempty =>
    let := hempty
    simp only [unrestrictedLargePrincipalSum,Finset.univ_eq_empty,Finset.sum_empty,norm_zero]
    exact smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a b
      (by linarith) (by linarith) hM.le hF.le (by norm_num)
  | inr hnonempty =>
    let := hnonempty
    let i₀ : m := Classical.choice hnonempty
    let Q : ℝ := Ideal.absNorm (sectorBadIdeal E)
    let good := fun i => goodSquarefreePart (rows i)
    let a' := fun j => a j*quadraticRow (left j) (idealGenerator (sectorBadIdeal E))
    let b' := fun k => b k*quadraticRow (right k) (idealGenerator (sectorBadIdeal E))
    have hQnz := sectorBadIdeal_ne_zero_of_row (rows i₀) (hrows i₀).1 E (hE i₀)
    have hQ : 1 ≤ Q := by
      dsimp only [Q]
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => hQnz (Ideal.absNorm_eq_zero_iff.mp h)))
    have hQp : 0 < Q := by linarith
    have hn (i : m) : (Ideal.absNorm (rows i):ℝ) = Q*(Ideal.absNorm (good i):ℝ) := by
      have hi := congrArg (fun I : Ideal O => (Ideal.absNorm I:ℝ))
        (sector_bad_good_product (rows i) (hrows i).1 E (hE i))
      simpa only [map_mul,Nat.cast_mul] using hi.symm
    have hgr : Function.Injective good := by
      intro i k h
      exact hr (goodSquarefreePart_injective_on_sector _ _ (hrows i).1 (hrows k).1
        ((hE i).trans (hE k).symm) h)
    have hg (i : m) : Admissible (good i) ∧ (B/Q)/2 ≤ (Ideal.absNorm (good i):ℝ) ∧
        (Ideal.absNorm (good i):ℝ) ≤ B/Q := by
      refine ⟨goodSquarefreePart_admissible _, ?_, ?_⟩
      · rw [show B/Q/2 = (B/2)/Q by ring]
        apply (div_le_iff₀ hQp).2
        have hx := (hrows i).2.1
        rw [hn i] at hx
        nlinarith
      · exact (le_div_iff₀ hQp).2 (by simpa only [mul_comm] using (hn i).symm.trans_le (hrows i).2.2)
    have hBQ : 1 ≤ B/Q := by
      have hh : 1 ≤ (Ideal.absNorm (good i₀):ℝ) := by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (fun h => (hg i₀).1.1 (Ideal.absNorm_eq_zero_iff.mp h)))
      exact hh.trans (hg i₀).2.2
    have hZg (i : m) : T*(N*Real.sqrt (F/((M*Q)*(Ideal.absNorm (good i):ℝ)))) ≤ Z i := by
      simpa only [hn i,mul_assoc] using hZ i
    have hbnd := hexp.dual_large_principal_sum deltaLoss hδ ε hε (B/Q) N (M*Q) F T hBQ hN
      (by positivity) hF (by linarith) good left right hgr hl hri hg hleft hright a' b' Z hZg
    have hmajor : ‖principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d:ℝ))‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε (B/Q) N (M*Q) F (1/2) a' b' := by
      apply hbnd.trans
      have ht : 4/T ≤ 1 := (div_le_one (by linarith : 0<T)).mpr hT
      have hlead : 4*(M*Q)/(F*T) ≤ (M*Q)/F := by
        calc
          _ = ((M*Q)/F)*(4/T) := by ring
          _ ≤ _ := mul_le_of_le_one_right (by positivity) ht
      have he := divisorEnergyFactor_nonneg ε hε N a' b'
      have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
      unfold smallPrincipalMajorant
      norm_num only [show (2:ℝ)*(1/2)=1 by norm_num,one_mul]
      gcongr
    have htr := unrestrictedLargePrincipalSum_sector rows left right a b M F Z hM hF
      (fun i => (hrows i).1) (fun j => (hleft j).1) (fun k => (hright k).1) hray E hE hQnz
    change unrestrictedLargePrincipalSum rows left right a b M F Z =
      ((1/Q:ℝ):ℂ)*principalDivisorCorrection good left right a' b' ((M*Q)/F)
        (fun d i => Z i < (Ideal.absNorm d:ℝ)) at htr
    rw [htr,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity : 0≤1/Q)]
    apply (mul_le_mul_of_nonneg_left hmajor (by positivity)).trans
    apply smallPrincipalMajorant_bad_scale hexp hα deltaLoss hδ ε hε B N M F (1/2) Q a a' b b'
      (by linarith) (by linarith) hM hF (by norm_num) hQ
    · intro j
      dsimp only [a']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)
    · intro k
      dsimp only [b']; rw [norm_mul]
      exact mul_le_of_le_one_right (norm_nonneg _) (quadraticRow_norm_le_one _ _)

theorem HasSieveExponent.unrestricted_large_principal_sum {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (B N M F T : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N) (hM : 0 < M) (hF : 0 < F) (hT : 4 ≤ T)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (hr : Function.Injective rows) (hl : Function.Injective left) (hri : Function.Injective right)
    (hrows : ∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B)
    (hleft : ∀ j, Admissible (left j) ∧ (Ideal.absNorm (left j):ℝ) ≤ N)
    (hright : ∀ k, Admissible (right k) ∧ (Ideal.absNorm (right k):ℝ) ≤ N)
    (hray : ∀ j k, columnRay (left j) = columnRay (right k))
    (a : n → ℂ) (b : p → ℂ) (Z : m → ℝ)
    (hZ : ∀ i, T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ)))) ≤ Z i) :
    ‖unrestrictedLargePrincipalSum rows left right a b M F Z‖ ≤
      4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b := by
  classical
  let σ := fun i => badPrimeSector (rows i)
  have hs : unrestrictedLargePrincipalSum rows left right a b M F Z =
      ∑ E : fixedBadPrimes.powerset, unrestrictedLargePrincipalSum
        (fun i : {i // σ i = E} => rows i.val) left right a b M F (fun i => Z i.val) := by
    unfold unrestrictedLargePrincipalSum
    exact (Fintype.sum_fiberwise σ _).symm
  have hb (E : fixedBadPrimes.powerset) :
      ‖unrestrictedLargePrincipalSum (fun i : {i // σ i = E} => rows i.val)
        left right a b M F (fun i => Z i.val)‖ ≤
      smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
    hexp.large_principal_sector hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
      (fun i : {i // σ i = E} => rows i.val) left right (fun i k h => Subtype.ext (hr h)) hl hri
      (fun i => hrows i.val) hleft hright hray a b (fun i => Z i.val) (fun i => hZ i.val)
      E (fun i => i.property)
  rw [hs]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _E : fixedBadPrimes.powerset, smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a b :=
      Finset.sum_le_sum (fun E _ => hb E)
    _ = _ := by
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Fintype.card_coe,fixedBadPrimes_powerset_card]
      norm_num

end

open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

lemma unrestrictedPairTerm_norm_le {m n p : Type}
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (i : m) (j : n) (k : p) :
    ‖unrestrictedPairTerm rows left right a b i j k‖ ≤ ‖a j‖*‖b k‖ := by
  classical
  unfold unrestrictedPairTerm
  split_ifs with hc
  · simp only [unrestrictedPairCharacter,norm_mul,norm_star]
    calc
      _ ≤ (‖a j‖*‖b k‖)*(1*1) := mul_le_mul_of_nonneg_left
        (mul_le_mul (quadraticRow_norm_le_one _ _) (quadraticRow_norm_le_one _ _)
          (norm_nonneg _) (by norm_num)) (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]
    positivity

theorem unrestricted_pair_error_energy {m n : Type} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ ≤
      Fintype.card m * Fintype.card n * E * ∑ j, ‖a j‖ ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun j : n => ‖a j‖) (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at hcs
  have hs : (∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E) = (∑ j, ‖a j‖) ^ 2 * E := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    ring
  calc
    _ ≤ ∑ i, ∑ j, ∑ k, ‖unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i hi
      apply (norm_sum_le _ _).trans
      exact Finset.sum_le_sum (fun j hj => norm_sum_le _ _)
    _ ≤ ∑ _i : m, ∑ j, ∑ k, ‖a j‖ * ‖a k‖ * E := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_mul]
      exact mul_le_mul (unrestrictedPairTerm_norm_le rows cols cols a a i j k) (herr i j k)
        (norm_nonneg _) (by positivity)
    _ = (Fintype.card m : ℝ) * ((∑ j, ‖a j‖) ^ 2 * E) := by
      simp only [hs, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ (Fintype.card m : ℝ) * (((∑ j, ‖a j‖ ^ 2) * Fintype.card n) * E) := by gcongr
    _ = _ := by ring

theorem unrestricted_pair_error_ideal_bound {m n : Type} [Fintype m] [Fintype n]
    (rows : m → Ideal O) (cols : n → Ideal O) (hr : Function.Injective rows) (hc : Function.Injective cols)
    (B N : ℝ) (hB : 1 ≤ B) (hN : 1 ≤ N)
    (hrows : ∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B)
    (hcols : ∀ j, cols j ≠ 0 ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N)
    (a : n → ℂ) (E : ℝ) (hE : 0 ≤ E) (error : m → n → n → ℂ)
    (herr : ∀ i j k, ‖error i j k‖ ≤ E) :
    ‖∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k * error i j k‖ ≤
      16384 * B * N * E * ∑ j, ‖a j‖ ^ 2 := by
  have hrc := finite_ideal_family_card_bound rows hr B hB (fun i => (hrows i).1) (fun i => (hrows i).2)
  have hcc := finite_ideal_family_card_bound cols hc N hN (fun j => (hcols j).1) (fun j => (hcols j).2)
  apply (unrestricted_pair_error_energy rows cols a E hE error herr).trans
  calc
    _ ≤ (128 * B) * (128 * N) * E * ∑ j, ‖a j‖ ^ 2 := by gcongr
    _ = _ := by ring

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def unrestrictedDualPrincipalErrorSum (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (W : 𝓢(ℝ, ℂ)) (M F N T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))

omit [DecidableEq m] [DecidableEq n] in
theorem unrestrictedDualPrincipal_actual_error_sum_bound (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖unrestrictedDualPrincipalErrorSum rows cols a W M F N T‖ ≤
            16384 * B * N *
              ((2 * M / (F * N)) * ((supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primePool_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (supportConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k)) hM hF hi (by linarith) (hcols j).2 (hcols k).2
    have hh := hb ε hε (cols j * cols k) (mul_ne_zero (hcols j).1.1 (hcols k).1.1) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2.2
      · exact (hcols k).2.2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k))
        hM hF (by linarith) (hcols j).2 (hcols k).2) he (norm_nonneg _) (by positivity)
  exact unrestricted_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2.2⟩) a _ (by positivity) error herr

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0166

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.RetainedDualBounds
Source SHA256: 700e9acc79afbc5f397062543b10ee623d074861ae4a4073ab6349afc03b212d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0167


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

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def primePoolDensity (G : Ideal O) : ℂ :=
  ∏ P : primePool {G}, (1-(1:ℂ)/(Ideal.absNorm P.val:ℂ))

theorem principalTruncation_scaled (G : Ideal O) (hG : Squarefree G)
    (W : ℝ → ℂ) (c X Z : ℝ) :
    (c:ℂ)*principalTruncation (fun P : primePool {G} => P.val) Finset.univ W X Z =
      ((c*X:ℝ):ℂ)*paperRadialFourier W 0*primePoolDensity G -
      paperRadialFourier W 0 * (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) := by
  classical
  have hl : (∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(((c*X)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) =
      ((c*X:ℝ):ℂ)*(∑ d ∈ idealDivisors G, if Z < (Ideal.absNorm d:ℝ) then
        (UniqueFactorizationMonoid.moebius d:ℂ)/(Ideal.absNorm d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : Z < (Ideal.absNorm d:ℝ)
    · simp only [hd,ite_true,Complex.ofReal_div,Complex.ofReal_natCast]
      ring
    · simp only [hd,ite_false,mul_zero]
  have hs : (∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ)*(c:ℂ) else 0) =
      (c:ℂ)*(∑ d ∈ idealDivisors G, if (Ideal.absNorm d:ℝ) ≤ Z then
        (UniqueFactorizationMonoid.moebius d:ℂ) else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    by_cases hd : (Ideal.absNorm d:ℝ) ≤ Z <;> simp only [hd,ite_true,ite_false,mul_zero] ; ring
  rw [principalTruncation_eq_ideal_divisors G hG,hl,hs]
  unfold primePoolDensity
  push_cast
  ring

variable {m n p : Type} [Fintype m] [Fintype n] [Fintype p]
  [DecidableEq m] [DecidableEq n] [DecidableEq p]

def unrestrictedPrincipalDensity
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (R : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    ((Real.sqrt (R/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primePoolDensity (left j*right k)

def unrestrictedDualPrincipalTruncation (W : ℝ → ℂ)
    (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows left right a b i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
      principalTruncation (fun P : primePool {left j*right k} => P.val) Finset.univ W
        (Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))) (Z i))

omit [DecidableEq m] [DecidableEq n] [DecidableEq p] in
theorem unrestrictedDualPrincipalTruncation_eq
    (W : ℝ → ℂ) (rows : m → Ideal O) (left : n → Ideal O) (right : p → Ideal O)
    (a : n → ℂ) (b : p → ℂ) (M F : ℝ) (Z : m → ℝ) (hM : 0 < M) (hF : 0 < F)
    (hrows : ∀ i, rows i ≠ 0) (hleft : ∀ j, Admissible (left j)) (hright : ∀ k, Admissible (right k)) :
    unrestrictedDualPrincipalTruncation W rows left right a b M F Z =
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows left right a b (M/F) -
      paperRadialFourier W 0*unrestrictedLargePrincipalSum rows left right a b M F Z -
      W 0*unrestrictedSmallPrincipalSum rows left right a b M F (fun d i => (Ideal.absNorm d:ℝ) ≤ Z i) := by
  classical
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  have ht (i : m) (j : n) (k : p) :
      unrestrictedPairTerm rows left right a b i j k *
        (((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) *
          principalTruncation (fun P : primePool {left j*right k} => P.val) Finset.univ W
            (Real.sqrt (F*(Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ)/
              (M*(Ideal.absNorm (rows i):ℝ)))) (Z i)) =
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ)):ℝ):ℂ)*primePoolDensity (left j*right k)) -
      paperRadialFourier W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors (left j*right k), if Z i < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((Real.sqrt ((M/F)/(Ideal.absNorm (rows i):ℝ))/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) -
      W 0 * (unrestrictedPairTerm rows left right a b i j k *
        ∑ d ∈ idealDivisors (left j*right k), if (Ideal.absNorm d:ℝ) ≤ Z i then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((M/(Real.sqrt ((Ideal.absNorm (left j):ℝ)*(Ideal.absNorm (right k):ℝ))*F):ℝ):ℂ) else 0) := by
    by_cases hc : IsCoprime (left j) (right k)
    · have hsq : Squarefree (left j*right k) :=
        squarefree_mul_iff.mpr ⟨hc.isRelPrime,(hleft j).2.1,(hright k).2.1⟩
      rw [principalTruncation_scaled _ hsq,dual_principal_prefactor_identity M F (Ideal.absNorm (rows i))
        (Ideal.absNorm (left j)) (Ideal.absNorm (right k)) hM hF
        (hpos _ (hrows i)) (hpos _ (hleft j).1) (hpos _ (hright k).1)]
      ring
    · have hz : unrestrictedPairTerm rows left right a b i j k = 0 := by
        simp only [unrestrictedPairTerm,hc,ite_false]
      simp only [hz,zero_mul,mul_zero,sub_zero]
  unfold unrestrictedDualPrincipalTruncation
  simp_rw [ht]
  simp only [unrestrictedPrincipalDensity,unrestrictedLargePrincipalSum,unrestrictedSmallPrincipalSum,
    Finset.sum_sub_distrib,Finset.mul_sum]

end

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson UnrestrictedIdealReindex GaussGeneratorTransport

theorem dualPrincipalIdeal_truncated_all_conductors
    (I J : Ideal O) (hI : Admissible I) (hJ : Admissible J)
    (V : 𝓢(ℝ,ℂ)) (X Y Z lengthScale : ℝ) (hX : 0<X) :
    dualPrincipalIdeal I J V X = (6:ℂ)⁻¹ *
      (principalTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Z +
       middleTruncation (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale +
       truncationError (fun P : primePool {I*J} => P.val) Finset.univ V X Y Z lengthScale) := by
  let P := fun P : primePool {I*J} => P.val
  let f : O → ℂ := fun z => rowCoprimeMask P Finset.univ z *
    (if z=0 then 0 else V (‖eisEmbedding z‖^2/X))
  have hV : Summable (fun z : O => ‖V (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest V X hX)
  have hf : Summable f := by
    apply Summable.of_norm
    apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ hV
    intro z
    dsimp only [f]
    by_cases hz : z=0
    · simp only [hz,ite_true,mul_zero,norm_zero]
      exact norm_nonneg _
    · rw [ite_eq_right hz,norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (QuadraticUnitInvariance.rowCoprimeMask_norm_le_one P Finset.univ z)
  have h0 : f 0=0 := by simp only [f,ite_true,mul_zero]
  have hu (u : Oˣ) (z : O) : f (u.val*z)=f z := by
    dsimp only [f]
    rw [QuadraticUnitInvariance.rowCoprimeMask_unit_mul,norm_eisEmbedding_unit_mul]
    simp only [mul_eq_zero,u.ne_zero,false_or]
  have he := tsum_unit_invariant_of_zero f hf h0 hu
  have hm (z : O) : rowCoprimeMask P Finset.univ z=idealZeroMask I z*idealZeroMask J z := by
    rw [singleton_rowCoprimeMask_eq_idealZeroMask,idealZeroMask_mul I J hI.1 hJ.1]
  have hd : (∑' A : NonzeroIdeal, f (idealGenerator A.val))=dualPrincipalIdeal I J V X := by
    unfold dualPrincipalIdeal
    apply tsum_congr
    intro A
    simp only [f,hm,ite_eq_right (idealGenerator_ne_zero A.val A.property),idealGenerator_norm_sq]
  rw [hd] at he
  have hs : principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale = ∑' z : O, f z := by
    unfold truncationError
    dsimp only [f]
    ring
  change dualPrincipalIdeal I J V X=(6:ℂ)⁻¹ *
    (principalTruncation P Finset.univ V X Z + middleTruncation P Finset.univ V X Y Z lengthScale +
      truncationError P Finset.univ V X Y Z lengthScale)
  rw [hs,he]
  ring

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem unrestrictedDualPrincipal_error_uniform (l : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n],
      ∀ (ε : ℝ) (hε : 0 < ε) (B N M F T : ℝ),
        1 ≤ B → 1 ≤ N → 0 < M → 0 < F → 4 ≤ T →
        ∀ (rows : m → Ideal O) (cols : n → Ideal O),
          Function.Injective rows → Function.Injective cols →
          (∀ i, rows i ≠ 0 ∧ (Ideal.absNorm (rows i) : ℝ) ≤ B) →
          (∀ j, Admissible (cols j) ∧ N / 2 ≤ (Ideal.absNorm (cols j) : ℝ) ∧ (Ideal.absNorm (cols j) : ℝ) ≤ N) →
          ∀ (a : n → ℂ) (W : 𝓢(ℝ, ℂ)),
          ‖unrestrictedDualPrincipalErrorSum rows cols a W M F N T‖ ≤
            16384 * B * N *
              ((2 * M / (F * N)) * ((supportConstant ε hε * (N * N) ^ ε) *
                (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l)) *
              ∑ j, ‖a j‖ ^ 2 := by
  obtain ⟨s, C, hC, hb⟩ := primePool_symmetric_error_bound l
  refine ⟨s, C, hC, ?_⟩
  intro m n _ _ _ _ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols a W
  let E₀ := (supportConstant ε hε * (N * N) ^ ε) *
    (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) / T ^ l
  let error : m → n → n → ℂ := fun i j k =>
    (((M / (Real.sqrt ((Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ)) * F) : ℝ) : ℂ) *
      truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4))
  have hsc := (supportConstant_pos ε hε).le
  have hE₀ : 0 ≤ E₀ := by dsimp only [E₀]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖ ≤ (2 * M / (F * N)) * E₀ := by
    have hi : 0 < (Ideal.absNorm (rows i) : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    obtain ⟨hX₀, hlo, hhi⟩ := dual_truncation_reference_bounds M F (Ideal.absNorm (rows i)) N
      (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k)) hM hF hi (by linarith) (hcols j).2 (hcols k).2
    have hh := hb ε hε (cols j * cols k) (mul_ne_zero (hcols j).1.1 (hcols k).1.1) W
      _ _ T hX₀ hlo hhi hT
    simp only [map_mul, Nat.cast_mul] at hh
    have he : ‖truncationError (fun P : primePool {cols j * cols k} => P.val) Finset.univ W
        (Real.sqrt (F * (Ideal.absNorm (cols j) : ℝ) * (Ideal.absNorm (cols k) : ℝ) /
          (M * (Ideal.absNorm (rows i) : ℝ))))
        ((N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ)))) / T)
        (T * (N * Real.sqrt (F / (M * (Ideal.absNorm (rows i) : ℝ))))) (T ^ 4)‖ ≤ E₀ := by
      apply hh.trans
      dsimp only [E₀]
      gcongr
      · exact (hcols j).2.2
      · exact (hcols k).2.2
    dsimp only [error]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact mul_le_mul
      (dual_truncation_prefactor_bound M F N (Ideal.absNorm (cols j)) (Ideal.absNorm (cols k))
        hM hF (by linarith) (hcols j).2 (hcols k).2) he (norm_nonneg _) (by positivity)
  exact unrestricted_pair_error_ideal_bound rows cols hr hc B N hB hN hrows
    (fun j => ⟨(hcols j).1.1, (hcols j).2.2⟩) a _ (by positivity) error herr

section
variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def retainedDualPrincipalSum (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M F : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, unrestrictedPairTerm rows cols cols a a i j k *
    (((M/(Real.sqrt ((Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ))*F):ℝ):ℂ) *
      dualPrincipalIdeal (cols j) (cols k) W
        (Real.sqrt (F*(Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ)/
          (M*(Ideal.absNorm (rows i):ℝ)))))

omit [DecidableEq m] [DecidableEq n] in
theorem retainedDualPrincipalSum_symmetric_truncation
    (W : 𝓢(ℝ,ℂ)) (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ)
    (M F N T : ℝ) (hM : 0<M) (hF : 0<F)
    (hrows : ∀ i, rows i ≠ 0) (hcols : ∀ j, Admissible (cols j)) :
    (6:ℂ)*retainedDualPrincipalSum W rows cols a M F =
      unrestrictedDualPrincipalTruncation W rows cols cols a a M F
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F
        (fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T)
        (fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))) (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
  have hpos (I : Ideal O) (hI : I ≠ 0) : 0 < (Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => hI (Ideal.absNorm_eq_zero_iff.mp h))
  unfold retainedDualPrincipalSum unrestrictedDualPrincipalTruncation
    unrestrictedDualTruncatedMiddle unrestrictedDualPrincipalErrorSum
  simp only [Finset.mul_sum,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [dualPrincipalIdeal_truncated_all_conductors (cols j) (cols k) (hcols j) (hcols k)]
  · ring
  · have hi := hpos _ (hrows i)
    have hj := hpos _ (hcols j).1
    have hk := hpos _ (hcols k).1
    exact Real.sqrt_pos.mpr (by positivity : 0 <
      F*(Ideal.absNorm (cols j):ℝ)*(Ideal.absNorm (cols k):ℝ)/(M*(Ideal.absNorm (rows i):ℝ)))

end

lemma norm_four_correction_terms (A B C D : ℂ) :
    ‖-A-B+C+D‖ ≤ ‖A‖+‖B‖+‖C‖+‖D‖ := by
  have hab := norm_sub_le (-A) B
  have habc := norm_add_le (-A-B) C
  have habcd := norm_add_le (-A-B+C) D
  simp only [norm_neg] at hab
  linarith

theorem retained_dual_principal_difference (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α), 1/2 ≤ α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ),
        1≤B → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, Squarefree (rows i) ∧ B/2 ≤ (Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ) ≤ B) →
        (∀ j, Admissible (cols j) ∧ N/2 ≤ (Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ) ≤ N) →
        (∀ j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F)‖ ≤
        ‖paperRadialFourier W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
        ‖W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
        4*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
        16384*B*N*((2*M/(F*N))*((supportConstant ε hε*(N*N)^ε)*
          (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,herr⟩ := unrestrictedDualPrincipal_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT rows cols hr hc hrows hcols hray a W
  let Z := fun i => T*(N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))
  let Y := fun i => (N*Real.sqrt (F/(M*(Ideal.absNorm (rows i):ℝ))))/T
  have hT0 : 0≤T := by linarith
  have hmain := unrestrictedDualPrincipalTruncation_eq W rows cols cols a a M F Z hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1) (fun k => (hcols k).1)
  have hsplit := retainedDualPrincipalSum_symmetric_truncation W rows cols a M F N T hM hF
    (fun i => (hrows i).1.ne_zero) (fun j => (hcols j).1)
  change (6:ℂ)*retainedDualPrincipalSum W rows cols a M F =
    unrestrictedDualPrincipalTruncation W rows cols cols a a M F Z +
    unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
    unrestrictedDualPrincipalErrorSum rows cols a W M F N T at hsplit
  have heq : (6:ℂ)*retainedDualPrincipalSum W rows cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity rows cols cols a a (M/F) =
      -(paperRadialFourier W 0*unrestrictedLargePrincipalSum rows cols cols a a M F Z) -
      (W 0*unrestrictedSmallPrincipalSum rows cols cols a a M F (fun d i => (Ideal.absNorm d:ℝ)≤Z i)) +
      unrestrictedDualTruncatedMiddle W rows cols cols a a M F Y Z (T^4) +
      unrestrictedDualPrincipalErrorSum rows cols a W M F N T := by
    rw [hsplit,hmain]
    ring
  have hl := hexp.unrestricted_large_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
    rows cols cols hr hc hc hrows (fun j => ⟨(hcols j).1,(hcols j).2.2⟩)
    (fun k => ⟨(hcols k).1,(hcols k).2.2⟩) hray a a Z (fun _ => le_rfl)
  have hs := hexp.unrestricted_small_principal_sum hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows hcols hcols hray a a (fun d i => (Ideal.absNorm d:ℝ)≤Z i)
    (fun _ _ h => h)
  have hm := hexp.unrestricted_dual_truncated_middle hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hray (fun _ => le_rfl)
  have he := herr ε hε B N M F T hB hN hM hF hT rows cols hr hc
    (fun i => ⟨(hrows i).1.ne_zero,(hrows i).2.2⟩) hcols a W
  rw [heq]
  apply (norm_four_correction_terms _ _ _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_left hl (norm_nonneg _))
    (mul_le_mul_of_nonneg_left hs (norm_nonneg _))) hm) he

lemma sum_ideal_subtype_dyadic {A : Type*} [AddCommMonoid A]
    (S : Finset (Ideal O)) (K : ℝ) (f : Ideal O → A) :
    (∑ I : S, f I.val) = ∑ j : Fin (columnDyadicLength K+1),
      ∑ I : divisorDyadicBin S K j, f I.val := by
  classical
  rw [Finset.sum_coe_sort S f,sum_divisorDyadicBins S K f]
  exact Finset.sum_congr rfl (fun j _ => (Finset.sum_coe_sort (divisorDyadicBin S K j) f).symm)

def retainedDualMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F (1/2) a a) +
  ‖W 0‖*(4*smallPrincipalMajorant hexp deltaLoss hδ ε hε B N M F T a a) +
  4*dualMiddleMajorant hexp deltaLoss hδ ε hε B N M F T a a W +
  16384*B*N*((2*M/(F*N))*((supportConstant ε hε*(N*N)^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l))*∑ j, ‖a j‖^2

lemma retainedDualMajorant_nonneg {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    0≤retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hs0 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F (1/2) a a hB hN hM hF (by norm_num)
  have hs1 := smallPrincipalMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a hB hN hM hF hT
  have hm := dualMiddleMajorant_nonneg hexp deltaLoss hδ ε hε B N M F T a a W hB hN hM hF hT
  have hc := (supportConstant_pos ε hε).le
  unfold retainedDualMajorant
  positivity

lemma retainedDualMajorant_mono {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (B' B N M F T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB' : 0≤B') (hB : B'≤B) (hN : 0≤N) (hM : 0≤M) (hF : 0≤F) (hT : 0≤T) :
    retainedDualMajorant s C l hexp deltaLoss hδ ε hε B' N M F T a W ≤
      retainedDualMajorant s C l hexp deltaLoss hδ ε hε B N M F T a W := by
  have hB0 := hB'.trans hB
  have hα0 : 0≤α-1/2 := by linarith
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (supportConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := dualMiddleDecayConstant_nonneg W
  unfold retainedDualMajorant smallPrincipalMajorant dualMiddleMajorant
  gcongr

lemma retainedDualPrincipalDifference_dyadic {n : Type} [Fintype n] [DecidableEq n]
    (W : 𝓢(ℝ,ℂ)) (S : Finset (Ideal O)) (K : ℝ) (cols : n → Ideal O) (a : n → ℂ) (M F : ℝ) :
    (6:ℂ)*retainedDualPrincipalSum W (fun I : S => I.val) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun I : S => I.val) cols cols a a (M/F) =
    ∑ j : Fin (columnDyadicLength K+1),
      ((6:ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)) := by
  classical
  have h := sum_ideal_subtype_dyadic (A := ℂ) S K (fun I =>
    (6:ℂ)*retainedDualPrincipalSum W (fun _ : Unit => I) cols a M F -
      paperRadialFourier W 0*unrestrictedPrincipalDensity (fun _ : Unit => I) cols cols a a (M/F))
  simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,unrestrictedPairTerm,
    Finset.mul_sum,←Finset.sum_sub_distrib,Fintype.sum_unique] using h

theorem retained_dual_principal_global (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (K N M F T : ℝ),
        1≤K → 1≤N → 0<M → 0<F → 4≤T →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀ j, Admissible (cols j) ∧ N/2≤(Ideal.absNorm (cols j):ℝ) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j k, columnRay (cols j)=columnRay (cols k)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖(6:ℂ)*retainedDualPrincipalSum W (fun I : squarefreeIdealRange K => I.val) cols a M F -
          paperRadialFourier W 0*unrestrictedPrincipalDensity
            (fun I : squarefreeIdealRange K => I.val) cols cols a a (M/F)‖ ≤
        (columnDyadicLength K+1:ℕ)*retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W := by
  obtain ⟨s,C,hC,hbound⟩ := retained_dual_principal_difference l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε K N M F T hK hN hM hF hT cols hc hcols hray a W
  classical
  let S := squarefreeIdealRange K
  let R := retainedDualMajorant s C l hexp deltaLoss hδ ε hε (2*K) N M F T a W
  have hS (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K := by
    have hi := mem_squarefreeIdealRange.mp hI
    refine ⟨?_,hi.2⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hi.1.ne_zero (Ideal.absNorm_eq_zero_iff.mp h))
  have hR : 0≤R := retainedDualMajorant_nonneg s C hC.le l hexp deltaLoss hδ ε hε (2*K) N M F T a W
    (by linarith) (by linarith) hM.le hF.le (by linarith)
  have hb (j : Fin (columnDyadicLength K+1)) :
      ‖(6:ℂ)*retainedDualPrincipalSum W (fun I : divisorDyadicBin S K j => I.val) cols a M F -
        paperRadialFourier W 0*unrestrictedPrincipalDensity
          (fun I : divisorDyadicBin S K j => I.val) cols cols a a (M/F)‖ ≤ R := by
    by_cases hj : (divisorDyadicBin S K j).Nonempty
    · let B := 2*divisorDyadicScale j.val
      have hB : 1≤B := by dsimp only [B]; linarith [divisorDyadicScale_ge_one j.val]
      have hBK : B≤2*K := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left (divisorDyadicBin_scale_le S K hS j hj) (by norm_num)
      have hrows (I : divisorDyadicBin S K j) : Squarefree I.val ∧
          B/2≤(Ideal.absNorm I.val:ℝ) ∧ (Ideal.absNorm I.val:ℝ)≤B := by
        have hi := divisorDyadicBin_bounds S K hS j I.val I.property
        refine ⟨(mem_squarefreeIdealRange.mp (Finset.mem_filter.mp I.property).1).1,?_,hi.2⟩
        dsimp only [B]
        linarith
      have hh := hbound hexp hα deltaLoss hδ ε hε B N M F T hB hN hM hF hT
        (fun I : divisorDyadicBin S K j => I.val) cols Subtype.val_injective hc hrows hcols hray a W
      apply hh.trans
      exact retainedDualMajorant_mono s C hC.le l hexp hα deltaLoss hδ ε hε B (2*K) N M F T a W
        (by linarith) hBK (by linarith) hM.le hF.le (by linarith)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hj
      have : IsEmpty (divisorDyadicBin S K j) := by
        refine ⟨fun I => ?_⟩
        have hi := I.property
        simp only [he,Finset.notMem_empty] at hi
      simpa only [retainedDualPrincipalSum,unrestrictedPrincipalDensity,Finset.univ_eq_empty,
        Finset.sum_empty,mul_zero,sub_zero,norm_zero] using hR
  rw [retainedDualPrincipalDifference_dyadic W (squarefreeIdealRange K) K cols a M F]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength K+1), R := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R]

end

open scoped BigOperators Classical
open ActualEisensteinCubic QuadraticSquarefreeKernel CompletedGauss

def highSquareParts (M K : ℝ) : Finset (Ideal O) := (highKernelRange M K).image squarePart

theorem highSquareParts_bounds (M K : ℝ) (hK : 0 < K) (A : Ideal O)
    (hA : A ∈ highSquareParts M K) :
    Supported A ∧ 1 ≤ (Ideal.absNorm A : ℝ) ∧
    (Ideal.absNorm A : ℝ) ≤ Real.sqrt (M/K) ∧
    1 ≤ M/(Ideal.absNorm A : ℝ)^2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  obtain ⟨hs,hN,hlarge⟩ := mem_highKernelRange.mp hI
  have hparts := (supported_square_parts I).mp hs
  have hna : 1 ≤ (Ideal.absNorm (squarePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hnb : 1 ≤ (Ideal.absNorm (squarefreePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hparts.2.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hprod : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) ≤ M := by
    have he : (Ideal.absNorm (squarePart I) : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) =
        (Ideal.absNorm I : ℝ) := by exact_mod_cast norm_decomposition I
    rwa [he]
  have hsquare : (Ideal.absNorm (squarePart I) : ℝ)^2 ≤ M/K := by
    apply (le_div_iff₀ hK).mpr
    exact (mul_le_mul_of_nonneg_left hlarge.le (sq_nonneg _)).trans hprod
  have hM : 0 ≤ M/K := (sq_nonneg _).trans hsquare
  have hroot : (Ideal.absNorm (squarePart I) : ℝ) ≤ Real.sqrt (M/K) := by
    nlinarith [Real.sq_sqrt hM,Real.sqrt_nonneg (M/K)]
  refine ⟨hparts.1,hna,hroot,?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (Ideal.absNorm (squarePart I) : ℝ)^2)).mpr
  nlinarith

theorem highSquarePart_fiber_row_bounds (M K : ℝ) (A I : Ideal O)
    (hI : I ∈ highKernelRange M K) (hA : squarePart I = A) :
    Admissible (squarefreePart I) ∧
      (Ideal.absNorm (squarefreePart I) : ℝ) ≤ M/(Ideal.absNorm A : ℝ)^2 := by
  have hs := (mem_highKernelRange.mp hI).1
  have hparts := (supported_square_parts I).mp hs
  have hna : 0 < (Ideal.absNorm A : ℝ) := by
    rw [←hA]
    exact_mod_cast Nat.pos_of_ne_zero (fun h => hparts.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  refine ⟨hparts.2,(le_div_iff₀ (sq_pos_of_pos hna)).mpr ?_⟩
  have he : (Ideal.absNorm A : ℝ)^2*(Ideal.absNorm (squarefreePart I) : ℝ) = (Ideal.absNorm I : ℝ) := by
    rw [←hA]
    exact_mod_cast norm_decomposition I
  simpa only [mul_comm,he] using (mem_highKernelRange.mp hI).2.1

def highSquarePartFiber (M K : ℝ) (A : Ideal O) : Finset (Ideal O) :=
  (highKernelRange M K).filter (fun I => squarePart I = A)

theorem highSquarePartFiber_energy (M N K : ℝ) (A : Ideal O)
    (a : idealRange N → ℂ) :
    (∑ I ∈ highSquarePartFiber M K A,
      ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖^2) ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N * ∑ J, ‖a J‖^2 := by
  let S := highSquarePartFiber M K A
  let b : idealRange N → ℂ := fun J => idealZeroMask J.val (primaryGenerator A) * a J
  let B : Matrix S (idealRange N) ℂ := fun I J =>
    quadraticRow J.val (primaryGenerator (squarefreePart I.val))
  have hinj : Function.Injective (fun I : S => squarefreePart I.val) := by
    intro I I' heq
    dsimp only at heq
    apply Subtype.ext
    have hI := (Finset.mem_filter.mp I.property).2
    have hI' := (Finset.mem_filter.mp I'.property).2
    calc
      I.val = A^2 * squarefreePart I.val := by
        simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
      _ = A^2 * squarefreePart I'.val := by rw [heq]
      _ = I'.val := by simpa only [hI'] using squarePart_sq_mul_squarefreePart I'.val
  have hnorm : ‖FiniteSieveOperator.operator B‖^2 ≤
      sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N := by
    apply family_squared_norm_le (fun I : S => squarefreePart I.val)
      (fun J : idealRange N => J.val) hinj Subtype.val_injective
    · intro I
      exact highSquarePart_fiber_row_bounds M K A I.val
        (Finset.mem_filter.mp I.property).1 (Finset.mem_filter.mp I.property).2
    · intro J
      exact mem_idealRange.mp J.property
  have hrow (I : S) :
      (∑ J : idealRange N, quadraticRow J.val (primaryGenerator I.val) * a J) =
      ∑ J : idealRange N, B I J * b J := by
    apply Finset.sum_congr rfl
    intro J _
    have hI := (Finset.mem_filter.mp I.property).2
    have he : I.val = A^2 * squarefreePart I.val := by
      simpa only [hI] using (squarePart_sq_mul_squarefreePart I.val).symm
    rw [he, canonical_quadraticRow_primary_squarefree J.val
      (mem_idealRange.mp J.property).1]
    change _ = quadraticRow J.val (primaryGenerator (squarefreePart I.val)) *
      (idealZeroMask J.val (primaryGenerator A) * a J)
    ring
  have hb (J : idealRange N) : ‖b J‖^2 ≤ ‖a J‖^2 := by
    dsimp only [b]
    unfold idealZeroMask
    split_ifs <;> simp
  rw [← Finset.sum_coe_sort S]
  simp_rw [hrow]
  exact (FiniteSieveOperator.energy_bound B b).trans
    ((mul_le_mul_of_nonneg_right hnorm (by positivity)).trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun J _ => hb J)
        (sieveNorm_nonneg _ _)))

theorem highKernelNorm_le_squarePart_sum (M N K : ℝ) :
    highKernelNorm M N K ≤
      ∑ A ∈ highSquareParts M K, sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N := by
  apply FiniteSieveOperator.squared_norm_le_of_energy _ _
    (Finset.sum_nonneg fun A _ => sieveNorm_nonneg _ _)
  intro a
  simp only [highKernelMatrix]
  rw [Finset.sum_coe_sort (highKernelRange M K)
    (fun I : Ideal O => ‖∑ J : idealRange N, quadraticRow J.val (primaryGenerator I) * a J‖^2)]
  have hmaps : ∀ I ∈ highKernelRange M K, squarePart I ∈ highSquareParts M K :=
    fun I hI => Finset.mem_image_of_mem squarePart hI
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ A ∈ highSquareParts M K,
        sieveNorm (M/(Ideal.absNorm A : ℝ)^2) N * ∑ J, ‖a J‖^2 := by
      apply Finset.sum_le_sum
      intro A hA
      exact highSquarePartFiber_energy M N K A a
    _ = _ := (Finset.sum_mul _ _ _).symm

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0167

/-! Original module: OAI.NumberTheory.DirichletL.CubicSieve.PrincipalDensity
Source SHA256: 52f35a5259e2f383a2f57e5e0924102c158904f71f5710cceb499e443e8e2e33
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0168


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

namespace SecondPassIntegration

open scoped BigOperators Classical
open MeasureTheory
open ActualEisensteinCubic SecondPassArithmetic

theorem childDensity_elementary_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*
        (∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3 := by
  let B := (6*128^4*K*(max 1 (X*Real.exp A))^2*M^2/X)*(X*F)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hXF : 0 < X*F := mul_pos hX (lt_of_lt_of_le zero_lt_one hF)
  have h₁ (a : ℝ) : childEnergy p hp hcop hg pool Ψ₁ m T V₁ X true false a 0 ≤ B*(1+‖a‖)^(2*J) := by
    have h := childEnergy_elementary_normalized p hp hcop hg hc hinj pool Ψ₁ hΨ₁ m T V₁
      X F K A M a 0 hX hF hK hA hM hV₁ hVs₁ hT true false
    have hh : childEnergy p hp hcop hg pool Ψ₁ m T V₁ X true false a 0 ≤ B := (div_le_iff₀ hXF).mp h
    exact hh.trans (le_mul_of_one_le_right hB (one_le_pow₀ (by linarith [norm_nonneg a])))
  have h₂ (a : ℝ) : childEnergy p hp hcop hg pool Ψ₂ m T V₂ X false true a 0 ≤ B*(1+‖a‖)^(2*J) := by
    have h := childEnergy_elementary_normalized p hp hcop hg hc hinj pool Ψ₂ hΨ₂ m T V₂
      X F K A M a 0 hX hF hK hA hM hV₂ hVs₂ hT false true
    have hh : childEnergy p hp hcop hg pool Ψ₂ m T V₂ X false true a 0 ≤ B := (div_le_iff₀ hXF).mp h
    exact hh.trans (le_mul_of_one_le_right hB (one_le_pow₀ (by linarith [norm_nonneg a])))
  have hd := densityChildEnergy_polynomial_bound p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X J B B hB hB h₁ h₂
  rw [Real.mul_self_sqrt hB] at hd
  apply (div_le_iff₀ hXF).mpr
  convert hd using 1 ; dsimp [B] ; ring

theorem childDensity_elementary_supported {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (hΨ₁ : ∀ a,‖Ψ₁ a‖ ≤ 1) (hΨ₂ : ∀ a,‖Ψ₂ a‖ ≤ 1)
    (m : O) (T : Finset (Ideal O × O)) (V₁ V₂ : ℝ → ℂ)
    (X F K A M : ℝ) (J : ℕ) (hX : 0 < X) (hF : 1 ≤ F) (hK : 1 ≤ K)
    (hA : 0 ≤ A) (hM : 0 ≤ M) (hscale : 1 ≤ X*Real.exp A)
    (hV₁ : ∀ s,‖V₁ s‖ ≤ M) (hV₂ : ∀ s,‖V₂ s‖ ≤ M)
    (hVs₁ : ∀ s,V₁ s ≠ 0 → |s| ≤ A) (hVs₂ : ∀ s,V₂ s ≠ 0 → |s| ≤ A)
    (hT : ∀ z∈T,z.1 ≠ ⊥ ∧ (Ideal.absNorm z.1 : ℝ) ≤ F ∧ ‖ConcreteTraceCRT.eisEmbedding z.2‖^2 ≤ K) :
    densityChildEnergy p hp hcop hg pool Ψ₁ Ψ₂ m T V₁ V₂ X X (2*J)/(X*F) ≤
      (6*128^4*(Real.exp A*M)^2*(∫ t : ℝ,FirstPassCubeLabels.firstLogDensity 0 t)^3)*K*X := by
  have h := childDensity_elementary_normalized p hp hcop hg hc hinj pool Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m T V₁ V₂ X F K A M J hX hF hK hA hM hV₁ hV₂ hVs₁ hVs₂ hT
  rw [max_eq_right hscale] at h
  convert h using 1
  field_simp

end SecondPassIntegration

open scoped BigOperators Classical SchwartzMap
namespace CanonicalQuadraticSieve

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealMobiusDivisorSum

def sourcePrincipalScale (M : ℝ) (I : Ideal O) : ℝ := Real.sqrt (M/(Ideal.absNorm I:ℝ))

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def maskedSourceDensity (G : Ideal O) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ((sourcePrincipalScale M (rows i):ℝ):ℂ)*primePoolDensity (G*(cols j*cols k))

def maskedPrincipalSourceSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    ∑' z : O, rowCoprimeMask (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ z *
      (if z=0 then 0 else W (‖eisEmbedding z‖^2/sourcePrincipalScale M (rows i)))

def maskedSourcePrincipalTruncation (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) (Z : m → ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    principalTruncation (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i)) (Z i)

def maskedSourceErrorSum (G : Ideal O) (W : 𝓢(ℝ,ℂ))
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M T : ℝ) : ℂ :=
  ∑ i, ∑ j, ∑ k, originalTerm rows cols cols a a 1 1 i j k *
    truncationError (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i))
      (sourcePrincipalScale M (rows i)/T)
      (T*sourcePrincipalScale M (rows i)) (T^4)

omit [DecidableEq m] [DecidableEq n] in
theorem maskedSourcePrincipalTruncation_eq (G : Ideal O) (hG : Squarefree G)
    (W : 𝓢(ℝ,ℂ)) (hW : W 0=0) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M : ℝ) (Z : m → ℝ)
    (hcols : ∀ j, Admissible (cols j)) (hGc : ∀ j, IsCoprime G (cols j)) :
    maskedSourcePrincipalTruncation G W rows cols a M Z =
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
      paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z := by
  classical
  have ht (i : m) (j k : n) :
      originalTerm rows cols cols a a 1 1 i j k *
        principalTruncation (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
          (sourcePrincipalScale M (rows i)) (Z i) =
      paperRadialFourier W 0*(originalTerm rows cols cols a a 1 1 i j k *
        ((sourcePrincipalScale M (rows i):ℝ):ℂ)*primePoolDensity (G*(cols j*cols k))) -
      paperRadialFourier W 0*(originalTerm rows cols cols a a 1 1 i j k *
        ∑ d ∈ idealDivisors (G*(cols j*cols k)), if Z i < (Ideal.absNorm d:ℝ) then
          (UniqueFactorizationMonoid.moebius d:ℂ)*
            ((sourcePrincipalScale M (rows i)/(Ideal.absNorm d:ℝ):ℝ):ℂ) else 0) := by
    by_cases hc : IsCoprime (cols j) (cols k)
    · have hC : Squarefree (cols j*cols k) := squarefree_mul_iff.mpr
        ⟨hc.isRelPrime,(hcols j).2.1,(hcols k).2.1⟩
      have hprod : Squarefree (G*(cols j*cols k)) := squarefree_mul_iff.mpr
        ⟨((hGc j).mul_right (hGc k)).isRelPrime,hG,hC⟩
      have hp := principalTruncation_scaled (G*(cols j*cols k)) hprod W 1
        (sourcePrincipalScale M (rows i)) (Z i)
      simp only [Complex.ofReal_one,one_mul,hW,zero_mul,sub_zero] at hp
      rw [hp]
      ring
    · have hz : originalTerm rows cols cols a a 1 1 i j k=0 := by simp only [originalTerm,hc,ite_false]
      simp only [hz,zero_mul,mul_zero,sub_zero]
  unfold maskedSourcePrincipalTruncation
  simp_rw [ht]
  simp only [maskedSourceDensity,maskedPrincipalDivisorCorrection,sourcePrincipalScale,Finset.sum_sub_distrib,Finset.mul_sum]

omit [DecidableEq m] [DecidableEq n] in
theorem maskedPrincipalSourceSum_eq (G : Ideal O) (hG : Squarefree G)
    (W : 𝓢(ℝ,ℂ)) (hW : W 0=0) (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (M T : ℝ)
    (hcols : ∀ j, Admissible (cols j)) (hGc : ∀ j, IsCoprime G (cols j)) :
    maskedPrincipalSourceSum G W rows cols a M =
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
      paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M
        (fun i => T*sourcePrincipalScale M (rows i)) +
      originalMaskedTruncatedMiddle G W rows cols cols a a M
        (fun i => sourcePrincipalScale M (rows i)/T)
        (fun i => T*sourcePrincipalScale M (rows i)) (T^4) +
      maskedSourceErrorSum G W rows cols a M T := by
  rw [←maskedSourcePrincipalTruncation_eq G hG W hW rows cols a M _ hcols hGc]
  unfold maskedPrincipalSourceSum maskedSourcePrincipalTruncation originalMaskedTruncatedMiddle maskedSourceErrorSum
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  unfold truncationError sourcePrincipalScale
  ring

end
section

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

theorem maskedSource_error_uniform (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        (ε : ℝ) (hε : 0<ε) (G : Ideal O), G≠0 →
      ∀ (B N M T : ℝ), 1≤B → 1≤N → 0<M → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, rows i≠0 ∧ (Ideal.absNorm (rows i):ℝ)≤B) →
        (∀ j, cols j≠0 ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)),
        ‖maskedSourceErrorSum G W rows cols a M T‖ ≤
          16384*B*N*((supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
            (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2 := by
  obtain ⟨s,C,hC,hbound⟩ := primePool_symmetric_error_bound l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ ε hε G hG B N M T hB hN hM hT rows cols hr hc hrows hcols a W
  let E := (supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l
  let error := fun i j k =>
    truncationError (fun P : primePool {G*(cols j*cols k)} => P.val) Finset.univ W
      (sourcePrincipalScale M (rows i)) (sourcePrincipalScale M (rows i)/T)
      (T*sourcePrincipalScale M (rows i)) (T^4)
  have hs := (supportConstant_pos ε hε).le
  have hE : 0≤E := by dsimp only [E]; positivity
  have herr (i : m) (j k : n) : ‖error i j k‖≤E := by
    have hi : 0<(Ideal.absNorm (rows i):ℝ) := by
      exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun h => (hrows i).1 (Ideal.absNorm_eq_zero_iff.mp h))
    have hX : 0<sourcePrincipalScale M (rows i) := Real.sqrt_pos.mpr (div_pos hM hi)
    have h := hbound ε hε (G*(cols j*cols k))
      (mul_ne_zero hG (mul_ne_zero (hcols j).1 (hcols k).1)) W
      (sourcePrincipalScale M (rows i)) (sourcePrincipalScale M (rows i)) T hX
      (by linarith) (by linarith) hT
    simp only [map_mul,Nat.cast_mul] at h
    apply h.trans
    dsimp only [E]
    gcongr
    · exact (hcols j).2
    · exact (hcols k).2
  exact actual_pair_error_ideal_bound rows cols hr hc B N hB hN hrows hcols a E hE error herr

section
open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator IdealMobiusDivisorSum

def sourcePrincipalMajorant {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) : ℝ :=
  ‖paperRadialFourier W 0‖*((idealDivisors G).card *
    (((columnDyadicLength N+1:ℕ):ℝ)^2 *
      (2*divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (4*N/T+Real.sqrt M*B^(α-1/2))))) +
  (idealDivisors G).card * (((columnDyadicLength N+1:ℕ):ℝ)^2 *
    ((2*nonzeroLatticeEnvelopeConstant*originalMiddleDecayConstant W)*
      divisorEnergyFactor ε hε N a a*(divisorExponentConstant hexp deltaLoss hδ*(B*N)^deltaLoss)*
        (N+(2*T)*Real.sqrt M*B^(α-1/2)))) +
  16384*B*N*((supportConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N))^ε)*
    (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/T^l)*∑ j, ‖a j‖^2

theorem masked_source_principal_difference (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
        {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε)
        (G : Ideal O), Squarefree G →
      ∀ (B N M T : ℝ), 1≤B → 1≤N → 0<M → 4≤T →
      ∀ (rows : m → Ideal O) (cols : n → Ideal O),
        Function.Injective rows → Function.Injective cols →
        (∀ i, Admissible (rows i) ∧ B/2≤(Ideal.absNorm (rows i):ℝ) ∧ (Ideal.absNorm (rows i):ℝ)≤B) →
        (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖maskedPrincipalSourceSum G W rows cols a M -
          paperRadialFourier W 0*maskedSourceDensity G rows cols a M‖ ≤
        sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  obtain ⟨s,C,hC,herr⟩ := maskedSource_error_uniform l
  refine ⟨s,C,hC,?_⟩
  intro m n _ _ _ _ α hexp deltaLoss hδ ε hε G hG B N M T hB hN hM hT rows cols hr hc hrows hcols hGc a W hW
  let Z := fun i => T*sourcePrincipalScale M (rows i)
  let Y := fun i => sourcePrincipalScale M (rows i)/T
  have hT0 : 0≤T := by linarith
  have hsplit := maskedPrincipalSourceSum_eq G hG W hW rows cols a M T (fun j => (hcols j).1) hGc
  change maskedPrincipalSourceSum G W rows cols a M =
    paperRadialFourier W 0*maskedSourceDensity G rows cols a M -
    paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z +
    originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
    maskedSourceErrorSum G W rows cols a M T at hsplit
  have heq : maskedPrincipalSourceSum G W rows cols a M -
      paperRadialFourier W 0*maskedSourceDensity G rows cols a M =
      -(paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) +
      originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4) +
      maskedSourceErrorSum G W rows cols a M T := by rw [hsplit]; ring
  have hl := hexp.masked_source_large_principal_sum deltaLoss hδ ε hε G hG.ne_zero B N M T hB hN hM (by linarith)
    rows cols cols hr hc hc hrows hcols hcols hGc hGc a a Z (fun _ => le_rfl)
  have hm := hexp.original_masked_truncated_middle deltaLoss hδ ε hε G hG B N M T hB hN hM hT0
    rows cols cols hr hc hc hrows a a W Y Z (T^4) hcols hcols hGc hGc (fun _ => le_rfl)
  have he := herr ε hε G hG.ne_zero B N M T hB hN hM hT rows cols hr hc
    (fun i => ⟨(hrows i).1.1,(hrows i).2.2⟩) (fun j => ⟨(hcols j).1.1,(hcols j).2⟩) a W
  have hn := norm_four_correction_terms
    (paperRadialFourier W 0*maskedPrincipalDivisorCorrection G rows cols cols a a M Z) 0
    (originalMaskedTruncatedMiddle G W rows cols cols a a M Y Z (T^4))
    (maskedSourceErrorSum G W rows cols a M T)
  simp only [sub_zero,norm_zero,add_zero] at hn
  rw [heq]
  apply hn.trans
  rw [norm_mul]
  exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hl (norm_nonneg _)) hm) he

lemma sourcePrincipalMajorant_nonneg {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB : 0≤B) (hN : 0≤N) (_hM : 0≤M) (hT : 0≤T) :
    0≤sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (supportConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := originalMiddleDecayConstant_nonneg W
  unfold sourcePrincipalMajorant
  positivity

lemma sourcePrincipalMajorant_mono {n : Type} [Fintype n]
    (s : Finset (ℕ×ℕ)) (C : ℝ) (hC : 0≤C) (l : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (hα : 1/2≤α) (deltaLoss : ℝ) (hδ : 0<deltaLoss)
    (ε : ℝ) (hε : 0<ε) (G : Ideal O) (B' B N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ))
    (hB' : 0≤B') (hB : B'≤B) (hN : 0≤N) (_hM : 0≤M) (hT : 0≤T) :
    sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B' N M T a W ≤
      sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G B N M T a W := by
  have hB0 := hB'.trans hB
  have hα0 : 0≤α-1/2 := by linarith
  have he := divisorEnergyFactor_nonneg ε hε N a a
  have hc := (divisorExponentConstant_pos hexp deltaLoss hδ).le
  have hs := (supportConstant_pos ε hε).le
  have hlat := nonzeroLatticeEnvelopeConstant_nonneg
  have hW := originalMiddleDecayConstant_nonneg W
  unfold sourcePrincipalMajorant
  gcongr

end

open ActualEisensteinCubic ConcreteTraceCRT ConcretePrimeRowBridge EisensteinSchwartzPoisson
open TruncatedPrincipalPoisson IdealCoprimeSieveOperator

lemma maskedPrincipalSourceDifference_dyadic {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (W : 𝓢(ℝ,ℂ)) (S : Finset (Ideal O)) (K : ℝ)
    (cols : n → Ideal O) (a : n → ℂ) (M : ℝ) :
    maskedPrincipalSourceSum G W (fun I : S => I.val) cols a M -
      paperRadialFourier W 0*maskedSourceDensity G (fun I : S => I.val) cols a M =
    ∑ j : Fin (columnDyadicLength K+1),
      (maskedPrincipalSourceSum G W (fun I : divisorDyadicBin S K j => I.val) cols a M -
        paperRadialFourier W 0*maskedSourceDensity G (fun I : divisorDyadicBin S K j => I.val) cols a M) := by
  classical
  have h := sum_ideal_subtype_dyadic (A := ℂ) S K (fun I =>
    maskedPrincipalSourceSum G W (fun _ : Unit => I) cols a M -
      paperRadialFourier W 0*maskedSourceDensity G (fun _ : Unit => I) cols a M)
  simpa only [maskedPrincipalSourceSum,maskedSourceDensity,originalTerm,
    Finset.mul_sum,←Finset.sum_sub_distrib,Fintype.sum_unique] using h

theorem masked_source_principal_global (l : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
      ∀ {n : Type} [Fintype n] [DecidableEq n] {α : ℝ} (hexp : HasSieveExponent α), 1/2≤α →
      ∀ (deltaLoss : ℝ) (hδ : 0<deltaLoss) (ε : ℝ) (hε : 0<ε) (G : Ideal O), Squarefree G →
      ∀ (K N M T : ℝ), 1≤K → 1≤N → 0<M → 4≤T →
      ∀ (S : Finset (Ideal O)), (∀ I∈S, Admissible I ∧ (Ideal.absNorm I:ℝ)≤K) →
      ∀ (cols : n → Ideal O), Function.Injective cols →
        (∀ j, Admissible (cols j) ∧ (Ideal.absNorm (cols j):ℝ)≤N) →
        (∀ j, IsCoprime G (cols j)) →
      ∀ (a : n → ℂ) (W : 𝓢(ℝ,ℂ)), W 0=0 →
        ‖maskedPrincipalSourceSum G W (fun I : S => I.val) cols a M -
          paperRadialFourier W 0*maskedSourceDensity G (fun I : S => I.val) cols a M‖ ≤
        (columnDyadicLength K+1:ℕ)*sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G (2*K) N M T a W := by
  obtain ⟨s,C,hC,hbound⟩ := masked_source_principal_difference l
  refine ⟨s,C,hC,?_⟩
  intro n _ _ α hexp hα deltaLoss hδ ε hε G hG K N M T hK hN hM hT S hS cols hc hcols hGc a W hW
  classical
  let R := sourcePrincipalMajorant s C l hexp deltaLoss hδ ε hε G (2*K) N M T a W
  have hSnorm (I : Ideal O) (hI : I∈S) : 1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤K := by
    have hi := hS I hI
    refine ⟨?_,hi.2⟩
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun h => hi.1.1 (Ideal.absNorm_eq_zero_iff.mp h))
  have hR : 0≤R := sourcePrincipalMajorant_nonneg s C hC.le l hexp deltaLoss hδ ε hε G (2*K) N M T a W
    (by linarith) (by linarith) hM.le (by linarith)
  have hb (j : Fin (columnDyadicLength K+1)) :
      ‖maskedPrincipalSourceSum G W (fun I : divisorDyadicBin S K j => I.val) cols a M -
        paperRadialFourier W 0*maskedSourceDensity G (fun I : divisorDyadicBin S K j => I.val) cols a M‖ ≤ R := by
    by_cases hj : (divisorDyadicBin S K j).Nonempty
    · let B := 2*divisorDyadicScale j.val
      have hB : 1≤B := by dsimp only [B]; linarith [divisorDyadicScale_ge_one j.val]
      have hBK : B≤2*K := by
        dsimp only [B]
        exact mul_le_mul_of_nonneg_left (divisorDyadicBin_scale_le S K hSnorm j hj) (by norm_num)
      have hrows (I : divisorDyadicBin S K j) : Admissible I.val ∧
          B/2≤(Ideal.absNorm I.val:ℝ) ∧ (Ideal.absNorm I.val:ℝ)≤B := by
        have hi := divisorDyadicBin_bounds S K hSnorm j I.val I.property
        refine ⟨(hS I.val (Finset.mem_filter.mp I.property).1).1,?_,hi.2⟩
        dsimp only [B]
        linarith
      have hh := hbound hexp deltaLoss hδ ε hε G hG B N M T hB hN hM hT
        (fun I : divisorDyadicBin S K j => I.val) cols Subtype.val_injective hc hrows hcols hGc a W hW
      apply hh.trans
      exact sourcePrincipalMajorant_mono s C hC.le l hexp hα deltaLoss hδ ε hε G B (2*K) N M T a W
        (by linarith) hBK (by linarith) hM.le (by linarith)
    · have he := Finset.not_nonempty_iff_eq_empty.mp hj
      have : IsEmpty (divisorDyadicBin S K j) := by
        refine ⟨fun I => ?_⟩
        have hi := I.property
        simp only [he,Finset.notMem_empty] at hi
      simpa only [maskedPrincipalSourceSum,maskedSourceDensity,Finset.univ_eq_empty,
        Finset.sum_empty,mul_zero,sub_zero,norm_zero] using hR
  rw [maskedPrincipalSourceDifference_dyadic G W S K cols a M]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength K+1), R := Finset.sum_le_sum (fun j _ => hb j)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,R]

end

section
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem primePoolDensity_eq_support (G : Ideal O) :
    primePoolDensity G = ∏ P ∈ primeSupport G, (1-(1:ℂ)/(Ideal.absNorm P:ℂ)) := by
  rw [primePoolDensity,Finset.prod_coe_sort (primePool {G})
    (fun P : Ideal O => (1-(1:ℂ)/(Ideal.absNorm P:ℂ)))]
  simp [primePool,primeSupport]

theorem primePoolDensity_eq_real (G : Ideal O) :
    primePoolDensity G = (idealPrimeDensity {G} G : ℂ) := by
  simp only [primePoolDensity,idealPrimeDensity,idealSupport_singleton_univ,
    Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
    Complex.ofReal_div,Complex.ofReal_natCast]

theorem primePoolDensity_norm_le_one (G : Ideal O) (hG : G ≠ 0) :
    ‖primePoolDensity G‖ ≤ 1 := by
  rw [primePoolDensity_eq_real,Complex.norm_real,Real.norm_eq_abs]
  have hb := idealPrimeDensity_mem_Icc {G}
    (by intro I hI; simpa only [Finset.mem_singleton.mp hI,Ideal.zero_eq_bot] using hG) G
  rw [abs_of_nonneg hb.1]
  exact hb.2

theorem primePoolDensity_star (G : Ideal O) : star (primePoolDensity G) = primePoolDensity G := by
  rw [primePoolDensity_eq_real]
  simp

theorem primePoolDensity_mul (G H : Ideal O) (hG : G ≠ 0) (hH : H ≠ 0)
    (hcop : IsCoprime G H) : primePoolDensity (G*H) = primePoolDensity G*primePoolDensity H := by
  simp only [primePoolDensity_eq_support,primeSupport]
  rw [UniqueFactorizationMonoid.normalizedFactors_mul hG hH,Multiset.toFinset_add,
    Finset.prod_union]
  apply Finset.disjoint_left.mpr
  intro P hPG hPH
  exact (Multiset.disjoint_left.mp (UniqueFactorizationMonoid.disjoint_normalizedFactors hcop.isRelPrime))
    (Multiset.mem_toFinset.mp hPG) (Multiset.mem_toFinset.mp hPH)

theorem idealZeroMask_generator_eq_one (I G : Ideal O) (hcop : IsCoprime I G) :
    idealZeroMask I (idealGenerator G) = 1 := by
  apply ite_eq_right
  rintro ⟨P,hP,hgen⟩
  have hPG : P ∣ G := by
    apply Ideal.dvd_iff_le.mpr
    rw [← span_idealGenerator G]
    exact Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hgen)
  exact (UniqueFactorizationMonoid.prime_of_normalized_factor P hP).not_isUnit
    (hcop.isRelPrime (UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hP) hPG)

theorem normalizedPairDensity_eq_primePoolDensity (I J G : Ideal O)
    (hI : IsCoprime I G) (hJ : IsCoprime J G) :
    normalizedPairDensity I J G = primePoolDensity G := by
  rw [normalizedPairDensity,primePoolDensity_eq_support]
  apply Finset.prod_congr rfl
  intro P hP
  have hPG : P ∣ G := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors
    (Multiset.mem_toFinset.mp hP)
  rw [idealZeroMask_generator_eq_one I P (hI.of_isCoprime_of_dvd_right hPG),
    idealZeroMask_generator_eq_one J P (hJ.of_isCoprime_of_dvd_right hPG),one_mul]

end

open ActualEisensteinCubic

def densityColumn {n : Type*} (cols : n → Ideal O) (a : n → ℂ) : n → ℂ :=
  fun j => primePoolDensity (cols j) * a j

theorem densityColumn_norm_le {n : Type*} (cols : n → Ideal O) (a : n → ℂ)
    (hcols : ∀ j, cols j ≠ 0) (j : n) : ‖densityColumn cols a j‖ ≤ ‖a j‖ := by
  rw [densityColumn,norm_mul]
  exact (mul_le_mul_of_nonneg_right (primePoolDensity_norm_le_one _ (hcols j))
    (norm_nonneg _)).trans_eq (one_mul _)

theorem densityColumn_energy_le {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (hcols : ∀ j, cols j ≠ 0) :
    (∑ j, ‖densityColumn cols a j‖^2) ≤ ∑ j, ‖a j‖^2 := by
  apply Finset.sum_le_sum
  intro j _
  exact pow_le_pow_left₀ (norm_nonneg _) (densityColumn_norm_le cols a hcols j) 2

theorem actualPrincipalDifference_densityColumn {n : Type*} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (K : ℝ)
    (hcols : ∀ j, cols j ≠ 0) (hcop : ∀ j, IsCoprime (cols j) G) :
    actualPrincipalDifference cols (densityColumn cols a) G K =
      (∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*primePoolDensity (cols j*cols k)*
          (normalizedPairPartial (cols j) (cols k) K * normalizedPairDivisors (cols j) (cols k) G)
        else 0) -
      primePoolDensity G * (∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
        star (a j)*a k*primePoolDensity (cols j*cols k)*
          normalizedPairCoprimePartial (cols j) (cols k) G K else 0) := by
  unfold actualPrincipalDifference
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hjk : IsCoprime (cols j) (cols k)
  · simp only [hjk,ite_true,densityColumn,star_mul,primePoolDensity_star,
      primePoolDensity_mul _ _ (hcols j) (hcols k) hjk,
      normalizedPairDensity_eq_primePoolDensity _ _ _ (hcop j) (hcop k)]
    ring
  · simp only [hjk,ite_false,mul_zero,sub_self]

theorem primePoolDensity_common_conductor (I J G : Ideal O)
    (hI : I ≠ 0) (hJ : J ≠ 0) (hG : G ≠ 0)
    (hIJ : IsCoprime I J) (hGI : IsCoprime G I) (hGJ : IsCoprime G J) :
    primePoolDensity (G*(I*J)) = primePoolDensity G*(primePoolDensity I*primePoolDensity J) := by
  rw [primePoolDensity_mul G (I*J) hG (mul_ne_zero hI hJ) (hGI.mul_right hGJ),
    primePoolDensity_mul I J hI hJ hIJ]

open ActualEisensteinCubic ConcretePrimeRowBridge CompletedGauss IdealMobiusDivisorSum

def densityPairSum {n : Type} [Fintype n] (cols : n → Ideal O) (a : n → ℂ)
    (P : Ideal O → Ideal O → ℂ) : ℂ :=
  ∑ j, ∑ k, if IsCoprime (cols j) (cols k) then
    star (a j)*a k*primePoolDensity (cols j*cols k)*P (cols j) (cols k) else 0

theorem unrestrictedPrincipalDensity_eq {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (R : ℝ) (hR : 0 ≤ R) :
    unrestrictedPrincipalDensity rows cols cols a a R =
      (Real.sqrt R : ℂ)*densityPairSum cols a
        (fun I J => ∑ i, normalizedIdealPair I J (rows i)) := by
  unfold unrestrictedPrincipalDensity
  rw [Finset.sum_comm]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [unrestrictedPairTerm,hc,ite_true,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Real.sqrt_div hR]
    simp only [Complex.ofReal_div,normalizedIdealPair]
    ring
  · simp only [unrestrictedPairTerm,hc,ite_false,zero_mul,mul_zero,Finset.sum_const_zero]

theorem unrestrictedPrincipalDensity_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (R K : ℝ) (hR : 0 ≤ R) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols a a R =
      (Real.sqrt R : ℂ)*densityPairSum cols a (fun I J => normalizedPairPartial I J K) := by
  simpa only [normalizedPairPartial] using
    unrestrictedPrincipalDensity_eq (fun I : squarefreeIdealRange K => I.val) cols a R hR

theorem originalTerm_one_eq_unrestricted {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (rows : m → Ideal O) (cols : n → Ideal O)
    (a : n → ℂ) (hrows : ∀ i, Supported (rows i)) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k)) (i : m) (j k : n) :
    originalTerm rows cols cols a a 1 1 i j k = unrestrictedPairTerm rows cols cols a a i j k := by
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [originalTerm,unrestrictedPairTerm,hc,ite_true,one_dvd,star_mul,
      canonical_quadraticRow_star _ (hcols j),
      unrestrictedPairCharacter_eq_primary _ _ (hcols j) (hcols k) (hray j k) _ (hrows i)]
    ring
  · simp only [originalTerm,unrestrictedPairTerm,hc,ite_false]

theorem maskedSourceDensity_eq {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (G : Ideal O) (hG : G ≠ 0)
    (rows : m → Ideal O) (cols : n → Ideal O) (a : n → ℂ) (M : ℝ)
    (hrows : ∀ i, Supported (rows i)) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) :
    maskedSourceDensity G rows cols a M =
      primePoolDensity G*unrestrictedPrincipalDensity rows cols cols a a M := by
  simp only [maskedSourceDensity,unrestrictedPrincipalDensity,Finset.mul_sum,sourcePrincipalScale]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [originalTerm_one_eq_unrestricted rows cols a hrows hcols hray]
  by_cases hc : IsCoprime (cols j) (cols k)
  · rw [primePoolDensity_mul G (cols j*cols k) hG (mul_ne_zero (hcols j).1 (hcols k).1)
      ((hGc j).mul_right (hGc k))]
    ring
  · simp only [unrestrictedPairTerm,hc,ite_false,zero_mul,mul_zero]

theorem maskedSourceDensity_coprime_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (G : Ideal O) (hG : G ≠ 0) (K M : ℝ) (hM : 0 ≤ M) (cols : n → Ideal O) (a : n → ℂ)
    (hcols : ∀ j, Admissible (cols j)) (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) :
    maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M =
      (Real.sqrt M : ℂ)*primePoolDensity G* densityPairSum cols a
        (fun I J => normalizedPairCoprimePartial I J G K) := by
  rw [maskedSourceDensity_eq G hG _ cols a M]
  · rw [unrestrictedPrincipalDensity_eq _ _ _ _ hM]
    unfold normalizedPairCoprimePartial
    ring
  · intro I
    exact admissible_supported ((mem_idealRange.mp
      (coprimeSquarefreeRange_subset_idealRange G hbad K I.property)).1)
  · exact hcols
  · exact hray
  · exact hGc

end CanonicalQuadraticSieve

end

end OAI
end OAIOriginalModule0168

/-! Original module: OAI.NumberTheory.DirichletL.QuadraticSieve.CuspCoercivity
Source SHA256: 96228e3d216646d2ae4e211a86159e78023ea5cc6e4c593073b6bc75dda5b570
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0169


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
open ActualEisensteinCubic ConcretePrimeRowBridge IdealMobiusDivisorSum

theorem unrestrictedPrincipalDensity_twisted_squarefree {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (q : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
      (fun j => a j*quadraticRow (cols j) (idealGenerator q))
      (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ)) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
  rw [unrestrictedPrincipalDensity_squarefree _ _ _ _ (by positivity),Real.sqrt_div hM]
  simp only [densityPairSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true,star_mul,canonical_quadraticRow_star _ (hcols j),
      normalizedIdealPair,unrestrictedPairCharacter,Complex.ofReal_div]
    ring
  · simp only [hc,ite_false,mul_zero]

theorem densityPairSum_weighted_sum {n : Type} [Fintype n]
    (cols : n → Ideal O) (a : n → ℂ) {ι : Type*} (S : Finset ι) (c : ι → ℂ)
    (P : Ideal O → Ideal O → ℂ) (Q : ι → Ideal O → Ideal O → ℂ) :
    (∑ q ∈ S, c q*densityPairSum cols a (fun I J => P I J*Q q I J)) =
      densityPairSum cols a (fun I J => P I J*∑ q ∈ S, c q*Q q I J) := by
  simp only [densityPairSum,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hc : IsCoprime (cols j) (cols k)
  · simp only [hc,ite_true]
    apply Finset.sum_congr rfl
    intro q hq
    ring
  · simp only [hc,ite_false,mul_zero,Finset.sum_const_zero]

theorem summed_dual_density {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (M K : ℝ) (hM : 0 ≤ M)
    (hcols : ∀ j, Admissible (cols j)) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) =
      (Real.sqrt M : ℂ)*densityPairSum cols a
        (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) := by
  simp_rw [unrestrictedPrincipalDensity_twisted_squarefree cols a _ M K hM hcols]
  calc
    _ = (Real.sqrt M : ℂ)*∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
        densityPairSum cols a (fun I J => normalizedPairPartial I J K*normalizedIdealPair I J q) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      ring
    _ = _ := by
      rw [densityPairSum_weighted_sum]
      rfl

theorem actual_source_dual_density_cancellation {n : Type} [Fintype n] [DecidableEq n]
    (cols : n → Ideal O) (a : n → ℂ) (G : Ideal O) (hG : G ≠ 0)
    (M K : ℝ) (hM : 0 ≤ M) (hcols : ∀ j, Admissible (cols j))
    (hray : ∀ j k, columnRay (cols j)=columnRay (cols k))
    (hGc : ∀ j, IsCoprime G (cols j)) (hbad : ∀ P ∈ fixedBadPrimes, P ∣ G) :
    (∑ q ∈ idealDivisors G, (UniqueFactorizationMonoid.moebius q:ℂ)*
      unrestrictedPrincipalDensity (fun I : squarefreeIdealRange K => I.val) cols cols
        (fun j => a j*quadraticRow (cols j) (idealGenerator q))
        (fun j => a j*quadraticRow (cols j) (idealGenerator q)) (M/(Ideal.absNorm q:ℝ))) -
      maskedSourceDensity G (fun I : coprimeSquarefreeRange G K => I.val) cols a M =
      (Real.sqrt M : ℂ)*actualPrincipalDifference cols (densityColumn cols a) G K := by
  rw [summed_dual_density cols a G M K hM hcols,
    maskedSourceDensity_coprime_squarefree G hG K M hM cols a hcols hray hGc hbad,
    actualPrincipalDifference_densityColumn cols a G K
      (fun j => (hcols j).1) (fun j => (hGc j).symm)]
  change _ = (Real.sqrt M:ℂ)*(densityPairSum cols a
    (fun I J => normalizedPairPartial I J K*normalizedPairDivisors I J G) -
    primePoolDensity G*densityPairSum cols a (fun I J => normalizedPairCoprimePartial I J G K))
  ring

end CanonicalQuadraticSieve

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

namespace CubicEisenstein

section

lemma cusp_hardy_square_identity (u du : ℂ) (v : ℝ) (hv : v≠0) :
    ‖du‖^2/v-‖u‖^2/v^3=
      ‖du-v⁻¹ • u‖^2/v+
        (2*⟪u,du⟫_ℝ/v^2-2*‖u‖^2/v^3) := by
  rw [norm_sub_sq_real,real_inner_smul_right,norm_smul,Real.norm_eq_abs,
    mul_pow,sq_abs,real_inner_comm du u]
  field_simp
  ; ring

lemma cusp_hardy_boundary_hasDerivAt (f : ℝ → ℂ) (v : ℝ)
    (hf : DifferentiableAt ℝ f v) (hv : v≠0) :
    HasDerivAt (fun t => ‖f t‖^2/t^2)
      (2*⟪f v,deriv f v⟫_ℝ/v^2-2*‖f v‖^2/v^3) v := by
  convert hf.hasDerivAt.norm_sq.div ((hasDerivAt_id v).pow 2) (pow_ne_zero 2 hv) using 1
  · rfl
  · dsimp
    field_simp

theorem cusp_hardy_interval_identity (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫t in a..b,‖deriv f t‖^2/t)-(∫t in a..b,‖f t‖^2/t^3)=
      (∫t in a..b,‖deriv f t-t⁻¹ • f t‖^2/t)+
        (‖f b‖^2/b^2-‖f a‖^2/a^2) := by
  have hfC : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hn : ∀t∈Set.Icc a b,t≠0 := fun t ht => (ha.trans_le ht.1).ne'
  have hiE : IntervalIntegrable (fun t => ‖deriv f t‖^2/t) volume a b :=
    ((hdf.norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiM : IntervalIntegrable (fun t => ‖f t‖^2/t^3) volume a b :=
    ((hfC.norm.pow 2).div (continuousOn_id.pow 3) (fun t ht => pow_ne_zero 3 (hn t ht))).intervalIntegrable_of_Icc hab
  have hiS : IntervalIntegrable (fun t => ‖deriv f t-t⁻¹ • f t‖^2/t) volume a b :=
    (((hdf.sub ((continuousOn_id.inv₀ hn).smul hfC)).norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiB : IntervalIntegrable
      (fun t => 2*⟪f t,deriv f t⟫_ℝ/t^2-2*‖f t‖^2/t^3) volume a b :=
    ((((hfC.inner hdf).const_mul 2).div (continuousOn_id.pow 2)
      (fun t ht => pow_ne_zero 2 (hn t ht))).sub
        (((hfC.norm.pow 2).const_mul 2).div (continuousOn_id.pow 3)
          (fun t ht => pow_ne_zero 3 (hn t ht)))).intervalIntegrable_of_Icc hab
  have hB := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t (ht : t∈Set.uIcc a b) => cusp_hardy_boundary_hasDerivAt f t
      (hf t (by simpa only [Set.uIcc_of_le hab] using ht))
      (hn t (by simpa only [Set.uIcc_of_le hab] using ht))) hiB
  rw [←intervalIntegral.integral_sub hiE hiM]
  calc
    _ = ∫t in a..b, ‖deriv f t-t⁻¹ • f t‖^2/t+
          (2*⟪f t,deriv f t⟫_ℝ/t^2-2*‖f t‖^2/t^3) := by
      apply intervalIntegral.integral_congr
      intro t ht
      exact cusp_hardy_square_identity (f t) (deriv f t) t
        (hn t (by simpa only [Set.uIcc_of_le hab] using ht))
    _ = _ := by rw [intervalIntegral.integral_add hiS hiB,hB]

theorem cusp_hardy_interval (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b) (hfa : f a=0)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫t in a..b,‖f t‖^2/t^3)≤∫t in a..b,‖deriv f t‖^2/t := by
  have hid := cusp_hardy_interval_identity f a b ha hab hf hdf
  have hsq : 0≤∫t in a..b,‖deriv f t-t⁻¹ • f t‖^2/t := by
    apply intervalIntegral.integral_nonneg hab
    intro t ht
    exact div_nonneg (sq_nonneg _) (ha.trans_le ht.1).le
  have hb : 0≤‖f b‖^2/b^2 := div_nonneg (sq_nonneg _) (sq_nonneg _)
  simp only [hfa,norm_zero,zero_pow (by decide : 2≠0),zero_div,sub_zero] at hid
  linarith

theorem cusp_hardy_halfline (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a))
    (hM : IntegrableOn (fun t => ‖f t‖^2/t^3) (Set.Ioi a) volume)
    (hE : IntegrableOn (fun t => ‖deriv f t‖^2/t) (Set.Ioi a) volume) :
    (∫t in Set.Ioi a,‖f t‖^2/t^3)≤∫t in Set.Ioi a,‖deriv f t‖^2/t := by
  apply le_of_tendsto_of_tendsto
    (intervalIntegral_tendsto_integral_Ioi a hM tendsto_id)
    (intervalIntegral_tendsto_integral_Ioi a hE tendsto_id)
  filter_upwards [eventually_ge_atTop a] with b hab
  exact cusp_hardy_interval f a b ha hab hfa
    (fun t ht => hf t ht.1) (hdf.mono (fun t ht => ht.1))

theorem cusp_hardy_interval_lintegral (f : ℝ → ℂ) (a b : ℝ)
    (ha : 0<a) (hab : a≤b) (hfa : f a=0)
    (hf : ∀t∈Set.Icc a b,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Icc a b)) :
    (∫⁻t in Set.Ioc a b,ENNReal.ofReal (‖f t‖^2/t^3))≤
      ∫⁻t in Set.Ioc a b,ENNReal.ofReal (‖deriv f t‖^2/t) := by
  have hfC : ContinuousOn f (Set.Icc a b) :=
    fun t ht => (hf t ht).continuousAt.continuousWithinAt
  have hn : ∀t∈Set.Icc a b,t≠0 := fun t ht => (ha.trans_le ht.1).ne'
  have hiE : IntervalIntegrable (fun t => ‖deriv f t‖^2/t) volume a b :=
    ((hdf.norm.pow 2).div continuousOn_id hn).intervalIntegrable_of_Icc hab
  have hiM : IntervalIntegrable (fun t => ‖f t‖^2/t^3) volume a b :=
    ((hfC.norm.pow 2).div (continuousOn_id.pow 3)
      (fun t ht => pow_ne_zero 3 (hn t ht))).intervalIntegrable_of_Icc hab
  have hEnn : 0≤ᵐ[volume.restrict (Set.Ioc a b)] (fun t => ‖deriv f t‖^2/t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (sq_nonneg _) (ha.trans ht.1).le
  have hMnn : 0≤ᵐ[volume.restrict (Set.Ioc a b)] (fun t => ‖f t‖^2/t^3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    exact div_nonneg (sq_nonneg _) (pow_nonneg (ha.trans ht.1).le 3)
  rw [←ofReal_integral_eq_lintegral_ofReal hiM.1 hMnn,
    ←ofReal_integral_eq_lintegral_ofReal hiE.1 hEnn]
  apply ENNReal.ofReal_le_ofReal
  simpa only [intervalIntegral.integral_of_le hab] using
    cusp_hardy_interval f a b ha hab hfa hf hdf

theorem cusp_hardy_halfline_lintegral (f : ℝ → ℂ) (a : ℝ) (ha : 0<a) (hfa : f a=0)
    (hf : ∀t∈Set.Ici a,DifferentiableAt ℝ f t)
    (hdf : ContinuousOn (deriv f) (Set.Ici a)) :
    (∫⁻t in Set.Ioi a,ENNReal.ofReal (‖f t‖^2/t^3))≤
      ∫⁻t in Set.Ioi a,ENNReal.ofReal (‖deriv f t‖^2/t) := by
  have hcover : (⋃n : ℕ,Set.Ioc a (a+n))=Set.Ioi a := by
    ext t
    constructor
    · rintro ⟨_,⟨n,rfl⟩,ht⟩
      exact ht.1
    · intro ht
      obtain ⟨n,hn⟩ := exists_nat_ge (t-a)
      exact Set.mem_iUnion.mpr ⟨n,ht,by linarith⟩
  have hdir : Directed (· ⊆ ·) (fun n : ℕ => Set.Ioc a (a+n)) := by
