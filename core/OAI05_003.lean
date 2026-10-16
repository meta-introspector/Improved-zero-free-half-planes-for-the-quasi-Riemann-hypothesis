    (hg : goodLambda∉P) (hchar : ringChar (O⧸P)≠2)
    (c e : ℕ) (hc : 1≤c) (he : ¬6∣e) (hcop : IsCoprime Q (P^c))
    [Fintype (O⧸Q)] [Fintype (O⧸P^c)] [Fintype (O⧸Q*P^c)]
    (F : O→O→ℂ) (hF : ∀x z y,x-z∈Q → F x y=F z y) (d : O) :
    (∑x : O⧸Q*P^c,∑y : O⧸Q*P^c,
      (actualSextic P hg^e) (Ideal.Quotient.mk P (d*x.out))*F x.out y.out)=0 := by
  let E := Ideal.quotientMulEquivQuotientProd Q (P^c) hcop
  have hE (x : O⧸Q*P^c) : E x=(Ideal.Quotient.mk Q x.out,Ideal.Quotient.mk (P^c) x.out) := by
    conv_lhs => rw [←Ideal.Quotient.mk_out x]
    rfl
  have hf (x : O⧸Q*P^c) (y : O) : F x.out y=F (E x).1.out y := by
    apply hF
    apply Ideal.Quotient.eq.mp
    rw [Ideal.Quotient.mk_out,hE]
  have hp (x : O⧸Q*P^c) : Ideal.Quotient.mk P (d*x.out)=
      Ideal.Quotient.mk P d*primePowerReduction P hc (E x).2 := by
    rw [map_mul,hE]
    rfl
  have hz := crt_joint_mean_zero Q P hg hchar c e hc he hcop
    (fun x y=>F x.out y.out) d
  convert hz using 1
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  rw [hp,hf]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule0896

/-! Original module: OAI.NumberTheory.DirichletL.Moments.MobiusRegroup
Source SHA256: 30326a9df8798a1ffd91c03643d6c82f0d94705da578699d9af0861b3d7e923d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0897


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentMobiusRegroup
open IdealMobiusDivisorSum UniqueFactorizationMonoid CenteredMomentMask
local notation "O" => ActualEisensteinCubic.O

def divisorPool {β : Type*} (T : Finset β) (B : β → Ideal O) : Finset (Ideal O) :=
  T.biUnion (fun j => idealDivisors (B j))

theorem mobius_on_pool {β : Type*} (T : Finset β) (B : β → Ideal O)
    (hB : ∀ j ∈ T, B j ≠ 0) (j : β) (hj : j ∈ T) (I : Ideal O) :
    (if IsCoprime I (B j) then (1 : ℂ) else 0) =
      ∑ D ∈ divisorPool T B, if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
  rw [ideal_coprime_mobius I (B j) (hB j hj)]
  have hsub : idealDivisors (B j) ⊆ divisorPool T B :=
    fun D hD => Finset.mem_biUnion.mpr ⟨j,hj,hD⟩
  calc
    _ = ∑ D ∈ idealDivisors (B j), if D ∣ I ∧ D ∣ B j then (moebius D : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro D hD
      simp only [(mem_idealDivisors (hB j hj)).mp hD, and_true]
    _ = _ := Finset.sum_subset hsub (by
      intro D hD hn
      have hnd : ¬ D ∣ B j := fun hd => hn ((mem_idealDivisors (hB j hj)).mpr hd)
      simp only [hnd, and_false, ite_false])

theorem finite_pair_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (A : α → Ideal O) (B : β → Ideal O) (hB : ∀ j ∈ T, B j ≠ 0)
    (F : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T, if IsCoprime (A i) (B j) then F i j else 0) =
      ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T, if D ∣ A i ∧ D ∣ B j then F i j else 0 := by
  have ht (i : α) (j : β) (hj : j ∈ T) :
      (if IsCoprime (A i) (B j) then F i j else 0) =
        ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
          (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
    have hm := congrArg (fun z : ℂ => z * F i j) (mobius_on_pool T B hB j hj (A i))
    simpa only [ite_mul, one_mul, zero_mul, Finset.sum_mul, mul_ite, mul_zero] using hm
  calc
    _ = ∑ i ∈ S, ∑ j ∈ T, ∑ D ∈ divisorPool T B, (moebius D : ℂ) *
        (if D ∣ A i ∧ D ∣ B j then F i j else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      exact ht i j hj
    _ = _ := by
      simp_rw [Finset.sum_comm (s := T) (t := divisorPool T B)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro D hD
      simp only [Finset.mul_sum]

open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation

theorem finite_correlation_mobius {α β : Type*} (S : Finset α) (T : Finset β)
    (D E : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ D - 1)
    (hpE : ConcretePrimeRowBridge.goodLambda ^ 2 ∣ E - 1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ a i - 1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda ^ 2 ∣ b j - 1)
    (hcopA : ∀ i, IsCoprime (D * E) (a i)) (hcopB : ∀ j, IsCoprime (D * E) (b j))
    (h : O) (c : α → ℂ) (d : β → ℂ) (K : α → β → ℂ) :
    (∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}), (moebius L : ℂ) *
        ∑ i ∈ S, ∑ j ∈ T,
          if L ∣ Ideal.span {a i} ∧ L ∣ Ideal.span {b j} then
            completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j
          else 0 := by
  have he (i : α) (j : β) :
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D * a i) (E * b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) h
       else 0) * (c i * star (d j)) * K i j =
      if IsCoprime (Ideal.span {a i}) (Ideal.span {b j}) then
        completeSupportExtension D E hD hE h (a i) (b j) * (c i * star (d j)) * K i j else 0 := by
    rw [Ideal.isCoprime_span_singleton_iff]
    by_cases hab : IsCoprime (a i) (b j)
    · rw [ite_eq_left hab, ite_eq_left hab, actual_complete_common_support D E (a i) (b j)
        hD hE (ha i) (hb j) hpD hpE (hpa i) (hpb j) (hcopA i) (hcopB j) hab]
    · simp only [ite_eq_right hab, zero_mul]
  simp_rw [he]
  exact finite_pair_mobius S T (fun i => Ideal.span {a i}) (fun j => Ideal.span {b j})
    (fun j _ => (hb j).1) _

end SevenEighths.CenteredMomentMobiusRegroup

end

end OAI
end OAIOriginalModule0897

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Support
Source SHA256: 2399cec862de47958a5240c0fcc82add5ecec41e589b619d174fd1791c59ea98
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0898


namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentSupport
open UniqueFactorizationMonoid IdealMobiusDivisorSum CanonicalQuadraticSieve

def supportExtract (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∈ S)).prod

def supportResidual (I : Ideal O) (S : Finset (Ideal O)) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P ∉ S)).prod

theorem supportExtract_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportExtract I S) = (normalizedFactors I).filter (fun P => P ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_factors (I : Ideal O) (S : Finset (Ideal O)) :
    normalizedFactors (supportResidual I S) = (normalizedFactors I).filter (fun P => P ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportExtract_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportExtract I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem supportResidual_ne_zero (I : Ideal O) (S : Finset (Ideal O)) : supportResidual I S ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors (fun _ h => (Multiset.mem_filter.mp h).1)

theorem support_reconstruct (I : Ideal O) (hI : I ≠ 0) (S : Finset (Ideal O)) :
    supportExtract I S * supportResidual I S = I := by
  rw [supportExtract, supportResidual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem supportExtract_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportExtract I S) = primeSupport I ∩ S := by
  ext P
  simp [primeSupport, supportExtract_factors]

theorem supportResidual_support (I : Ideal O) (S : Finset (Ideal O)) :
    primeSupport (supportResidual I S) = primeSupport I \ S := by
  ext P
  simp [primeSupport, supportResidual_factors]

theorem supportExtract_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportExtract I S)).count P =
      if P ∈ S then (normalizedFactors I).count P else 0 := by
  rw [supportExtract_factors, Multiset.count_filter]

theorem supportResidual_count (I P : Ideal O) (S : Finset (Ideal O)) :
    (normalizedFactors (supportResidual I S)).count P =
      if P ∈ S then 0 else (normalizedFactors I).count P := by
  rw [supportResidual_factors, Multiset.count_filter]
  split_ifs <;> rfl

theorem supportExtract_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportExtract I S) := by
  refine ⟨supportExtract_ne_zero I S, ?_⟩
  intro P hP
  rw [supportExtract_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem supportResidual_supported (I : Ideal O) (hI : Supported I) (S : Finset (Ideal O)) :
    Supported (supportResidual I S) := by
  refine ⟨supportResidual_ne_zero I S, ?_⟩
  intro P hP
  rw [supportResidual_factors] at hP
  exact hI.2 P (Multiset.mem_filter.mp hP).1

theorem extracted_residual_coprime (I J : Ideal O) (S : Finset (Ideal O)) :
    IsCoprime (supportExtract I S) (supportResidual J S) := by
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportExtract_ne_zero I S) (supportResidual_ne_zero J S)).mp
  rw [supportExtract_support, supportResidual_support]
  exact Finset.disjoint_left.mpr (by
    intro P hP hQ
    exact (Finset.mem_sdiff.mp hQ).2 (Finset.mem_inter.mp hP).2)

theorem common_support_residual_coprime (I J : Ideal O) :
    let S := primeSupport I ∩ primeSupport J
    IsCoprime (supportResidual I S) (supportResidual J S) := by
  dsimp only
  apply (IdealCoprimeSieveOperator.primeSupport_disjoint_iff
    (supportResidual_ne_zero I _) (supportResidual_ne_zero J _)).mp
  rw [supportResidual_support, supportResidual_support]
  apply Finset.disjoint_left.mpr
  intro P hP hQ
  exact (Finset.mem_sdiff.mp hP).2
    (Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hP).1, (Finset.mem_sdiff.mp hQ).1⟩)

theorem supportExtract_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportExtract (I * J) S = supportExtract I S * supportExtract J S := by
  simp only [supportExtract, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportResidual_mul (I J : Ideal O) (hI : I ≠ 0) (hJ : J ≠ 0)
    (S : Finset (Ideal O)) :
    supportResidual (I * J) S = supportResidual I S * supportResidual J S := by
  simp only [supportResidual, normalizedFactors_mul hI hJ, Multiset.filter_add, Multiset.prod_add]

theorem supportExtract_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportExtract P S = if P ∈ S then P else 1 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportExtract, hf, Multiset.filter_singleton]
  split_ifs <;> simp

theorem supportResidual_prime (P : Ideal O) (hP : Prime P) (S : Finset (Ideal O)) :
    supportResidual P S = if P ∈ S then 1 else P := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP))
  simp only [supportResidual, hf, Multiset.filter_singleton]
  split_ifs <;> simp_all

theorem shared_prime_slot_freeze (P I : Ideal O) (hP : Prime P) (hI : I ≠ 0)
    (S : Finset (Ideal O)) (hPS : P ∈ S) :
    supportExtract (P * I) S = P * supportExtract I S ∧
      supportResidual (P * I) S = supportResidual I S := by
  rw [supportExtract_mul P I hP.ne_zero hI S, supportResidual_mul P I hP.ne_zero hI S,
    supportExtract_prime P hP S, supportResidual_prime P hP S]
  simp only [hPS, ite_true, one_mul, and_self]

theorem supportExtract_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportExtract (∏ i ∈ T, p i) S = ∏ i ∈ T, supportExtract (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportExtract, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportExtract_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

theorem supportResidual_prod {ι : Type*} (T : Finset ι) (p : ι → Ideal O)
    (hp : ∀ i ∈ T, p i ≠ 0) (S : Finset (Ideal O)) :
    supportResidual (∏ i ∈ T, p i) S = ∏ i ∈ T, supportResidual (p i) S := by
  induction T using Finset.cons_induction with
  | empty => simp only [Finset.prod_empty, supportResidual, normalizedFactors_one, Multiset.filter_zero, Multiset.prod_zero]
  | cons i T hi ih =>
    rw [Finset.prod_cons, Finset.prod_cons,
      supportResidual_mul _ _ (hp i (Finset.mem_cons_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hp j (Finset.mem_cons_of_mem hj))) S,
      ih (fun j hj => hp j (Finset.mem_cons_of_mem hj))]

open CompletedGauss hiding primeSupport
open CanonicalRowCompletion CenteredMomentSupportedCorrelation

def idealCorrelation (I J : Ideal O) (hI : Supported I) (hJ : Supported J) (j : O) : ℂ :=
  actualCorrelation (primaryGenerator I) (primaryGenerator J)
    ((supported_span_primaryGenerator_iff I).mpr hI) ((supported_span_primaryGenerator_iff J).mpr hJ) j

theorem idealCorrelation_complete_extraction (I J : Ideal O)
    (hI : Supported I) (hJ : Supported J) (j : O) :
    let S := primeSupport I ∩ primeSupport J
    let D := supportExtract I S
    let E := supportExtract J S
    let A := supportResidual I S
    let B := supportResidual J S
    idealCorrelation I J hI hJ j =
      idealCorrelation D E (supportExtract_supported I hI S) (supportExtract_supported J hJ S) j *
        sexticReciprocityPhase (primaryGenerator A) (primaryGenerator E) *
        star (sexticReciprocityPhase (primaryGenerator B) (primaryGenerator D)) *
        sexticReciprocityPhase (primaryGenerator A) (primaryGenerator B) *
        idealRowHom j A * star (idealRowHom (-j) B) := by
  let S := primeSupport I ∩ primeSupport J
  let D := supportExtract I S
  let E := supportExtract J S
  let A := supportResidual I S
  let B := supportResidual J S
  have hD := supportExtract_supported I hI S
  have hE := supportExtract_supported J hJ S
  have hA := supportResidual_supported I hI S
  have hB := supportResidual_supported J hJ S
  have hpD := primaryGenerator_spec D (supported_primaryGenerator_ne_zero D hD)
  have hpE := primaryGenerator_spec E (supported_primaryGenerator_ne_zero E hE)
  have hpA := primaryGenerator_spec A (supported_primaryGenerator_ne_zero A hA)
  have hpB := primaryGenerator_spec B (supported_primaryGenerator_ne_zero B hB)
  have hcpA : IsCoprime (primaryGenerator D * primaryGenerator E) (primaryGenerator A) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpD.1, hpE.1, hpA.1]
    exact (extracted_residual_coprime I I S).mul_left (extracted_residual_coprime J I S)
  have hcpB : IsCoprime (primaryGenerator D * primaryGenerator E) (primaryGenerator B) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [← Ideal.span_singleton_mul_span_singleton, hpD.1, hpE.1, hpB.1]
    exact (extracted_residual_coprime I J S).mul_left (extracted_residual_coprime J J S)
  have hcpAB : IsCoprime (primaryGenerator A) (primaryGenerator B) := by
    apply (Ideal.isCoprime_span_singleton_iff _ _).mp
    rw [hpA.1, hpB.1]
    exact common_support_residual_coprime I J
  have h := actual_complete_common_support
    (primaryGenerator D) (primaryGenerator E) (primaryGenerator A) (primaryGenerator B)
    ((supported_span_primaryGenerator_iff D).mpr hD)
    ((supported_span_primaryGenerator_iff E).mpr hE)
    ((supported_span_primaryGenerator_iff A).mpr hA)
    ((supported_span_primaryGenerator_iff B).mpr hB)
    hpD.2 hpE.2 hpA.2 hpB.2 hcpA hcpB hcpAB j
  have hDA : D * A = I := support_reconstruct I hI.1 S
  have hEB : E * B = J := support_reconstruct J hJ.1 S
  simpa only [completeSupportExtension, ← primaryGenerator_mul, hDA, hEB, hpA.1, hpB.1,
    idealCorrelation] using h

end SevenEighths.CenteredMomentSupport
end

end OAI
end OAIOriginalModule0898

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Twist
Source SHA256: 4037b36343435e0d685e578d293c8e1a30c425155894b0083beeb2f1b1537af2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0899


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTwist
open ActualEisensteinCubic EisensteinSchwartzPoisson
open CenteredMomentLattice CenteredMomentCancellation CenteredMomentCounting

def twistedMaskedSum (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (t X : ℝ) : ℂ :=
  ∑' I : Ideal O, (if IsCoprime I R then (1 : ℂ) else 0) *
    (CenteredMomentPrimary.primaryIdealCharacter c χ I *
      (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * W ((Ideal.absNorm I : ℝ) / X))

lemma normPowerProfile_support (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    Function.support (normPowerProfile W a b ha hs hW t : ℝ → ℂ) ⊆ Function.support W := by
  intro x hx hz
  exact hx (by rw [normPowerProfile_apply, hz, mul_zero])

lemma normPowerProfile_norm (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W) (t x : ℝ) :
    ‖normPowerProfile W a b ha hs hW t x‖ = ‖W x‖ := by
  rw [normPowerProfile, CompletedHeight.uniformTwistedSchwartz_apply,
    CompletedHeight.normTwistedSource, norm_mul, FourierBridge.logPhase_norm, one_mul]

lemma norm_real_imaginary_power (X t : ℝ) (hX : 0 < X) :
    ‖(X : ℂ) ^ (Complex.I * t)‖ = 1 := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hX]
  simp

theorem twistedMaskedSum_scale (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    twistedMaskedSum c χ R W t X = (X : ℂ) ^ (Complex.I * t) *
      maskedSum c χ R (normPowerProfile W a b ha hs hW t) X := by
  unfold twistedMaskedSum maskedSum
  rw [← tsum_mul_left]
  apply tsum_congr
  intro I
  rw [normPowerProfile_apply]
  have hphase : (Ideal.absNorm I : ℂ) ^ (Complex.I * t) =
      (X : ℂ) ^ (Complex.I * t) *
        (((Ideal.absNorm I : ℝ) / X : ℝ) : ℂ) ^ (Complex.I * t) := by
    have h := Complex.mul_cpow_ofReal_nonneg hX.le
      (div_nonneg (Nat.cast_nonneg (Ideal.absNorm I)) hX.le) (Complex.I * t)
    have heq : X * ((Ideal.absNorm I : ℝ) / X) = (Ideal.absNorm I : ℝ) := by field_simp
    rw [← Complex.ofReal_mul, heq, Complex.ofReal_natCast] at h
    exact h
  rw [hphase]
  ring

theorem twistedMaskedSum_volume (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum c χ R W t X -
      (X : ℂ) ^ (1 + Complex.I * t) * maskedDensity c hc χ R *
        paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      maskedError c hc χ R (normPowerProfile W a b ha hs hW t) := by
  rw [twistedMaskedSum_scale c χ R W a b ha hs hW t X hX]
  have hmain : (X : ℂ) ^ (1 + Complex.I * t) * maskedDensity c hc χ R *
      paperRadialFourier (normPowerProfile W a b ha hs hW t) 0 =
    (X : ℂ) ^ (Complex.I * t) * ((X : ℂ) *
      (maskedDensity c hc χ R * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0)) := by
    rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hX.ne'), Complex.cpow_one]
    ring
  rw [hmain, ← mul_sub, norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_volume c hc h3 χ R hR _ b X hX
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twistedMaskedSum_absolute (c : O) (hc : c ≠ 0)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (W : ℝ → ℂ) (a b M : ℝ) (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t X : ℝ) (hX : 0 < X) :
    ‖twistedMaskedSum c χ R W t X‖ ≤ (128 * b * M) * X := by
  rw [twistedMaskedSum_scale c χ R W a b ha hs hW t X hX,
    norm_mul, norm_real_imaginary_power X t hX, one_mul]
  exact maskedSum_absolute c hc χ R _ b M X hb hM hX
    (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y))
    ((normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2))

theorem twisted_volumeCoefficient_norm_le (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W : ℝ → ℂ) (a b M : ℝ)
    (ha : 0 < a) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (hbound : ∀ y, ‖W y‖ ≤ M) (t : ℝ) :
    ‖maskedDensity c hc χ R * paperRadialFourier (normPowerProfile W a b ha hs hW t) 0‖ ≤
      128 * b * M := by
  let V := normPowerProfile W a b ha hs hW t
  have hV : Function.support (V : ℝ → ℂ) ⊆ Set.Iic b :=
    (normPowerProfile_support W a b ha hs hW t).trans (fun _ hx => (hs hx).2)
  exact norm_linear_coefficient_le (fun X => maskedSum c χ R V X)
    _ (128 * b * M) (maskedError c hc χ R V) (maskedError_nonneg c hc χ R V)
    (fun X hX => maskedSum_volume c hc h3 χ R hR V b X hX hV)
    (fun X hX => maskedSum_absolute c hc χ R V b M X hb hM hX
      (fun y => (normPowerProfile_norm W a b ha hs hW t y).trans_le (hbound y)) hV)

theorem twisted_rectangle_saving
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (hR : R ≠ 0) (W₁ W₂ : ℝ → ℂ) (a₁ b₁ a₂ b₂ M₁ M₂ : ℝ)
    (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (hbound₁ : ∀ y, ‖W₁ y‖ ≤ M₁) (hbound₂ : ∀ y, ‖W₂ y‖ ≤ M₂)
    (t X₁ X₂ Y₁ Y₂ T L : ℝ) (hL : 0 < L)
    (hX₁ : L ≤ X₁) (hX₂ : L ≤ X₂) (hY₁ : L ≤ Y₁) (hY₂ : L ≤ Y₂)
    (hprodX : X₁ * X₂ = T) (hprodY : Y₁ * Y₂ = T) :
    let E := maskedError c hc χ R (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
      maskedError c hc χ R (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
    ‖twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
      twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂‖ ≤
      4 * E * (128 * (b₁ * M₁ + b₂ * M₂)) * (T / L) := by
  let V₁ := normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t
  let V₂ := normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t
  let E := maskedError c hc χ R V₁ + maskedError c hc χ R V₂
  let C := 128 * (b₁ * M₁ + b₂ * M₂)
  let v₁ := maskedDensity c hc χ R * paperRadialFourier V₁ 0
  let v₂ := maskedDensity c hc χ R * paperRadialFourier V₂ 0
  let m₁ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₁
  let m₂ := fun X : ℝ => (X : ℂ) ^ (1 + Complex.I * t) * v₂
  have hE₁ := maskedError_nonneg c hc χ R V₁
  have hE₂ := maskedError_nonneg c hc χ R V₂
  have hE : 0 ≤ E := add_nonneg hE₁ hE₂
  have hC : 0 ≤ C := mul_nonneg (by norm_num) (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  have hC₁ : 128 * b₁ * M₁ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₂ hM₂]
  have hC₂ : 128 * b₂ * M₂ ≤ C := by dsimp only [C]; nlinarith [mul_nonneg hb₁ hM₁]
  have he₁ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₁ t X - m₁ X‖ ≤ E := by
    have h := twistedMaskedSum_volume c hc h3 χ R hR W₁ a₁ b₁ ha₁ hs₁ hW₁ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₁‖ ≤ E
    simpa only [v₁, mul_assoc] using h.trans (le_add_of_nonneg_right hE₂)
  have he₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₂ t X - m₂ X‖ ≤ E := by
    have h := twistedMaskedSum_volume c hc h3 χ R hR W₂ a₂ b₂ ha₂ hs₂ hW₂ t X
      (lt_of_lt_of_le hL hX)
    change ‖_ - _ * v₂‖ ≤ E
    simpa only [v₂, mul_assoc] using h.trans (le_add_of_nonneg_left hE₁)
  have hmain₁ (X : ℝ) (hX : L ≤ X) : ‖m₁ X‖ ≤ C * X := by
    have hv := (twisted_volumeCoefficient_norm_le c hc h3 χ R hR W₁ a₁ b₁ M₁
      ha₁ hb₁ hM₁ hs₁ hW₁ hbound₁ t).trans hC₁
    dsimp only [m₁]
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le hL hX)]
    simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.I_re, zero_mul,
      Complex.ofReal_im, mul_zero, sub_self, add_zero, Real.rpow_one]
    nlinarith [mul_le_mul_of_nonneg_left hv (le_trans hL.le hX)]
  have habs₂ (X : ℝ) (hX : L ≤ X) : ‖twistedMaskedSum c χ R W₂ t X‖ ≤ C * X :=
    (twistedMaskedSum_absolute c hc χ R W₂ a₂ b₂ M₂ ha₂ hb₂ hM₂ hs₂ hW₂ hbound₂ t X
      (lt_of_lt_of_le hL hX)).trans (mul_le_mul_of_nonneg_right hC₂ (le_trans hL.le hX))
  have hmain : m₁ X₁ * m₂ X₂ = m₁ Y₁ * m₂ Y₂ := by
    have hpow := CenteredMoment.volume_products_eq
      (1 : ℂ) v₁ v₂ t X₁ X₂ Y₁ Y₂ (le_trans hL.le hX₁) (le_trans hL.le hX₂)
      (le_trans hL.le hY₁) (le_trans hL.le hY₂) (hprodX.trans hprodY.symm)
    simpa only [CenteredMoment.volumeTerm, one_mul, m₁, m₂] using hpow
  exact CenteredMoment.centered_saving_of_approx _ _ _ _ _ _ _ _
    X₁ X₂ Y₁ Y₂ T L C E hmain hC hE (he₁ X₁ hX₁) (he₂ X₂ hX₂)
    (he₁ Y₁ hY₁) (he₂ Y₂ hY₂) (habs₂ X₂ hX₂) (hmain₁ X₁ hX₁)
    (habs₂ Y₂ hY₂) (hmain₁ Y₁ hY₁) hL hX₁ hX₂ hY₁ hY₂ hprodX hprodY

end SevenEighths.CenteredMomentTwist
end

end OAI
end OAIOriginalModule0899

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Height
Source SHA256: fbbacbc778756595e60b96291a80f624796fede5d485f9c1e530fb8b2bea4ea8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0900


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentHeight
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open QuadraticInitialBound CenteredMomentLattice CenteredMomentMask
open CenteredMomentPrimary CenteredMomentCancellation CenteredMomentTwist

lemma normalized_height_le (t : ℝ) : ‖t / (2 * Real.pi)‖ ≤ ‖t‖ := by
  rw [norm_div, Real.norm_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
  exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])

theorem maskedError_polynomial_height (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (a b ε B : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ n : ℕ, ∀ W : ℝ → ℂ, ∀ hs : Function.support W ⊆ Set.Icc a b,
      ∀ hW : ContDiff ℝ ∞ W, ∃ C : ℝ, 0 < C ∧
      ∀ Z : ℝ, 1 ≤ Z → ∀ R : Ideal O, R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ t : ℝ, maskedError c hc χ R (normPowerProfile W a b ha hs hW t) ≤
        C * Z ^ ε * (1 + ‖t‖) ^ n := by
  obtain ⟨n, hn⟩ := normPowerProfile_uniform_degree a b ha pvSeminorms
  obtain ⟨D, hD, hdiv⟩ := polynomial_mask_divisor_bound ε B hε hB
  refine ⟨n, ?_⟩
  intro W hs hW
  obtain ⟨C, hC, hprofile⟩ := hn W hs hW
  let : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  let : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let mass : ℝ := ∑ r : O ⧸ Ideal.span {c}, ‖primaryResidueValue c χ r‖
  have hmass : 0 ≤ mass := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  let A := D * mass * pvConstant * C
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (mul_nonneg hD.le hmass) pvConstant_pos.le) hC.le
  refine ⟨1 + A, by linarith, ?_⟩
  intro Z hZ R hR hnorm t
  have hheight : (1 + ‖t / (2 * Real.pi)‖) ^ n ≤ (1 + ‖t‖) ^ n := by
    gcongr
    exact normalized_height_le t
  have hseminorm := (hprofile t).trans (mul_le_mul_of_nonneg_left hheight hC.le)
  have herr : maskedError c hc χ R (normPowerProfile W a b ha hs hW t) ≤
      (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := by
    unfold maskedError pvControl
    apply mul_le_mul (hdiv Z hZ R hR hnorm)
      (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hseminorm pvConstant_pos.le) hmass)
    · exact mul_nonneg hmass (mul_nonneg pvConstant_pos.le (apply_nonneg _ _))
    · exact mul_nonneg hD.le (Real.rpow_nonneg (by linarith) _)
  calc
    _ ≤ (D * Z ^ ε) * (mass * (pvConstant * (C * (1 + ‖t‖) ^ n))) := herr
    _ = A * Z ^ ε * (1 + ‖t‖) ^ n := by dsimp only [A]; ring
    _ ≤ (1 + A) * Z ^ ε * (1 + ‖t‖) ^ n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by linarith : A ≤ 1 + A)
          (Real.rpow_nonneg (le_trans zero_le_one hZ) ε)) (by positivity)

theorem normalized_masked_rectangle_estimate
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal O, R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁ * X₂ = T → Y₁ * Y₂ = T →
      ‖(Real.sqrt T : ℂ)⁻¹ *
        (twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
          twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂)‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ J * (Real.sqrt T / L) := by
  obtain ⟨n₁, hn₁⟩ := maskedError_polynomial_height c hc χ a₁ b₁ ε B ha₁ hε hB
  obtain ⟨n₂, hn₂⟩ := maskedError_polynomial_height c hc χ a₂ b₂ ε B ha₂ hε hB
  refine ⟨max n₁ n₂, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨D₁, hD₁, herr₁⟩ := hn₁ W₁ hs₁ hW₁
  obtain ⟨D₂, hD₂, herr₂⟩ := hn₂ W₂ hs₂ hW₂
  let M₁ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ 0)
  let M₂ := SchwartzMap.seminorm ℝ 0 0 (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ 0)
  have hM₁ : 0 ≤ M₁ := apply_nonneg _ _
  have hM₂ : 0 ≤ M₂ := apply_nonneg _ _
  have hbound₁ (y : ℝ) : ‖W₁ y‖ ≤ M₁ := by
    rw [← normPowerProfile_norm W₁ a₁ b₁ ha₁ hs₁ hW₁ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  have hbound₂ (y : ℝ) : ‖W₂ y‖ ≤ M₂ := by
    rw [← normPowerProfile_norm W₂ a₂ b₂ ha₂ hs₂ hW₂ 0 y]
    exact SchwartzMap.norm_le_seminorm ℝ _ _
  let V := 128 * (b₁ * M₁ + b₂ * M₂)
  have hV : 0 ≤ V := mul_nonneg (by norm_num)
    (add_nonneg (mul_nonneg hb₁ hM₁) (mul_nonneg hb₂ hM₂))
  let C := 1 + 4 * (D₁ + D₂) * V
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  let E := maskedError c hc χ R (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) +
    maskedError c hc χ R (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
  have ht : 1 ≤ 1 + ‖t‖ := by linarith [norm_nonneg t]
  have hpow₁ := pow_le_pow_right₀ ht (le_max_left n₁ n₂)
  have hpow₂ := pow_le_pow_right₀ ht (le_max_right n₁ n₂)
  have hz : 0 ≤ Z ^ ε := Real.rpow_nonneg (le_trans zero_le_one hZ) ε
  have hE : E ≤ (D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ := by
    have h₁ := (herr₁ Z hZ R hR hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₁ (mul_nonneg hD₁.le hz))
    have h₂ := (herr₂ Z hZ R hR hnorm t).trans
      (mul_le_mul_of_nonneg_left hpow₂ (mul_nonneg hD₂.le hz))
    dsimp only [E]
    nlinarith
  have hraw := twisted_rectangle_saving c hc h3 χ R hR W₁ W₂ a₁ b₁ a₂ b₂ M₁ M₂
    ha₁ ha₂ hb₁ hb₂ hM₁ hM₂ hs₁ hs₂ hW₁ hW₂ hbound₁ hbound₂
    t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hT : 0 < T := hpX ▸ mul_pos (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
  have hnormalized := CenteredMoment.normalized_centered_saving _ T L V E hT hraw
  have hratio : 0 ≤ Real.sqrt T / L := div_nonneg (Real.sqrt_nonneg T) hL.le
  calc
    _ ≤ 4 * E * V * (Real.sqrt T / L) := hnormalized
    _ ≤ 4 * ((D₁ + D₂) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂) * V *
        (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hE (by norm_num)) hV) hratio
    _ = (4 * (D₁ + D₂) * V) * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ *
        (Real.sqrt T / L) := by ring
    _ ≤ C * Z ^ ε * (1 + ‖t‖) ^ max n₁ n₂ * (Real.sqrt T / L) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) hz) (by positivity)) hratio

end SevenEighths.CenteredMomentHeight
end

end OAI
end OAIOriginalModule0900

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Rectangle
Source SHA256: ab9b973e9c4255c9c50e939222121820191a6fd6a72e0e74514bd1248320fba5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0901


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentRectangle
open CenteredMomentPrimary CenteredMomentMask CenteredMomentTwist

def idealWeight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I : Ideal O) : ℂ :=
  (if IsCoprime I R then (1 : ℂ) else 0) *
    primaryIdealCharacter c χ I * (Ideal.absNorm I : ℂ) ^ (Complex.I * t)

theorem idealWeight_mul (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (I J : Ideal O) :
    idealWeight c χ R t (I * J) = idealWeight c χ R t I * idealWeight c χ R t J := by
  have hpow : ((Ideal.absNorm I : ℂ) * (Ideal.absNorm J : ℂ)) ^ (Complex.I * t) =
      (Ideal.absNorm I : ℂ) ^ (Complex.I * t) * (Ideal.absNorm J : ℂ) ^ (Complex.I * t) := by
    exact_mod_cast Complex.mul_cpow_ofReal_nonneg
      (Nat.cast_nonneg (Ideal.absNorm I) : (0 : ℝ) ≤ Ideal.absNorm I)
      (Nat.cast_nonneg (Ideal.absNorm J) : (0 : ℝ) ≤ Ideal.absNorm J) (Complex.I * t)
  simp only [idealWeight, map_mul, Nat.cast_mul, hpow, IsCoprime.mul_left_iff]
  by_cases hI : IsCoprime I R <;> by_cases hJ : IsCoprime J R <;> simp [hI, hJ] ; ring

def idealRectangle (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (I J : Ideal O) : ℂ :=
  W₁ ((Ideal.absNorm I : ℝ) / X₁) * W₂ ((Ideal.absNorm J : ℝ) / X₂) -
    W₁ ((Ideal.absNorm I : ℝ) / Y₁) * W₂ ((Ideal.absNorm J : ℝ) / Y₂)

theorem twistedMaskedSum_eq_weight (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (R : Ideal O) (t : ℝ) (W : ℝ → ℂ) (X : ℝ) :
    twistedMaskedSum c χ R W t X =
      ∑' I : Ideal O, idealWeight c χ R t I * W ((Ideal.absNorm I : ℝ) / X) := by
  apply tsum_congr
  intro I
  unfold idealWeight
  ring

theorem actual_rectangle_sum
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁)
    (hs₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      idealWeight c χ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J) =
      twistedMaskedSum c χ R W₁ t X₁ * twistedMaskedSum c χ R W₂ t X₂ -
        twistedMaskedSum c χ R W₁ t Y₁ * twistedMaskedSum c χ R W₂ t Y₂ := by
  let w := idealWeight c χ R t
  let f₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / X₁)
  let f₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / X₂)
  let g₁ := fun I : Ideal O => w I * W₁ ((Ideal.absNorm I : ℝ) / Y₁)
  let g₂ := fun J : Ideal O => w J * W₂ ((Ideal.absNorm J : ℝ) / Y₂)
  have hf₁ : Summable f₁ := annular_ideal_sum_summable w W₁ b₁ X₁ hX₁ hs₁
  have hf₂ : Summable f₂ := annular_ideal_sum_summable w W₂ b₂ X₂ hX₂ hs₂
  have hg₁ : Summable g₁ := annular_ideal_sum_summable w W₁ b₁ Y₁ hY₁ hs₁
  have hg₂ : Summable g₂ := annular_ideal_sum_summable w W₂ b₂ Y₂ hY₂ hs₂
  have hterm (I J : Ideal O) :
      idealWeight c χ R t (I * J) * idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ I J =
        f₁ I * f₂ J - g₁ I * g₂ J := by
    rw [idealWeight_mul]
    dsimp only [idealRectangle, f₁, f₂, g₁, g₂, w]
    ring
  simp_rw [hterm]
  have hinner (I : Ideal O) : (∑' J : Ideal O, (f₁ I * f₂ J - g₁ I * g₂ J)) =
      f₁ I * (∑' J : Ideal O, f₂ J) - g₁ I * (∑' J : Ideal O, g₂ J) := by
    rw [Summable.tsum_sub (hf₂.mul_left _) (hg₂.mul_left _), tsum_mul_left, tsum_mul_left]
  simp_rw [hinner]
  rw [Summable.tsum_sub (hf₁.mul_right _) (hg₁.mul_right _), tsum_mul_right, tsum_mul_right]
  simp only [twistedMaskedSum_eq_weight]
  rfl

end SevenEighths.CenteredMomentRectangle
end

end OAI
end OAIOriginalModule0901

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Extraction
Source SHA256: 61ef32b1cc86714301ad0f18867afd8621877155e34bbed925a875b8655115cc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0902



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentExtraction
open CenteredMomentRectangle CenteredMomentPrimary CenteredMomentTwist

theorem idealRectangle_extract (W₁ W₂ : ℝ → ℂ)
    (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealRectangle W₁ W₂
        (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
        (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp only [idealRectangle, map_mul, Nat.cast_mul, div_div_eq_mul_div]
  congr 2 <;> congr 1 <;> ring

theorem extracted_rectangle_coefficient (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (P B₁ B₂ I J : Ideal O) :
    idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J) =
      idealWeight c χ R t (P * B₁ * B₂) *
        (idealWeight c χ R t (I * J) *
          idealRectangle W₁ W₂
            (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
            (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J) := by
  rw [idealRectangle_extract]
  simp only [idealWeight_mul]
  ring

theorem extracted_rectangle_sum (c : O)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (P B₁ B₂ : Ideal O) :
    (∑' I : Ideal O, ∑' J : Ideal O,
      idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J)) =
      idealWeight c χ R t (P * B₁ * B₂) *
        ∑' I : Ideal O, ∑' J : Ideal O,
          idealWeight c χ R t (I * J) * idealRectangle W₁ W₂
            (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
            (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J := by
  simp_rw [extracted_rectangle_coefficient, tsum_mul_left]

theorem extracted_product_scale (X₁ X₂ Y₁ Y₂ T : ℝ) (B₁ B₂ : Ideal O)
    (hX : X₁ * X₂ = T) (hY : Y₁ * Y₂ = T) :
    (X₁ / Ideal.absNorm B₁) * (X₂ / Ideal.absNorm B₂) =
      T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ) ∧
    (Y₁ / Ideal.absNorm B₁) * (Y₂ / Ideal.absNorm B₂) =
      T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ) := by
  simp only [div_mul_div_comm, hX, hY, and_self]

theorem idealWeight_norm_le_one (c : O) (hc : c ≠ 0)
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (I : Ideal O) (hI : I ≠ 0) : ‖idealWeight c χ R t I‖ ≤ 1 := by
  have hnorm : (0 : ℝ) < Ideal.absNorm I := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hpow := norm_real_imaginary_power (Ideal.absNorm I : ℝ) t hnorm
  norm_cast at hpow
  simp only [idealWeight, norm_mul, hpow, mul_one]
  by_cases hcop : IsCoprime I R
  · simpa only [hcop, ite_true, norm_one, one_mul] using primaryIdealCharacter_norm_le_one c hc χ I
  · simp only [hcop, ite_false, norm_zero, zero_mul, zero_le_one]

theorem normalized_extracted_rectangle_estimate
    (c : O) (hc : c ≠ 0) (h3 : (3 : O) ∣ c)
    [Nontrivial (O ⧸ Ideal.span {c})] (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ K : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 ≤ Z →
      ∀ R : Ideal O, R ≠ 0 → (Ideal.absNorm R : ℝ) ≤ Z ^ B →
      ∀ P B₁ B₂ : Ideal O, P ≠ 0 → B₁ ≠ 0 → B₂ ≠ 0 →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ / Ideal.absNorm B₁ → L ≤ X₂ / Ideal.absNorm B₂ →
      L ≤ Y₁ / Ideal.absNorm B₁ → L ≤ Y₂ / Ideal.absNorm B₂ →
      X₁ * X₂ = T → Y₁ * Y₂ = T →
      let T' := T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ)
      ‖(Real.sqrt T' : ℂ)⁻¹ *
        (∑' I : Ideal O, ∑' J : Ideal O,
          idealWeight c χ R t (P * (B₁ * I) * (B₂ * J)) *
            idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J))‖ ≤
        C * Z ^ ε * (1 + ‖t‖) ^ K * (Real.sqrt T' / L) := by
  obtain ⟨K, hK⟩ := CenteredMomentHeight.normalized_masked_rectangle_estimate
    c hc h3 χ a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨K, ?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C, hC, hbound⟩ := hK W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C, hC, ?_⟩
  intro Z hZ R hR hnorm P B₁ B₂ hP hB₁ hB₂ t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  dsimp only
  obtain ⟨heqX, heqY⟩ := extracted_product_scale X₁ X₂ Y₁ Y₂ T B₁ B₂ hpX hpY
  have hraw := hbound Z hZ R hR hnorm t
    (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
    (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂)
    (T / (Ideal.absNorm B₁ * Ideal.absNorm B₂ : ℝ)) L hL hX₁ hX₂ hY₁ hY₂ heqX heqY
  rw [extracted_rectangle_sum, actual_rectangle_sum c χ R t W₁ W₂ b₁ b₂
    (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
    (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂)
    (fun x hx => (hs₁ hx).2) (fun x hx => (hs₂ hx).2)
    (lt_of_lt_of_le hL hX₁) (lt_of_lt_of_le hL hX₂)
    (lt_of_lt_of_le hL hY₁) (lt_of_lt_of_le hL hY₂)]
  have hw := idealWeight_norm_le_one c hc χ R t (P * B₁ * B₂)
    (mul_ne_zero (mul_ne_zero hP hB₁) hB₂)
  rw [mul_left_comm, norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) hw).trans hraw

theorem centered_slot_allocation {ι : Type*} (T : Finset ι)
    (p : ι → Ideal O) (ν : ι → ℂ) (S : Finset (Ideal O))
    (c : O) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (R : Ideal O) (t : ℝ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ : ℝ) (B₁ B₂ I J : Ideal O) :
    let F := T.filter (fun i => p i ∈ S)
    let L := T.filter (fun i => p i ∉ S)
    (∏ i ∈ T, ν i) *
      (idealWeight c χ R t ((∏ i ∈ T, p i) * (B₁ * I) * (B₂ * J)) *
        idealRectangle W₁ W₂ X₁ X₂ Y₁ Y₂ (B₁ * I) (B₂ * J)) =
      ((∏ i ∈ F, ν i) * idealWeight c χ R t ((∏ i ∈ F, p i) * B₁ * B₂)) *
        ((∏ i ∈ L, ν i) *
          (idealWeight c χ R t ((∏ i ∈ L, p i) * I * J) *
            idealRectangle W₁ W₂
              (X₁ / Ideal.absNorm B₁) (X₂ / Ideal.absNorm B₂)
              (Y₁ / Ideal.absNorm B₁) (Y₂ / Ideal.absNorm B₂) I J)) := by
  dsimp only
  rw [← Finset.prod_filter_mul_prod_filter_not T (fun i => p i ∈ S) ν,
    ← Finset.prod_filter_mul_prod_filter_not T (fun i => p i ∈ S) p,
    idealRectangle_extract]
  simp only [idealWeight_mul]
  ring

theorem prime_slot_allocation {ι : Type*} (T : Finset ι)
    (p : ι → Ideal O) (hp : ∀ i ∈ T, Prime (p i)) (S : Finset (Ideal O)) :
    CenteredMomentSupport.supportExtract (∏ i ∈ T, p i) S =
        ∏ i ∈ T.filter (fun i => p i ∈ S), p i ∧
      CenteredMomentSupport.supportResidual (∏ i ∈ T, p i) S =
        ∏ i ∈ T.filter (fun i => p i ∉ S), p i := by
  rw [CenteredMomentSupport.supportExtract_prod T p (fun i hi => (hp i hi).ne_zero) S,
    CenteredMomentSupport.supportResidual_prod T p (fun i hi => (hp i hi).ne_zero) S]
  constructor
  · rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    exact CenteredMomentSupport.supportExtract_prime (p i) (hp i hi) S
  · rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    rw [CenteredMomentSupport.supportResidual_prime (p i) (hp i hi) S]
    split_ifs <;> rfl

end SevenEighths.CenteredMomentExtraction
end

end OAI
end OAIOriginalModule0902

/-! Original module: OAI.NumberTheory.DirichletL.ParametersProbeWindows
Source SHA256: 322ae5b168555830ccdacd6b82ec8133cde894f2c0e1fd7a725531364822ab78
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0903



namespace OAI

noncomputable section
open scoped ContDiff
namespace SevenEighths.Parameters

theorem exists_probe_window : ∃ (w : ℝ→ℝ) (W : SchwartzMap ℝ ℂ),
    ContDiff ℝ ∞ w ∧ HasCompactSupport w ∧
    Function.support w ⊆ Set.Ioo 1 2 ∧ (∀ x,0≤w x ∧ w x≤1) ∧
    w (3/2)=1 ∧ w≠0 ∧ (∀ x,W x=(w x:ℂ)) ∧ W≠0 ∧
    Function.support W ⊆ Set.Icc 1 2 ∧
    (∀x,(W x).im=0) ∧ (∀x,0≤(W x).re) := by
  obtain ⟨w,hs,hc,hw,hr,hval⟩ := exists_contDiff_tsupport_subset
    (n:=⊤) (E:=ℝ) (s:=Set.Ioo 1 2) (x:=3/2)
    (Ioo_mem_nhds (by norm_num) (by norm_num))
  let f : ℝ→ℂ := fun x=>(w x:ℂ)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hw
  have hfc : HasCompactSupport f := hc.comp_left (show (fun x:ℝ=>(x:ℂ)) 0=0 by simp)
  let W : SchwartzMap ℝ ℂ := hfc.toSchwartzMap hf
  have hne : w≠0 := by intro hz;have := congrFun hz (3/2);simp [hval] at this
  refine ⟨w,W,hw,hc,(subset_tsupport w).trans hs,fun x=>hr ⟨x,rfl⟩,hval,hne,
    fun _=>rfl,?_,?_,fun _=>rfl,?_⟩
  · intro hz
    apply hne
    funext x
    have h := congrArg (fun F : SchwartzMap ℝ ℂ => (F x).re) hz
    change w x=0 at h
    exact h
  · intro x hx
    have hwx : w x≠0 := by intro h;apply hx;change (w x:ℂ)=0;rw [h];rfl
    exact Set.Ioo_subset_Icc_self (hs (subset_tsupport w hwx))
  · intro x
    exact (hr ⟨x,rfl⟩).1
end SevenEighths.Parameters

end

end OAI
end OAIOriginalModule0903

/-! Original module: OAI.NumberTheory.DirichletL.PrimeCounting.IdealPrimeMass
Source SHA256: b5eed6cc5c03c507d2fe0f098f390778e33e5c3c5d28b5412978bc5cd49da909
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0904



namespace OAI

namespace SevenEighths.PNT.IdealPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter
open SevenEighths.IdealMangoldt
open scoped BigOperators Classical Topology

noncomputable section

def primeClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ Prime I} n

def higherClassCoeff (C : Set (Ideal O)) (n : ℕ) : ℝ :=
  classCoeff {I | I ∈ C ∧ ¬Prime I} n

theorem value_prime {P : Ideal O} (hP : Prime P) : value P = Real.log (Ideal.absNorm P) := by
  simpa only [pow_one] using value_pow hP (k := 1) (by decide)

theorem prime_of_isPrimePow_of_norm_prime {I : Ideal O}
    (hI : IsPrimePow I) (hn : (Ideal.absNorm I).Prime) : Prime I := by
  obtain ⟨P, k, hP, hk, rfl⟩ := hI
  rw [map_pow] at hn
  rw [hn.eq_one_of_pow, pow_one]
  exact hP

theorem value_eq_zero_of_nonprime_of_norm_prime {I : Ideal O}
    (hI : ¬Prime I) (hn : (Ideal.absNorm I).Prime) : value I = 0 := by
  apply ite_eq_right
  exact fun hpow => hI (prime_of_isPrimePow_of_norm_prime hpow hn)

theorem primeClassCoeff_eq_sum_log (C : Set (Ideal O)) (n : ℕ) :
    primeClassCoeff C n =
      ∑ P ∈ (normFiber n).filter (fun P => P ∈ C ∧ Prime P), Real.log (Ideal.absNorm P) := by
  unfold primeClassCoeff classCoeff coeff
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases h : I ∈ C ∧ Prime I
  · simp [h, value_prime h.2]
  · simp only [Set.mem_ofPred_eq, h, ite_false, zero_mul]

theorem primeClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ primeClassCoeff C n :=
  classCoeff_nonneg _ n

theorem higherClassCoeff_nonneg (C : Set (Ideal O)) (n : ℕ) : 0 ≤ higherClassCoeff C n :=
  classCoeff_nonneg _ n

theorem classCoeff_eq_prime_add_higher (C : Set (Ideal O)) (n : ℕ) :
    classCoeff C n = primeClassCoeff C n + higherClassCoeff C n := by
  unfold primeClassCoeff higherClassCoeff classCoeff coeff
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro I hI
  by_cases hC : I ∈ C <;> by_cases hP : Prime I <;> simp [hC, hP]

@[simp] theorem higherClassCoeff_zero (C : Set (Ideal O)) : higherClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

@[simp] theorem primeClassCoeff_zero (C : Set (Ideal O)) : primeClassCoeff C 0 = 0 :=
  coeff_eq_zero_of_not_primePow not_isPrimePow_zero _

theorem higherClassCoeff_eq_zero_of_prime (C : Set (Ideal O)) {n : ℕ} (hn : n.Prime) :
    higherClassCoeff C n = 0 := by
  apply Finset.sum_eq_zero
  intro I hI
  simp only [Set.mem_ofPred_eq]
  split_ifs with h
  · rw [value_eq_zero_of_nonprime_of_norm_prime h.2
      (by simpa only [(mem_normFiber n I).mp hI] using hn), mul_zero]
  · exact zero_mul _

theorem higherClassCoeff_le_nonprime_vonMangoldt (C : Set (Ideal O)) (n : ℕ) :
    higherClassCoeff C n ≤ 2 * (if n.Prime then 0 else vonMangoldt n) := by
  by_cases hn : n.Prime
  · rw [higherClassCoeff_eq_zero_of_prime C hn, ite_eq_left hn, mul_zero]
  · rw [ite_eq_right hn]
    exact classCoeff_le_two_vonMangoldt _ n

theorem summable_nonprime_vonMangoldt_div :
    Summable (fun n : ℕ => (if n.Prime then 0 else vonMangoldt n) / n) := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  simpa only [vonMangoldt.residueClass, Subsingleton.elim (α := ZMod 1) _ 0,
    Set.ofPred_true, Set.indicator_univ] using h

theorem higherClassCoeff_summable_div (C : Set (Ideal O)) :
    Summable (fun n : ℕ => higherClassCoeff C n / n) := by
  apply (summable_nonprime_vonMangoldt_div.mul_left 2).of_nonneg_of_le
  · intro n
    exact div_nonneg (higherClassCoeff_nonneg C n) (Nat.cast_nonneg n)
  · intro n
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (higherClassCoeff_le_nonprime_vonMangoldt C n)
      (Nat.cast_nonneg n)

theorem higherClassCoeff_ratio_tendsto_zero (C : Set (Ideal O)) :
    Tendsto (fun N : ℕ => cumsum (higherClassCoeff C) N / N) atTop (𝓝 0) :=
  cumsum_div_tendsto_zero_of_summable_div (higherClassCoeff_nonneg C)
    (higherClassCoeff_zero C) (higherClassCoeff_summable_div C)

theorem primeClassCoeff_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => cumsum (primeClassCoeff C) N / N) atTop (𝓝 A) := by
  have h' := h.sub (higherClassCoeff_ratio_tendsto_zero C)
  have heq (N : ℕ) :
      cumsum (classCoeff C) N / N - cumsum (higherClassCoeff C) N / N =
        cumsum (primeClassCoeff C) N / N := by
    rw [← sub_div]
    congr 1
    simp only [cumsum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    rw [classCoeff_eq_prime_add_higher, add_sub_cancel_right]
  simpa only [heq, sub_zero] using h'

def primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOfPred_absNorm_le (S := O) N).toFinset.filter
    (fun P => P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N)

@[simp] theorem mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) (P : Ideal O) :
    P ∈ primeIdealsBelow C N ↔ P ∈ C ∧ Prime P ∧ Ideal.absNorm P < N := by
  simp only [primeIdealsBelow, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
  exact ⟨fun h => h.2, fun h => ⟨h.2.2.le, h⟩⟩

theorem zero_not_mem_primeIdealsBelow (C : Set (Ideal O)) (N : ℕ) :
    (0 : Ideal O) ∉ primeIdealsBelow C N := by
  intro h
  exact ((mem_primeIdealsBelow C N 0).mp h).2.1.ne_zero rfl

def primeLogMass (C : Set (Ideal O)) (N : ℕ) : ℝ :=
  ∑ P ∈ primeIdealsBelow C N, Real.log (Ideal.absNorm P)

theorem primeLogMass_eq_cumsum (C : Set (Ideal O)) (N : ℕ) :
    primeLogMass C N = cumsum (primeClassCoeff C) N := by
  have hmap : ∀ P ∈ primeIdealsBelow C N, Ideal.absNorm P ∈ Finset.range N := by
    intro P hP
    exact Finset.mem_range.mpr ((mem_primeIdealsBelow C N P).mp hP).2.2
  rw [primeLogMass, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold cumsum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_primeIdealsBelow, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_range.mp hn⟩, heq⟩
  · intro P hP
    rfl

theorem primeLogMass_ratio_tendsto (C : Set (Ideal O)) {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A)) :
    Tendsto (fun N : ℕ => primeLogMass C N / N) atTop (𝓝 A) := by
  simpa only [primeLogMass_eq_cumsum] using primeClassCoeff_ratio_tendsto C h

end

end SevenEighths.PNT.IdealPrimeMass

end OAI
end OAIOriginalModule0904

/-! Original module: OAI.NumberTheory.DirichletL.PrimeCounting.AnnularPrimeMass
Source SHA256: d69022ebfc0c84ea6729ff47241c1fb7105c3d027070ab817f194e3da12b8949
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0905





namespace OAI

namespace SevenEighths.PNT.AnnularPrimeMass

open ActualEisensteinCubic ArithmeticFunction Filter MeasureTheory
open SevenEighths.IdealMangoldt SevenEighths.PNT.IdealPrimeMass
open scoped BigOperators Classical Topology ContDiff

noncomputable section

def cumulative (f : ℕ → ℝ) (t : ℝ) : ℝ := cumsum f (⌊t⌋₊ + 1)

def scaledCumulative (f : ℕ → ℝ) (x y : ℝ) : ℝ := cumulative f (x * y) / x

theorem cumulative_ratio_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A)) :
    Tendsto (fun t : ℝ => cumulative f t / t) atTop (𝓝 A) := by
  have ht : Tendsto (fun t : ℝ => ⌊t⌋₊ + 1) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.le_succ _) tendsto_nat_floor_atTop
  have hr : Tendsto (fun t : ℝ => ((⌊t⌋₊ + 1 : ℕ) : ℝ) / t) atTop (𝓝 1) := by
    convert (tendsto_nat_floor_div_atTop (R := ℝ)).add
      (show Tendsto (fun t : ℝ => 1 / t) atTop (𝓝 0) by simpa only [one_div] using tendsto_inv_atTop_zero) using 1 <;> simp [add_div]
  convert (h.comp ht).mul hr using 1
  · ext t
    simp only [Function.comp_def, cumulative]
    field_simp
  · simp

theorem scaledCumulative_tendsto {f : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ => scaledCumulative f x y) atTop (𝓝 (A * y)) := by
  have ht : Tendsto (fun x : ℝ => x * y) atTop atTop := tendsto_id.atTop_mul_const hy
  apply ((cumulative_ratio_tendsto h).comp ht).mul_const y |>.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold scaledCumulative
  dsimp only [Function.comp_def]
  field_simp

theorem cumulative_nonneg {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n) (t : ℝ) :
    0 ≤ cumulative f t := cumsum_nonneg hf _

theorem scaledCumulative_bound {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {C : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    {x y b : ℝ} (hx : 1 ≤ x) (hy : 0 ≤ y) (hyb : y ≤ b) :
    ‖scaledCumulative f x y‖ ≤ C * (b + 1) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  rw [scaledCumulative, Real.norm_eq_abs, abs_of_nonneg
    (div_nonneg (cumulative_nonneg hf _) hx0.le)]
  calc
    cumulative f (x * y) / x ≤ (C * (⌊x * y⌋₊ + 1 : ℕ)) / x := by
      exact div_le_div_of_nonneg_right (hbound _) hx0.le
    _ ≤ (C * (x * y + 1)) / x := by
      gcongr
      push_cast
      linarith [Nat.floor_le (mul_nonneg hx0.le hy)]
    _ ≤ C * (b + 1) := by
      rw [div_le_iff₀ hx0]
      nlinarith [mul_le_mul_of_nonneg_left hyb hx0.le,
        mul_nonneg hC (sub_nonneg.mpr hx)]

theorem measurable_cumulative (f : ℕ → ℝ) : Measurable (cumulative f) :=
  (measurable_of_countable (cumsum f)).comp (measurable_id.nat_floor.add_const 1)

theorem measurable_scaledCumulative (f : ℕ → ℝ) (x : ℝ) :
    Measurable (scaledCumulative f x) :=
  ((measurable_cumulative f).comp (measurable_const.mul measurable_id)).div_const x

def annularSum (f : ℕ → ℝ) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊, f n * φ (n / x)

theorem annularSum_div_eq_integral (f : ℕ → ℝ) (φ : ℝ → ℝ)
    (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    {a b x : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x)
    (hφa : φ a = 0) (hφb : φ b = 0) :
    annularSum f φ a b x / x =
      -(∫ y in a..b, deriv φ y * scaledCumulative f x y) := by
  let g : ℝ → ℝ := fun t => φ (t / x)
  have hg (t : ℝ) : HasDerivAt g (deriv φ (t / x) / x) t := by
    convert (hφ (t / x)).hasDerivAt.comp t ((hasDerivAt_id t).div_const x) using 1 <;>
      simp only [g, Function.comp_def, div_eq_mul_inv, id_eq, one_mul]
  have hgc : Continuous (deriv g) := by
    have heq : deriv g = fun t => deriv φ (t / x) / x := funext (fun t => (hg t).deriv)
    rw [heq]
    exact (hφ'.comp (continuous_id.div_const x)).div_const x
  have h := sum_mul_eq_sub_sub_integral_mul f (a := x * a) (b := x * b)
    (mul_nonneg hx.le ha) (mul_le_mul_of_nonneg_left hab hx.le)
    (fun t _ => (hg t).differentiableAt) hgc.integrableOn_Icc
  have hcum (t : ℝ) : (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, f k) = cumulative f t := by
    simp only [cumulative, cumsum, Nat.range_succ_eq_Icc_zero]
  simp_rw [hcum, (hg _).deriv] at h
  have hga : g (x * a) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφa]
  have hgb : g (x * b) = 0 := by simp only [g, mul_div_cancel_left₀ _ hx.ne', hφb]
  rw [hga, hgb, zero_mul, zero_mul, sub_zero, zero_sub,
    ← intervalIntegral.integral_of_le (mul_le_mul_of_nonneg_left hab hx.le)] at h
  have hs : annularSum f φ a b x =
      -(∫ t in x * a..x * b, (deriv φ (t / x) / x) * cumulative f t) := by
    rw [← h]
    unfold annularSum g
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [hs, neg_div]
  congr 1
  have hi := intervalIntegral.integral_comp_mul_left
    (fun t => (deriv φ (t / x) / x) * cumulative f t) hx.ne' (a := a) (b := b)
  simp only [smul_eq_mul, ← div_eq_inv_mul] at hi
  rw [← hi]
  apply intervalIntegral.integral_congr
  intro y hy
  simp only [mul_div_cancel_left₀ _ hx.ne', scaledCumulative]
  ring

theorem integral_scaledCumulative_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (ha : 0 < a) (hab : a ≤ b) (g : ℝ → ℝ) (hg : Continuous g) :
    Tendsto (fun x : ℝ => ∫ y in a..b, g y * scaledCumulative f x y) atTop
      (𝓝 (∫ y in a..b, g y * (A * y))) := by
  simp_rw [intervalIntegral.integral_of_le hab]
  apply tendsto_integral_filter_of_dominated_convergence (fun y => ‖g y‖ * (C * (b + 1)))
  · exact Eventually.of_forall (fun x =>
      (hg.measurable.mul (measurable_scaledCumulative f x)).aestronglyMeasurable)
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left
      (scaledCumulative_bound hf hC hbound hx (ha.le.trans hy.1.le) hy.2) (norm_nonneg _)
  · exact (hg.norm.mul_const _).integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
    exact (scaledCumulative_tendsto hmass (ha.trans hy.1)).const_mul (g y)

theorem annularSum_div_tendsto {f : ℕ → ℝ} (hf : ∀ n, 0 ≤ f n)
    {A C a b : ℝ} (hC : 0 ≤ C) (hbound : ∀ N : ℕ, cumsum f N ≤ C * N)
    (hmass : Tendsto (fun N : ℕ => cumsum f N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => annularSum f φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (integral_scaledCumulative_tendsto hf hC hbound hmass ha hab (deriv φ) hφ').neg
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun y : ℝ => y) (u' := fun _ => (1 : ℝ)) (v := φ) (v' := deriv φ)
    (fun y _ => hasDerivAt_id y) (fun y _ => (hφ y).hasDerivAt)
    (continuous_const.intervalIntegrable a b) (hφ'.intervalIntegrable a b)
  have heq : -(∫ y in a..b, deriv φ y * (A * y)) = A * ∫ y in a..b, φ y := by
    have hfun : (fun y => deriv φ y * (A * y)) = fun y => A * (y * deriv φ y) := by
      ext y
      ring
    rw [hfun, intervalIntegral.integral_const_mul, hibp, hφa, hφb]
    simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (annularSum_div_eq_integral f φ hφ hφ' ha.le hab hx hφa hφb).symm

def annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) : Finset (Ideal O) :=
  (primeIdealsBelow C (⌊x * b⌋₊ + 1)).filter (fun P => ⌊x * a⌋₊ < Ideal.absNorm P)

@[simp] theorem mem_annularPrimeIdeals (C : Set (Ideal O)) (a b x : ℝ) (P : Ideal O) :
    P ∈ annularPrimeIdeals C a b x ↔
      P ∈ C ∧ Prime P ∧ ⌊x * a⌋₊ < Ideal.absNorm P ∧ Ideal.absNorm P ≤ ⌊x * b⌋₊ := by
  simp only [annularPrimeIdeals, Finset.mem_filter, mem_primeIdealsBelow, Nat.lt_succ_iff]
  tauto

def primeAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, φ (Ideal.absNorm P / x)

def primeLogAnnularSum (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) * φ (Ideal.absNorm P / x)

theorem primeLogAnnularSum_eq (C : Set (Ideal O)) (φ : ℝ → ℝ) (a b x : ℝ) :
    primeLogAnnularSum C φ a b x = annularSum (primeClassCoeff C) φ a b x := by
  have hmap : ∀ P ∈ annularPrimeIdeals C a b x,
      Ideal.absNorm P ∈ Finset.Ioc ⌊x * a⌋₊ ⌊x * b⌋₊ := by
    intro P hP
    exact Finset.mem_Ioc.mpr ((mem_annularPrimeIdeals C a b x P).mp hP).2.2
  rw [primeLogAnnularSum, ← Finset.sum_fiberwise_of_maps_to hmap]
  unfold annularSum
  apply Finset.sum_congr rfl
  intro n hn
  rw [primeClassCoeff_eq_sum_log, Finset.sum_mul]
  apply Finset.sum_congr
  · ext P
    simp only [Finset.mem_filter, mem_annularPrimeIdeals, mem_normFiber]
    constructor
    · rintro ⟨⟨hC, hP, hN⟩, heq⟩
      exact ⟨heq, hC, hP⟩
    · rintro ⟨heq, hC, hP⟩
      exact ⟨⟨hC, hP, heq ▸ Finset.mem_Ioc.mp hn⟩, heq⟩
  · intro P hP
    rw [(mem_normFiber n P).mp (Finset.mem_filter.mp hP).1]

theorem primeClassCoeff_chebyshev (C : Set (Ideal O)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N := by
  obtain ⟨B, hB⟩ := classCoeff_chebyshev {I | I ∈ C ∧ Prime I}
  have hbound (N : ℕ) : cumsum (primeClassCoeff C) N ≤ B * N := by
    convert hB N using 1
    congr 1
    funext n
    exact (Complex.norm_of_nonneg (primeClassCoeff_nonneg C n)).symm
  refine ⟨B, ?_, hbound⟩
  have h := (cumsum_nonneg (primeClassCoeff_nonneg C) 1).trans (hbound 1)
  simpa only [Nat.cast_one, mul_one, Pi.zero_apply] using h

theorem primeLogAnnularSum_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => primeLogAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  simpa only [primeLogAnnularSum_eq] using annularSum_div_tendsto
    (primeClassCoeff_nonneg C) hB hbound (primeClassCoeff_ratio_tendsto C hmass)
    φ hφ hφ' ha hab hφa hφb

theorem norm_bounds_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    x * a < (Ideal.absNorm P : ℝ) ∧ (Ideal.absNorm P : ℝ) ≤ x * b := by
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  exact ⟨(Nat.floor_lt (mul_nonneg hx.le ha)).mp h.2.2.1,
    (Nat.le_floor_iff (mul_nonneg hx.le (ha.trans hab))).mp h.2.2.2⟩

theorem ratio_mem_of_mem_annularPrimeIdeals {C : Set (Ideal O)} {a b x : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) (hx : 0 < x) {P : Ideal O}
    (hP : P ∈ annularPrimeIdeals C a b x) :
    (Ideal.absNorm P : ℝ) / x ∈ Set.Icc a b := by
  obtain ⟨hl, hu⟩ := norm_bounds_of_mem_annularPrimeIdeals ha hab hx hP
  exact ⟨(le_div_iff₀ hx).mpr (by nlinarith), (div_le_iff₀ hx).mpr (by nlinarith)⟩

theorem log_norm_difference_bound {a b x : ℝ} (ha : 0 < a) (_hab : a ≤ b)
    (hx : 0 < x) {n : ℕ} (hn : (n : ℝ) / x ∈ Set.Icc a b) :
    |Real.log x - Real.log n| ≤ |Real.log a| + |Real.log b| := by
  have hn0 : 0 < (n : ℝ) := by
    have h := (le_div_iff₀ hx).mp hn.1
    exact (mul_pos ha hx).trans_le h
  have hl := Real.log_le_log ha hn.1
  have hu := Real.log_le_log (ha.trans_le hn.1) hn.2
  rw [Real.log_div hn0.ne' hx.ne'] at hl hu
  apply abs_le.mpr
  constructor <;> linarith [le_abs_self (Real.log a), neg_abs_le (Real.log a),
    le_abs_self (Real.log b), neg_abs_le (Real.log b), abs_nonneg (Real.log a),
    abs_nonneg (Real.log b)]

theorem annularPrime_card_div_bound (C : Set (Ideal O)) {B a b x : ℝ}
    (hB : 0 ≤ B) (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ((annularPrimeIdeals C a b x).card : ℝ) / x ≤ B * (b + 1) / Real.log (x * a) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hlog : 0 < Real.log (x * a) := Real.log_pos hxa
  have hlower : Real.log (x * a) * (annularPrimeIdeals C a b x).card ≤
      ∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P) := by
    rw [mul_comm, ← nsmul_eq_mul, ← Finset.sum_const]
    apply Finset.sum_le_sum
    intro P hP
    exact Real.log_le_log (mul_pos hx0 ha)
      (norm_bounds_of_mem_annularPrimeIdeals ha.le hab hx0 hP).1.le
  have hupper : (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) ≤
      cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) := by
    rw [← primeLogMass_eq_cumsum, primeLogMass]
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    intro P hP _
    rw [← value_prime ((mem_primeIdealsBelow C _ P).mp hP).2.1]
    exact value_nonneg P
  have hnorm := scaledCumulative_bound (primeClassCoeff_nonneg C) hB hbound hx
    (ha.le.trans hab) (le_refl b)
  have hcum : cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x ≤ B * (b + 1) :=
    (le_abs_self _).trans (by simpa only [Real.norm_eq_abs, scaledCumulative, cumulative] using hnorm)
  apply (le_div_iff₀ hlog).mpr
  calc
    ((annularPrimeIdeals C a b x).card : ℝ) / x * Real.log (x * a) =
        (Real.log (x * a) * (annularPrimeIdeals C a b x).card) / x := by ring
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x, Real.log (Ideal.absNorm P)) / x :=
      div_le_div_of_nonneg_right hlower hx0.le
    _ ≤ cumsum (primeClassCoeff C) (⌊x * b⌋₊ + 1) / x :=
      div_le_div_of_nonneg_right hupper hx0.le
    _ ≤ _ := hcum

theorem primeAnnularSum_log_error_bound (C : Set (Ideal O)) (φ : ℝ → ℝ)
    {B M a b x : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ N : ℕ, cumsum (primeClassCoeff C) N ≤ B * N)
    (hM : 0 ≤ M) (hφ : ∀ y ∈ Set.Icc a b, |φ y| ≤ M)
    (ha : 0 < a) (hab : a ≤ b) (hx : 1 ≤ x) (hxa : 1 < x * a) :
    ‖Real.log x * primeAnnularSum C φ a b x / x - primeLogAnnularSum C φ a b x / x‖ ≤
      ((|Real.log a| + |Real.log b|) * M) * (B * (b + 1) / Real.log (x * a)) := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have heq : Real.log x * primeAnnularSum C φ a b x - primeLogAnnularSum C φ a b x =
      ∑ P ∈ annularPrimeIdeals C a b x,
        (Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x) := by
    simp only [primeAnnularSum, primeLogAnnularSum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      sub_mul]
  rw [← sub_div, heq, norm_div, Real.norm_of_nonneg hx0.le]
  calc
    _ ≤ (∑ P ∈ annularPrimeIdeals C a b x,
        ‖(Real.log x - Real.log (Ideal.absNorm P)) * φ (Ideal.absNorm P / x)‖) / x :=
      div_le_div_of_nonneg_right (norm_sum_le _ _) hx0.le
    _ ≤ (∑ _P ∈ annularPrimeIdeals C a b x, (|Real.log a| + |Real.log b|) * M) / x := by
      apply div_le_div_of_nonneg_right _ hx0.le
      apply Finset.sum_le_sum
      intro P hP
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      have hratio := ratio_mem_of_mem_annularPrimeIdeals ha.le hab hx0 hP
      exact mul_le_mul (log_norm_difference_bound ha hab hx0 hratio) (hφ _ hratio)
        (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
    _ = ((|Real.log a| + |Real.log b|) * M) * ((annularPrimeIdeals C a b x).card / x) := by
      rw [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (annularPrime_card_div_bound C hB hbound ha hab hx hxa)
      (mul_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _)) hM)

theorem primeAnnularSum_log_error_tendsto (C : Set (Ideal O)) (φ : ℝ → ℝ)
    (hφ : Continuous φ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x -
      primeLogAnnularSum C φ a b x / x) atTop (𝓝 0) := by
  obtain ⟨B, hB, hbound⟩ := primeClassCoeff_chebyshev C
  obtain ⟨M, hMbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hφ.continuousOn
  have hM : 0 ≤ M := (norm_nonneg _).trans (hMbound a ⟨le_rfl, hab⟩)
  have hup : Tendsto (fun x : ℝ => ((|Real.log a| + |Real.log b|) * M) *
      (B * (b + 1) / Real.log (x * a))) atTop (𝓝 0) := by
    have hi := tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp (tendsto_id.atTop_mul_const ha))
    convert (hi.const_mul (B * (b + 1))).const_mul ((|Real.log a| + |Real.log b|) * M)
      using 1 <;> simp only [div_eq_mul_inv, mul_zero, Function.comp_def, id_eq]
  apply squeeze_zero_norm' _ hup
  filter_upwards [eventually_ge_atTop (1 : ℝ),
    (tendsto_id.atTop_mul_const ha).eventually_gt_atTop 1] with x hx hxa
  exact primeAnnularSum_log_error_bound C φ hB hbound hM
    (fun y hy => by simpa only [Real.norm_eq_abs] using hMbound y hy) ha hab hx hxa

theorem primeAnnularSum_log_div_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (φ : ℝ → ℝ) (hφ : Differentiable ℝ φ) (hφ' : Continuous (deriv φ))
    (ha : 0 < a) (hab : a ≤ b) (hφa : φ a = 0) (hφb : φ b = 0) :
    Tendsto (fun x : ℝ => Real.log x * primeAnnularSum C φ a b x / x) atTop
      (𝓝 (A * ∫ y in a..b, φ y)) := by
  have h := (primeAnnularSum_log_error_tendsto C φ hφ.continuous ha hab).add
    (primeLogAnnularSum_div_tendsto C hmass φ hφ hφ' ha hab hφa hφb)
  simpa only [sub_add_cancel, zero_add] using h

theorem contDiff_powerWeight (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    {a b : ℝ} (ha : 0 < a) (hsupp : Function.support W ⊆ Set.Ioo a b) (r : ℝ) :
    ContDiff ℝ ∞ (fun y => W y * y ^ r) := by
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases hy : y = 0
  · subst y
    apply (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds ha] with y hy
    have hWy : W y = 0 := Function.notMem_support.mp (by
      intro h
      exact (not_lt_of_ge (hsupp h).1.le) hy)
    simp only [hWy, zero_mul]
  · exact hW.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne hy)

def weightedPrimeAnnularSum (C : Set (Ideal O)) (W : ℝ → ℝ) (a b x : ℝ) : ℝ :=
  ∑ P ∈ annularPrimeIdeals C a b x,
    W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ)

theorem weightedPrimeAnnularSum_normalization (C : Set (Ideal O)) (W : ℝ → ℝ)
    (a b : ℝ) {x : ℝ} (hx : 0 < x) :
    Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x =
      Real.log x * primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x / x := by
  have heq : primeAnnularSum C (fun y => W y * y ^ (-5 / 6 : ℝ)) a b x =
      weightedPrimeAnnularSum C W a b x / x ^ (-5 / 6 : ℝ) := by
    unfold primeAnnularSum weightedPrimeAnnularSum
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro P hP
    dsimp only
    rw [Real.div_rpow (Nat.cast_nonneg _) hx.le]
    ring
  have hp : x ^ (-5 / 6 : ℝ) * x = x ^ (1 / 6 : ℝ) := by
    calc
      _ = x ^ (-5 / 6 : ℝ) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((-5 / 6 : ℝ) + 1) := (Real.rpow_add hx _ _).symm
      _ = _ := by norm_num
  rw [heq, mul_div_assoc, div_div, hp]
  ring

theorem weightedPrimeAnnularSum_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeAnnularSum C W a b x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  let φ : ℝ → ℝ := fun y => W y * y ^ (-5 / 6 : ℝ)
  have hφ : ContDiff ℝ ∞ φ := contDiff_powerWeight W hW ha hsupp _
  have hWa : W a = 0 := Function.notMem_support.mp (fun h => (hsupp h).1.false)
  have hWb : W b = 0 := Function.notMem_support.mp (fun h => (hsupp h).2.false)
  have hφa : φ a = 0 := by simp only [φ, hWa, zero_mul]
  have hφb : φ b = 0 := by simp only [φ, hWb, zero_mul]
  have hint : (∫ y in a..b, φ y) = ∫ y, φ y := by
    rw [intervalIntegral.integral_of_le hab]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hWy : W y = 0 := Function.notMem_support.mp
      (fun h => hy ⟨(hsupp h).1, (hsupp h).2.le⟩)
    simp only [φ, hWy, zero_mul]
  have h := primeAnnularSum_log_div_tendsto C hmass φ (hφ.differentiable (by simp))
    (hφ.continuous_deriv (by simp)) ha hab hφa hφb
  rw [hint] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact (weightedPrimeAnnularSum_normalization C W a b hx).symm

theorem weightedPrimeAnnularSum_nat_tendsto (C : Set (Ideal O)) {A a b : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (ha : 0 < a) (hab : a ≤ b) (hsupp : Function.support W ⊆ Set.Ioo a b) :
    Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 6 : ℝ) *
      weightedPrimeAnnularSum C W a b N) atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) :=
  (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab hsupp).comp tendsto_natCast_atTop_atTop

theorem exists_positive_support_annulus (W : ℝ → ℝ) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ Function.support W ⊆ Set.Ioo a b := by
  by_cases hne : (tsupport W).Nonempty
  · obtain ⟨m, hm, hmin⟩ := hc.exists_isMinOn hne continuous_id.continuousOn
    obtain ⟨M, hM, hmax⟩ := hc.exists_isMaxOn hne continuous_id.continuousOn
    have hm0 : 0 < m := hp hm
    have hmM : m ≤ M := hmin hM
    refine ⟨m / 2, M + 1, by positivity, by linarith, ?_⟩
    intro y hy
    have hyt : y ∈ tsupport W := subset_closure hy
    have hl : m ≤ y := hmin hyt
    have hu : y ≤ M := hmax hyt
    exact ⟨by linarith, by linarith⟩
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro y hy
    exact (hne ⟨y, subset_closure hy⟩).elim

theorem mem_annularPrimeIdeals_of_weight_ne_zero {C : Set (Ideal O)} {W : ℝ → ℝ}
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x)
    {P : Ideal O} (hC : P ∈ C) (hP : Prime P) (hW : W (Ideal.absNorm P / x) ≠ 0) :
    P ∈ annularPrimeIdeals C a b x := by
  have hy := hsupp hW
  apply (mem_annularPrimeIdeals C a b x P).mpr
  refine ⟨hC, hP, ?_, ?_⟩
  · apply (Nat.floor_lt (mul_nonneg hx.le ha.le)).mpr
    have h := (lt_div_iff₀ hx).mp hy.1
    nlinarith
  · apply (Nat.le_floor_iff (mul_nonneg hx.le (ha.le.trans hab))).mpr
    have h := (div_lt_iff₀ hx).mp hy.2
    nlinarith

def primeWeightTerm (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) (P : Ideal O) : ℝ :=
  if P ∈ C ∧ Prime P then W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) else 0

def weightedPrimeSum (C : Set (Ideal O)) (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, primeWeightTerm C W x P

theorem primeWeightTerm_support_subset (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    Function.support (primeWeightTerm C W x) ⊆ (annularPrimeIdeals C a b x : Set (Ideal O)) := by
  intro P hP
  change primeWeightTerm C W x P ≠ 0 at hP
  unfold primeWeightTerm at hP
  split_ifs at hP with h
  · exact mem_annularPrimeIdeals_of_weight_ne_zero ha hab hsupp hx h.1 h.2
      (left_ne_zero_of_mul hP)
  · exact (hP rfl).elim

theorem primeWeightTerm_hasFiniteSupport (C : Set (Ideal O)) (W : ℝ → ℝ)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0) {x : ℝ} (hx : 0 < x) :
    (Function.support (primeWeightTerm C W x)).Finite := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  exact (annularPrimeIdeals C a b x).finite_toSet.subset
    (primeWeightTerm_support_subset C W ha hab.le hsupp hx)

theorem weightedPrimeSum_eq_annular (C : Set (Ideal O)) (W : ℝ → ℝ)
    {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSum C W x = weightedPrimeAnnularSum C W a b x := by
  rw [weightedPrimeSum, finsum_eq_finsetSum_of_support_subset _
    (primeWeightTerm_support_subset C W ha hab hsupp hx)]
  apply Finset.sum_congr rfl
  intro P hP
  have h := (mem_annularPrimeIdeals C a b x P).mp hP
  simp only [primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem weightedPrimeSum_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSum C W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  apply (weightedPrimeAnnularSum_tendsto C hmass W hW ha hab.le hsupp).congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [weightedPrimeSum_eq_annular C W ha hab.le hsupp hx]

def weightedPrimeSumDeleted (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ᶠ P : Ideal O, if P ∈ S then 0 else primeWeightTerm C W x P

theorem finite_prime_weights_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, ∀ P ∈ S, primeWeightTerm C W x P = 0 := by
  have hz : ∀ᶠ y in 𝓝 (0 : ℝ), W y = 0 :=
    notMem_tsupport_iff_eventuallyEq.mp (fun h => (show (0 : ℝ) < 0 from hp h).false)
  rw [eventually_all_finset]
  intro P hP
  have ht : Tendsto (fun x : ℝ => (Ideal.absNorm P : ℝ) / x) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      tendsto_inv_atTop_zero.const_mul (Ideal.absNorm P : ℝ)
  filter_upwards [ht hz] with x hx
  change W (Ideal.absNorm P / x) = 0 at hx
  simp only [primeWeightTerm, hx, zero_mul, ite_self]

theorem fixed_prime_deletion_eventually_eq (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    weightedPrimeSumDeleted C S W =ᶠ[atTop] weightedPrimeSum C W := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  unfold weightedPrimeSumDeleted weightedPrimeSum
  congr 1
  ext P
  by_cases hP : P ∈ S
  · simp only [hP, ite_true, hx P hP]
  · simp only [hP, ite_false]

theorem finite_prime_deleted_mass_eventually_zero (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) (hp : tsupport W ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in atTop, (∑ P ∈ S, primeWeightTerm C W x P) = 0 := by
  filter_upwards [finite_prime_weights_eventually_zero C S W hp] with x hx
  exact Finset.sum_eq_zero hx

theorem weightedPrimeSumDeleted_tendsto (C : Set (Ideal O)) (S : Finset (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun x : ℝ => Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) := by
  apply (weightedPrimeSum_tendsto C hmass W hW hc hp).congr'
  filter_upwards [fixed_prime_deletion_eventually_eq C S W hp] with x hx
  rw [hx]

theorem weightedPrimeSumDeleted_eq_annular (C : Set (Ideal O)) (S : Finset (Ideal O))
    (W : ℝ → ℝ) {a b x : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hsupp : Function.support W ⊆ Set.Ioo a b) (hx : 0 < x) :
    weightedPrimeSumDeleted C S W x =
      ∑ P ∈ annularPrimeIdeals C a b x \ S,
        W (Ideal.absNorm P / x) * (Ideal.absNorm P : ℝ) ^ (-5 / 6 : ℝ) := by
  have hsub : Function.support (fun P => if P ∈ S then 0 else primeWeightTerm C W x P) ⊆
      (↑(annularPrimeIdeals C a b x \ S) : Set (Ideal O)) := by
    intro P hP
    change (if P ∈ S then 0 else primeWeightTerm C W x P) ≠ 0 at hP
    by_cases hPS : P ∈ S
    · simp only [hPS, ite_true, ne_self_iff_false] at hP
    · simp only [hPS, ite_false] at hP
      exact Finset.mem_sdiff.mpr ⟨primeWeightTerm_support_subset C W ha hab hsupp hx hP, hPS⟩
  rw [weightedPrimeSumDeleted, finsum_eq_finsetSum_of_support_subset _ hsub]
  apply Finset.sum_congr rfl
  intro P hP
  have hS := (Finset.mem_sdiff.mp hP).2
  have h := (mem_annularPrimeIdeals C a b x P).mp (Finset.mem_sdiff.mp hP).1
  simp only [hS, ite_false, primeWeightTerm, h.1, h.2.1, and_self, ite_true]

theorem powerWeight_integral_pos (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W)
    (hc : HasCompactSupport W) (hp : tsupport W ⊆ Set.Ioi 0)
    (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    0 < ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ) := by
  obtain ⟨a, b, ha, hab, hsupp⟩ := exists_positive_support_annulus W hc hp
  have hφ := contDiff_powerWeight W hW ha hsupp (-5 / 6)
  obtain ⟨y, hy⟩ : ∃ y : ℝ, W y ≠ 0 := by
    by_contra h
    push Not at h
    exact hWne (funext h)
  have hy0 : 0 < y := hp (subset_closure hy)
  apply hφ.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hc.mul_right
  · intro z
    by_cases hz : W z = 0
    · simp only [hz, zero_mul, Pi.zero_apply, le_refl]
    · have hz0 : 0 < z := hp (subset_closure hz)
      exact mul_nonneg (hW0 z) (Real.rpow_nonneg hz0.le _)
  · exact mul_ne_zero hy (Real.rpow_pos_of_pos hy0 _).ne'

theorem weightedPrimeSumDeleted_eventually_lower_bound (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ x : ℝ in atTop,
      c * x ^ (1 / 6 : ℝ) / Real.log x ≤ weightedPrimeSumDeleted C S W x := by
  let L : ℝ := A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ)
  have hL : 0 < L := mul_pos hA (powerWeight_integral_pos W hW hc hp hW0 hWne)
  refine ⟨L / 2, half_pos hL, ?_⟩
  have ht := weightedPrimeSumDeleted_tendsto C S hmass W hW hc hp
  have he := ht (Ioi_mem_nhds (half_lt_self hL))
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  change L / 2 < Real.log x / x ^ (1 / 6 : ℝ) * weightedPrimeSumDeleted C S W x at hx
  have hxp : 0 < x ^ (1 / 6 : ℝ) := Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  have hmul := (le_div_iff₀ hxp).mp (show L / 2 ≤
      (Real.log x * weightedPrimeSumDeleted C S W x) / x ^ (1 / 6 : ℝ) by
    convert hx.le using 1; ring)
  nlinarith

theorem weightedPrimeSumDeleted_eventually_pos (C : Set (Ideal O))
    (S : Finset (Ideal O)) {A : ℝ} (hA : 0 < A)
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) (hW0 : ∀ y, 0 ≤ W y) (hWne : W ≠ 0) :
    ∀ᶠ x : ℝ in atTop, 0 < weightedPrimeSumDeleted C S W x := by
  obtain ⟨c, hc0, he⟩ := weightedPrimeSumDeleted_eventually_lower_bound C S hA hmass
    W hW hc hp hW0 hWne
  filter_upwards [he, eventually_gt_atTop (1 : ℝ)] with x hx hx1
  exact (div_pos (mul_pos hc0 (Real.rpow_pos_of_pos (zero_lt_one.trans hx1) _))
    (Real.log_pos hx1)).trans_le hx

theorem weightedPrimeSum_nat_tendsto (C : Set (Ideal O)) {A : ℝ}
    (hmass : Tendsto (fun N : ℕ => cumsum (classCoeff C) N / N) atTop (𝓝 A))
    (W : ℝ → ℝ) (hW : ContDiff ℝ ∞ W) (hc : HasCompactSupport W)
    (hp : tsupport W ⊆ Set.Ioi 0) :
    Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ (1 / 6 : ℝ) * weightedPrimeSum C W N)
      atTop (𝓝 (A * ∫ y : ℝ, W y * y ^ (-5 / 6 : ℝ))) :=
  (weightedPrimeSum_tendsto C hmass W hW hc hp).comp tendsto_natCast_atTop_atTop

end

end SevenEighths.PNT.AnnularPrimeMass

end OAI
end OAIOriginalModule0905

/-! Original module: OAI.NumberTheory.DirichletL.PrimeCounting.RayAsymptotic
Source SHA256: c94d064e68a68ab49e211d5f077e79c4ea6fe3cd2fb9193240a06acb99afd22b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0906



namespace OAI

namespace SevenEighths.PNT.RayAsymptotic

open ActualEisensteinCubic RayOrthogonality Filter
open scoped BigOperators Classical Topology

noncomputable section

variable (M : Ideal O) [Finite (O ⧸ M)]

def classCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (principalIdeals M) n

theorem sum_coeff (n : ℕ) :
    (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) =
      (rayCard M : ℂ) * (classCoeff M n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold classCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, sum_idealCharacters]
  by_cases hI : I ∈ principalIdeals M
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem average_coeff (n : ℕ) :
    (classCoeff M n : ℂ) =
      (∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) n) /
        (rayCard M : ℂ) := by
  rw [sum_coeff]
  have hc : (rayCard M : ℂ) ≠ 0 := by exact_mod_cast (rayCard_pos M).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem classCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (classCoeff M n : ℂ)) s =
      (∑ χ : rayCharacters M, LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s) /
        (rayCard M : ℂ) := by
  have heq : (fun n => (classCoeff M n : ℂ)) =
      (rayCard M : ℂ)⁻¹ • ∑ χ : rayCharacters M, IdealLogDerivative.coeff (idealCharacter M χ) := by
    funext n
    rw [average_coeff]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (norm_idealCharacter_le_one M χ) s hs

def principalRegularization (F : ℂ → ℂ) (residue : ℂ) : ℂ → ℂ :=
  Function.update (fun s => (s - 1) * F s) 1 residue

omit [Finite (O ⧸ M)] in
theorem principalRegularization_eventuallyEq (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) :
    principalRegularization F residue =ᶠ[𝓝 s] (fun z => (z - 1) * F z) := by
  refine eventuallyEq_iff_exists_mem.mpr ?_
  exact ⟨_, isOpen_ne.mem_nhds hs, fun z hz => Function.update_of_ne (Set.mem_ofPred.mp hz) ..⟩

omit [Finite (O ⧸ M)] in
theorem principalRegularization_analyticAt (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) :
    AnalyticAt ℂ (principalRegularization F residue) s :=
  ((analyticAt_id.sub analyticAt_const).mul hF).congr
    (principalRegularization_eventuallyEq F residue hs).symm

omit [Finite (O ⧸ M)] in

theorem principalRegularization_analyticAt_of_local (F R : ℂ → ℂ)
    (hR : AnalyticAt ℂ R 1)
    (hFR : ∀ᶠ s in 𝓝 (1 : ℂ), s ≠ 1 → (s - 1) * F s = R s) :
    AnalyticAt ℂ (principalRegularization F (R 1)) 1 := by
  apply hR.congr
  filter_upwards [hFR] with s hs
  by_cases hs1 : s = 1
  · subst s
    simp only [principalRegularization, Function.update_self]
  · rw [principalRegularization, Function.update_of_ne hs1]
    exact (hs hs1).symm

omit [Finite (O ⧸ M)] in
theorem principalRegularization_logDeriv (F : ℂ → ℂ) (residue : ℂ)
    {s : ℂ} (hs : s ≠ 1) (hF : AnalyticAt ℂ F s) (hF0 : F s ≠ 0) :
    -deriv (principalRegularization F residue) s / principalRegularization F residue s =
      -deriv F s / F s - 1 / (s - 1) := by
  have hd := (principalRegularization_eventuallyEq F residue hs).deriv_eq
  rw [hd, principalRegularization, Function.update_of_ne hs,
    deriv_fun_mul (by fun_prop) hF.differentiableAt, deriv_sub_const, deriv_id'', one_mul]
  field_simp
  ring

def regularizedFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ)
    (χ : rayCharacters M) : ℂ → ℂ :=
  if χ = 1 then principalRegularization (F χ) residue else F χ

def remainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : rayCharacters M,
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s) /
      (rayCard M : ℂ)

structure AnalyticFamily (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) : Prop where
  eq_series : ∀ (χ : rayCharacters M) (s : ℂ), 1 < s.re →
    F χ s = IdealEuler.series (idealCharacter M χ) s
  analytic : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → AnalyticAt ℂ (F χ) s
  nonzero : ∀ (χ : rayCharacters M) (s : ℂ), 1 ≤ s.re →
    χ ≠ 1 ∨ s ≠ 1 → F χ s ≠ 0
  pole_analytic : AnalyticAt ℂ (principalRegularization (F 1) residue) 1
  residue_ne_zero : residue ≠ 0

theorem regularizedFamily_analyticAt {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    AnalyticAt ℂ (regularizedFamily M F residue χ) s := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      exact hF.pole_analytic
    · exact principalRegularization_analyticAt _ _ hs1 (hF.analytic 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.analytic χ s hs (Or.inl hχ)

theorem regularizedFamily_ne_zero {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 ≤ s.re) :
    regularizedFamily M F residue χ s ≠ 0 := by
  by_cases hχ : χ = 1
  · subst χ
    rw [regularizedFamily, ite_eq_left rfl]
    by_cases hs1 : s = 1
    · subst s
      simpa only [principalRegularization, Function.update_self] using hF.residue_ne_zero
    · rw [principalRegularization, Function.update_of_ne hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1) (hF.nonzero 1 s hs (Or.inr hs1))
  · rw [regularizedFamily, ite_eq_right hχ]
    exact hF.nonzero χ s hs (Or.inl hχ)

theorem remainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (remainder M F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF χ s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt (regularizedFamily_ne_zero M hF χ s hs)

theorem regularizedFamily_logDeriv {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) (χ : rayCharacters M) (s : ℂ) (hs : 1 < s.re) :
    -deriv (regularizedFamily M F residue χ) s / regularizedFamily M F residue χ s =
      -deriv (F χ) s / F χ s - (if χ = 1 then 1 / (s - 1) else 0) := by
  by_cases hχ : χ = 1
  · rw [regularizedFamily, ite_eq_left hχ, ite_eq_left hχ]
    have hs1 : s ≠ 1 := by intro heq; simp only [heq, Complex.one_re] at hs; linarith
    exact principalRegularization_logDeriv _ _ hs1
      (hF.analytic χ s hs.le (Or.inr hs1)) (hF.nonzero χ s hs.le (Or.inr hs1))
  · simp only [regularizedFamily, hχ, ite_false, sub_zero]

theorem remainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (remainder M F residue)
      (fun s => LSeries (fun n => (classCoeff M n : ℂ)) s -
        (rayCard M : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change remainder M F residue s = LSeries (fun n => (classCoeff M n : ℂ)) s -
    (rayCard M : ℂ)⁻¹ / (s - 1)
  rw [remainder, classCoeff_LSeries M s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : rayCharacters M, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : rayCharacters M) : -deriv (F χ) s / F χ s =
      LSeries (IdealLogDerivative.coeff (idealCharacter M χ)) s :=
    (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M χ) (F χ) (hF.eq_series χ) s hs).symm
  simp_rw [hlog]
  ring

theorem classCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (classCoeff M) N / N)
      atTop (𝓝 ((rayCard M : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (principalIdeals M))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (principalIdeals M) hσ)
    (IdealMangoldt.classCoeff_chebyshev (principalIdeals M))
    (remainder_continuousOn M hF)
  simpa only [classCoeff, Complex.ofReal_inv, Complex.ofReal_natCast] using remainder_eqOn M hF

section Quotient

variable (H : Subgroup (O ⧸ M)ˣ) (hH : globalUnits M ≤ H)

def quotientClassCoeff (n : ℕ) : ℝ := IdealMangoldt.classCoeff (RayQuotient.identityClass M H) n

theorem quotient_sum_coeff (n : ℕ) :
    (∑ χ : RayQuotient.Characters M H,
      IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) =
      (RayQuotient.classNumber M H : ℂ) * (quotientClassCoeff M H n : ℂ) := by
  unfold IdealLogDerivative.coeff ShortDraftHeckeBridge.normFiberCoeff
  rw [Finset.sum_comm]
  unfold quotientClassCoeff IdealMangoldt.classCoeff IdealMangoldt.coeff IdealMangoldt.normFiber
  rw [Complex.ofReal_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [← Finset.mul_sum, RayQuotient.sum_idealCharacters]
  by_cases hI : I ∈ RayQuotient.identityClass M H
  · simp only [hI, ite_true, one_mul, mul_comm]
  · simp only [hI, ite_false, zero_mul, Complex.ofReal_zero, mul_zero]

theorem quotient_average_coeff (n : ℕ) :
    (quotientClassCoeff M H n : ℂ) =
      (∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) n) /
          (RayQuotient.classNumber M H : ℂ) := by
  rw [quotient_sum_coeff]
  have hc : (RayQuotient.classNumber M H : ℂ) ≠ 0 := by
    exact_mod_cast (RayQuotient.classNumber_pos M H).ne'
  exact (mul_div_cancel_left₀ _ hc).symm

theorem quotientClassCoeff_LSeries (s : ℂ) (hs : 1 < s.re) :
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s =
      (∑ χ : RayQuotient.Characters M H,
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s) /
          (RayQuotient.classNumber M H : ℂ) := by
  have heq : (fun n => (quotientClassCoeff M H n : ℂ)) =
      (RayQuotient.classNumber M H : ℂ)⁻¹ • ∑ χ : RayQuotient.Characters M H,
        IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ) := by
    funext n
    rw [quotient_average_coeff M H hH]
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [heq, LSeries_smul, LSeries_sum]
  · rw [div_eq_mul_inv, mul_comm]
  · intro χ _
    exact IdealLogDerivative.coeff_summable _ (RayQuotient.norm_idealCharacter_le_one M H hH χ) s hs

def quotientRemainder (F : rayCharacters M → ℂ → ℂ) (residue : ℂ) (s : ℂ) : ℂ :=
  (∑ χ : RayQuotient.Characters M H,
    -deriv (regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ)) s /
      regularizedFamily M F residue (RayQuotient.toFullRay M H hH χ) s) /
        (RayQuotient.classNumber M H : ℂ)

theorem quotientRemainder_continuousOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    ContinuousOn (quotientRemainder M H hH F residue) {s : ℂ | 1 ≤ s.re} := by
  intro s hs
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.div_const
  apply tendsto_finsetSum
  intro χ _
  have h := regularizedFamily_analyticAt M hF (RayQuotient.toFullRay M H hH χ) s hs
  exact h.deriv.continuousAt.neg.div h.continuousAt
    (regularizedFamily_ne_zero M hF (RayQuotient.toFullRay M H hH χ) s hs)

theorem quotientRemainder_eqOn {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Set.EqOn (quotientRemainder M H hH F residue)
      (fun s => LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
        (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)) {s : ℂ | 1 < s.re} := by
  intro s hs
  change quotientRemainder M H hH F residue s =
    LSeries (fun n => (quotientClassCoeff M H n : ℂ)) s -
      (RayQuotient.classNumber M H : ℂ)⁻¹ / (s - 1)
  rw [quotientRemainder, quotientClassCoeff_LSeries M H hH s hs]
  simp_rw [regularizedFamily_logDeriv M hF _ s hs, RayQuotient.toFullRay_eq_one]
  rw [Finset.sum_sub_distrib]
  have hsum : (∑ χ : RayQuotient.Characters M H, if χ = 1 then 1 / (s - 1) else (0 : ℂ)) =
      1 / (s - 1) := by simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [hsum]
  have hlog (χ : RayQuotient.Characters M H) :
      -deriv (F (RayQuotient.toFullRay M H hH χ)) s / F (RayQuotient.toFullRay M H hH χ) s =
        LSeries (IdealLogDerivative.coeff (RayQuotient.idealCharacter M H hH χ)) s := by
    rw [RayQuotient.idealCharacter_eq_fullRay]
    exact (IdealLogDerivative.coeff_LSeries_eq_neg_logDeriv_of_eq _
      (norm_idealCharacter_le_one M _) (F _) (hF.eq_series _) s hs).symm
  simp_rw [hlog]
  ring

include hH in

theorem quotientClassCoeff_ratio_tendsto {F : rayCharacters M → ℂ → ℂ} {residue : ℂ}
    (hF : AnalyticFamily M F residue) :
    Tendsto (fun N : ℕ => cumsum (quotientClassCoeff M H) N / N)
      atTop (𝓝 ((RayQuotient.classNumber M H : ℝ)⁻¹)) := by
  apply WienerIkeharaTheorem'
    (IdealMangoldt.classCoeff_nonneg (RayQuotient.identityClass M H))
    (fun σ hσ => IdealMangoldt.classCoeff_summable_nterm (RayQuotient.identityClass M H) hσ)
    (IdealMangoldt.classCoeff_chebyshev (RayQuotient.identityClass M H))
    (quotientRemainder_continuousOn M H hH hF)
  simpa only [quotientClassCoeff, Complex.ofReal_inv, Complex.ofReal_natCast]
    using quotientRemainder_eqOn M H hH hF

end Quotient

end
end SevenEighths.PNT.RayAsymptotic

end OAI
end OAIOriginalModule0906

/-! Original module: OAI.NumberTheory.DirichletL.PrimeLogProfile
Source SHA256: d4f8d1d6923cc340afa0d1a5144b5335e55b2600243d2d6db94f2577973288b3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0907


namespace OAI

noncomputable section
open scoped Classical ContDiff Topology FourierTransform SchwartzMap
open Set Filter MeasureTheory
namespace SevenEighths.PrimeLogProfile

def safeInverse (x : ℝ) : ℂ :=
  (1-QuadraticInitialBound.sieveCutoff (4*x))/(x : ℂ)

theorem safeInverse_eq (x : ℝ) (hx : 1/2≤|x|) : safeInverse x=(x : ℂ)⁻¹ := by
  have hz : QuadraticInitialBound.sieveBump (4*x)=0 := by
    apply QuadraticInitialBound.sieveBump.zero_of_le_dist
    change 2≤dist (4*x) 0
    rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
    norm_num
    linarith
  simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hz]

theorem safeInverse_smooth : ContDiff ℝ ∞ safeInverse := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x=0
  · subst x
    have he : safeInverse =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0 : ℝ)<1/4)] with y hy
      have hy' : |y|<1/4 := by simpa [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] using hy
      have hone : QuadraticInitialBound.sieveBump (4*y)=1 := by
        apply QuadraticInitialBound.sieveBump.one_of_mem_closedBall
        change dist (4*y) 0≤1
        rw [dist_zero_right, Real.norm_eq_abs, abs_mul]
        norm_num
        linarith
      simp [safeInverse, QuadraticInitialBound.sieveCutoff_apply, hone]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · have hnum : ContDiff ℝ ∞ (fun y : ℝ => (1 : ℂ)-QuadraticInitialBound.sieveCutoff (4*y)) :=
      contDiff_const.sub ((QuadraticInitialBound.sieveCutoff.smooth ⊤).comp
        (contDiff_const.mul contDiff_id))
    change ContDiffAt ℝ ∞ (fun y : ℝ => (1-QuadraticInitialBound.sieveCutoff (4*y))/(y : ℂ)) x
    simpa only [div_eq_mul_inv, Pi.inv_apply, Complex.ofRealCLM_apply] using hnum.contDiffAt.mul
      (Complex.ofRealCLM.contDiff.contDiffAt.inv (Complex.ofReal_ne_zero.mpr hx))

def profile (W : ℝ→ℂ) (A y : ℝ) : ℂ :=
  W y * (A : ℂ) * safeInverse (1+A*Real.log y)

theorem profile_support (W : ℝ→ℂ) (A : ℝ) :
    Function.support (profile W A) ⊆ Function.support W := by
  intro y hy hW
  exact hy (by simp [profile,hW])

theorem profile_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℝ) :
    ContDiff ℝ ∞ (profile W A) := by
  apply contDiff_iff_contDiffAt.mpr
  intro y
  by_cases hy : y=0
  · subst y
    have he : profile W A =ᶠ[nhds (0 : ℝ)] (fun _ => 0) := by
      filter_upwards [(isOpen_Iio.mem_nhds ha)] with y hy
      have hw : W y=0 := by
        by_contra hh
        exact (not_le_of_gt hy) (hWs hh).1
      simp [profile,hw]
    exact contDiffAt_const.congr_of_eventuallyEq he
  · exact ((hW.contDiffAt.mul contDiffAt_const).mul
      (safeInverse_smooth.contDiffAt.comp y
        (contDiffAt_const.add (contDiffAt_const.mul (Real.contDiffAt_log.mpr hy)))))

def logFamily (W : ℝ→ℂ) (p : ℝ×ℝ) (u : ℝ) : ℂ :=
  Real.exp (-p.2*u) • (W (Real.exp (-u)) * (p.1 : ℂ) * safeInverse (1-p.1*u))

theorem logFamily_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (logFamily W)) := by
  change ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ =>
    Real.exp (-p.1.2*p.2) • (W (Real.exp (-p.2)) * (p.1.1 : ℂ) * safeInverse (1-p.1.1*p.2)))
  exact (Real.contDiff_exp.comp (contDiff_fst.snd.neg.mul contDiff_snd)).smul
    (((hW.comp (Real.contDiff_exp.comp contDiff_snd.neg)).mul
      (Complex.ofRealCLM.contDiff.comp contDiff_fst.fst)).mul
      (safeInverse_smooth.comp (contDiff_const.sub (contDiff_fst.fst.mul contDiff_snd))))

theorem logFamily_eq (W : ℝ→ℂ) (A σ u : ℝ) :
    logFamily W (A,σ) u = CubicReflectionKernel.mellinLogFamily (profile W A) σ u := by
  simp only [logFamily, CubicReflectionKernel.mellinLogFamily, profile, Real.log_exp]
  congr 3
  ring

theorem logFamily_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (logFamily W p) ⊆ Icc (-Real.log b) (-Real.log a) := by
  have he : logFamily W p = CubicReflectionKernel.mellinLogFamily (profile W p.1) p.2 := by
    funext u
    exact logFamily_eq W p.1 p.2 u
  rw [he]
  exact CubicReflectionKernel.mellinLogFamily_support _ a b ha ((profile_support W p.1).trans hWs) _

theorem uniform_mellin_decay (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (lo hi : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ A ∈ Icc (0 : ℝ) 1, ∀ σ ∈ Icc lo hi, ∀ t : ℝ,
      (1+|t|)^j*‖mellin (profile W A) ((σ : ℂ)+t*Complex.I)‖≤C := by
  obtain ⟨C,hC,hb⟩ := CompactProfileFamily.compact_family_fourier_weighted_bound
    (logFamily W) (logFamily_smooth W hW)
    (Icc (-Real.log b) (-Real.log a)) isCompact_Icc
    (logFamily_support W a b ha hWs)
    ((Icc (0 : ℝ) 1) ×ˢ (Icc lo hi)) (isCompact_Icc.prod isCompact_Icc) j
  refine ⟨(1+2*Real.pi)^j*C,by positivity,?_⟩
  intro A hA σ hσ t
  rw [CubicReflectionKernel.mellin_eq_logFamily_fourier]
  have he : CubicReflectionKernel.mellinLogFamily (profile W A) σ = logFamily W (A,σ) := by
    funext u
    exact (logFamily_eq W A σ u).symm
  rw [he]
  have ht : |t|=(2*Real.pi)*|t/(2*Real.pi)| := by
    rw [abs_div,abs_of_pos (by positivity : 0<2*Real.pi)]
    field_simp
  have hbase : 1+|t|≤(1+2*Real.pi)*(1+|t/(2*Real.pi)|) := by
    rw [ht]
    nlinarith [Real.pi_pos,abs_nonneg (t/(2*Real.pi))]
  calc
    _ ≤ ((1+2*Real.pi)*(1+|t/(2*Real.pi)|))^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖ :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (by positivity) hbase j) (norm_nonneg _)
    _ = (1+2*Real.pi)^j*((1+|t/(2*Real.pi)|)^j *
        ‖𝓕 (logFamily W (A,σ)) (t/(2*Real.pi))‖) := by rw [mul_pow,mul_assoc]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb (A,σ) ⟨hA,hσ⟩ _) (by positivity)

theorem profile_eq_log_division (W : ℝ→ℂ) (a b P : ℝ) (ha : 0<a)
    (hWs : Function.support W⊆Icc a b) (hP : 0<P)
    (hlarge : 2*(|Real.log a|+|Real.log b|)+1≤Real.log P) :
    profile W (1/Real.log P) = fun y => W y / (Real.log (P*y) : ℂ) := by
  funext y
  by_cases hy : W y=0
  · simp [profile,hy]
  have hs := hWs hy
  have hyp : 0<y := ha.trans_le hs.1
  have hlogs : |Real.log y|≤|Real.log a|+|Real.log b| := by
    apply abs_le.mpr
    constructor
    · have h := Real.log_le_log ha hs.1
      linarith [neg_abs_le (Real.log a),abs_nonneg (Real.log b)]
    · have h := Real.log_le_log hyp hs.2
      linarith [le_abs_self (Real.log b),abs_nonneg (Real.log a)]
  have hp : 0<Real.log P := by linarith [abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
  have hhalf : 1/2≤1+(1/Real.log P)*Real.log y := by
    have he : 1+(1/Real.log P)*Real.log y = (Real.log P+Real.log y)/Real.log P := by field_simp
    rw [he]
    apply (le_div_iff₀ hp).mpr
    linarith [(abs_le.mp hlogs).1]
  have hi := safeInverse_eq (1+(1/Real.log P)*Real.log y)
    (hhalf.trans (le_abs_self _))
  rw [profile,hi,Real.log_mul (ne_of_gt hP) (ne_of_gt hyp)]
  push_cast
  have hn : (Real.log P : ℂ)≠0 := Complex.ofReal_ne_zero.mpr hp.ne'
  have hn' : (Real.log P : ℂ)+(Real.log y : ℂ)≠0 := by
    have : 0<Real.log P+Real.log y := by
      linarith [(abs_le.mp hlogs).1,abs_nonneg (Real.log a),abs_nonneg (Real.log b)]
    exact_mod_cast this.ne'
  field_simp

end SevenEighths.PrimeLogProfile

end

end OAI
end OAIOriginalModule0907

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Local
Source SHA256: 65f8833c452db19a54061c14d39f19201a163033dd2447b96463bb35c80e1d5b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0908



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open LocalReflectionBrackets
noncomputable section

lemma scalar_inverse_pair (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hd : d ≠ 0)
    (h : c*a*b=d) : a⁻¹*b⁻¹ = d⁻¹*c := by
  field_simp
  linear_combination -h

theorem marked_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (B z : F)
    (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 0 ε =
      (-tau χ ψ 2)*(χ (-1))⁻¹^2*(χ B)^2*(χ z)^2 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  simp only [phase, show (0 : ℕ) ≠ 4 by decide, ↓reduceIte,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  calc
    _ = (-tau χ ψ 2)*((χ σ)⁻¹*(χ ε)⁻¹)^2 := by ring
    _ = _ := by rw [hi]; ring

theorem residual_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1) :
    ((χ⁻¹)^2) σ * phase χ ψ 1 ε =
      (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*
        (χ (-1))⁻¹^3*(χ A)*(χ B)^3*(χ z)^4 := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase, show (1 : ℕ) ≠ 4 by decide, show (1 : ℕ) ≠ 0 by decide,
    ↓reduceIte, show (1 : ℕ)+2 = 3 by decide,
    MulChar.pow_apply_coe, MulChar.inv_apply_eq_inv']
  have hid : (χ σ)⁻¹^2*(χ ε)⁻¹^3 = (χ σ)*((χ σ)⁻¹*(χ ε)⁻¹)^3 := by
    field_simp
  calc
    _ = (tau χ (ψ.mulShift (-1)) 1*tau χ ψ 3)*((χ σ)⁻¹^2*(χ ε)⁻¹^3) := by ring
    _ = _ := by rw [hid,hi,hsig]; ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0908

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Cofactor
Source SHA256: dbd3024e9f12aabda812471b487f28326e4ca4b610461b6f298245c05e821927
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0909


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance phaseField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def markedPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (-tau χ (quotientTrace p hp) 2)*(χ (-1))⁻¹^2*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^2

def residualPrimeScalar (p c0 : Eis) [hP : (Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  (tau χ ((quotientTrace p hp).mulShift (-1)) 1*tau χ (quotientTrace p hp) 3)*
    (χ (-1))⁻¹^3*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)))*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c0)))^3

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}

theorem controlled_marked_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 0 (D.epsilon i) =
        markedPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 2 := by
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [marked_local_phase _ _ _ _ _ _ he]
  change _ = _
  simp only [markedPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

theorem controlled_residual_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) 1 (D.epsilon i) =
        residualPrimeScalar (p i) c0 (hp i) (hg i)*
          ∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 4 := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c0)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c0)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  rw [residual_local_phase _ _ _ _ _ _ _ hs he]
  simp only [residualPrimeScalar, cofactor, map_prod, Finset.prod_pow,
    MixedCrossSeparation.crossSymbol]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0909

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Partition
Source SHA256: 6308539e1159338a26a1180d3a31b8eda80406cf9002b5f4e12bafb204f23d95
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0910


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = Finset.univ) :
    (∏ i, ((∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : Finset.univ.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, ite_eq_left hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ Finset.univ.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : Finset.univ.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, ite_eq_right hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ Finset.univ.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0910

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.PowerfulBudget
Source SHA256: 1009d9196abc52da0f22df00e68a066ba491a2c20d4f6d45e8a36c095fc1850b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0911



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseReflectedPhasePowerfulBudget
open ActualEisensteinCubic CompletedGauss CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

theorem powerful_half_norm_sum (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (S : Finset (Ideal O)) (X : ℝ),1≤X →
      (∀ I∈S,PowerfulIdeal I ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∑ I∈S,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ C*X^ε := by
  let δ := ε/2
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨D,hD,hcount⟩ := powerful_ideal_count δ hδ
  let C := D*(2:ℝ)^(1/2+δ)*(2+1/(δ*Real.log 2))
  have hl : 0<Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C,by dsimp [C];positivity,?_⟩
  intro S X hX hS
  have hx : 0<X := zero_lt_one.trans_le hX
  have hnorm (I : Ideal O) (hI : I∈S) :
      1≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤X :=
    ⟨QuadraticMainBoundary.norm_one_le (hS I hI).1.1,(hS I hI).2⟩
  have hbin (j : Fin (columnDyadicLength X+1)) :
      ∑ I∈divisorDyadicBin S X j,(Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤
        D*(2:ℝ)^(1/2+δ)*X^δ := by
    let R := divisorDyadicScale j.val
    have hR : 1≤R := divisorDyadicScale_ge_one _
    have hr : 0<R := zero_lt_one.trans_le hR
    by_cases he : (divisorDyadicBin S X j).Nonempty
    · have hRX : R≤X := divisorDyadicBin_scale_le S X hnorm j he
      have hc : ((divisorDyadicBin S X j).card:ℝ) ≤ D*(2*R)^(1/2+δ) := by
        apply hcount _ _ (by linarith)
        intro I hI
        exact ⟨(hS I (Finset.mem_filter.mp hI).1).1,
          (divisorDyadicBin_bounds S X hnorm j I hI).2⟩
      have hw (I : Ideal O) (hI : I∈divisorDyadicBin S X j) :
          (Ideal.absNorm I:ℝ)^(-1/2:ℝ) ≤ R^(-1/2:ℝ) :=
        Real.rpow_le_rpow_of_nonpos hr (divisorDyadicBin_bounds S X hnorm j I hI).1
          (by norm_num)
      calc
        _ ≤ ((divisorDyadicBin S X j).card:ℝ)*R^(-1/2:ℝ) := by
          apply (Finset.sum_le_sum hw).trans_eq
          simp only [Finset.sum_const,nsmul_eq_mul]
        _ ≤ (D*(2*R)^(1/2+δ))*R^(-1/2:ℝ) :=
          mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hr.le _)
        _ = (D*(2:ℝ)^(1/2+δ))*(R^(1/2+δ)*R^(-1/2:ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hr.le]
          ring
        _ = D*(2:ℝ)^(1/2+δ)*R^δ := by
          rw [←Real.rpow_add hr]
          congr 2
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hr.le hRX hδ.le) (by positivity)
    · rw [Finset.not_nonempty_iff_eq_empty.mp he,Finset.sum_empty]
      positivity
  rw [sum_divisorDyadicBins S X]
  calc
    _ ≤ ∑ _j : Fin (columnDyadicLength X+1),D*(2:ℝ)^(1/2+δ)*X^δ :=
      Finset.sum_le_sum (fun j _=>hbin j)
    _ = (columnDyadicLength X+1:ℝ)*(D*(2:ℝ)^(1/2+δ)*X^δ) := by simp
    _ ≤ ((2+1/(δ*Real.log 2))*X^δ)*(D*(2:ℝ)^(1/2+δ)*X^δ) :=
      mul_le_mul_of_nonneg_right (columnDyadicLength_small_power δ hδ X hX) (by positivity)
    _ = C*X^ε := by
      calc
        _ = C*(X^δ*X^δ) := by dsimp [C];ring
        _ = _ := by rw [←Real.rpow_add hx,show δ+δ=ε by dsimp [δ];ring]

lemma rowPowerful_norm_le (I : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowPowerfulPart I):ℝ) ≤ Ideal.absNorm I := by
  apply QuadraticMainBoundary.norm_le_of_dvd hI
  exact ⟨rowSimplePart I,(row_powerful_simple_product I hI).symm⟩

theorem row_mask_powerful_budget (L ε : ℝ) (hL : 0≤L) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (Z : ℝ),2≤Z → ∀ (S : Finset (Ideal O)) (Q : Ideal O),
      (∀ I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^L) → Q≠0 → (Ideal.absNorm Q:ℝ)≤Z^L →
      ((S.image (fun I=>rowMaskPart I Q)).card:ℝ)*
        (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ C*Z^ε := by
  let δ := ε/(2*(L+1))
  have hδ : 0<δ := by dsimp [δ];positivity
  obtain ⟨Cp,hCp,hpower⟩ := powerful_half_norm_sum δ hδ
  obtain ⟨Cd,hCd,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power δ hδ
  refine ⟨Cd*Cp,mul_pos hCd hCp,?_⟩
  intro Z hZ S Q hS hQ hQN
  have hz : 0<Z := by linarith
  have hX : 1≤Z^L := Real.one_le_rpow (by linarith) hL
  have hp : (∑ A∈S.image rowPowerfulPart,(Ideal.absNorm A:ℝ)^(-1/2:ℝ)) ≤ Cp*(Z^L)^δ := by
    apply hpower _ _ hX
    intro A hA
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
    exact ⟨rowPowerfulPart_powerful I,(rowPowerful_norm_le I (hS I hI).1).trans (hS I hI).2⟩
  have hm : ((S.image (fun I=>rowMaskPart I Q)).card:ℝ) ≤ Cd*(Z^L)^δ :=
    ((Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)).trans (hdiv Q hQ)).trans
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hQN hδ.le) hCd.le)
  have he : L*(δ+δ) ≤ ε := by
    have heq : δ*(2*(L+1))=ε := by dsimp [δ];field_simp
    nlinarith
  calc
    _ ≤ (Cd*(Z^L)^δ)*(Cp*(Z^L)^δ) :=
      mul_le_mul hm hp (Finset.sum_nonneg (fun A _=>Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by positivity)
    _ = (Cd*Cp)*((Z^L)^δ*(Z^L)^δ) := by ring
    _ = (Cd*Cp)*Z^(L*(δ+δ)) := by
      rw [←Real.rpow_add (Real.rpow_pos_of_pos hz L),←Real.rpow_mul hz.le]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith) he) (mul_pos hCd hCp).le

end SevenEighths.InverseReflectedPhasePowerfulBudget

end

end OAI
end OAIOriginalModule0911

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Split
Source SHA256: daf8632b541d2cdf35de0efb9b56f7d6e91c0d0be0329745ed1184fcf067b737
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0912


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
open ActualEisensteinCubic CubicEisenstein CompletedGauss ConcreteTraceCRT
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a0 c0 : Eis} {mode : Bool}
noncomputable local instance splitPhaseFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def residualBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c0 : Eis) (R : Finset ι) : ℂ :=
  ∏ i ∈ R, (∏ k ∈ R.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 4)*
    residualPrimeScalar (p i) c0 (hp i) (hg i)

def markedBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c0 : Eis) (P : Finset ι) : ℂ :=
  ∏ i ∈ P, (∏ k ∈ P.erase i, MixedCrossSeparation.crossSymbol p hg i k ^ 2)*
    markedPrimeScalar (p i) c0 (hp i) (hg i)

theorem activePhase_row_slot [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P : Finset ι)
    (hd : Disjoint R P) (hu : R ∪ P = Finset.univ) :
    D.activePhase hp hg (fun i => if i ∈ R then 1 else 0) =
      residualBlock hp hg c0 R * markedBlock hp hg c0 P := by
  let l : ι → ℂ := fun i => if i ∈ R then residualPrimeScalar (p i) c0 (hp i) (hg i)
    else markedPrimeScalar (p i) c0 (hp i) (hg i)
  have he : D.activePhase hp hg (fun i => if i ∈ R then 1 else 0) =
      ∏ i, (∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^
        (if i ∈ R then 4 else 2))*l i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : i ∈ R
    · simp only [hr,ite_true,l]
      rw [controlled_residual_phase]
      ring
    · simp only [hr,ite_false,l]
      rw [controlled_marked_phase]
      ring
  rw [he, ordered_cross_partition _ l 4 2 R P hd hu,
    InverseMoment.row_slot_product_phase p hcop hg hprimary R P hd, mul_one]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    simp [l,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun h => Finset.disjoint_left.mp hd h hi
    simp [l,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0912

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Sector
Source SHA256: 7d69b03ce98388e77fc8db6453b076af38a29d9efcd5bfbe3df8cd5779dd55f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0913


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem separate_product_congruence {A : Type*} [CommRing A]
    (M f r r₀ P P₀ : A) (hr : M^2 ∣ r-r₀) (hP : M^2 ∣ P-P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  have h := dvd_add (dvd_mul_of_dvd_left hr P) (dvd_mul_of_dvd_right hP r₀)
  convert dvd_mul_of_dvd_right h f using 1 ; ring

def separateSector (M r P : Eis) :
    (Eis ⧸ Ideal.span {M^2}) × (Eis ⧸ Ideal.span {M^2}) :=
  (Ideal.Quotient.mk _ r, Ideal.Quotient.mk _ P)

theorem separateSector_product (M f r r₀ P P₀ : Eis)
    (h : separateSector M r P = separateSector M r₀ P₀) :
    M^2 ∣ f*r*P-f*r₀*P₀ := by
  apply separate_product_congruence
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.fst h))
  · exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (congrArg Prod.snd h))

theorem separate_numerator_congruence {ι κ : Type*} [Fintype ι] [Fintype κ]
    (M a c l f r r₀ P P₀ : Eis) (p h : ι → Eis) (p₀ h₀ : κ → Eis)
    (hc : c ∣ M) (hh : ∀ i, M^2 ∣ h i) (hh₀ : ∀ i, M^2 ∣ h₀ i)
    (hp : (∏ i, p i) = f*r*P) (hp₀ : (∏ i, p₀ i) = f*r₀*P₀)
    (hs : separateSector M r P = separateSector M r₀ P₀) :
    M*c ∣ ShortDraftCRT.finiteCrossNumerator a c l p h -
      ShortDraftCRT.finiteCrossNumerator a c l p₀ h₀ := by
  apply ShortDraftCRT.finiteCrossNumerator_fixed_sector M a c l p h p₀ h₀ hc hh hh₀
  rw [hp,hp₀]
  exact separateSector_product M f r r₀ P P₀ hs

theorem controlled_bad_phase_eq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (hbad : ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1) :
    ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U =
      ShortDraftCusp.A4BadPhase c hc (D₀.matrix (fun _ => 1) 1 1) D₀.U := by
  have hu : ramifiedTraceLambda^3*c ∣ D.U*(∏ i, p i)-1 := by
    refine ⟨-D.w, ?_⟩
    linear_combination D.bezout
  have hu₀ : ramifiedTraceLambda^3*c ∣ D₀.U*(∏ i, p₀ i)-1 := by
    refine ⟨-D₀.w, ?_⟩
    linear_combination D₀.bezout
  have hcop : IsCoprime (ramifiedTraceLambda^3*c) (∏ i, p i) := by
    refine ⟨D.w,D.U,?_⟩
    linear_combination D.bezout
  have he := ShortDraftCRT.inverse_weight_residue_congr
    (ramifiedTraceLambda^3*c) (∏ i, p i) (∏ i, p₀ i) D.U D₀.U
    (D.matrix (fun _ => 1) 1 1) (D₀.matrix (fun _ => 1) 1 1)
    hcop (hbad.trans hr) hu hu₀ (hbad.trans hd)
  rw [ShortDraftCusp.A4BadPhase_as_fixed_residue, ShortDraftCusp.A4BadPhase_as_fixed_residue]
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr he)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0913

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Matrices
Source SHA256: b68ceba8a4b3dc345793afc86ecee4c612331c936305738810a1fc85684bf523
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0914


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators MatrixGroups
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT FiniteGaussPhase ShortDraftCRT
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

theorem simultaneous_controlled_matrices {α ι Q : Type*} [Fintype ι]
    (p : α → ι → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ mat : ∀ x, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) → SL(2,Eis),
      (∀ x v, mat x v 0 0 = (D x).matrix v 0 0) ∧
      (∀ x v, mat x v 1 0 = c*∏ i, p x i) ∧
      (∀ x v, if mode then (9:Eis) ∣ mat x v 0 1 ∧ (3:Eis) ∣ mat x v 1 1-1
        else (3:Eis) ∣ mat x v 0 1+1 ∧ (9:Eis) ∣ mat x v 1 1) ∧
      ∀ x y v w, sector x = sector y → ∀ i j, N ∣ mat x v i j-mat y w i j := by
  let X := Σ x : α, (∀ i, (Eis ⧸ Ideal.span {p x i})ˣ)
  let aa : X → Eis := fun x => (D x.1).matrix x.2 0 0
  let rr : X → Eis := fun x => ∏ i, p x.1 i
  let ss : X → Q := fun x => sector x.1
  have h3N : (3:Eis) ∣ N := (show (3:Eis) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  have hacop (x : X) : IsCoprime (aa x) (c*rr x) := by
    refine ⟨(D x.1).matrix x.2 1 1, -(D x.1).matrix x.2 0 1, ?_⟩
    have hd := ((D x.1).matrix x.2).property
    rw [Matrix.det_fin_two] at hd
    change (D x.1).matrix x.2 0 0 * (D x.1).matrix x.2 1 1 -
      (D x.1).matrix x.2 0 1 * (D x.1).matrix x.2 1 0 = 1 at hd
    rw [(D x.1).denominator] at hd
    dsimp [aa,rr]
    linear_combination hd
  have haa (x y : X) (h : ss x = ss y) : N*c ∣ aa x-aa y := by
    dsimp [aa]
    rw [(D x.1).numerator,(D y.1).numerator]
    exact finiteCrossNumerator_fixed_sector N a c ramifiedTraceLambda
      (p x.1) ((D x.1).lift x.2) (p y.1) ((D y.1).lift y.2)
      hcN ((D x.1).lift_period x.2) ((D y.1).lift_period y.2) (hsector x.1 y.1 h)
  have hrr (x y : X) (h : ss x = ss y) : N ∣ rr x-rr y :=
    (dvd_pow_self N (by decide : (2:ℕ) ≠ 0)).trans (hsector x.1 y.1 h)
  have hex : ∃ (b d : X → Eis) (C : Q → Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N})),
      (∀ x, aa x*d x-b x*(c*rr x)=1) ∧
      (∀ x, if mode then (9:Eis) ∣ b x ∧ (3:Eis) ∣ d x-1
        else (3:Eis) ∣ b x+1 ∧ (9:Eis) ∣ d x) ∧
      ∀ x, (!![aa x,b x;c*rr x,d x] : Matrix (Fin 2) (Fin 2) Eis).map
        (Ideal.Quotient.mk (Ideal.span {N})) = C (ss x) := by
    cases mode
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_denominator_sector_completions
        N c h9N hbase ss aa rr (fun x => hprimary x.1) hacop
        (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
    · obtain ⟨b,d,C,hd,hb,hz,hm⟩ := exists_primary_numerator_sector_completions
        N c hc h9N ss aa rr
        (fun x => (D x.1).numerator_primary h3N (hprimary x.1) hbase x.2)
        (fun x => hprimary x.1) hacop (fun x => hcop x.1) haa hrr
      exact ⟨b,d,C,hd,fun x => ⟨hb x,hz x⟩,hm⟩
  obtain ⟨b,d,C,hdet,hcond,hmat⟩ := hex
  let mat := fun (x : α) (v : ∀ i, (Eis ⧸ Ideal.span {p x i})ˣ) =>
    controlledCompletionMatrix (aa ⟨x,v⟩) (b ⟨x,v⟩) (c*rr ⟨x,v⟩) (d ⟨x,v⟩) (hdet ⟨x,v⟩)
  refine ⟨mat,fun _ _ => rfl,fun _ _ => rfl,fun x v => hcond ⟨x,v⟩,?_⟩
  intro x y v w hs i j
  have hs' : ss ⟨x,v⟩ = ss ⟨y,w⟩ := hs
  have he := (hmat ⟨x,v⟩).trans ((congrArg C hs').trans (hmat ⟨y,w⟩).symm)
  have he' := congrArg (fun T : Matrix (Fin 2) (Fin 2) (Eis ⧸ Ideal.span {N}) => T i j) he
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp he')

theorem exists_sector_controlled_arithmetic {α ι Q : Type*} [Fintype ι]
    (p : α → ι → Eis) (N a c : Eis) (mode : Bool)
    (D : ∀ x, ControlledStratumArithmetic (p x) N a c mode)
    (hc : c ≠ 0) (h9N : (9:Eis) ∣ N) (hcN : c ∣ N)
    (hprimary : ∀ x, λ₀^2 ∣ (∏ i, p x i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (hcop : ∀ x, IsCoprime (∏ i, p x i) (N*c))
    (sector : α → Q)
    (hsector : ∀ x y, sector x = sector y → N^2 ∣ (∏ i, p x i)-(∏ i, p y i)) :
    ∃ E : ∀ x, ControlledStratumArithmetic (p x) N a c mode,
      (∀ x, (E x).lift = (D x).lift) ∧
      (∀ x, (E x).U = (D x).U) ∧
      (∀ x, (E x).sigma = (D x).sigma) ∧
      (∀ x, (E x).epsilon = (D x).epsilon) ∧
      ∀ x y v w, sector x = sector y → ∀ i j,
        N ∣ (E x).matrix v i j-(E y).matrix w i j := by
  obtain ⟨mat,ha,hr,hcond,hfixed⟩ := simultaneous_controlled_matrices
    p N a c mode D hc h9N hcN hprimary hbase hcop sector hsector
  let E : ∀ x, ControlledStratumArithmetic (p x) N a c mode := fun x =>
    { D x with
      matrix := mat x
      numerator := fun v => (ha x v).trans ((D x).numerator v)
      denominator := hr x
      matrix_fixed := fun v i j => hfixed x x v (fun _ => 1) rfl i j
      conditions := hcond x }
  exact ⟨E,fun _ => rfl,fun _ => rfl,fun _ => rfl,fun _ => rfl,hfixed⟩

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0914

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Static
Source SHA256: b9f0d9ece2960830861030d64f5ab27e23db9b7f3e44ace74cbc0a664f481661
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0915


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss ShortDraftCusp
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  {p : ι → Eis} {p₀ : κ → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_fixedFactor_eq
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode)
    (hN : (9:Eis)*c ∣ N)
    (hr : λ₀^2 ∣ (∏ i, p i)-1) (hr₀ : λ₀^2 ∣ (∏ i, p₀ i)-1)
    (hbase : if mode then λ₀^2 ∣ a-1 else λ₀^2 ∣ c-1)
    (ha : N ∣ D.matrix (fun _ => 1) 0 0 - D₀.matrix (fun _ => 1) 0 0)
    (hb : N ∣ D.matrix (fun _ => 1) 0 1 - D₀.matrix (fun _ => 1) 0 1) :
    D.fixedFactor = D₀.fixedFactor := by
  have h9N : (9:Eis) ∣ N := (dvd_mul_right 9 c).trans hN
  have hcN : c ∣ N := (dvd_mul_left c 9).trans hN
  have h3N : (3:Eis) ∣ N := (show (3:Eis) ∣ 9 from ⟨3,by norm_num⟩).trans h9N
  cases mode
  · exact congrArg eisEmbedding (A3_unramified_fixed_factor_congr N c _ _ hcN ha)
  · apply congrArg eisEmbedding
    exact A3_ramified_fixed_factor_congr N 1 c _ _ _ _ h9N (one_dvd _) hcN
      (D.numerator_primary h3N hr hbase _) (D₀.numerator_primary h3N hr₀ hbase _)
      (A3_ramified_relative_primary _ c (D.ramified_relative h3N hr hbase c (by simp) _))
      (A3_ramified_relative_primary _ c (D₀.ramified_relative h3N hr₀ hbase c (by simp) _)) ha hb

theorem controlled_static_array_eq
    (D : ControlledStratumArithmetic p N a c mode)
    (D₀ : ControlledStratumArithmetic p₀ N a c mode) (hc : c ≠ 0)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hbad : ramifiedTraceLambda^3*c ∣ N)
    (hr : N ∣ (∏ i, p i)-(∏ i, p₀ i))
    (hd : N ∣ D.matrix (fun _ => 1) 1 1 - D₀.matrix (fun _ => 1) 1 1)
    (u : Eisˣ) (m : ℕ) (I J : Ideal Eis) :
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
        (s.modelDualNumerator u) u) m I J =
    fixedCuspArrayWithPhase s.index u
      (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D₀.matrix (fun _ => 1) 1 1)*D₀.U))
        (s.modelDualNumerator u) u) m I J := by
  rw [s.fixedCuspArrayWithPhase_reflectionStaticPhase, s.fixedCuspArrayWithPhase_reflectionStaticPhase]
  have he := congrFun (controlled_bad_phase_eq D D₀ hc hbad hr hd) (s.modelDualNumerator u m I J)
  rw [A4BadPhase_as_fixed_residue,A4BadPhase_as_fixed_residue] at he
  rw [he]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0915

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Brackets
Source SHA256: ce87d2ae072b33f81ef84b31b6acd7b2ddeead1147ef3bb1396833fbb2964110
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0916



namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance bracketField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance bracketFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem marked_bracket_cube (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (n b : Eis) :
    bracket (actualSextic P hg) 0 (Ideal.Quotient.mk P (n*b^3)) =
      (Real.sqrt (Ideal.absNorm P : ℝ) : ℂ)⁻¹ *
      (idealRowHom n P)⁻¹^2 * (if IsCoprime P (Ideal.span {b}) then 1 else 0) := by
  have h6 : (actualSextic P hg (Ideal.Quotient.mk P b))^6 =
      if b ∈ P then 0 else 1 := by
    simpa only [map_pow] using canonicalSextic_sixth_power_mask P hg b
  have h6' : (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 0 ∨
      (actualSextic P hg (Ideal.Quotient.mk P b))^6 = 1 := by
    rw [h6]; split_ifs <;> simp
  let ψ : Eis →* ℂ := (actualSextic P hg).toMonoidHom.comp (Ideal.Quotient.mk P).toMonoidHom
  have he := InverseMoment.inverse_square_cube_mask ψ n b h6'
  change ((actualSextic P hg) (Ideal.Quotient.mk P (n*b^3)))⁻¹^2 =
    ((actualSextic P hg) (Ideal.Quotient.mk P n))⁻¹^2 *
      ((actualSextic P hg) (Ideal.Quotient.mk P b))^6 at he
  simp only [bracket,show (0:ℕ) ≠ 4 by decide,↓reduceIte,
    MulChar.inv_apply_eq_inv',MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),inv_pow]
  simp only [inv_pow] at he
  rw [he,rootCard_eq_sqrt_absNorm,idealRowHom_prime n P hg,h6,
    SixthPowerAverage.prime_coprime_span_iff]
  by_cases hb : b ∈ P <;> simp [hb]

theorem marked_bracket_product {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Eis) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0 (Ideal.Quotient.mk (P i) (n*b^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (idealRowHom n (∏ i, P i))⁻¹^2 *
      (if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0) := by
  simp_rw [marked_bracket_cube]
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]
  have hn : (∏ i, (Real.sqrt (Ideal.absNorm (P i) : ℝ) : ℂ)⁻¹) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ := by
    rw [map_prod,Nat.cast_prod,Real.sqrt_prod,Complex.ofReal_prod,Finset.prod_inv_distrib]
    intro i hi
    positivity
  have hc : (∏ i, (idealRowHom n (P i))⁻¹^2) = (idealRowHom n (∏ i, P i))⁻¹^2 := by
    rw [map_prod,Finset.prod_pow,Finset.prod_inv_distrib]
  have hm : (∏ i, if IsCoprime (P i) (Ideal.span {b}) then (1:ℂ) else 0) =
      if IsCoprime (∏ i, P i) (Ideal.span {b}) then 1 else 0 := by
    classical
    by_cases h : ∀ i, IsCoprime (P i) (Ideal.span {b})
    · simp [h,IsCoprime.prod_left (fun i _ => h i)]
    · obtain ⟨i,hi⟩ := not_forall.mp h
      have hp : ¬ IsCoprime (∏ i, P i) (Ideal.span {b}) := by
        intro hp
        exact hi (hp.of_isCoprime_of_dvd_left (Finset.dvd_prod_of_mem P (Finset.mem_univ i)))
      rw [ite_eq_right hp]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)
  rw [hn,hc,hm]

theorem marked_bracket_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  rw [marked_bracket_product,InverseMoment.inverseCubicKernel_eq_inverse_square,
    (primaryGenerator_spec b hb).1]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0916

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Branch
Source SHA256: 4cbadd8513e6fc1d5b9b854790c44a504745c0e0b541d372af0b45da6dbdc294
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0917


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open CanonicalQuadraticSieve
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance branchFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem residual_branch_zero (K : Ideal Eis) (hK : Admissible K) (n b : Ideal Eis) :
    reflectedBranch (fun P : PrimeIndex K => P.val) (admissiblePrimeGood K hK)
      (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) =
      quadraticRow K (primaryGenerator (n*b)) := by
  simp only [reflectedBranch,reflectedLocalPiece,show (1:ℕ) ≠ 4 by decide,↓reduceIte]
  have hh := residual_bracket_product (fun P : PrimeIndex K => P.val)
    (admissiblePrimeGood K hK) 1 (primaryGenerator n) (primaryGenerator b)
  simp only [one_mul] at hh
  rw [hh,← quadraticRow_eq_primeIndex K hK,← quadraticRow_eq_primeIndex K hK,
    canonical_quadraticRow_one K hK,one_mul,primaryGenerator_mul]

theorem marked_branch_zero {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) =
      (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) := by
  simpa only [reflectedBranch,reflectedLocalPiece,show (0:ℕ) ≠ 4 by decide,↓reduceIte]
    using marked_bracket_hybrid P hg n b hb

theorem moving_branches_hybrid {ι : Type*} [Fintype ι]
    (K : Ideal Eis) (hK : Admissible K)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal] (hg : ∀ i, λ₀ ∉ P i)
    (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    reflectedBranch (fun R : PrimeIndex K => R.val) (admissiblePrimeGood K hK)
      (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
    reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) =
    (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      quadraticRow K (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) := by
  rw [residual_branch_zero K hK n b,marked_branch_zero P hg n b hb]
  ring

theorem frozen_moving_branches_hybrid {ι κ : Type*} [Fintype ι] [Fintype κ]
    (K : Ideal Eis) (hK : Admissible K)
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal] (hg : ∀ i, λ₀ ∉ P i)
    (F : κ → Ideal Eis) [∀ i, (F i).IsMaximal] (hf : ∀ i, λ₀ ∉ F i)
    (j : κ → ℕ) (e : κ → Fin 3) (β : Ideal Eis → Ideal Eis → ℂ)
    (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    β n b * reflectedBranch F hf j e (primaryGenerator n) (primaryGenerator b) *
      (reflectedBranch (fun R : PrimeIndex K => R.val) (admissiblePrimeGood K hK)
        (fun _ => 1) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
      reflectedBranch P hg (fun _ => 0) (fun _ => 0) (primaryGenerator n) (primaryGenerator b) *
        (if IsCoprime K (∏ i, P i) then 1 else 0)) =
    (Real.sqrt (Ideal.absNorm (∏ i, P i) : ℝ) : ℂ)⁻¹ *
      (β n b * reflectedBranch F hf j e (primaryGenerator n) (primaryGenerator b)) *
      quadraticRow K (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i, P i) n *
      (if IsCoprime (∏ i, P i) b then 1 else 0) *
      (if IsCoprime K (∏ i, P i) then 1 else 0) := by
  rw [moving_branches_hybrid K hK P hg n b hb]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0917

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Frozen
Source SHA256: adaed52f640cc968e5cd97730973ee9b2fbfb3b09d0403b3805365a11264687d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0918


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss
open LocalReflectionBrackets FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

lemma scalar_phase_power (a b : ℂ) (ha : a ≠ 0) (j : ℕ) :
    a⁻¹^2*b⁻¹^(j+2) = a^j*(a⁻¹*b⁻¹)^(j+2) := by
  symm
  calc
    _ = (a^j*(a⁻¹)^j)*(a⁻¹)^2*(b⁻¹)^(j+2) := by rw [mul_pow,pow_add]; ring
    _ = _ := by rw [← mul_pow,mul_inv_cancel₀ ha,one_pow,one_mul]

theorem general_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A B z : F)
    (hsigma : (σ : F) = A*z) (he : B*z*(σ : F)*(ε : F) = -1)
    (j : ℕ) (hj0 : j ≠ 0) (hj4 : j ≠ 4) :
    ((χ⁻¹)^2) σ * phase χ ψ j ε =
      (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2)) *
        (χ (-1))⁻¹^(j+2)*(χ A)^j*(χ B)^(j+2)*(χ z)^(2*j+2) := by
  have hs : χ (σ : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr σ.isUnit
  have he' : χ (ε : F) ≠ 0 := MulChar.apply_ne_zero_iff.mpr ε.isUnit
  have hn : χ (-1) ≠ 0 := MulChar.apply_ne_zero_iff.mpr isUnit_neg_one
  have hh := congrArg χ he
  simp only [map_mul] at hh
  have hi := scalar_inverse_pair (χ σ) (χ ε) (χ B*χ z) (χ (-1)) hs he' hn hh
  have hsig : χ (σ : F) = χ A*χ z := by rw [hsigma,map_mul]
  simp only [phase,hj4,hj0,↓reduceIte,MulChar.pow_apply_coe,MulChar.inv_apply_eq_inv']
  calc
    _ = (tau χ (ψ.mulShift (-1)) j*tau χ ψ (j+2))*((χ σ)⁻¹^2*(χ ε)⁻¹^(j+2)) := by ring
    _ = _ := by
      rw [scalar_phase_power _ _ hs j,hi,hsig]
      simp only [mul_pow,pow_add,show 2*j=j+j by omega]
      ring

theorem exceptional_local_phase {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (σ ε : Fˣ) (A z : F)
    (hsigma : (σ : F) = A*z) :
    ((χ⁻¹)^2) σ * phase χ ψ 4 ε =
      (tau χ (ψ.mulShift (-1)) 4*(χ A)⁻¹^2)*(χ z)⁻¹^2 := by
  simp only [phase,↓reduceIte,hsigma,map_mul,
    ]
  simp only [MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
  ring

noncomputable local instance frozenField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance frozenFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenPrimeScalar (p c : Eis) [(Ideal.span {p}).IsMaximal]
    (hp : p ≠ 0) (hg : λ₀ ∉ Ideal.span {p}) (j : ℕ) : ℂ :=
  let χ := actualSextic (Ideal.span {p}) hg
  if j=4 then tau χ ((quotientTrace p hp).mulShift (-1)) 4*
      (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))⁻¹^2
  else if j=0 then markedPrimeScalar p c hp hg
  else (tau χ ((quotientTrace p hp).mulShift (-1)) j*tau χ (quotientTrace p hp) (j+2)) *
    (χ (-1))⁻¹^(j+2)*(χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)))^j*
    (χ (Ideal.Quotient.mk _ (ramifiedTraceLambda^3*c)))^(j+2)

def frozenCofactorCharacter (P : Ideal Eis) [P.IsMaximal]
    (hg : λ₀ ∉ P) (j : ℕ) : Eis →* ℂ :=
  (if j=4 then ((actualSextic P hg)⁻¹)^2 else (actualSextic P hg)^(2*j+2)).toMonoidHom.comp
    (Ideal.Quotient.mk P).toMonoidHom

variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}

theorem controlled_frozen_phase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (i : ι) (j : ℕ) :
    (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i) =
    frozenPrimeScalar (p i) c (hp i) (hg i) j *
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) j (cofactor p i) := by
  have hs : (D.sigma i : Eis ⧸ Ideal.span {p i}) =
      Ideal.Quotient.mk _ (ramifiedTraceLambda^2*c)*Ideal.Quotient.mk _ (cofactor p i) := by
    simpa only [map_mul] using D.sigma_value i
  have he : Ideal.Quotient.mk (Ideal.span {p i}) (ramifiedTraceLambda^3*c)*
      Ideal.Quotient.mk _ (cofactor p i)*(D.sigma i : Eis ⧸ Ideal.span {p i})*
      (D.epsilon i : Eis ⧸ Ideal.span {p i}) = -1 := by
    simpa only [map_mul] using D.epsilon_value i
  by_cases hj4 : j=4
  · subst j
    rw [exceptional_local_phase _ _ _ _ _ _ hs]
    simp only [frozenPrimeScalar,frozenCofactorCharacter,↓reduceIte,MonoidHom.comp_apply,
      RingHom.toMonoidHom_eq_coe,MulChar.coe_toMonoidHom,
      MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0),MulChar.inv_apply_eq_inv']
    rfl
  · by_cases hj0 : j=0
    · subst j
      rw [marked_local_phase _ _ _ _ _ _ he]
      simp [frozenPrimeScalar,frozenCofactorCharacter,markedPrimeScalar,
        MulChar.pow_apply' _ (by decide : (2:ℕ) ≠ 0)]
    · rw [general_local_phase _ _ _ _ _ _ _ hs he j hj0 hj4]
      simp only [frozenPrimeScalar,frozenCofactorCharacter,hj4,hj0,↓reduceIte,
        MonoidHom.comp_apply,RingHom.toMonoidHom_eq_coe,
        MulChar.coe_toMonoidHom,MulChar.pow_apply' _ (by omega : 2*j+2 ≠ 0)]
      rfl

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0918

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Cross
Source SHA256: b139fa041302a5dfe16f2f99b9b4d009332f8e8eaf41279bd82ea8961e3035ce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0919


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped BigOperators Classical
noncomputable section

theorem ordered_cross_partition_on {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (A B U : Finset ι)
    (hd : Disjoint A B) (hu : A ∪ B = U) :
    (∏ i ∈ U, ((∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
      (∏ i ∈ A, ∏ k ∈ B, x i k ^ a * x k i ^ b) := by
  have hA (i : ι) (hi : i ∈ A) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ A.erase i, x i k ^ a) * (∏ k ∈ B, x i k ^ a) := by
    have hn : i ∉ B := fun hb => Finset.disjoint_left.mp hd hi hb
    have he : U.erase i = A.erase i ∪ B := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk]
    rw [he, ite_eq_left hi, Finset.prod_union (hd.mono_left (Finset.erase_subset _ _))]
  have hB (i : ι) (hi : i ∈ B) :
      (∏ k ∈ U.erase i, x i k ^ (if i ∈ A then a else b)) =
        (∏ k ∈ B.erase i, x i k ^ b) * (∏ k ∈ A, x i k ^ b) := by
    have hn : i ∉ A := fun ha => Finset.disjoint_left.mp hd ha hi
    have he : U.erase i = B.erase i ∪ A := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk, or_comm]
    rw [he, ite_eq_right hn, Finset.prod_union (hd.symm.mono_left (Finset.erase_subset _ _))]
  have hpA : (∏ i ∈ A, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ A, (∏ k ∈ A.erase i, x i k ^ a) * l i) *
        (∏ i ∈ A, ∏ k ∈ B, x i k ^ a) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hA i hi]
    ring
  have hpB : (∏ i ∈ B, ((∏ k ∈ U.erase i,
      x i k ^ (if i ∈ A then a else b)) * l i)) =
      (∏ i ∈ B, (∏ k ∈ B.erase i, x i k ^ b) * l i) *
        (∏ i ∈ B, ∏ k ∈ A, x i k ^ b) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    rw [hB i hi]
    ring
  calc
    _ = (∏ i ∈ A, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) *
        (∏ i ∈ B, ((∏ k ∈ U.erase i,
            x i k ^ (if i ∈ A then a else b)) * l i)) := by
      rw [← Finset.prod_union hd, hu]
    _ = _ := by
      rw [hpA, hpB]
      rw [Finset.prod_comm (s := B) (t := A)]
      simp only [Finset.prod_mul_distrib]
      ring

theorem ordered_cross_frozen_partition {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ι → ℂ) (l : ι → ℂ) (a b : ℕ) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F)
    (hu : (R ∪ P) ∪ F = Finset.univ) :
    (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      (∏ i ∈ R, (∏ k ∈ R.erase i, x i k^a)*(l i*∏ k ∈ F, x i k^a)) *
      (∏ i ∈ P, (∏ k ∈ P.erase i, x i k^b)*(l i*∏ k ∈ F, x i k^b)) *
      (∏ i ∈ R, ∏ k ∈ P, x i k^a*x k i^b) := by
  let ll := fun i => l i*∏ k ∈ F, x i k ^ (if i ∈ R then a else b)
  have hx : (∏ i ∈ R ∪ P, (∏ k ∈ Finset.univ.erase i,
      x i k ^ (if i ∈ R then a else b))*l i) =
      ∏ i ∈ R ∪ P, (∏ k ∈ (R ∪ P).erase i,
        x i k ^ (if i ∈ R then a else b))*ll i := by
    apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ F := fun hf => Finset.disjoint_left.mp hF hi hf
    have he : Finset.univ.erase i = (R ∪ P).erase i ∪ F := by
      rw [← hu]
      ext k
      by_cases hk : k = i
      · subst k; simp [hn]
      · simp [hk,or_assoc]
    rw [he,Finset.prod_union (hF.mono_left (Finset.erase_subset _ _))]
    dsimp [ll]
    ring
  rw [hx,ordered_cross_partition_on x ll a b R P (R ∪ P) hRP rfl]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [ll,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [ll,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0919

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.IdealBridge
Source SHA256: 536def867d6e7d368bb7d4d156875be982707228134383ba58b9f39a29f71e16
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0920


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open CanonicalQuadraticSieve CanonicalRowCompletion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
noncomputable local instance idealBridgeFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

theorem admissible_primeIndex_product (K : Ideal Eis) (hK : Admissible K) :
    (∏ P : PrimeIndex K, P.val) = K := by
  have hn := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hK.1).mp hK.2.1
  have hv : (CompletedGauss.primeSupport K).val = UniqueFactorizationMonoid.normalizedFactors K := by
    simpa only [CompletedGauss.primeSupport, Multiset.toFinset_val] using hn.dedup
  calc
    _ = ∏ P ∈ CompletedGauss.primeSupport K, P := Finset.prod_coe_sort _ _
    _ = (CompletedGauss.primeSupport K).val.prod := (Finset.prod_val _).symm
    _ = K := by rw [hv]; exact Ideal.prod_normalizedFactors_eq_self hK.1

theorem idealRowHom_cube_eq_quadratic (K : Ideal Eis) (hK : Admissible K) (z : Eis) :
    idealRowHom z K ^ 3 = quadraticRow K z := by
  conv_lhs => rw [← admissible_primeIndex_product K hK,map_prod,← Finset.prod_pow]
  rw [quadraticRow_eq_primeIndex K hK]
  simp only [finiteSexticRow,MulChar.pow_apply' _ (by decide : (3:ℕ) ≠ 0)]
  apply Finset.prod_congr rfl
  intro P hP
  rw [idealRowHom_prime z P.val (admissiblePrimeGood K hK P)]

theorem residual_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (R : Finset ι) (hR : Admissible (∏ i ∈ R, P i))
    (n b : Ideal Eis) :
    (∏ i ∈ R, bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
  have hl (i : ι) : bracket (actualSextic (P i) (hg i)) 1
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) =
      idealRowHom (primaryGenerator (n*b)) (P i)^3 := by
    have he := residual_bracket_cube (P i) (hg i) 1 (primaryGenerator n) (primaryGenerator b)
    simpa only [one_mul,map_one,one_pow,primaryGenerator_mul,idealRowHom_prime _ (P i) (hg i)] using he
  simp_rw [hl]
  rw [Finset.prod_pow,← map_prod,idealRowHom_cube_eq_quadratic _ hR]

theorem marked_bracket_finset {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (S : Finset ι) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  have he := marked_bracket_hybrid (fun i : S => P i.val) (fun i => hg i.val) n b hb
  have hl : (∏ i : S, bracket (actualSextic (P i.val) (hg i.val)) 0
      (Ideal.Quotient.mk (P i.val) (primaryGenerator n*(primaryGenerator b)^3))) =
      ∏ i ∈ S, bracket (actualSextic (P i) (hg i)) 0
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)) := by
    exact Finset.prod_coe_sort S (fun i => bracket (actualSextic (P i) (hg i)) 0
      (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3)))
  rw [hl] at he
  simpa only [Finset.prod_coe_sort] using he

theorem full_branch_sum_hybrid {ι : Type*} [Fintype ι]
    (P : ι → Ideal Eis) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, λ₀ ∉ P i) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hSj : ∀ i ∈ S, j i = 0)
    (hR : Admissible (∏ i ∈ R, P i)) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    (∑ e : ι → Fin 3, reflectedBranch P hg j e (primaryGenerator n) (primaryGenerator b)) =
      (∏ i ∈ F, bracket (actualSextic (P i) (hg i)) (j i)
        (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))) *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
  trans ∏ i, bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  · exact (prod_bracket_eq_full_branches P hg j (primaryGenerator n) (primaryGenerator b)).symm
  let v := fun i => bracket (actualSextic (P i) (hg i)) (j i)
    (Ideal.Quotient.mk (P i) (primaryGenerator n*(primaryGenerator b)^3))
  have hr : (∏ i ∈ R, v i) = quadraticRow (∏ i ∈ R, P i) (primaryGenerator (n*b)) := by
    rw [← residual_bracket_finset P hg R hR n b]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hRj i hi]
  have hs : (∏ i ∈ S, v i) =
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, P i) : ℝ) : ℂ)⁻¹ *
      InverseMoment.inverseCubicKernel (∏ i ∈ S, P i) n *
      (if IsCoprime (∏ i ∈ S, P i) b then 1 else 0) := by
    rw [← marked_bracket_finset P hg S n b hb]
    apply Finset.prod_congr rfl
    intro i hi
    simp only [v,hSj i hi]
  have hv : (∏ i, v i) = (∏ i ∈ R, v i)*(∏ i ∈ S, v i)*(∏ i ∈ F, v i) := by
    rw [← Finset.prod_union hRS,← Finset.prod_union hF,hu]
  change (∏ i, v i) = _
  rw [hv,hr,hs]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0920

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.ThreeBlocks
Source SHA256: f9010948cd4748e5c24f637527b4a86075f09becb1cde12e98b311b8f9e7f571
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0921


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance threeBlockFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def residualWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (R F : Finset ι) : ℂ :=
  ∏ i ∈ R, (∏ k ∈ R.erase i, MixedCrossSeparation.crossSymbol p hg i k^4)*
    (residualPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, MixedCrossSeparation.crossSymbol p hg i k^4)

def markedWithFrozen [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis) (P F : Finset ι) : ℂ :=
  ∏ i ∈ P, (∏ k ∈ P.erase i, MixedCrossSeparation.crossSymbol p hg i k^2)*
    (markedPrimeScalar (p i) c (hp i) (hg i)*∏ k ∈ F, MixedCrossSeparation.crossSymbol p hg i k^2)

def frozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)

theorem activePhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0) :
    D.activePhase hp hg j = residualWithFrozen hp hg c R F *
      markedWithFrozen hp hg c P F * frozenPhase D hp hg j F := by
  let l : ι → ℂ := fun i => if i ∈ R then residualPrimeScalar (p i) c (hp i) (hg i)
    else markedPrimeScalar (p i) c (hp i) (hg i)
  let v : ι → ℂ := fun i => (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
    phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) (j i) (D.epsilon i)
  have hm : (∏ i ∈ R ∪ P, v i) = ∏ i ∈ R ∪ P,
      (∏ k ∈ Finset.univ.erase i, MixedCrossSeparation.crossSymbol p hg i k ^
        (if i ∈ R then 4 else 2))*l i := by
    apply Finset.prod_congr rfl
    intro i hi
    by_cases hr : i ∈ R
    · simp only [v,hRj i hr,l,hr,ite_true]
      rw [controlled_residual_phase]
      ring
    · have hp' : i ∈ P := (Finset.mem_union.mp hi).resolve_left hr
      simp only [v,hPj i hp',l,hr,ite_false]
      rw [controlled_marked_phase]
      ring
  have hfull : D.activePhase hp hg j = (∏ i ∈ R ∪ P, v i)*frozenPhase D hp hg j F := by
    change (∏ i, v i) = (∏ i ∈ R ∪ P, v i)*(∏ i ∈ F, v i)
    rw [← Finset.prod_union hF,hu]
  rw [hfull,hm,ordered_cross_frozen_partition _ l 4 2 R P F hRP hF hu,
    InverseMoment.row_slot_product_phase p hcop hg hprimary R P hRP,mul_one]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    simp [l,hi]
  · apply Finset.prod_congr rfl
    intro i hi
    have hn : i ∉ R := fun hr => Finset.disjoint_left.mp hRP hr hi
    simp [l,hn]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0921

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.FrozenSplit
Source SHA256: ae4ea2ad9992562800d38ac4a8451f1c20c8f8f8c75a81b7163974db88819f98
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0922


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss FiniteGaussPhase
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance frozenSplitFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def frozenArgument [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) : Eis →* ℂ :=
  ∏ i ∈ F, frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i)

def frozenCore [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (j : ι → ℕ) (F : Finset ι) : ℂ :=
  ∏ i ∈ F, frozenPrimeScalar (p i) c (hp i) (hg i) (j i) *
    frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k)

theorem frozen_cofactor_split (hp : ∀ i, p i ≠ 0) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (i : ι) (hi : i ∈ F) :
    cofactor p i = (∏ k ∈ F.erase i, p k)*(∏ k ∈ R, p k)*(∏ k ∈ S, p k) := by
  apply mul_left_cancel₀ (hp i)
  rw [prime_mul_cofactor,← hu,Finset.prod_union hF,Finset.prod_union hRS,
    ← Finset.mul_prod_erase F p hi]
  ring

theorem frozenPhase_split [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ)
    (R S F : Finset ι) (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F)
    (hu : (R ∪ S) ∪ F = Finset.univ) :
    frozenPhase D hp hg j F = frozenCore hp hg c j F *
      frozenArgument hg j F (∏ i ∈ R, p i) * frozenArgument hg j F (∏ i ∈ S, p i) := by
  unfold frozenPhase
  simp_rw [controlled_frozen_phase]
  have he (i : ι) (hi : i ∈ F) :
      frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (cofactor p i) =
      (frozenPrimeScalar (p i) c (hp i) (hg i) (j i)*
        frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ F.erase i, p k))*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ R, p k)*
      frozenCofactorCharacter (Ideal.span {p i}) (hg i) (j i) (∏ k ∈ S, p k) := by
    rw [frozen_cofactor_split hp R S F hRS hF hu i hi,map_mul,map_mul]
    ring
  rw [Finset.prod_congr rfl he]
  simp only [Finset.prod_mul_distrib,frozenCore,frozenArgument,MonoidHom.finsetProd_apply]

omit [Fintype ι] in
theorem frozenArgument_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι) (z : Eis) :
    ‖frozenArgument hg j F z‖ ≤ 1 := by
  simp only [frozenArgument,MonoidHom.finsetProd_apply,norm_prod]
  apply Finset.prod_le_one₀
  · intro i hi; exact norm_nonneg _
  · intro i hi
    unfold frozenCofactorCharacter
    split_ifs
    · exact FiniteRayExpansion.norm_char_le_one (((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2)
        (Ideal.Quotient.mk (Ideal.span {p i}) z)
    · exact FiniteRayExpansion.norm_char_le_one ((actualSextic (Ideal.span {p i}) (hg i))^(2*j i+2))
        (Ideal.Quotient.mk (Ideal.span {p i}) z)

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0922

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Ramified
Source SHA256: 52a5035adfc7e32d2db60efb76f6a21aabeff61f66697064dc60e86158ede696
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0923


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance ramifiedFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def ramifiedBlock [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  ∏ i ∈ S, unitArgumentFactor (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (u.val*λ₀^m))

theorem ramifiedPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg (fun _ => 1) R u m * ramifiedBlock hg (fun _ => 0) P u m *
      ramifiedBlock hg j F u m := by
  have hh : ramifiedBranchPhase (fun i => Ideal.span {p i}) hg j u m =
      ramifiedBlock hg j R u m * ramifiedBlock hg j P u m * ramifiedBlock hg j F u m := by
    unfold ramifiedBranchPhase ramifiedBlock
    rw [← Finset.prod_union hRP,← Finset.prod_union hF,hu]
    rfl
  rw [hh]
  congr 2
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hRj i hi]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [hPj i hi]

theorem modelRowPhase_three_blocks [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R P F : Finset ι)
    (hRP : Disjoint R P) (hF : Disjoint (R ∪ P) F) (hu : (R ∪ P) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1) (hPj : ∀ i ∈ P, j i = 0)
    (u : Eisˣ) (m : ℕ) :
    D.modelRowPhase s hp hg j u m =
      (residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (markedWithFrozen hp hg c P F * ramifiedBlock hg (fun _ => 0) P
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) *
      (star D.fixedFactor * frozenPhase D hp hg j F * ramifiedBlock hg j F
        (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)) := by
  dsimp only [ControlledStratumArithmetic.modelRowPhase]
  rw [activePhase_three_blocks D hp hg hcop hprimary R P F hRP hF hu j hRj hPj,
    ramifiedPhase_three_blocks hg R P F hRP hF hu j hRj hPj]
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0923

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Norms
Source SHA256: e598a120b40972864d5605df29f293694fe725bcbbdff693bb15d74ce3bffb23
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0924


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance phaseNormField (P : Ideal Eis) [P.IsMaximal] : Field (Eis ⧸ P) := Ideal.Quotient.field P
noncomputable local instance phaseNormFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] in
theorem crossSymbol_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (i k : ι) (hik : i ≠ k) : ‖MixedCrossSeparation.crossSymbol p hg i k‖ = 1 := by
  have hnot : p k ∉ Ideal.span {p i} := by
    intro hm
    have hle : Ideal.span {p k} ≤ Ideal.span {p i} :=
      Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
    have ht := (hcop hik).sup_eq
    rw [sup_eq_left.mpr hle] at ht
    exact (inferInstance : (Ideal.span {p i}).IsMaximal).ne_top ht
  have h6 : MixedCrossSeparation.crossSymbol p hg i k ^ 6 = 1 := by
    simpa only [MixedCrossSeparation.crossSymbol,map_pow,ite_eq_right hnot] using
      canonicalSextic_sixth_power_mask (Ideal.span {p i}) (hg i) (p k)
  apply (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by decide : (6:ℕ) ≠ 0)).mp
  simpa only [norm_pow,norm_one] using congrArg norm h6

theorem local_phase_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (i : ι) (j : ℕ) (hj : j < 6) :
    ‖(((actualSextic (Ideal.span {p i}) (hg i))⁻¹)^2) (D.sigma i)*
      phase (actualSextic (Ideal.span {p i}) (hg i)) (quotientTrace (p i) (hp i)) j (D.epsilon i)‖ = 1 := by
  rw [norm_mul,FiniteRayExpansion.norm_char_unit,one_mul]
  exact canonical_phase_norm (Ideal.span {p i}) (hg i) (hchar i) (quotientTrace (p i) (hp i))
    (GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive (p i) (hp i)) j hj (D.epsilon i)

theorem markedPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖markedPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 0 (by decide)
  rw [controlled_marked_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^2‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualPrimeScalar_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (i : ι) :
    ‖residualPrimeScalar (p i) c (hp i) (hg i)‖ = 1 := by
  have h := local_phase_norm D hp hg hchar i 1 (by decide)
  rw [controlled_residual_phase,norm_mul,norm_prod] at h
  have he : (∏ k ∈ Finset.univ.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k^4‖) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [norm_pow,crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  simpa only [he,mul_one] using h

theorem residualWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (R F : Finset ι) (hd : Disjoint R F) : ‖residualWithFrozen hp hg c R F‖ = 1 := by
  unfold residualWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,residualPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hR : (∏ k ∈ R.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^4) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hR,hF,one_mul]

theorem markedWithFrozen_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (P F : Finset ι) (hd : Disjoint P F) : ‖markedWithFrozen hp hg c P F‖ = 1 := by
  unfold markedWithFrozen
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  simp only [norm_mul,norm_prod,norm_pow,markedPrimeScalar_norm D hp hg hchar hcop i,one_mul]
  have hP : (∏ k ∈ P.erase i, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (Finset.mem_erase.mp hk).1.symm,one_pow]
  have hF : (∏ k ∈ F, ‖MixedCrossSeparation.crossSymbol p hg i k‖^2) = 1 := by
    apply Finset.prod_eq_one
    intro k hk
    rw [crossSymbol_norm hg hcop i k (fun h => Finset.disjoint_left.mp hd hi (h ▸ hk)),one_pow]
  rw [hP,hF,one_mul]

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0924

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Coefficient
Source SHA256: 6517bda77904edee77974c7af4f85953290e1d2a64d72d338efdcf153482ba7b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0925




namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein ConcreteTraceCRT CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance coefficientFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

def sourceRowPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (R F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  residualWithFrozen hp hg c R F * ramifiedBlock hg (fun _ => 1) R
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ R, p i)

def sourceSlotPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  markedWithFrozen hp hg c S F * ramifiedBlock hg (fun _ => 0) S
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m) * frozenArgument hg j F (∏ i ∈ S, p i)

def sourceFrozenPhase [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (F : Finset ι) (u : Eisˣ) (m : ℕ) : ℂ :=
  star D.fixedFactor * frozenCore hp hg c j F * ramifiedBlock hg j F
    (sourcePhaseUnit s.index s.phaseUpperUnit u) (sourcePhaseExponent s.index m)

def sourceColumn [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (F : Finset ι)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) : ℂ :=
  fixedCuspArrayWithPhase s.index u
    (s.reflectionStaticPhase c hc (Ideal.Quotient.mk _ (-(D.matrix (fun _ => 1) 1 1)*D.U))
      (s.modelDualNumerator u) u) m n b *
  ∏ i ∈ F, bracket (actualSextic (Ideal.span {p i}) (hg i)) (j i)
    (Ideal.Quotient.mk _ (primaryGenerator n*(primaryGenerator b)^3))

theorem mixed_coefficient_hybrid [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg (markedActiveExponent S j) R F u m * sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m *
      sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m) *
      sourceColumn D s hc hg (markedActiveExponent S j) F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hrj : ∀ i ∈ R, markedActiveExponent S j i = 1 := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hRS hi hs
    simp only [markedActiveExponent,hn,ite_false,hRj i hi]
  have hsj : ∀ i ∈ S, markedActiveExponent S j i = 0 := by
    intro i hi
    simp only [markedActiveExponent,hi,ite_true]
  have hmask : IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) := by
    apply IsCoprime.prod_left
    intro i hi
    apply IsCoprime.prod_right
    intro k hk
    exact hcop (fun h => Finset.disjoint_left.mp hRS hi (h ▸ hk))
  rw [mixed_model_coefficient,modelRowPhase_three_blocks D s hp hg hcop hprimary R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj,
    frozenPhase_split D hp hg (markedActiveExponent S j) R S F hRS hF hu,← Finset.mul_sum,
    full_branch_sum_hybrid (fun i => Ideal.span {p i}) hg R S F hRS hF hu
      (markedActiveExponent S j) hrj hsj hR n b hb,ite_eq_left hmask,mul_one]
  unfold sourceRowPhase sourceSlotPhase sourceFrozenPhase sourceColumn
  ring

end
end SevenEighths.InverseReflectedPhase

end OAI
end OAIOriginalModule0925

/-! Original module: OAI.NumberTheory.DirichletL.Reflection.Independent
Source SHA256: b82b9fb6026e14c56b7e9011a3d9e91fdf1255cbf68fa56f4bbd27dd1108d5cf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0926


namespace OAI

namespace SevenEighths.InverseReflectedPhase
open scoped Classical BigOperators
open ActualEisensteinCubic CubicEisenstein CompletedGauss LocalReflectionBrackets
open InverseMoment
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda
variable {ι : Type*} [Fintype ι] {p : ι → Eis} {N a c : Eis} {mode : Bool}
noncomputable local instance independentFinite (P : Ideal Eis) [P.IsMaximal] : Fintype (Eis ⧸ P) := Fintype.ofFinite _

omit [Fintype ι] in
theorem ramifiedBlock_norm [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S : Finset ι) (u : Eisˣ) (m : ℕ) :
    ‖ramifiedBlock hg j S u m‖ = 1 := by
  unfold ramifiedBlock
  rw [norm_prod]
  apply Finset.prod_eq_one
  intro i hi
  exact unitArgumentFactor_norm _ _ _ (unit_ramified_quotient_ne_zero _ (hg i) u m)

theorem sourceRowPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (R F : Finset ι) (hd : Disjoint R F) (u : Eisˣ) (m : ℕ) :
    ‖sourceRowPhase s hp hg j R F u m‖ ≤ 1 := by
  rw [sourceRowPhase,norm_mul,norm_mul,residualWithFrozen_norm D hp hg hchar hcop R F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

theorem sourceSlotPhase_norm_le_one [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    ‖sourceSlotPhase s hp hg j S F u m‖ ≤ 1 := by
  rw [sourceSlotPhase,norm_mul,norm_mul,markedWithFrozen_norm D hp hg hchar hcop S F hd,
    ramifiedBlock_norm,one_mul,one_mul]
  exact frozenArgument_norm_le_one hg j F _

omit [Fintype ι] in
theorem frozenArgument_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) : frozenArgument hg j F = frozenArgument hg j' F := by
  unfold frozenArgument
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem frozenCore_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (c : Eis)
    (j j' : ι → ℕ) (F : Finset ι) (hj : ∀ i ∈ F, j i = j' i) :
    frozenCore hp hg c j F = frozenCore hp hg c j' F := by
  unfold frozenCore
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

omit [Fintype ι] in
theorem ramifiedBlock_congr [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j j' : ι → ℕ) (F : Finset ι)
    (hj : ∀ i ∈ F, j i = j' i) (u : Eisˣ) (m : ℕ) :
    ramifiedBlock hg j F u m = ramifiedBlock hg j' F u m := by
  unfold ramifiedBlock
  apply Finset.prod_congr rfl
  intro i hi
  rw [hj i hi]

theorem marked_phases_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (j : ι → ℕ) (R S F : Finset ι) (hd : Disjoint S F) (u : Eisˣ) (m : ℕ) :
    sourceRowPhase s hp hg (markedActiveExponent S j) R F u m = sourceRowPhase s hp hg j R F u m ∧
    sourceSlotPhase s hp hg (markedActiveExponent S j) S F u m = sourceSlotPhase s hp hg j S F u m ∧
    sourceFrozenPhase D s hp hg (markedActiveExponent S j) F u m = sourceFrozenPhase D s hp hg j F u m := by
  have hj : ∀ i ∈ F, markedActiveExponent S j i = j i := by
    intro i hi
    have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
    simp only [markedActiveExponent,hn,ite_false]
  simp only [sourceRowPhase,sourceSlotPhase,sourceFrozenPhase,
    frozenArgument_congr hg _ _ F hj,frozenCore_congr hp hg c _ _ F hj,
    ramifiedBlock_congr hg _ _ F hj]
  simp

theorem marked_sourceColumn_eq [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode)) (hc : c ≠ 0)
    (hg : ∀ i, λ₀ ∉ Ideal.span {p i}) (j : ι → ℕ) (S F : Finset ι) (hd : Disjoint S F)
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) :
    sourceColumn D s hc hg (markedActiveExponent S j) F u m n b =
      sourceColumn D s hc hg j F u m n b := by
  unfold sourceColumn
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hn : i ∉ S := fun hs => Finset.disjoint_left.mp hd hs hi
  simp only [markedActiveExponent,hn,ite_false]

theorem mixed_coefficient_hybrid_original_exponents [∀ i, (Ideal.span {p i}).IsMaximal]
    (D : ControlledStratumArithmetic p N a c mode)
    (s : FixedCuspShape (ControlledStratumArithmetic.fixedCusp a c mode))
    (hp : ∀ i, p i ≠ 0) (hc : c ≠ 0) (hg : ∀ i, λ₀ ∉ Ideal.span {p i})
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hprimary : ∀ i, λ₀^2 ∣ p i-1) (R S F : Finset ι)
    (hRS : Disjoint R S) (hF : Disjoint (R ∪ S) F) (hu : (R ∪ S) ∪ F = Finset.univ)
    (j : ι → ℕ) (hRj : ∀ i ∈ R, j i = 1)
    (hR : CanonicalQuadraticSieve.Admissible (∏ i ∈ R, Ideal.span {p i}))
    (u : Eisˣ) (m : ℕ) (n b : Ideal Eis) (hb : primaryGenerator b ≠ 0) :
    s.amplitude u m n b *
      (star D.fixedFactor * ShortDraftCusp.A4BadPhase c hc (D.matrix (fun _ => 1) 1 1) D.U
        (s.modelDualNumerator u m n b)) *
      (∏ i, mixedActiveBracket hp hg j S D i (s.modelDualNumerator u m n b)) =
    ((-1:ℂ)^S.card * sourceRowPhase s hp hg j R F u m * sourceSlotPhase s hp hg j S F u m *
      sourceFrozenPhase D s hp hg j F u m) *
      sourceColumn D s hc hg j F u m n b *
      (Real.sqrt (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) : ℂ)⁻¹ *
      CanonicalQuadraticSieve.quadraticRow (∏ i ∈ R, Ideal.span {p i}) (primaryGenerator (n*b)) *
      inverseCubicKernel (∏ i ∈ S, Ideal.span {p i}) n *
      (if IsCoprime (∏ i ∈ S, Ideal.span {p i}) b then 1 else 0) *
      (if IsCoprime (∏ i ∈ R, Ideal.span {p i}) (∏ i ∈ S, Ideal.span {p i}) then 1 else 0) := by
  have hd : Disjoint S F := hF.mono_left Finset.subset_union_right
  have he := mixed_coefficient_hybrid D s hp hc hg hcop hprimary R S F hRS hF hu j hRj hR u m n b hb
  obtain ⟨hr,hs,hf⟩ := marked_phases_eq D s hp hg j R S F hd u m
  rw [hr,hs,hf,marked_sourceColumn_eq D s hc hg j S F hd u m n b] at he
  exact he

end
end SevenEighths.InverseReflectedPhase

end OAI
