Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1646


namespace OAI

noncomputable section
namespace SevenEighths.CenteredMomentFinalStageLedger

theorem capped_loss (M v : ℝ) : M/6≤2*v/3+max (M/4-v) 0 := by
  by_cases h : 0≤M/4-v
  · rw [max_eq_left h]
    linarith
  · rw [max_eq_right (le_of_not_ge h)]
    linarith

theorem final_exponent (A M v loss₁ loss₂ : ℝ) :
    A-5*M/6-2*v/3-max (M/4-v) 0+loss₁+loss₂≤
      max (A-M) 0+loss₁+loss₂ := by
  have h:=capped_loss M v
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

theorem saving_exponent (A M v F₁ F₂ loss₁ loss₂ : ℝ)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    A-5*M/6-F₁-F₂≤max (A-M) 0+loss₁+loss₂ := by
  linarith [final_exponent A M v loss₁ loss₂]

theorem saving_power (Z A M v F₁ F₂ loss₁ loss₂ : ℝ) (hZ:1≤Z)
    (h₁:2*v/3-loss₁≤F₁) (h₂:max (M/4-v) 0-loss₂≤F₂) :
    Z^(A-5*M/6-F₁-F₂)≤Z^(max (A-M) 0+loss₁+loss₂) :=
  Real.rpow_le_rpow_of_exponent_le hZ (saving_exponent A M v F₁ F₂ loss₁ loss₂ h₁ h₂)

end SevenEighths.CenteredMomentFinalStageLedger

end

end OAI
end OAIOriginalModule1646

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondScaled
Source SHA256: 401fad97f9c653419b699cbf92f23276fee9fdeb623da533179d7402b7d3ae93
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1647




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondScaled
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentPlainChildEnergy RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentProductCRT CenteredMomentUnequal CenteredMomentPartition
local notation "O" => ActualEisensteinCubic.O

def movingCoefficient {α : Type*} (A : O) (a : α → O) (c : α → ℂ) (i : α) : ℂ :=
  c i*idealRowHom A (Ideal.span {a i})

theorem divisorCoefficient_moving {α : Type*} (L : Ideal O) (A : O) (a : α → O)
    (c : α → ℂ) (χ : RayCharacter) (i : α) :
    divisorCoefficient L a (movingCoefficient A a c) χ i =
      divisorCoefficient L a c χ i*idealRowHom A (Ideal.span {a i}) := by
  unfold divisorCoefficient movingCoefficient
  split_ifs <;> ring

theorem actual_child_column {α : Type*} (L : Ideal O) (η : HeckeFamily.Character)
    (χ : RayCharacter) (m A₀ h : O) (a : α → O) (β : α → ℂ) (i : α)
    (ha : Supported (Ideal.span {a i}))
    (hp : ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) :
    divisorCoefficient L a (movingCoefficient A₀ a
      (fun j => β j*HeckeFamily.elementCoeff η (a j)*coprimalityMask m (a j))) χ i *
      idealRowHom h (Ideal.span {a i}) =
    (if L ∣ Ideal.span {a i} then β i else 0) *
      rowTwist (HeckeRowClosure.elementHom (CenteredMomentChildRows.childCharacter η χ))
        m 1 (A₀*h) (a i) := by
  rw [CenteredMomentChildRows.child_row_primary η χ m A₀ h (a i) ha hp]
  simp only [divisorCoefficient,movingCoefficient,idealRowHom_argument_mul]
  split_ifs <;> ring

theorem scaled_partition_scalar {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (V₀ h : O)
    (hpart : part (V₀*h) → ∀ i ∈ U, c i=d i ∧ ¬6∣c i ∧
      ¬p i∣CenteredMomentPartition.dividedFrequency p c d (V₀*h) i) :
    ‖(if part (V₀*h) then (1:ℂ)/(CenteredMomentPartition.partitionNormalizer p c d U : ℂ) else 0) *
      actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        (((∏ i, p i^min (c i) (d i))*V₀)*h)‖ ≤ 1 := by
  have hb := CenteredMomentPartition.normalized_partition_norm_le_one
    p hp hg hchar hcop c d hc hd U part (V₀*h) hpart
  by_cases hh : part (V₀*h)
  · simpa only [ite_eq_left hh,one_div,div_eq_mul_inv,mul_assoc,mul_comm,mul_left_comm,one_mul] using hb
  · simp only [ite_eq_right hh,zero_mul,norm_zero,zero_le_one]

theorem actual_scaled_row_children {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
    (D E A₀ : O) (a : α → O) (b : β → O)
    (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
    (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j}))
    (hpD : ConcretePrimeRowBridge.goodLambda^2 ∣ D-1)
    (hpE : ConcretePrimeRowBridge.goodLambda^2 ∣ E-1)
    (hpa : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1)
    (hpb : ∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1)
    (hcopA : ∀ i, IsCoprime (D*E) (a i)) (hcopB : ∀ j, IsCoprime (D*E) (b j))
    (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (K : O → α → β → ℂ) :
    (∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
      (if IsCoprime (a i) (b j) then
        actualCorrelation (D*a i) (E*b j)
          (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
        else 0) * (c i*star (d j))*K z i j) =
      ∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
        (UniqueFactorizationMonoid.moebius L : ℂ) *
          ∑ χ : RayCharacter, ∑ ξ : RayCharacter, pairCoeff (phaseTable D E) χ ξ *
            ∑ z ∈ rows, (q z*actualCorrelation D E hD hE (A₀*z)) *
              ∑ i ∈ S, ∑ j ∈ T,
                ((divisorCoefficient L a (movingCoefficient A₀ a c) χ i*idealRowHom z (Ideal.span {a i})) *
                  star (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹) j*idealRowHom (-z) (Ideal.span {b j}))) * K z i j := by
  simp_rw [finite_correlation_children S T D E a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro L hL
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [Finset.sum_comm (s := rows)]
  apply Finset.sum_congr rfl
  intro ξ hξ
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -(A₀*z)=A₀*(-z) by ring]
  simp only [idealRowHom_argument_mul,divisorCoefficient_moving,star_mul]
  ring

theorem whole_kernel_scaled_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ),
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (rowEnergy S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K).re ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (rowEnergy T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K).re ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_plain_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondScaled

end

end OAI
end OAIOriginalModule1647

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondChildProfile
Source SHA256: da45b2c13bf33cc0f218f269b151bd5e7e37eb75d245484ab5737a36cbf71dce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1648



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondChildProfile
open HeckeFamily HeckeRowClosure CenteredMomentChildRows CenteredMomentHeckeExpansion
open CenteredMomentHeckeColumnWindow CenteredMomentSourceRow CenteredMomentChildAssembly
open CenteredMomentSecondScaled CanonicalRowCompletion CanonicalQuadraticSieve RayFourExpansion
open ConcretePrimeRowBridge CenteredMomentCommonSupport
local notation "O" => ActualEisensteinCubic.O

theorem child_ideal_primary (η : Character) (χ : RayCharacter)
    (I : Ideal O) (hI : Supported I) :
    idealCoeff (childCharacter η χ) I=idealCoeff η I*rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  have hn := supported_primaryGenerator_ne_zero I hI
  have hs := primary_span_supported I hI
  have hc := idealCoeff_span (childCharacter η χ) hn
  have he := idealCoeff_span η hn
  rw [hs] at hc he
  rw [hc,childCharacter_primary η χ _ (by rw [hs];exact hI)
    (CompletedGauss.primaryGenerator_spec I hn).2,←he]

theorem exists_second_height_character (η : Character) (χ : RayCharacter) (m A : O)
    (hm : m≠0) (hA : A≠0) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m) :
    ∃ τ : Character,τ.modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
          rayCharacter χ (CompletedGauss.primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) m 1 A hm one_ne_zero hA hmLam hm2
  refine ⟨τ,hN,?_⟩
  intro I hI t
  have he := idealCoeff_eq_row (childCharacter η χ) τ m 1 A hτ I
  simp only [one_pow,mul_one] at he
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff η I*idealRowHom (m^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*
      idealRowHom A I*rayCharacter χ (CompletedGauss.primaryGenerator I)
  rw [he,child_ideal_primary η χ I hI,idealRowHom_argument_mul]
  simp only [mul_one]
  ring

theorem second_divisor_column (η τ : Character) (χ : RayCharacter) (m A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=rowWeight η m 1 1 t I*idealRowHom A I*
        rayCharacter χ (CompletedGauss.primaryGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => CompletedGauss.primaryGenerator J)
      (movingCoefficient A (fun J : Ideal O => CompletedGauss.primaryGenerator J)
        (fun J => β J*rowWeight η m 1 1 t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

end SevenEighths.CenteredMomentSecondChildProfile

end

end OAI
end OAIOriginalModule1648

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondHeightFamily
Source SHA256: e8dc3742e61f79d9bc24d81238d18f9601dbde6f5990c6b9a1157edac3f25e18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1649


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondHeightFamily
open HeckeFamily CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredMomentSecondChildProfile CenteredMomentChildRows CenteredMomentChildAssembly
open CenteredMomentSecondScaled RayFourExpansion ConcretePrimeRowBridge ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O

def fixedBadMask : O := goodLambda*2

theorem fixedBadMask_ne_zero : fixedBadMask≠0 :=
  mul_ne_zero PrimaryIdealUnitReindex.lambda_prime_actual.ne_zero (by norm_num)

theorem fixedBadMask_coprime (n : O) (hn : Supported (Ideal.span {n})) :
    IsCoprime fixedBadMask n := by
  have hl := PrimaryIdealUnitReindex.lambda_prime_actual.irreducible.coprime_iff_not_dvd.mpr
    ((supported_span_iff n).mp hn).1
  have h2 := negative_two_prime.irreducible.coprime_iff_not_dvd.mpr
    (by simpa only [neg_dvd] using ((supported_span_iff n).mp hn).2)
  have htwo : IsCoprime (2:O) n := h2.of_isCoprime_of_dvd_left ⟨-1,by ring⟩
  exact hl.mul_left htwo

theorem heightCoeff_eq_fixed_rowWeight (τ : Character) (t : ℝ)
    (I : Ideal O) (hI : Supported I) :
    heightCoeff τ t I=rowWeight τ fixedBadMask 1 1 t I := by
  have hc : IsCoprime (Ideal.span {fixedBadMask}) I := by
    rw [←primary_span_supported I hI,Ideal.isCoprime_span_singleton_iff]
    exact fixedBadMask_coprime _ ((supported_span_primaryGenerator_iff I).mpr hI)
  have hs := idealRowHom_sixth_mask fixedBadMask I hI
  rw [ite_eq_left hc.symm] at hs
  change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=
    ((idealCoeff τ I*idealRowHom (fixedBadMask^6*(1*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))
  simp only [mul_one,hs]

theorem exists_second_family (η : Character) (χ : RayCharacter) (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤HeckeRowClosure.rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*
          rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_second_height_character η χ fixedBadMask A fixedBadMask_ne_zero hA
    (by exact dvd_mul_right goodLambda (2:O)) (by exact dvd_mul_left (2:O) goodLambda)
  refine ⟨τ,hN,?_⟩
  intro I hI t
  rw [hτ I hI t,←heightCoeff_eq_fixed_rowWeight η t I hI]

theorem second_height_divisor_column (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ I : Ideal O,Supported I → ∀ t : ℝ,
      heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I))
    (L I : Ideal O) (hI : Supported I) (β : Ideal O → ℂ) (t : ℝ) :
    divisorCoefficient L (fun J : Ideal O => primaryGenerator J)
      (movingCoefficient A (fun J : Ideal O => primaryGenerator J)
        (fun J => β J*heightCoeff η t J)) χ I=
      (if L∣I then β I else 0)*heightCoeff τ t I := by
  rw [divisorCoefficient,movingCoefficient,primary_span_supported I hI,hτ I hI t]
  split_ifs <;> ring

end SevenEighths.CenteredMomentSecondHeightFamily

end

end OAI
end OAIOriginalModule1649

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondFamilyTransport
Source SHA256: 55adc5b89a4d92420e171804c36a7a48377ac83e0d68b6ad882eca5f10fd60a9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1650



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondFamilyTransport
open HeckeFamily HeckeRowClosure CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open CenteredMomentSecondHeightFamily CenteredMomentSecondChildProfile CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentHeckeColumnWindow CenteredMomentHeckeExpansion
open CenteredExceptionalProfile CenteredMomentRestrictedEnergy RayFourExpansion
local notation "O" => ActualEisensteinCubic.O

theorem row_presentation_height (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (I : Ideal O) (hI : Supported I) (t : ℝ) :
    heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  have he := idealCoeff_eq_row (childCharacter η χ) τ fixedBadMask 1 A hτ I
  have he' : heightCoeff τ t I=rowWeight (childCharacter η χ) fixedBadMask 1 A t I := by
    change idealCoeff τ I*(Ideal.absNorm I:ℂ)^(Complex.I*t)=_
    rw [he]
    simp only [rowWeight,MonoidWithZeroHom.coe_mk,ZeroHom.coe_mk,one_pow,one_mul,mul_one]
  rw [he',rowWeight_split,←heightCoeff_eq_fixed_rowWeight (childCharacter η χ) t I hI]
  simp only [heightCoeff,child_ideal_primary η χ I hI]
  ring

theorem exists_second_family_presentation (η : Character) (χ : RayCharacter)
    (A : O) (hA : A≠0) :
    ∃ τ : Character,
      τ.modulus.absNorm≤rowConductorBound (childCharacter η χ) fixedBadMask 1 A ∧
      (∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n) ∧
      ∀ I : Ideal O,Supported I → ∀ t : ℝ,
        heightCoeff τ t I=heightCoeff η t I*idealRowHom A I*rayCharacter χ (primaryGenerator I) := by
  obtain ⟨τ,hN,hτ⟩ := exists_row_character_with_conductor (childCharacter η χ) fixedBadMask 1 A
    fixedBadMask_ne_zero one_ne_zero hA (dvd_mul_right _ _) (dvd_mul_left _ _)
  exact ⟨τ,hN,hτ,fun I hI t => row_presentation_height η τ χ A hτ I hI t⟩

theorem row_presentation_twist (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (z n : O) :
    rowTwist (elementHom τ) fixedBadMask 1 z n=
      rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n := by
  by_cases hn : Supported (Ideal.span {n})
  · have hc : coprimalityMask fixedBadMask n=1 := by
      change (if IsCoprime fixedBadMask n then (1:ℂ) else 0)=1
      rw [ite_eq_left (fixedBadMask_coprime n hn)]
    have ht := hτ n
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn] at ht
    rw [rowTwist_extract_sixth_mask _ _ _ _ n hn,rowTwist_extract_sixth_mask _ _ _ _ n hn]
    change elementCoeff τ n*coprimalityMask fixedBadMask n*idealRowHom (1^4*z) (Ideal.span {n})=_
    rw [ht,hc]
    simp only [one_pow,one_mul,mul_one,idealRowHom_argument_mul]
    ring
  · have hmLam : ConcretePrimeRowBridge.goodLambda∣fixedBadMask := dvd_mul_right _ _
    have hm2 : (2:O)∣fixedBadMask := dvd_mul_left _ _
    exact (rowTwist_zero_of_not_supported (elementHom τ) fixedBadMask 1 z n hmLam hm2 hn).trans
      (rowTwist_zero_of_not_supported (elementHom (childCharacter η χ)) fixedBadMask 1 (A*z) n hmLam hm2 hn).symm

theorem fixedInducingRow_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    FixedInducingRow τ Q fixedBadMask 1 z ↔
      FixedInducingRow (childCharacter η χ) Q fixedBadMask A z := by
  unfold FixedInducingRow
  simp only [one_mul,row_presentation_twist η τ χ A hτ]

theorem nonexceptional_transport (η τ : Character) (χ : RayCharacter) (A : O)
    (hτ : ∀ n,elementCoeff τ n=rowTwist (elementHom (childCharacter η χ)) fixedBadMask 1 A n)
    (Q : Ideal O) (z : O) :
    nonexceptional η χ Q fixedBadMask A z ↔
      z≠0 ∧ ¬FixedInducingRow τ Q fixedBadMask 1 z := by
  rw [nonexceptional,fixedInducingRow_transport η τ χ A hτ Q z]

end SevenEighths.CenteredMomentSecondFamilyTransport

end

end OAI
end OAIOriginalModule1650

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondNonexceptional
Source SHA256: 21961176a61b9d6de5d6496cec5dfaf46d6acfffb780c87ae80053e915468a1b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1651



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentSecondNonexceptional
open CanonicalRowCompletion CanonicalQuadraticSieve CenteredMomentSupportedCorrelation
open CenteredMomentChildAssembly CenteredMomentMobiusRegroup CenteredMomentFixedRay
open CenteredMomentRowNorm CenteredMomentSmooth RayFourExpansion
open CenteredMomentSecondDescent CenteredMomentSecondScaled CenteredMomentRestrictedEnergy
local notation "O" => ActualEisensteinCubic.O

theorem whole_kernel_nonexceptional_second_bound (W : 𝓢(ℝ, ℂ)) (V : Fin 4 → ℝ → ℂ)
    (M : Fin 4 → ℝ) (hM : ∀ i, 0 ≤ M i)
    (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i) (A J₁ J₂ : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R →
      ∀ {α β : Type*} (rows : Finset O) (S : Finset α) (T : Finset β)
        (D E A₀ : O) (a : α → O) (b : β → O)
        (hD : Supported (Ideal.span {D})) (hE : Supported (Ideal.span {E}))
        (ha : ∀ i, Supported (Ideal.span {a i})) (hb : ∀ j, Supported (Ideal.span {b j})),
      (ConcretePrimeRowBridge.goodLambda^2 ∣ D-1) →
      (ConcretePrimeRowBridge.goodLambda^2 ∣ E-1) →
      (∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ a i-1) →
      (∀ j, ConcretePrimeRowBridge.goodLambda^2 ∣ b j-1) →
      (∀ i, IsCoprime (D*E) (a i)) → (∀ j, IsCoprime (D*E) (b j)) →
      ∀ (q : O → ℂ) (c : α → ℂ) (d : β → ℂ) (u : α → ℝ) (v : β → ℝ)
        (ρ x : O → ℝ) (η₀ : HeckeFamily.Character) (χ₀ : RayCharacter)
        (Q : Ideal O) (m : O),
      (Q ≤ Ideal.span {(72:O)}) → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      (∀ z ∈ rows, nonexceptional η₀ χ₀ Q m A₀ z) →
      (∀ z ∈ rows, ‖q z*actualCorrelation D E hD hE (A₀*z)‖ ≤ 1) →
      (∀ z ∈ rows, ‖V 0 (ρ z)‖ ≤ 1) → (∀ z ∈ rows, ‖V 1 (x z)‖ ≤ 1) →
      ∀ (U : 𝓢(ℝ, ℂ)) (K : ℝ), 0 < K →
      (∀ z : O, 0 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      (∀ z ∈ rows, 1 ≤ (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) →
      ∀ (B₁ B₂ : Ideal O → ℝ),
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₁ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), 0 ≤ B₂ L) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ χ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ χ Q m A₀) S a (fun i => divisorCoefficient L a (movingCoefficient A₀ a c) χ i*columnPhase (V 2) (u i) t) U K) ≤
          (B₁ L*(1+‖t‖)^J₁)^2) →
      (∀ L ∈ divisorPool T (fun j => Ideal.span {b j}), ∀ ξ : RayCharacter, ∀ t : ℝ,
        (restrictedEnergy (nonexceptional η₀ ξ Q m A₀) T b (fun j => divisorCoefficient L b (movingCoefficient A₀ b d) ξ j*star (columnPhase (V 3) (v j) t)) U K) ≤
          (B₂ L*(1+‖t‖)^J₂)^2) →
      (1+R)^A * ‖∑ z ∈ rows, q z * ∑ i ∈ S, ∑ j ∈ T,
        (if IsCoprime (a i) (b j) then
          actualCorrelation (D*a i) (E*b j)
            (supported_mul_elements _ _ hD (ha i)) (supported_mul_elements _ _ hE (hb j)) (A₀*z)
          else 0) * (c i*star (d j))*wholeKernel W V R (ρ z) (x z) (u i) (v j)‖ ≤
        C*∑ L ∈ divisorPool T (fun j => Ideal.span {b j}),
          ‖(UniqueFactorizationMonoid.moebius L : ℂ)‖*(B₁ L*B₂ L) := by
  obtain ⟨C,hC,hbound⟩ := whole_kernel_restricted_child_bound W V M hM hV A J₁ J₂
  refine ⟨256*C,mul_nonneg (by norm_num) hC,?_⟩
  intro R hR α β rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB
    q c d u v ρ x η₀ χ₀ Q m hQ hmLam hm2 hrows hq hV₀ hV₁ U K hK hU hmajor B₁ B₂ hB₁ hB₂ hleft hright
  rw [actual_scaled_row_children rows S T D E A₀ a b hD hE ha hb hpD hpE hpa hpb hcopA hcopB]
  apply finite_ray_divisor_bound _ D E _ ((1+R)^A) C (by positivity) hC B₁ B₂ hB₁ hB₂
  intro L hL χ ξ
  exact hbound R hR rows S T a b ha hb
    (divisorCoefficient L a (movingCoefficient A₀ a c) χ) (divisorCoefficient L b (movingCoefficient A₀ b d) (ξ⁻¹)) u v ρ x
    (fun z => q z*actualCorrelation D E hD hE (A₀*z))
    (nonexceptional η₀ χ Q m A₀) (nonexceptional η₀ (ξ⁻¹) Q m A₀)
    (fun z hz => (nonexceptional_ray_independent η₀ χ₀ χ Q hQ m A₀ z hmLam hm2).mp (hrows z hz))
    (fun z hz => (nonexceptional_reflection η₀ χ₀ (ξ⁻¹) Q hQ m A₀ z hmLam hm2).mp (hrows z hz)) hq hV₀ hV₁ U K hK hU hmajor
    (B₁ L) (B₂ L) (hB₁ L hL) (hB₂ L hL) (hleft L hL χ) (hright L hL (ξ⁻¹))

end SevenEighths.CenteredMomentSecondNonexceptional

end

end OAI
end OAIOriginalModule1651

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SectorLocalization
Source SHA256: 4ef4f37afa0faa756f212aefab63af497809f145480ed7f5320e8822f5d6cda8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1652



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentSectorLocalization
open CubicEisenstein ConcreteTraceCRT EisensteinSchwartzPoisson CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
local notation "O" => ActualEisensteinCubic.O

def cutoff (x : ℝ) : ℝ := Real.smoothTransition (2-2*x)

theorem cutoff_one (x : ℝ) (hx : x ≤ 1/2) : cutoff x=1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoff_zero (x : ℝ) (hx : 1 ≤ x) : cutoff x=0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

theorem cutoff_bounds (x : ℝ) : 0 ≤ cutoff x ∧ cutoff x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoff_antitone : Antitone cutoff := by
  intro x y hxy
  exact Real.smoothTransition.monotone (by linarith)

def annulus (x : ℝ) : ℝ := cutoff x-cutoff (2*x)

theorem annulus_zero_low (x : ℝ) (hx : x ≤ 1/4) : annulus x=0 := by
  rw [annulus, cutoff_one x (by linarith),cutoff_one (2*x) (by linarith),sub_self]

theorem annulus_zero_high (x : ℝ) (hx : 1 ≤ x) : annulus x=0 := by
  rw [annulus,cutoff_zero x hx,cutoff_zero (2*x) (by linarith),sub_self]

theorem annulus_bounds (x : ℝ) : 0 ≤ annulus x ∧ annulus x ≤ 1 := by
  by_cases hx : x ≤ 1/4
  · rw [annulus_zero_low x hx]; constructor <;> norm_num
  have hm := cutoff_antitone (show x ≤ 2*x by linarith)
  have h₁ := cutoff_bounds x
  have h₂ := cutoff_bounds (2*x)
  unfold annulus
  constructor <;> linarith

theorem annulus_smooth : ContDiff ℝ ∞ annulus := by
  have hc : ContDiff ℝ ∞ cutoff :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_const.mul contDiff_id))
  exact hc.sub (hc.comp (contDiff_const.mul contDiff_id))

def dyadicScale (n : ℤ) : ℝ := (2:ℝ)^n

theorem dyadicScale_pos (n : ℤ) : 0 < dyadicScale n := by
  unfold dyadicScale
  positivity

theorem dyadicScale_add (n : ℤ) : dyadicScale (n+1)=2*dyadicScale n := by
  simp only [dyadicScale,zpow_add₀ (by norm_num : (2:ℝ) ≠ 0),zpow_one]
  ring

def dyadicWeight (n : ℤ) (q : ℝ) : ℝ := annulus (q/dyadicScale n)

theorem dyadicWeight_smooth (n : ℤ) : ContDiff ℝ ∞ (dyadicWeight n) :=
  annulus_smooth.comp (contDiff_id.div_const _)

theorem dyadicWeight_bounds (n : ℤ) (q : ℝ) :
    0 ≤ dyadicWeight n q ∧ dyadicWeight n q ≤ 1 := annulus_bounds _

theorem dyadicWeight_zero_low (n : ℤ) (q : ℝ) (hq : q ≤ dyadicScale n/4) :
    dyadicWeight n q=0 := by
  apply annulus_zero_low
  apply (div_le_iff₀ (dyadicScale_pos n)).mpr
  linarith

theorem dyadicWeight_zero_high (n : ℤ) (q : ℝ) (hq : dyadicScale n ≤ q) :
    dyadicWeight n q=0 := by
  apply annulus_zero_high
  exact (le_div_iff₀ (dyadicScale_pos n)).mpr (by simpa using hq)

theorem dyadicWeight_support (n : ℤ) :
    Function.support (dyadicWeight n) ⊆ Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  intro q hq
  constructor
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_low n q h))
  · exact lt_of_not_ge (fun h => hq (dyadicWeight_zero_high n q h))

theorem dyadicWeight_tsupport (n : ℤ) :
    tsupport (dyadicWeight n) ⊆ Set.Icc (dyadicScale n/4) (dyadicScale n) :=
  closure_minimal (fun _ h => Set.Ioo_subset_Icc_self (dyadicWeight_support n h)) isClosed_Icc

theorem dyadicWeight_outside_pair (q : ℝ) (k : ℤ)
    (hlo : dyadicScale k ≤ q) (hhi : q < dyadicScale (k+1))
    (n : ℤ) (hn : n ∉ ({k+1,k+2} : Finset ℤ)) : dyadicWeight n q=0 := by
  have hn₁ : n ≠ k+1 := by simpa using fun h => hn (by simp [h])
  have hn₂ : n ≠ k+2 := by simpa using fun h => hn (by simp [h])
  by_cases hnk : n ≤ k
  · exact dyadicWeight_zero_high n q ((zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hnk).trans hlo)
  · have hkn : k+3 ≤ n := by omega
    have hmono : dyadicScale (k+3) ≤ dyadicScale n :=
      zpow_le_zpow_right₀ (by norm_num : (1:ℝ) ≤ 2) hkn
    have he : dyadicScale (k+3)=4*dyadicScale (k+1) := by
      rw [show k+3=(k+1)+1+1 by omega,dyadicScale_add,dyadicScale_add]
      ring
    apply dyadicWeight_zero_low
    rw [he] at hmono
    linarith

theorem dyadicWeight_finite (q : ℝ) : (Function.support (fun n => dyadicWeight n q)).Finite := by
  by_cases hq : 0 < q
  · obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
    apply (Set.toFinite (({k+1,k+2} : Finset ℤ) : Set ℤ)).subset
    intro n hn
    by_contra hh
    exact hn (dyadicWeight_outside_pair q k hlo hhi n hh)
  · have hz : ∀ n,dyadicWeight n q=0 := fun n =>
      dyadicWeight_zero_low n q ((le_of_not_gt hq).trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))
    simp [hz]

theorem dyadicWeight_summable (q : ℝ) : Summable (fun n => dyadicWeight n q) :=
  summable_of_hasFiniteSupport (dyadicWeight_finite q)

theorem dyadicWeight_partition (q : ℝ) (hq : 0 < q) : ∑' n,dyadicWeight n q=1 := by
  obtain ⟨k,hlo,hhi⟩ := exists_mem_Ico_zpow hq (by norm_num : (1:ℝ) < 2)
  rw [tsum_eq_sum (s := {k+1,k+2}) (dyadicWeight_outside_pair q k hlo hhi)]
  change dyadicScale k ≤ q at hlo
  change q < dyadicScale (k+1) at hhi
  have hk : k+1 ≠ k+2 := by omega
  rw [Finset.sum_pair hk]
  simp only [dyadicWeight,annulus]
  have h₁ : 2*(q/dyadicScale (k+1))=q/dyadicScale k := by
    rw [dyadicScale_add]; field_simp
  have h₂ : 2*(q/dyadicScale (k+2))=q/dyadicScale (k+1) := by
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]; field_simp
  rw [h₁,h₂,cutoff_zero _ ((le_div_iff₀ (dyadicScale_pos k)).mpr (by simpa using hlo))]
  have hs : q/dyadicScale (k+2) ≤ 1/2 := by
    apply (div_le_iff₀ (dyadicScale_pos (k+2))).mpr
    rw [show k+2=(k+1)+1 by omega,dyadicScale_add]
    linarith
  rw [cutoff_one _ hs]
  ring

def Retained (R : ℝ) (n : ℤ) : Prop :=
  ∃ q : ℝ, 0 < q ∧ q ≤ R ∧ q ∈ tsupport (dyadicWeight n)

def retainedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then dyadicWeight n q else 0

def discardedWeight (R q : ℝ) : ℝ := ∑' n : ℤ, if Retained R n then 0 else dyadicWeight n q

theorem retained_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then dyadicWeight n q else 0) :=
  (dyadicWeight_summable q).indicator {n | Retained R n}

theorem discarded_summable (R q : ℝ) :
    Summable (fun n : ℤ => if Retained R n then 0 else dyadicWeight n q) := by
  have h := (dyadicWeight_summable q).sub (retained_summable R q)
  convert h using 1
  ext n
  split_ifs <;> simp

theorem retained_add_discarded (R q : ℝ) (hq : 0 < q) :
    retainedWeight R q+discardedWeight R q=1 := by
  rw [retainedWeight,discardedWeight,← (retained_summable R q).tsum_add (discarded_summable R q)]
  convert dyadicWeight_partition q hq using 1
  apply tsum_congr
  intro n
  split_ifs <;> simp

theorem dyadicWeight_zero_nonpos (n : ℤ) (q : ℝ) (hq : q ≤ 0) : dyadicWeight n q=0 :=
  dyadicWeight_zero_low n q (hq.trans (div_nonneg (dyadicScale_pos n).le (by norm_num)))

theorem retainedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : retainedWeight R q=0 := by
  simp [retainedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem discardedWeight_zero_nonpos (R q : ℝ) (hq : q ≤ 0) : discardedWeight R q=0 := by
  simp [discardedWeight,dyadicWeight_zero_nonpos _ q hq]

theorem retainedWeight_nonneg (R q : ℝ) : 0 ≤ retainedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact (dyadicWeight_bounds n q).1
  · exact le_rfl

theorem discardedWeight_nonneg (R q : ℝ) : 0 ≤ discardedWeight R q := by
  apply tsum_nonneg
  intro n
  split_ifs
  · exact le_rfl
  · exact (dyadicWeight_bounds n q).1

theorem retainedWeight_bounds (R q : ℝ) : 0 ≤ retainedWeight R q ∧ retainedWeight R q ≤ 1 := by
  refine ⟨retainedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := discardedWeight_nonneg R q
    linarith
  · rw [retainedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem discardedWeight_bounds (R q : ℝ) : 0 ≤ discardedWeight R q ∧ discardedWeight R q ≤ 1 := by
  refine ⟨discardedWeight_nonneg R q,?_⟩
  by_cases hq : 0 < q
  · have hp := retained_add_discarded R q hq
    have hd := retainedWeight_nonneg R q
    linarith
  · rw [discardedWeight_zero_nonpos R q (le_of_not_gt hq)]; norm_num

theorem retained_scale_le (R : ℝ) (n : ℤ) (hn : Retained R n) : dyadicScale n ≤ 4*R := by
  obtain ⟨q,hq,hqR,hs⟩ := hn
  have hb := (dyadicWeight_tsupport n hs).1
  linarith

theorem retainedWeight_zero_above (R q : ℝ) (hq : 4*R ≤ q) : retainedWeight R q=0 := by
  unfold retainedWeight
  trans ∑' _n : ℤ, (0:ℝ)
  · apply tsum_congr
    intro n
    split_ifs with hn
    · exact dyadicWeight_zero_high n q ((retained_scale_le R n hn).trans hq)
    · rfl
  · exact tsum_zero

theorem retainedWeight_enclosure (R q : ℝ) (hq : retainedWeight R q ≠ 0) : 0 < q ∧ q ≤ 4*R := by
  constructor
  · exact lt_of_not_ge (fun h => hq (retainedWeight_zero_nonpos R q h))
  · exact le_of_not_gt (fun h => hq (retainedWeight_zero_above R q h.le))

theorem discardedWeight_zero_below (R q : ℝ) (hq : q ≤ R) : discardedWeight R q=0 := by
  by_cases hp : 0 < q
  · unfold discardedWeight
    trans ∑' _n : ℤ, (0:ℝ)
    · apply tsum_congr
      intro n
      split_ifs with hn
      · rfl
      · by_contra hne
        exact hn ⟨q,hp,hq,subset_tsupport _ hne⟩
    · exact tsum_zero
  · exact discardedWeight_zero_nonpos R q (le_of_not_gt hp)

theorem discardedWeight_support (R q : ℝ) (hq : discardedWeight R q ≠ 0) : R < q :=
  lt_of_not_ge (fun h => hq (discardedWeight_zero_below R q h))

theorem retainedWeight_one_below (R q : ℝ) (hq : 0 < q) (hR : q ≤ R) : retainedWeight R q=1 := by
  have h := retained_add_discarded R q hq
  rwa [discardedWeight_zero_below R q hR,add_zero] at h

theorem finite_retained_integral_dyads (R : ℝ) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, 1 ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc (1:ℤ) (k:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have : (2:ℝ)^(0:ℤ) < (2:ℝ)^n := by simpa [dyadicScale] using hq.trans_lt hs
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp this
    omega
  · have h : (2:ℝ)^n < (2:ℝ)^(k:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hk
    have := (zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h
    omega

theorem annulus_pos (x : ℝ) (hlo : 1/4 < x) (hhi : x < 1) : 0 < annulus x := by
  by_cases hx : x ≤ 1/2
  · rw [annulus,cutoff_one x hx]
    have h := Real.smoothTransition.lt_one_of_lt_one (by linarith : 2-2*(2*x) < 1)
    exact sub_pos.mpr h
  · rw [annulus,cutoff_zero (2*x) (by linarith),sub_zero]
    exact Real.smoothTransition.pos_of_pos (by linarith)

theorem dyadicWeight_support_eq (n : ℤ) :
    Function.support (dyadicWeight n)=Set.Ioo (dyadicScale n/4) (dyadicScale n) := by
  apply Set.Subset.antisymm (dyadicWeight_support n)
  intro q hq
  apply ne_of_gt
  apply annulus_pos
  · apply (lt_div_iff₀ (dyadicScale_pos n)).mpr
    linarith [hq.1]
  · exact (div_lt_one (dyadicScale_pos n)).mpr hq.2

theorem dyadicWeight_tsupport_eq (n : ℤ) :
    tsupport (dyadicWeight n)=Set.Icc (dyadicScale n/4) (dyadicScale n) := by
  rw [tsupport,dyadicWeight_support_eq,closure_Ioo]
  linarith [dyadicScale_pos n]

theorem retained_iff_scale (R : ℝ) (n : ℤ) : Retained R n ↔ dyadicScale n ≤ 4*R := by
  refine ⟨retained_scale_le R n,fun hn => ?_⟩
  refine ⟨dyadicScale n/4,div_pos (dyadicScale_pos n) (by norm_num),by linarith,?_⟩
  rw [dyadicWeight_tsupport_eq]
  exact ⟨le_rfl,by linarith [dyadicScale_pos n]⟩

theorem retained_boundary (n : ℤ) : Retained (dyadicScale n/4) n := by
  rw [retained_iff_scale]
  linarith

def normValue (h : O) : ℝ := Ideal.absNorm (Ideal.span {h})

theorem normValue_eq_embedding (h : O) : normValue h=‖eisEmbedding h‖^2 :=
  (ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span h).symm

theorem normValue_mul (v h : O) : normValue (v*h)=normValue v*normValue h := by
  simp only [normValue,← Ideal.span_singleton_mul_span_singleton,map_mul,Nat.cast_mul]

theorem normValue_pos (h : O) (hh : h ≠ 0) : 0 < normValue h := by
  unfold normValue
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem normValue_ge_one (h : O) (hh : h ≠ 0) : 1 ≤ normValue h := by
  unfold normValue
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr hh))

theorem retained_pullback (R : ℝ) (v h : O) :
    retainedWeight R (normValue (v*h))=retainedWeight R (normValue v*normValue h) := by
  rw [normValue_mul]

theorem retained_norm_enclosure (R : ℝ) (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : normValue h ≤ 4*R/normValue v := by
  have hb := (retainedWeight_enclosure R _ hne).2
  rw [normValue_mul] at hb
  apply (le_div_iff₀ (normValue_pos v hv)).mpr
  nlinarith

def frequencyRadius (Tsec Z ξ : ℝ) : ℝ := Tsec*Z^(ξ/2)

def frequencyLoss (Z Csec ξ : ℝ) : ℝ := ξ/2+Real.logb Z (4*Csec)

theorem frequencyLoss_nonneg (Z Csec ξ : ℝ) (hZ : 1 < Z) (hC : 1 ≤ Csec) (hξ : 0 ≤ ξ) :
    0 ≤ frequencyLoss Z Csec ξ := by
  have hlog := Real.logb_nonneg hZ (show 1 ≤ 4*Csec by linarith)
  unfold frequencyLoss
  linarith

theorem source_enclosure_power (Z Csec L ξ Nv : ℝ) (hZ : 1 < Z) (hC : 0 < Csec) (hNv : 0 < Nv) :
    4*(Csec*Z^L)*Z^(ξ/2)/Nv=Z^(L-Real.logb Z Nv+frequencyLoss Z Csec ξ) := by
  have hz : 0 < Z := zero_lt_one.trans hZ
  rw [frequencyLoss,show L-Real.logb Z Nv+(ξ/2+Real.logb Z (4*Csec))=
    (L+ξ/2)+Real.logb Z (4*Csec)-Real.logb Z Nv by ring,
    Real.rpow_sub hz,Real.rpow_add hz,Real.rpow_add hz,
    Real.rpow_logb hz (ne_of_gt hZ),Real.rpow_logb hz (ne_of_gt hZ)]
  · ring
  · exact hNv
  · positivity

theorem actual_retained_row_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ) := by
  have hb := retained_norm_enclosure (frequencyRadius Tsec Z ξ) v h hv hne
  apply hb.trans
  rw [← source_enclosure_power Z Csec L ξ (normValue v) hZ hC (normValue_pos v hv)]
  apply div_le_div_of_nonneg_right _ (normValue_pos v hv).le
  dsimp only [frequencyRadius]
  nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]

theorem actual_nonempty_width (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  have he := (normValue_ge_one h hh).trans (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hne)
  by_contra hn
  have hh := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  linarith

theorem actual_declared_width_drop (Tsec Z Csec L ξ M J g g₂ t₂ σ q' : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) (hh : h ≠ 0)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0)
    (hwidth : (L-Real.logb Z (normValue v))+q'=M+J-g-g₂+t₂)
    (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂) :
    max 0 (L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)+q' ≤
      M-σ+frequencyLoss Z Csec ξ :=
  CenteredMomentDescentLedger.declared_width_drop M J g g₂ t₂ σ _ q' _ hwidth hg hcommon
    (actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne)

theorem retained_first_dyad_enclosure (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (n : ℤ) (hn : Retained (frequencyRadius Tsec Z ξ) n) :
    Real.logb Z (dyadicScale n) ≤ L+frequencyLoss Z Csec ξ := by
  have hb := retained_scale_le _ n hn
  have hp := source_enclosure_power Z Csec L ξ 1 hZ hC (by norm_num)
  simp only [Real.logb_one,sub_zero,div_one] at hp
  have he : dyadicScale n ≤ Z^(L+frequencyLoss Z Csec ξ) := by
    rw [← hp]
    dsimp only [frequencyRadius] at hb
    nlinarith [mul_le_mul_of_nonneg_right hT (Real.rpow_nonneg (zero_lt_one.trans hZ).le (ξ/2))]
  have hl := Real.logb_le_logb_of_le hZ (dyadicScale_pos n) he
  rwa [Real.logb_rpow (zero_lt_one.trans hZ) (ne_of_gt hZ)] at hl

def kernelReference (Tsec H : ℝ) : ℝ := Real.exp (-2*H)/Tsec

theorem kernelReference_pos (Tsec H : ℝ) (hT : 0 < Tsec) : 0 < kernelReference Tsec H :=
  div_pos (Real.exp_pos _) hT

theorem frequencyLoss_lt (Z Csec H ξ : ℝ) (hZ : 1 < Z) (hH : 0 ≤ H) (hξ : 0 < ξ)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) :
    frequencyLoss Z Csec ξ < ξ := by
  have h := div_nonneg (show 0 ≤ 2*H by linarith) (Real.log_pos hZ).le
  unfold frequencyLoss Real.logb
  linarith

theorem discarded_kernel_argument (Tsec Z Csec H ξ q : ℝ)
    (hT : 0 < Tsec) (hZ : 1 < Z) (hC : 1 ≤ Csec)
    (hthreshold : 2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4)
    (hne : discardedWeight (frequencyRadius Tsec Z ξ) q ≠ 0) :
    Z^(ξ/4) ≤ kernelReference Tsec H*q := by
  have hlog := Real.log_nonneg (show 1 ≤ 4*Csec by linarith)
  have hlogdiv := div_nonneg hlog (Real.log_pos hZ).le
  have he : 2*H < ξ/4*Real.log Z :=
    (div_lt_iff₀ (Real.log_pos hZ)).mp (by linarith : 2*H/Real.log Z < ξ/4)
  have hs : Z^(ξ/4) ≤ Real.exp (-2*H)*Z^(ξ/2) := by
    rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ),Real.rpow_def_of_pos (zero_lt_one.trans hZ),← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith
  have hq := (discardedWeight_support _ q hne).le
  have hm := mul_le_mul_of_nonneg_left hq (kernelReference_pos Tsec H hT).le
  have hid : kernelReference Tsec H*frequencyRadius Tsec Z ξ=Real.exp (-2*H)*Z^(ξ/2) := by
    unfold kernelReference frequencyRadius
    field_simp
  rw [hid] at hm
  exact hs.trans hm

theorem retained_pullback_zero_extension (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L)
    (v h : O) (hv : v ≠ 0) :
    retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) =
      if normValue h ≤ Z^(L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ)
      then retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) else 0 := by
  split_ifs with hb
  · rfl
  · by_contra hn
    exact hb (actual_retained_row_enclosure Tsec Z Csec L ξ hZ hC hT v h hv hn)

theorem actual_discarded_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K B : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*
        paperRadialFourier W (K*normValue h)‖ ≤
      B*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := CenteredMomentTail.uniform_sector_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K B hT hZ hCsec hthreshold hK hB c hc
  let D : Set O := {h | discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0}
  have hb := ht W D (kernelReference Tsec H) (Z^(ξ/4)) B
    (kernelReference_pos Tsec H hT) (Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hB
    (fun h hh => by
      rw [← normValue_eq_embedding]
      exact discarded_kernel_argument Tsec Z Csec H ξ (normValue h) hT hZ hCsec hthreshold hh)
    K hK c (fun h => (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ))
    (fun h _ => hc h) (fun h _ => by
      rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg _ _)]
      exact (discardedWeight_bounds _ _).2)
  simp_rw [← normValue_eq_embedding] at hb
  have he := tsum_subtype_eq_of_support_subset (f := fun h : O =>
    (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*c h*paperRadialFourier W (K*normValue h))
    (s := D) (by
      intro h hh
      change discardedWeight (frequencyRadius Tsec Z ξ) (normValue h) ≠ 0
      intro hz
      exact hh (by simp [hz]))
  rwa [he] at hb

theorem actual_discarded_second_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        CenteredMomentSupportedCorrelation.actualCorrelation u v hu hv (-h)*
        paperRadialFourier W (K*normValue h)‖ ≤
      (normValue u*normValue v)*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK u v hu hv
  exact ht W Tsec Z Csec H ξ K (normValue u*normValue v) hT hZ hCsec hthreshold hK
    (by unfold normValue; positivity) _ (fun h => CenteredMomentTail.actualCorrelation_norm_le u v hu hv (-h))

theorem actual_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ K : ℝ),
      0 < Tsec → 1 < Z → 1 ≤ Csec →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      kernelReference Tsec H ≤ K →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2) (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let χr := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) χr
            (Ideal.Quotient.mk _ h)*
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h)/
            (Real.sqrt (normValue a):ℂ))*
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h))/
            (Real.sqrt (normValue b):ℂ)))*paperRadialFourier W (K*normValue h)‖ ≤
      (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ K hT hZ hCsec hthreshold hK ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W Tsec Z Csec H ξ K 1 hT hZ hCsec hthreshold hK zero_le_one _ (by
    intro h
    rw [norm_mul,norm_mul,norm_star]
    calc
      _ ≤ (1*1)*1 := mul_le_mul
        (mul_le_mul (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)
          (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one a ha χa _)
          (norm_nonneg _) zero_le_one)
        (CenteredMomentTail.normalizedResidueGauss_div_root_norm_le_one b hb χb _)
        (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num)

theorem retained_product_ne_zero (R : ℝ) (v h : O)
    (hne : retainedWeight R (normValue (v*h)) ≠ 0) : v ≠ 0 ∧ h ≠ 0 := by
  have hp := (retainedWeight_enclosure R _ hne).1
  constructor <;> intro hz <;> simp [hz,normValue] at hp

theorem actual_nonempty_width_of_weight (Tsec Z Csec L ξ : ℝ)
    (hZ : 1 < Z) (hC : 0 < Csec) (hT : Tsec ≤ Csec*Z^L) (v h : O)
    (hne : retainedWeight (frequencyRadius Tsec Z ξ) (normValue (v*h)) ≠ 0) :
    0 ≤ L-Real.logb Z (normValue v)+frequencyLoss Z Csec ξ := by
  obtain ⟨hv,hh⟩ := retained_product_ne_zero _ v h hne
  exact actual_nonempty_width Tsec Z Csec L ξ hZ hC hT v h hv hh hne

theorem actual_second_pullback (R : ℝ) (Gc V h : O) :
    retainedWeight R (normValue ((Gc*V)*h))=
      retainedWeight R ((normValue Gc*normValue V)*normValue h) := by
  simp only [normValue_mul]

theorem retained_integral_empty (R : ℝ) (hR : 4*R < 1) (h : O) :
    retainedWeight R (normValue h)=0 := by
  by_contra hn
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hn (by simpa [normValue] using retainedWeight_zero_nonpos R 0 le_rfl)
  have hb := (retainedWeight_enclosure R _ hn).2
  linarith [normValue_ge_one h hh]

theorem finite_retained_above (R a : ℝ) (ha : 0 < a) :
    {n : ℤ | Retained R n ∧ ∃ q : ℝ, a ≤ q ∧ dyadicWeight n q ≠ 0}.Finite := by
  obtain ⟨k,hk,_⟩ := exists_mem_Ico_zpow ha (by norm_num : (1:ℝ) < 2)
  obtain ⟨l,hl⟩ := pow_unbounded_of_one_lt (4*R) (by norm_num : (1:ℝ) < 2)
  apply (Set.finite_Icc k (l:ℤ)).subset
  intro n hn
  obtain ⟨hr,q,hq,hne⟩ := hn
  have hu := retained_scale_le R n hr
  have hs := (dyadicWeight_support n hne).2
  constructor
  · have h : (2:ℝ)^k < (2:ℝ)^n := hk.trans_lt (hq.trans_lt hs)
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le
  · have h : (2:ℝ)^n < (2:ℝ)^(l:ℤ) := by
      simpa only [zpow_natCast,dyadicScale] using hu.trans_lt hl
    exact ((zpow_lt_zpow_iff_right₀ (by norm_num : (1:ℝ) < 2)).mp h).le

theorem retainedWeight_finite_formula (R a : ℝ) (ha : 0 < a) :
    ∃ S : Finset ℤ, ∀ q : ℝ, a ≤ q →
      retainedWeight R q=∑ n ∈ S, if Retained R n then dyadicWeight n q else 0 := by
  let hs := finite_retained_above R a ha
  refine ⟨hs.toFinset,fun q hq => ?_⟩
  apply tsum_eq_sum
  intro n hn
  split_ifs with hr
  · by_contra hne
    exact hn (hs.mem_toFinset.mpr ⟨hr,q,hq,hne⟩)
  · rfl

theorem retainedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (retainedWeight R) q := by
  obtain ⟨S,hS⟩ := retainedWeight_finite_formula R (q/2) (by linarith)
  have hc : ContDiff ℝ ∞ (fun x : ℝ => ∑ n ∈ S, if Retained R n then dyadicWeight n x else 0) := by
    apply ContDiff.sum
    intro n hn
    by_cases hr : Retained R n
    · simpa [hr] using dyadicWeight_smooth n
    · simpa [hr] using (contDiff_const : ContDiff ℝ ∞ (fun _x : ℝ => (0:ℝ)))
  apply hc.contDiffAt.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds (show q/2 < q by linarith)] with x hx
  exact hS x hx.le

theorem discardedWeight_smooth_positive (R q : ℝ) (hq : 0 < q) :
    ContDiffAt ℝ ∞ (discardedWeight R) q := by
  have hc : ContDiffAt ℝ ∞ (fun x => (1:ℝ)-retainedWeight R x) q :=
    contDiffAt_const.sub (retainedWeight_smooth_positive R q hq)
  apply hc.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hq] with x hx
  have he := retained_add_discarded R x hx
  linarith

end SevenEighths.CenteredMomentSectorLocalization

end

end OAI
end OAIOriginalModule1652

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DyadicCount
Source SHA256: cd26719a1f24465eb4d47391f2d754a08bf3e1debb8d7392957bfb9289295e5e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1653




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.CenteredMomentDyadicCount
open CenteredMomentSectorLocalization

def indices (a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈Real.logb 2 a⌉ ⌊Real.logb 2 (4*b)⌋

lemma logb_dyadicScale (n : ℤ) : Real.logb 2 (dyadicScale n)=(n:ℝ) := by
  rw [dyadicScale,←Real.rpow_intCast,Real.logb_rpow (by norm_num : (0:ℝ)<2) (by norm_num)]

lemma mem_indices_iff_scale (a b : ℝ) (ha : 0<a) (hb : 0<b) (n : ℤ) :
    n∈indices a b ↔ a≤dyadicScale n ∧ dyadicScale n≤4*b := by
  rw [indices,Finset.mem_Icc,Int.ceil_le,Int.le_floor]
  rw [←logb_dyadicScale n]
  constructor
  · rintro ⟨h1,h2⟩
    exact ⟨(Real.logb_le_logb (by norm_num) ha (dyadicScale_pos n)).mp h1,
      (Real.logb_le_logb (by norm_num) (dyadicScale_pos n) (by positivity)).mp h2⟩
  · rintro ⟨h1,h2⟩
    exact ⟨Real.logb_le_logb_of_le (by norm_num) ha h1,
      Real.logb_le_logb_of_le (by norm_num) (dyadicScale_pos n) h2⟩

lemma mem_indices_iff_whole_support (a b : ℝ) (ha : 0<a) (hab : a≤b) (n : ℤ) :
    n∈indices a b ↔ ∃q∈Icc a b,q∈tsupport (dyadicWeight n) := by
  rw [mem_indices_iff_scale a b ha (ha.trans_le hab) n]
  constructor
  · rintro ⟨hlo,hhi⟩
    refine ⟨max a (dyadicScale n/4),⟨le_max_left _ _,max_le hab (by linarith)⟩,?_⟩
    rw [dyadicWeight_tsupport_eq]
    exact ⟨le_max_right _ _,max_le hlo (by linarith [dyadicScale_pos n])⟩
  · rintro ⟨q,hq,hq'⟩
    have hh := dyadicWeight_tsupport n hq'
    exact ⟨hq.1.trans hh.2,by linarith [hq.2,hh.1]⟩

lemma support_indices (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b)
    (n : ℤ) (hne : dyadicWeight n q≠0) : n∈indices a b :=
  (mem_indices_iff_whole_support a b ha (hq.1.trans hq.2) n).mpr
    ⟨q,hq,subset_tsupport _ hne⟩

lemma finite_active_indices (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    {n : ℤ | ∃q∈Icc a b,q∈tsupport (dyadicWeight n)}.Finite := by
  apply (indices a b).finite_toSet.subset
  intro n hn
  exact (mem_indices_iff_whole_support a b ha hab n).mpr hn

lemma logb_four_mul (b : ℝ) (hb : 0<b) :
    Real.logb 2 (4*b)=2+Real.logb 2 b := by
  rw [Real.logb_mul (by norm_num) hb.ne']
  congr 1
  rw [show (4:ℝ)=(2:ℝ)^2 by norm_num,Real.logb_pow]
  norm_num [Real.logb_self_eq_one]

theorem indices_card_bound (a b : ℝ) (ha : 0<a) (hab : a≤b) :
    ((indices a b).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have hb := ha.trans_le hab
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha hab
  have hu := Int.ceil_lt_add_one (Real.logb 2 a)
  have hl := Int.sub_one_lt_floor (Real.logb 2 (4*b))
  have he := logb_four_mul b hb
  have hle : ⌈Real.logb 2 a⌉≤⌊Real.logb 2 (4*b)⌋+1 := by
    have hh : (⌈Real.logb 2 a⌉:ℝ)≤(⌊Real.logb 2 (4*b)⌋:ℝ)+1 := by linarith
    exact_mod_cast hh
  have hcard := Int.card_Icc_of_le _ _ hle
  have hcard' : ((indices a b).card:ℝ)=(⌊Real.logb 2 (4*b)⌋:ℝ)+1-(⌈Real.logb 2 a⌉:ℝ) := by
    exact_mod_cast hcard
  rw [hcard',Real.logb_div hb.ne' ha.ne']
  linarith [Int.floor_le (Real.logb 2 (4*b)),Int.le_ceil (Real.logb 2 a)]

theorem scaled_indices_card_bound (a b T : ℝ) (ha : 0<a) (hab : a≤b) (hT : 0<T) :
    ((indices (a/T) (b/T)).card:ℝ)≤3+Real.logb 2 (b/a) := by
  have h := indices_card_bound (a/T) (b/T) (div_pos ha hT)
    (div_le_div_of_nonneg_right hab hT.le)
  have he : (b/T)/(a/T)=b/a := by field_simp
  rwa [he] at h

lemma dyadic_partition_on_interval (a b q : ℝ) (ha : 0<a) (hq : q∈Icc a b) :
    (∑n∈indices a b,dyadicWeight n q)=1 := by
  rw [←dyadicWeight_partition q (ha.trans_le hq.1)]
  symm
  apply tsum_eq_sum
  intro n hn
  by_contra hne
  exact hn (support_indices a b q ha hq n hne)

theorem four_indices_card_bound (a b : Fin 4→ℝ)
    (ha : ∀j,0<a j) (hab : ∀j,a j≤b j) :
    (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤
      ∏j:Fin 4,(3+Real.logb 2 (b j/a j)) := by
  rw [Fintype.card_pi]
  push_cast
  apply Finset.prod_le_prod₀
  · intro j hj
    positivity
  · intro j hj
    simpa only [Fintype.card_coe] using indices_card_bound (a j) (b j) (ha j) (hab j)

lemma retained_integral_mem (R q : ℝ) (hq : 1≤q) (n : ℤ)
    (hr : Retained R n) (hne : dyadicWeight n q≠0) :
    n∈indices 1 (max 1 R) := by
  rw [mem_indices_iff_scale 1 (max 1 R) (by norm_num) (by positivity) n]
  exact ⟨hq.trans (dyadicWeight_support n hne).2.le,
    (retained_scale_le R n hr).trans (by linarith [le_max_right (1:ℝ) R])⟩

theorem indices_card_log_bound (C R Z a b : ℝ) (hC : 1≤C) (hR : 0≤R)
    (hZ : 1≤Z) (ha : 0<a) (hab : a≤b) (hratio : b/a≤C*Z^R) :
    ((indices a b).card:ℝ)≤
      (3+Real.logb 2 C+R/Real.log 2)*(1+Real.log Z) := by
  have hb := ha.trans_le hab
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hCp : 0<C := zero_lt_one.trans_le hC
  have hlog := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) (div_pos hb ha) hratio
  rw [Real.logb_mul hCp.ne' (Real.rpow_pos_of_pos hZp R).ne',
    Real.logb_rpow_eq_mul_logb_of_pos hZp] at hlog
  apply (indices_card_bound a b ha hab).trans
  have hc0 := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
  have hz0 := Real.log_nonneg hZ
  have hr0 : 0≤R/Real.log 2 := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  have hp := mul_nonneg (show 0≤3+Real.logb 2 C by linarith) hz0
  have he : R*Real.logb 2 Z=(R/Real.log 2)*Real.log Z := by unfold Real.logb;ring
  rw [he] at hlog
  nlinarith

theorem four_indices_subpower (C R ε : ℝ) (hC : 1≤C) (hR : 0≤R) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀ᶠZ : ℝ in Filter.atTop,
      ∀a b : Fin 4→ℝ,(∀j,0<a j) → (∀j,a j≤b j) →
      (∀j,b j/a j≤C*Z^R) →
      (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤D*Z^ε := by
  let K : ℝ := 3+Real.logb 2 C+R/Real.log 2
  have hK : 0<K := by
    have hc := Real.logb_nonneg (by norm_num : (1:ℝ)<2) hC
    have hr := div_nonneg hR (Real.log_pos (by norm_num : (1:ℝ)<2)).le
    dsimp [K]
    linarith
  have hlog := (isLittleO_log_rpow_rpow_atTop (4:ℝ) hε).bound (by norm_num : (0:ℝ)<1)
  refine ⟨16*K^4,by positivity,?_⟩
  filter_upwards [hlog,Filter.eventually_ge_atTop (Real.exp 1),Filter.eventually_ge_atTop (1:ℝ)] with Z hlog hZexp hZ
  intro a b ha hab hratio
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hz : 1≤Real.log Z := by
    have hh := Real.log_le_log (Real.exp_pos (1:ℝ)) hZexp
    simpa only [Real.log_exp] using hh
  have hp : (Real.log Z)^4≤Z^ε := by
    apply (le_abs_self _).trans
    simpa only [Real.rpow_ofNat,Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hZp.le _),one_mul] using hlog
  have hcard : (Fintype.card (∀j:Fin 4,↥(indices (a j) (b j))):ℝ)≤(K*(1+Real.log Z))^4 := by
    rw [Fintype.card_pi]
    push_cast
    calc
      _ ≤ ∏j:Fin 4,K*(1+Real.log Z) := by
        apply Finset.prod_le_prod₀ (by intros;positivity)
        intro j hj
        simpa only [Fintype.card_coe] using indices_card_log_bound C R Z (a j) (b j) hC hR hZ (ha j) (hab j) (hratio j)
      _ = _ := by simp
  calc
    _ ≤ (K*(1+Real.log Z))^4 := hcard
    _ ≤ (K*(2*Real.log Z))^4 := by gcongr;linarith
    _ = (16*K^4)*(Real.log Z)^4 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

end SevenEighths.CenteredMomentDyadicCount

end

end OAI
end OAIOriginalModule1653

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssembly
Source SHA256: b3e3bf3a42e77127aa1bd8deaf4679dd40ab8ad3909fc16bfe01cbe1f2ebd0a0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1654



namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis" => ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

abbrev Windows (a b : Fin 4→ℝ) := ∀ i:Fin 4,↥(indices (a i) (b i))

def exponent (Z:ℝ) (k:ℤ) : ℝ := Real.logb Z (dyadicScale k)

def cutoff : Fin 4→ℝ→ℂ := fun _ y=>(annulus y:ℂ)

def weight (k:Fin 4→ℤ) (q:Fin 4→ℝ) : ℂ :=
  ∏i:Fin 4,(dyadicWeight (k i) (q i):ℂ)

theorem exponent_scale (Z:ℝ) (hZ:1<Z) (k:ℤ) :
    Z^(exponent Z k)=dyadicScale k :=
  Real.rpow_logb (by positivity) (ne_of_gt hZ) (dyadicScale_pos k)

theorem weight_partition (a b q:Fin 4→ℝ) (ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    (∑k:Windows a b,weight (fun i=>(k i).val) q)=1 := by
  unfold weight
  rw [←Fintype.prod_sum (fun (i:Fin 4) (k:↥(indices (a i) (b i)))=>(dyadicWeight k.val (q i):ℂ))]
  have he (i:Fin 4) : (∑k:↥(indices (a i) (b i)),(dyadicWeight k.val (q i):ℂ))=1 := by
    rw [Finset.sum_coe_sort (indices (a i) (b i)) (fun k=>(dyadicWeight k (q i):ℂ))]
    exact_mod_cast dyadic_partition_on_interval (a i) (b i) (q i) (ha i) (hq i)
  simp only [he,Finset.prod_const_one]

theorem weight_eq_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ) (q:Fin 6→ℝ) :
    weight k (fun i=>q (outerIndex i)) =
      outerCutoff cutoff (relativeNorm q Z D (exponent Z (k 0))
        (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))) := by
  simp [weight,Fin.prod_univ_succ,dyadicWeight,outerIndex,outerCutoff,cutoff,
    relativeNorm,secondRelativeNorm,exponent_scale Z hZ,mul_assoc]

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def sourceNorms (x:Source (ι:=ι) 0) : Fin 4→ℝ :=
  fun i=>coordinates p (sourcePoint x ∅ ∅) (outerIndex i)

omit [DecidableEq ι] in
theorem source_weight_cutoff (Z D:ℝ) (hZ:1<Z) (k:Fin 4→ℤ)
    (x:Source (ι:=ι) 0) :
    weight k (sourceNorms p x)=outerCutoff cutoff
      (sourceRelative p x Z D (exponent Z (k 0)) (exponent Z (k 2))
        (exponent Z (k 1)) (exponent Z (k 3))) :=
  weight_eq_cutoff Z D hZ k _

omit [DecidableEq ι] in
theorem sourceNorms_one_le (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal] (x:Source (ι:=ι) 0)
    (hf:x.frequency≠0) : ∀i,1≤sourceNorms p x i := by
  have hi (I:Ideal Eis) (hI:I≠0) : (1:ℝ)≤(Ideal.absNorm I:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  intro i
  fin_cases i
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · exact hi _ (sourceIdeal_ne_zero p hp _)
  · change 1≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hi _ (by change Ideal.span {x.frequency}≠⊥; exact Ideal.span_singleton_eq_bot.not.mpr hf)

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*weight (fun i=>(k i).val) (sourceNorms p x))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨s,hsS,hx⟩:=Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩:=Finset.mem_image.mp hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply,erase_sourcePoint]
  rw [←Finset.sum_mul,←Finset.mul_sum,weight_partition a b _ ha (hs s hsS),mul_one]

theorem physicalBlock_window_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,physicalBlock p hp hcop hg
      (pointSource pool (windowSource p S cutoff Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))
      ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
        (exponent Z (k 0).val) (exponent Z (k 2).val)
        (exponent Z (k 1).val) (exponent Z (k 3).val)))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  rw [physicalBlock_partition p hp hcop hg pool S a b ha hs]
  apply Finset.sum_congr rfl
  intro k hk
  simp_rw [source_weight_cutoff p Z D hZ]
  exact physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m w Ψ j marks W₁ W₂ Φ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end OAIOriginalModule1654

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyBounds
Source SHA256: d8af4e51be07dd86eabdb3a99e3434fbe4d362549c3bb861153792cc0d863cea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1655


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

theorem windows_card_log (a b:Fin 4→ℝ)(ha:∀i,0<a i)(hab:∀i,a i≤b i) :
    (Fintype.card (Windows a b):ℝ)≤∏i:Fin 4,(3+Real.logb 2 (b i/a i)) :=
  four_indices_card_bound a b ha hab

theorem windows_card_subpower (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀a b:Fin 4→ℝ,(∀i,0<a i)→(∀i,a i≤b i)→(∀i,b i/a i≤C*Z^R)→
        (Fintype.card (Windows a b):ℝ)≤A*Z^ε :=
  four_indices_subpower C R ε hC hR hε

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def windowBlock (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(k:Fin 4→ℤ) : ℂ :=
  physicalBlock p hp hcop hg
    (pointSource pool (windowSource p S cutoff Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))
    ((fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D
      (exponent Z (k 0)) (exponent Z (k 2)) (exponent Z (k 1)) (exponent Z (k 3))))∘erasePoint)
    Ψ j marks W₁ W₂ Φ Z D m

theorem physicalBlock_norm_le_windows
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (hs:∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (E:ℝ)(hblock:∀k:Windows a b,
      ‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
        (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_window_partition p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑k:Windows a b,E := Finset.sum_le_sum (fun k hk=>hblock k)
    _ = _ := by simp

omit p hp hcop hg [DecidableEq ι] [∀i,(Ideal.span {p i}).IsMaximal] in

theorem physicalBlock_uniform_subpower
    (C R ε:ℝ)(hC:1≤C)(hR:0≤R)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in Filter.atTop,
      ∀{κ:Type*}[DecidableEq κ](p:κ→Eis)(hp:∀i,p i≠0)
        [∀i,(Ideal.span {p i}).IsMaximal]
        (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
        (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
        (pool:Finset κ)(S:Finset (Source (ι:=κ) 0))
        (a b:Fin 4→ℝ),(∀i,0<a i)→(∀i,a i≤b i)→
        (∀i,b i/a i≤C*Z^R)→
        (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i))→
      ∀(w:Source (ι:=κ) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset κ→ℂ)
        (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(D m E:ℝ),0≤E→
        (∀k:Windows a b,‖windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m
          (fun i=>(k i).val)‖≤E)→
        ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
          Ψ j marks W₁ W₂ Φ Z D m‖≤A*Z^ε*E := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower C R ε hC hR hε
  refine ⟨A,hA,?_⟩
  filter_upwards [hcount,Filter.eventually_gt_atTop (1:ℝ)] with Z hc hZ
  intro κ _ p hp _ hcop hg pool S a b ha hab hr hs w Ψ j marks W₁ W₂ Φ D m E hE hb
  exact (physicalBlock_norm_le_windows p hp hcop hg pool S a b ha hs w Ψ j marks W₁ W₂ Φ Z D m hZ E hb).trans
    (mul_le_mul_of_nonneg_right (hc a b ha hab hr) hE)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end OAIOriginalModule1655

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyLive
Source SHA256: 8d00cce7eb6ae80b74eaedde73fa199881fc442a828114745a064082b887ccc4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1656


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

def cappedSource (S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ) : Finset (Source (ι:=ι) 0) :=
  S.filter (fun x=>∀i,sourceNorms p x i∈Set.Icc (a i) (b i))

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem physicalBlock_cap_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg (pointSource pool (cappedSource p S a b))
      (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,cappedSource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hb:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)
  · rw [ite_eq_left hb]
  · rw [ite_eq_right hb]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro M hM
    apply Finset.sum_eq_zero
    intro ρ hρ
    simp only [Function.comp_apply,erase_sourcePoint]
    by_contra hn
    exact hb (hcap x hx N hN M hM ρ hn)

theorem physicalBlock_live_partition
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows a b,windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_window_partition p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ

theorem physicalBlock_live_norm
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))(a b:Fin 4→ℝ)(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)
    (hcap:∀x∈S,∀N∈(pool\x.overlap).powerset,∀M∈(pool\x.overlap).powerset,
      ∀ρ:SecondRayIndex,w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m
        (sourcePoint x N M) ρ≠0→∀i,sourceNorms p x i∈Set.Icc (a i) (b i))
    (E:ℝ)(he:∀k:Windows a b,‖windowBlock p hp hcop hg pool (cappedSource p S a b)
      w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)‖≤E) :
    ‖physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m‖≤(Fintype.card (Windows a b):ℝ)*E := by
  rw [physicalBlock_cap_filter p hp hcop hg pool S a b w Ψ j marks W₁ W₂ Φ Z D m hcap]
  exact physicalBlock_norm_le_windows p hp hcop hg pool (cappedSource p S a b) a b ha
    (fun x hx=>(Finset.mem_filter.mp hx).2) w Ψ j marks W₁ W₂ Φ Z D m hZ E he

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end OAIOriginalModule1656

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblySourceCaps
Source SHA256: f8ed1099c8288c5eafe125a30381ab4193d7438b2a6af6eccf75e4581c638b45
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1657



namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open InverseInitialKernelBridge InverseSecondChildWindows

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)

omit [DecidableEq ι] in
theorem sourceNorms_fresh (x:Source (ι:=ι) 0)(N M:Finset ι)(i:Fin 4) :
    sourceNorms p x i=coordinates p (sourcePoint x N M) (outerIndex i) := by
  fin_cases i <;> simp only [sourceNorms,coordinates,sourcePoint,physicalCoordinates,
    outerIndex,Fin.castLE,Matrix.cons_val_zero',Matrix.cons_val_succ']

def physicalCaps (b Z D T:ℝ) : Fin 4→ℝ := ![b*Z^D,b*Z^D,b*Z^D,T]

variable (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem actual_live_caps
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:0<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T)
    (x:Source (ι:=ι) 0)(hx:x∈S)(N:Finset ι)(hN:N∈(pool\x.overlap).powerset)
    (M:Finset ι)(hM:M∈(pool\x.overlap).powerset)(ρ:SecondRayIndex)
    (hn:w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m (sourcePoint x N M) ρ≠0) :
    ∀i,sourceNorms p x i∈Set.Icc 1 (physicalCaps b Z D T i) := by
  have hpnt:sourcePoint x N M∈pointSource pool S := by
    apply Finset.mem_biUnion.mpr
    refine ⟨x,hx,?_⟩
    exact Finset.mem_image.mpr ⟨(N,M),Finset.mem_product.mpr ⟨hN,hM⟩,rfl⟩
  have hv:=pointSource_valid pool S hdiv hf _ hpnt
  have hc:=InverseInitialRetainedSupport.live_ideal_caps p hp hcop hg hpr Ψ j marks W₁ W₂ Φ
    Z D m b hZ hW₁ hW₂ (sourcePoint x N M) hv ρ (mul_ne_zero_iff.mp hn).2
  intro i
  refine ⟨sourceNorms_one_le p hp x (hf x hx) i,?_⟩
  fin_cases i
  · change sourceNorms p x 0≤b*Z^D
    rw [sourceNorms_fresh p x N M 0]
    exact hc.1
  · change sourceNorms p x 1≤b*Z^D
    rw [sourceNorms_fresh p x N M 1]
    exact hc.2.1
  · change sourceNorms p x 2≤b*Z^D
    rw [sourceNorms_fresh p x N M 2]
    exact hc.2.2.1
  · exact hT x hx

theorem actual_physical_partition
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    ∑k:Windows (fun _=>1) (physicalCaps b Z D T),
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val) := by
  exact physicalBlock_live_partition p hp hcop hg pool S (fun _=>1) (physicalCaps b Z D T)
    (by intro i; norm_num) w Ψ j marks W₁ W₂ Φ Z D m hZ
    (actual_live_caps p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ Z D m b T
      (by linarith) hW₁ hW₂ hT)

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end OAIOriginalModule1657

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyWindows
Source SHA256: 5606fcd09caeed967d234216391b8cac1a3a7601184bc889715b4d10e457ac81
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1658


namespace OAI

noncomputable section

open scoped Classical BigOperators ContDiff
namespace SevenEighths.InverseInitialDyadicAssembly
open CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

theorem cutoff_smooth (i:Fin 4) : ContDiff ℝ ∞ (cutoff i) :=
  Complex.ofRealCLM.contDiff.comp annulus_smooth

theorem cutoff_norm_le (i:Fin 4)(x:ℝ) : ‖cutoff i x‖≤1 := by
  simpa only [cutoff,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (annulus_bounds x).1] using (annulus_bounds x).2

theorem cutoff_support (i:Fin 4) :
    Function.support (cutoff i)⊆Set.Ioo (1/4:ℝ) 1 := by
  intro x hx
  have hn:annulus x≠0 := by simpa only [Function.mem_support,cutoff,ne_eq,Complex.ofReal_eq_zero] using hx
  exact ⟨lt_of_not_ge (fun h=>hn (annulus_zero_low x h)),
    lt_of_not_ge (fun h=>hn (annulus_zero_high x h))⟩

theorem cutoff_tsupport (i:Fin 4) :
    tsupport (cutoff i)⊆Set.Icc (1/4:ℝ) 1 :=
  closure_minimal (fun _ hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx)) isClosed_Icc

theorem cutoff_eventual_width (η:ℝ)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀i:Fin 4,
      tsupport (cutoff i)⊆Set.Icc (Z^(-η)) (Z^η) := by
  have ht:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro i x hx
  have hs:=cutoff_tsupport i hx
  have hlo:Z^(-η)≤(1/4:ℝ) := by
    rw [Real.rpow_neg (by positivity)]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) ht
  exact ⟨hlo.trans hs.1,hs.2.trans (by linarith)⟩

theorem window_exponent_nonneg (Z b:ℝ)(hZ:1<Z)(hb:0<b)
    (k:ℤ)(hk:k∈indices 1 b) : 0≤exponent Z k := by
  have hs:1≤dyadicScale k := ((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).1
  exact Real.logb_nonneg hZ hs

theorem window_exponent_eventual_upper (C η:ℝ)(_hC:0<C)(hη:0<η) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀(b R:ℝ),0<b→b≤C*Z^R→
      ∀k:ℤ,k∈indices 1 b→exponent Z k∈Set.Icc 0 (R+η) := by
  have ht:∀ᶠZ:ℝ in atTop,4*C≤Z^η :=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (4*C))
  filter_upwards [eventually_gt_atTop (1:ℝ),ht] with Z hZ ht
  refine ⟨hZ,?_⟩
  intro b R hb hbR k hk
  refine ⟨window_exponent_nonneg Z b hZ hb k hk,?_⟩
  have hs:=((mem_indices_iff_scale 1 b (by norm_num) hb k).mp hk).2
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [exponent_scale Z hZ,Real.rpow_add (by positivity)]
  calc
    dyadicScale k≤4*b:=hs
    _≤4*(C*Z^R):=mul_le_mul_of_nonneg_left hbR (by norm_num)
    _=(4*C)*Z^R:=by ring
    _≤Z^η*Z^R:=mul_le_mul_of_nonneg_right ht (Real.rpow_nonneg (by positivity) _)
    _=Z^R*Z^η:=mul_comm _ _

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end OAIOriginalModule1658

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyRetained
Source SHA256: fe0e59831f7ffdac7e8efdd688a5183b90d0c2d849e6d614c80ed915fcbc9428
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1659



namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicAssembly
open InverseInitialProfile CenteredMomentSectorLocalization CenteredMomentDyadicCount
open Filter

def retainedWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val)≤L)

def tailWindows (a b:Fin 4→ℝ)(Z D m L:ℝ) : Finset (Windows a b) :=
  Finset.univ.filter (fun k=>L<radialCenter m (exponent Z (k 3).val)
    (exponent Z (k 1).val) D (exponent Z (k 0).val))

theorem window_sum_split (a b:Fin 4→ℝ)(Z D m L:ℝ)(f:Windows a b→ℂ) :
    (∑k,f k)=(∑k∈retainedWindows a b Z D m L,f k)+
      ∑k∈tailWindows a b Z D m L,f k := by
  simpa only [retainedWindows,tailWindows,not_le] using
    (Finset.sum_filter_add_sum_filter_not (Finset.univ:Finset (Windows a b))
      (fun k=>radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
        (exponent Z (k 0).val)≤L) f).symm

theorem retained_exponents_eventually (b R Λ:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D m L T:ℝ,D≤R→0≤m→L≤Λ→0<T→
      ∀k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
        ∀i,exponent Z (k i).val∈Set.Icc 0 (3*R+Λ+1) := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro D m L T hD hm hL hT k hk
  have hs:radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D
      (exponent Z (k 0).val)≤L := (Finset.mem_filter.mp hk).2
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hZ.1]) D)
  have h0:=hZ.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hZ.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  have h2:=hZ.2 (b*Z^D) D hp le_rfl (k 2).val (k 2).property
  have h3:=window_exponent_nonneg Z T hZ.1 hT (k 3).val (k 3).property
  unfold radialCenter at hs
  intro i
  fin_cases i
  · change exponent Z (k 0).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h0.1,by linarith [h0.2]⟩
  · change exponent Z (k 1).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h1.1,by linarith [h1.2]⟩
  · change exponent Z (k 2).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h2.1,by linarith [h2.2]⟩
  · change exponent Z (k 3).val∈Set.Icc 0 (3*R+Λ+1)
    exact ⟨h3,by linarith [h0.1,h1.2]⟩

theorem window_quotient_eventually (b R:ℝ)(hb:0<b) :
    ∀ᶠZ:ℝ in atTop,1<Z ∧ ∀D T η:ℝ,D≤R→0<T→η≤1→
      ∀k:Windows (fun _=>1) (physicalCaps b Z D T),
        exponent Z (k 0).val-exponent Z (k 1).val+2*η≤R+3 := by
  filter_upwards [window_exponent_eventual_upper b 1 hb (by norm_num)] with Z hz
  refine ⟨hz.1,?_⟩
  intro D T η hD hT hη k
  have hp:0<b*Z^D := mul_pos hb (Real.rpow_pos_of_pos (by linarith [hz.1]) D)
  have h0:=hz.2 (b*Z^D) D hp le_rfl (k 0).val (k 0).property
  have h1:=hz.2 (b*Z^D) D hp le_rfl (k 1).val (k 1).property
  linarith [h0.2,h1.1]

theorem retained_card_of_exponents (a b:Fin 4→ℝ)(Z D m L A:ℝ)(hZ:1<Z)
    (he:∀k∈retainedWindows a b Z D m L,∀i,exponent Z (k i).val∈Set.Icc 0 A) :
    (retainedWindows a b Z D m L).card≤
      Fintype.card (Windows (fun _=>1) (fun _=>Z^A)) := by
  have hZp:0<Z := by linarith
  let f:↥(retainedWindows a b Z D m L)→Windows (fun _=>1) (fun _=>Z^A) :=
    fun k i=>⟨(k.val i).val,(mem_indices_iff_scale 1 (Z^A) (by norm_num)
      (Real.rpow_pos_of_pos hZp A) (k.val i).val).mpr ⟨by
        rw [←exponent_scale Z hZ]
        simpa only [Real.rpow_zero] using
          (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).1,by
        have hh:(dyadicScale (k.val i).val)≤Z^A := by
          rw [←exponent_scale Z hZ]
          exact (Real.rpow_le_rpow_left_iff hZ).mpr (he k.val k.property i).2
        exact hh.trans (by nlinarith [Real.rpow_pos_of_pos hZp A])⟩⟩
  have hf:Function.Injective f := by
    intro k l h
    apply Subtype.ext
    funext i
    apply Subtype.ext
    simpa only [f] using congrArg Subtype.val (congrFun h i)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hf

theorem retained_card_subpower (b R Λ ε:ℝ)(hb:0<b)(hR:0≤R)(hΛ:0≤Λ)(hε:0<ε) :
    ∃A:ℝ,0<A ∧ ∀ᶠZ:ℝ in atTop,
      ∀D m L T:ℝ,D≤R→0≤m→L≤Λ→0<T→
        ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤A*Z^ε := by
  obtain ⟨A,hA,hcount⟩:=windows_card_subpower 1 (3*R+Λ+1) ε (by norm_num) (by positivity) hε
  refine ⟨A,hA,?_⟩
  filter_upwards [retained_exponents_eventually b R Λ hb hR hΛ,hcount] with Z hz hc
  intro D m L T hD hm hL hT
  have he:=hz.2 D m L T hD hm hL hT
  have hi:=retained_card_of_exponents (fun _=>1) (physicalCaps b Z D T) Z D m L
    (3*R+Λ+1) hz.1 he
  have hp:(1:ℝ)≤Z^(3*R+Λ+1) := Real.one_le_rpow (le_of_lt hz.1) (by positivity)
  exact (by exact_mod_cast hi :
    ((retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L).card:ℝ)≤
      (Fintype.card (Windows (fun _=>1) (fun _=>Z^(3*R+Λ+1))):ℝ)).trans
    (hc (fun _=>1) (fun _=>Z^(3*R+Λ+1)) (by intro i; norm_num)
      (fun _=>hp) (by intro i; simp))

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end OAIOriginalModule1659

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicAssemblyTail
Source SHA256: 1f502c24dde6d05edfba5942739fdf10c4c1c484e1512a0f596e05c7f8ea6bf1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1660


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
namespace SevenEighths.InverseInitialDyadicAssembly
local notation "Eis"=>ActualEisensteinCubic.O
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialEnergyCallerWindows InverseInitialProfile InverseInitialClippedColumns
open CenteredMomentSectorLocalization CenteredMomentDyadicCount

def windowMass {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) : ℝ :=
  ∑k∈F,∏i:Fin 4,dyadicWeight (k i).val (q i)

theorem windowMass_cast {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    (windowMass F q:ℂ)=∑k∈F,weight (fun i=>(k i).val) q := by
  simp only [windowMass,weight,Complex.ofReal_sum,Complex.ofReal_prod]

theorem windowMass_nonneg {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ) :
    0≤windowMass F q := by
  apply Finset.sum_nonneg
  intro k hk
  exact Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1)

theorem windowMass_univ (a b q:Fin 4→ℝ)(ha:∀i,0<a i)
    (hq:∀i,q i∈Set.Icc (a i) (b i)) :
    windowMass (Finset.univ:Finset (Windows a b)) q=1 := by
  apply Complex.ofReal_injective
  rw [windowMass_cast,Complex.ofReal_one]
  exact weight_partition a b q ha hq

theorem windowMass_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : windowMass F q≤1 := by
  rw [←windowMass_univ a b q ha hq]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ F)
    (fun k hk hnot=>Finset.prod_nonneg (fun i hi=>(dyadicWeight_bounds (k i).val (q i)).1))

theorem windowMass_norm_le_one {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (ha:∀i,0<a i)(hq:∀i,q i∈Set.Icc (a i) (b i)) : ‖(windowMass F q:ℂ)‖≤1 := by
  simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (windowMass_nonneg F q)]
    using windowMass_le_one F q ha hq

theorem windowMass_ne_zero_exists {a b:Fin 4→ℝ}(F:Finset (Windows a b))(q:Fin 4→ℝ)
    (h:windowMass F q≠0) : ∃k∈F,weight (fun i=>(k i).val) q≠0 := by
  have hc:(windowMass F q:ℂ)≠0:=by exact_mod_cast h
  rw [windowMass_cast] at hc
  exact Finset.exists_ne_zero_of_sum_ne_zero hc

variable {ι:Type*}[DecidableEq ι](p:ι→Eis)
  (hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem windowBlock_eq_full
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z)(k:Fin 4→ℤ) :
    windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m k =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*weight k (sourceNorms p x))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [source_weight_cutoff p Z D hZ]
  exact (physicalBlock_windowSource p hp hcop hg pool S cutoff Z D _ _ _ _ m
    w Ψ j marks W₁ W₂ Φ).symm

theorem sum_windowBlock_eq_mass
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)(hZ:1<Z) :
    (∑k∈F,windowBlock p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) =
      physicalBlock p hp hcop hg (pointSource pool S)
        ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
        Ψ j marks W₁ W₂ Φ Z D m := by
  simp_rw [windowBlock_eq_full p hp hcop hg pool S w Ψ j marks W₁ W₂ Φ Z D m hZ]
  unfold physicalBlock
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ρ hρ
  simp only [Function.comp_apply]
  rw [←Finset.sum_mul,←Finset.mul_sum,←windowMass_cast]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem mass_weight_bound
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))(ha:∀i,0<a i)
    (w:Source (ι:=ι) 0→ℂ)(x:Source (ι:=ι) 0)
    (hx:∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) :
    ‖w x*(windowMass F (sourceNorms p x):ℂ)‖≤‖w x‖ := by
  rw [norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (windowMass_norm_le_one F _ ha hx)

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L<radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))≠0 := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  rwa [source_weight_cutoff p Z D hZ] at hne

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem tail_mass_live_bounds (a b:Fin 4→ℝ)(Z D m L:ℝ)(hZ:1<Z)
    (x:Source (ι:=ι) 0)
    (hn:windowMass (tailWindows a b Z D m L) (sourceNorms p x)≠0) :
    ∃k∈tailWindows a b Z D m L,
      L<radialCenter m (exponent Z (k 3).val) (exponent Z (k 1).val) D (exponent Z (k 0).val) ∧
      ∀i,sourceNorms p x i∈Set.Ioo (Z^(exponent Z (k i).val)/4) (Z^(exponent Z (k i).val)) := by
  obtain ⟨k,hk,hne⟩:=windowMass_ne_zero_exists _ _ hn
  refine ⟨k,hk,(Finset.mem_filter.mp hk).2,?_⟩
  intro i
  have hi:(dyadicWeight (k i).val (sourceNorms p x i):ℂ)≠0 :=
    Finset.prod_ne_zero_iff.mp hne i (Finset.mem_univ i)
  have hr:dyadicWeight (k i).val (sourceNorms p x i)≠0 := by exact_mod_cast hi
  rw [exponent_scale Z hZ]
  exact dyadicWeight_support (k i).val hr

theorem physicalBlock_filter_of_live
    (source:Finset (Point ι))(P:Point ι→Prop)(w:Point ι→ℂ)
    (Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ)
    (hP:∀x∈source,∀ρ:SecondRayIndex,
      w x*physicalTerm p hp hcop hg Ψ j marks W₁ W₂ Φ Z D m x ρ≠0→P x) :
    physicalBlock p hp hcop hg source w Ψ j marks W₁ W₂ Φ Z D m =
      physicalBlock p hp hcop hg (source.filter P) w Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hh:P x
  · rw [ite_eq_left hh]
  · rw [ite_eq_right hh]
    apply Finset.sum_eq_zero
    intro ρ hρ
    by_contra hn
    exact hh (hP x hx ρ hn)

theorem physicalBlock_mass_filter
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (a b:Fin 4→ℝ)(F:Finset (Windows a b))
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m:ℝ) :
    physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m =
    physicalBlock p hp hcop hg
      (pointSource pool (S.filter (fun x=>windowMass F (sourceNorms p x)≠0)))
      ((fun x=>w x*(windowMass F (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j marks W₁ W₂ Φ Z D m := by
  unfold physicalBlock
  rw [pointSource_sum,pointSource_sum,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hn:windowMass F (sourceNorms p x)=0
  · simp only [hn,ne_eq,not_true_eq_false,ite_false,Function.comp_apply,
      erase_sourcePoint,Complex.ofReal_zero,mul_zero,zero_mul,Finset.sum_const_zero]
  · rw [ite_eq_left hn]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem exists_source_frequency_cap (S:Finset (Source (ι:=ι) 0)) :
    ∃T:ℝ,0<T ∧ ∀x∈S,sourceNorms p x 3≤T := by
  have hn (x:Source (ι:=ι) 0) : 0≤sourceNorms p x 3 := by
    change 0≤‖ConcreteTraceCRT.eisEmbedding x.frequency‖^2
    positivity
  have hs:0≤∑x∈S,sourceNorms p x 3:=Finset.sum_nonneg (fun x hx=>hn x)
  refine ⟨1+∑x∈S,sourceNorms p x 3,by linarith,?_⟩
  intro x hx
  have he:sourceNorms p x 3≤∑y∈S,sourceNorms p y 3 :=
    Finset.single_le_sum (fun y hy=>hn y) hx
  linarith

theorem actual_physical_retained_tail
    (hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool:Finset ι)(S:Finset (Source (ι:=ι) 0))
    (hdiv:∀x∈S,x.divisor⊆x.common)(hf:∀x∈S,x.frequency≠0)
    (w:Source (ι:=ι) 0→ℂ)(Ψ:Eis→*ℂ)(j:Eis)(marks:Finset ι→ℂ)
    (W₁ W₂:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(Z D m b T L:ℝ)(hZ:1<Z)
    (hW₁:Function.support W₁⊆Set.Iic b)(hW₂:Function.support W₂⊆Set.Iic b)
    (hT:∀x∈S,sourceNorms p x 3≤T) :
    physicalBlock p hp hcop hg (pointSource pool S) (w∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m =
    (∑k∈retainedWindows (fun _=>1) (physicalCaps b Z D T) Z D m L,
      windowBlock p hp hcop hg pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T))
        w Ψ j marks W₁ W₂ Φ Z D m (fun i=>(k i).val)) +
    physicalBlock p hp hcop hg
      (pointSource pool (cappedSource p S (fun _=>1) (physicalCaps b Z D T)))
      ((fun x=>w x*(windowMass (tailWindows (fun _=>1) (physicalCaps b Z D T) Z D m L)
        (sourceNorms p x):ℂ))∘erasePoint) Ψ j marks W₁ W₂ Φ Z D m := by
  rw [actual_physical_partition p hp hcop hg hpr pool S hdiv hf w Ψ j marks W₁ W₂ Φ
    Z D m b T hZ hW₁ hW₂ hT]
  rw [window_sum_split (fun _=>1) (physicalCaps b Z D T) Z D m L]
  congr 1
  exact sum_windowBlock_eq_mass p hp hcop hg pool
    (cappedSource p S (fun _=>1) (physicalCaps b Z D T)) _ _ _ w Ψ j marks W₁ W₂ Φ Z D m hZ

end SevenEighths.InverseInitialDyadicAssembly

end

end OAI
end OAIOriginalModule1660

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailGates
Source SHA256: ffcc10359ac09964be55f02741f42fd725303a373c5ec71de6010eda2d3a6e4f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1661




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialKernelBridge
open InverseInitialEnergyCallerModes InverseInitialEnergyCallerSource
open InverseInitialDyadicAssembly InverseInitialProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

theorem pointSource_erase_mem (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (x : Point ι) (hx : x∈pointSource pool S) : erasePoint x∈S := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  simpa only [erase_sourcePoint] using hy

theorem pointSource_supports (pool : Finset ι) (S : Finset (Source (ι:=ι) 0))
    (hC : ∀x∈S,x.common⊆pool) (hV : ∀x∈S,x.overlap⊆pool)
    (hdiv : ∀x∈S,x.divisor⊆x.common)
    (x : Point ι) (hx : x∈pointSource pool S) :
    ∀i,InverseInitialHighFrequencyTail.sourceKey x i⊆pool := by
  obtain ⟨y,hy,hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨⟨N,M⟩,hNM,rfl⟩ := Finset.mem_image.mp hx
  intro i
  fin_cases i
  · exact hC y hy
  · exact (hdiv y hy).trans (hC y hy)
  · exact hV y hy
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).1).trans Finset.sdiff_subset
  · exact (Finset.mem_powerset.mp (Finset.mem_product.mp hNM).2).trans Finset.sdiff_subset

def idealIndex : Fin 5→Fin 6 := ![0,1,2,4,5]

omit [DecidableEq ι] in
theorem sourceKey_norm_coordinate (p : ι→O) (x : Point ι) (i : Fin 5) :
    primeProductNorm p (InverseInitialHighFrequencyTail.sourceKey x i)=coordinates p x (idealIndex i) := by
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  fin_cases i <;> simp [InverseInitialHighFrequencyTail.sourceKey,coordinates,physicalCoordinates,idealIndex,hn]

omit [DecidableEq ι] in
theorem sourceNorms_erase (p : ι→O) (x : Point ι) (i : Fin 4) :
    sourceNorms p (erasePoint x) i=coordinates p x (InverseSecondChildWindows.outerIndex i) := by
  have he : InverseInitialEnergyCallerModes.sourcePoint (erasePoint x) x.left x.right=x := by
    cases x
    rfl
  simpa only [he] using sourceNorms_fresh p (erasePoint x) x.left x.right i

omit [DecidableEq ι] in
theorem live_mass_radial_gate
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (a b : Fin 4→ℝ) (Z D m η τ bW : ℝ) (hZ : 1<Z) (hη : 0≤η)
    (hbW : 0<bW) (hfixed : 64*bW^2≤Z^η)
    (x : Point ι) (hx : Valid x)
    (hleft : coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D)
    (hright : coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D)
    (hmass : windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0) :
    Z^τ≤(Z^m/(primeProductNorm p x.divisor*(primeProductNorm p x.overlap)^2*
      primeProductNorm p x.left*primeProductNorm p x.right))*‖eisEmbedding x.frequency‖^2 := by
  obtain ⟨k,hk,hhigh,hbounds⟩ := tail_mass_live_bounds p a b Z D m (4*η+τ) hZ (erasePoint x) hmass
  have hc := coordinates_pos p hp x hx
  have h₀ := (hbounds 0).1.le
  have h₁ := (hbounds 1).2.le
  have h₃ := (hbounds 3).1.le
  rw [sourceNorms_erase] at h₀ h₁ h₃
  have hh := InverseInitialHighFrequencyTail.actual_annulus_high_gate Z D m
    (exponent Z (k 0).val) (exponent Z (k 1).val) (exponent Z (k 3).val) η τ bW
    (coordinates p x 0) (coordinates p x 1) (coordinates p x 2)
    (coordinates p x 4) (coordinates p x 5) (coordinates p x 3)
    hZ.le hη hbW (hc 1) (hc 2) (hc 4) (hc 5) h₀ h₁ h₃ hleft hright hfixed hhigh.le
  have hn (A : Finset ι) : ((sourceIdeal p A).absNorm:ℝ)=primeProductNorm p A := by
    rw [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
    rfl
  simpa [coordinates,physicalCoordinates,hn] using hh

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI
end OAIOriginalModule1661

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialDyadicTailBound
Source SHA256: 0cd7c25aa26870571444ac7ed114be0d9add700dfb5e90596940e4423f867660
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1662


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialDyadicTailBound
open ActualEisensteinCubic ConcreteTraceCRT FirstPassCubeLabels SecondPassArithmetic
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure
open InverseInitialEnergyCallerSource InverseInitialDyadicAssembly InverseInitialProfile
open InverseInitialRetainedSupport InverseInitialHighFrequencyTail
local notation "O"=>ActualEisensteinCubic.O

theorem actual_high_mass_tail (Lcap saving τ : ℝ) (hτ : 0<τ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ), 0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (Ψ : O→*ℂ), (∀n,‖Ψ n‖≤1) → ∀ (j : O)
      (slots : Finset σ) (lists : σ→Finset ι) (weights : σ→ι→ℂ),
    (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
    ∀ (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Z D m η bW Γ B₁ B₂ : ℝ),
    1<Z → 0≤η → 0<bW → 64*bW^2≤Z^η →
    0≤Lcap → bW*Z^D≤Z^Lcap → -m≤Lcap → m-D≤Lcap →
    0≤Γ → 0≤B₁ → 0≤B₂ → (∀x,‖W₁ x‖≤B₁) → (∀x,‖W₂ x‖≤B₂) →
    Function.support W₁⊆Set.Iic bW → Function.support W₂⊆Set.Iic bW →
    ∀ (pool : Finset ι) (S : Finset (Source (ι:=ι) 0)) (w : Source (ι:=ι) 0→ℂ),
    (∀x∈S,x.common⊆pool) → (∀x∈S,x.overlap⊆pool) →
    (∀x∈S,x.divisor⊆x.common) → (∀x∈S,x.frequency≠0) → (∀x∈S,‖w x‖≤Γ) →
    ∀ (a b : Fin 4→ℝ), (∀i,0<a i) → (∀x∈S,∀i,sourceNorms p x i∈Set.Icc (a i) (b i)) →
    ‖physicalBlock p hp hcop hg (pointSource pool S)
      ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p x):ℂ))∘erasePoint)
      Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) := by
  obtain ⟨s,C,hC,hrapid⟩ := original_physical_tail_rapid Lcap saving τ hτ
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc hpr Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m η bW Γ B₁ B₂ hZ hη hbW hfixed hcap hsize hm hmd hΓ hB₁ hB₂ hW₁ hW₂ hs₁ hs₂
    pool S w hcommon hoverlap hdiv hfreq hw a b ha hrange
  let wt : Point ι→ℂ := ((fun x=>w x*(windowMass (tailWindows a b Z D m (4*η+τ))
    (sourceNorms p x):ℂ))∘erasePoint)
  let live (x : Point ι) : Prop := ∃ρ : SecondRayIndex,
    wt x*physicalTerm p hp hcop hg Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m x ρ≠0
  let F := (pointSource pool S).filter live
  have hmem (x) (hx : x∈F) : x∈pointSource pool S := (Finset.mem_filter.mp hx).1
  have hvalid (x) (hx : x∈F) : Valid x := pointSource_valid pool S hdiv hfreq x (hmem x hx)
  have hold (x) (hx : x∈F) : erasePoint x∈S := pointSource_erase_mem pool S x (hmem x hx)
  have hgeometry (x) (hx : x∈F) :
      (coordinates p x 0≤bW*Z^D ∧ coordinates p x 1≤bW*Z^D ∧
       coordinates p x 2≤bW*Z^D ∧ coordinates p x 4≤bW*Z^D ∧ coordinates p x 5≤bW*Z^D) ∧
      (coordinates p x 0*coordinates p x 2*coordinates p x 4≤bW*Z^D ∧
       coordinates p x 0*coordinates p x 2*coordinates p x 5≤bW*Z^D) ∧
      windowMass (tailWindows a b Z D m (4*η+τ)) (sourceNorms p (erasePoint x))≠0 := by
    obtain ⟨ρ,hρ⟩ := (Finset.mem_filter.mp hx).2
    have hpterm := (mul_ne_zero_iff.mp hρ).2
    refine ⟨live_ideal_caps p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,
      live_whole_columns p hp hcop hg hpr Ψ j _ W₁ W₂ Φ Z D m bW
      (by linarith) hs₁ hs₂ x (hvalid x hx) ρ hpterm,?_⟩
    intro hz
    apply (mul_ne_zero_iff.mp hρ).1
    simp only [wt,Function.comp_apply,hz,Complex.ofReal_zero,mul_zero]
  have hn (x : Point ι) (i : Fin 5) := sourceKey_norm_coordinate p x i
  have hwhole (x) (hx : x∈F) :
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.left≤bW*Z^D ∧
      primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p x.right≤bW*Z^D := by
    have he := (hgeometry x hx).2.1
    have hn0 := hn x 0
    have hn2 := hn x 2
    have hn3 := hn x 3
    have hn4 := hn x 4
    simp [sourceKey,idealIndex] at hn0 hn2 hn3 hn4
    rw [←hn0,←hn2,←hn3,←hn4] at he
    exact he
  have hfilter := physicalBlock_filter_of_live p hp hcop hg (pointSource pool S) live wt Ψ j
    (primeMark slots lists weights) W₁ W₂ Φ Z D m (fun x hx ρ hn=>⟨ρ,hn⟩)
  change ‖physicalBlock p hp hcop hg (pointSource pool S) wt Ψ j _ W₁ W₂ Φ Z D m‖≤_
  rw [hfilter]
  have hr := hrapid p hp hcop hg hinj hc Ψ hΨ j slots lists weights hdis hwgt W₁ W₂ Φ
    Z D m (max 1 (bW*Z^D)) Γ B₁ B₂ hZ.le (le_max_left _ _) hcap
    (max_le (Real.one_le_rpow hZ.le hcap) hsize) hm hmd hΓ hB₁ hB₂ hW₁ hW₂ pool F wt hvalid
  suffices hbound : ‖physicalBlock p hp hcop hg F wt Ψ j (primeMark slots lists weights) W₁ W₂ Φ Z D m‖≤
      C*Γ*B₁*B₂*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-saving) by
    have hset : @Finset.filter (Point ι) live (fun x=>Classical.propDecidable (live x))
        (pointSource pool S)=F := by
      ext x
      simp only [Finset.mem_filter,F]
    rw [hset]
    exact hbound
  refine hr ?_ ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact (mass_weight_bound p a b _ ha w (erasePoint x) (hrange _ (hold x hx))).trans (hw _ (hold x hx))
  · intro x hx
    exact pointSource_supports pool S hcommon hoverlap hdiv x (hmem x hx)
  · intro x hx i
    rw [sourceKey_norm_coordinate]
    have he := (hgeometry x hx).1
    apply le_trans _ (le_max_right 1 (bW*Z^D))
    fin_cases i
    · exact he.1
    · exact he.2.1
    · exact he.2.2.1
    · exact he.2.2.2.1
    · exact he.2.2.2.2
  · intro x hx
    exact (hwhole x hx).1.trans (le_max_right _ _)
  · intro x hx
    exact (hwhole x hx).2.trans (le_max_right _ _)
  · intro x hx
    exact live_mass_radial_gate p hp a b Z D m η τ bW hZ hη hbW hfixed x
      (hvalid x hx) (hgeometry x hx).2.1.1 (hgeometry x hx).2.1.2 (hgeometry x hx).2.2

end SevenEighths.InverseInitialDyadicTailBound

end

end OAI
end OAIOriginalModule1662

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialRetainedSum
Source SHA256: 365f44a9e7db00199d36a76da958921350547429b92931dba9d0ee5235a589d1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1663



namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialRetainedSum
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseSecondChildWindows Filter
local notation "O"=>ActualEisensteinCubic.O

theorem retained_sum_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
    ∀(D m r T:ℝ),0≤m→0<T→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖∑k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ),
        windowBlock p hp hcop hg Finset.univ
          (cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)) w Ψ
          (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
          (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  have hb:0<max 1 b₀:=zero_lt_one.trans_le (le_max_left _ _)
  obtain ⟨J,Btree,Tclip,hBtree,hTclip,hwindow⟩:=
    InverseInitialRetainedWindow.retained_window_bound W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
      (fun _=>1/4) (fun _=>1) (by intros;norm_num) (by intros;norm_num)
      cap gap eps (cap+3) π hcap hgap heps (by linarith) hπ K
  obtain ⟨A,hA,hcount⟩:=retained_card_subpower (max 1 b₀) cap (4*η+τ) loss hb hcap (by positivity) hloss
  have hpowers:∀ᶠZ:ℝ in atTop,(4:ℝ)≤Z^η:=
    (tendsto_rpow_atTop hη).eventually (eventually_ge_atTop 4)
  have hlogs:∀ᶠZ:ℝ in atTop,Tclip≤3*η*Real.log Z:=by
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (Tclip/(3*η)))] with Z hZ
    exact (div_le_iff₀ (by positivity : 0<3*η)).mp hZ |>.trans_eq (mul_comm _ _)
  have hevent:=window_exponent_eventual_upper (max 1 b₀) 1 hb (by norm_num)
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp (hcount.and (hpowers.and (hlogs.and hevent)))
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Zq,hC,hZq,hw⟩:=hwindow q hq
  refine ⟨A*C,max Zq Zaux,mul_pos hA hC,lt_max_of_lt_left hZq,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf D m r T hm hT
    hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hweight
  have hZq':Zq≤Z:=(le_max_left _ _).trans hZ
  obtain ⟨hcZ,hpow,hlog,hexp⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hZp:1<Z:=hZq.trans_le hZq'
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq]
    linarith
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have hdivc:∀x∈Sc,x.divisor⊆x.common:=fun x hx=>hdiv x (Finset.mem_filter.mp hx).1
  have hfc:∀x∈Sc,x.frequency≠0:=fun x hx=>hf x (Finset.mem_filter.mp hx).1
  have hlo:Z^(-η)≤(1/4:ℝ):=by
    rw [Real.rpow_neg (zero_lt_one.trans hZp).le]
    simpa only [one_div] using inv_anti₀ (by norm_num : (0:ℝ)<4) hpow
  have hnorm (k:Windows (fun _=>1) (physicalCaps (max 1 b₀) Z D T))
      (hk:k∈retainedWindows (fun _=>1) (physicalCaps (max 1 b₀) Z D T) Z D m (4*η+τ)):
      ‖windowBlock p hp hcop hg Finset.univ Sc w Ψ (assignedElement assigned qelem)
        (primeMark (all\assigned) lists coeff) (clippedSource W₁ c₁ θ₁)
        (clippedSource W₂ c₂ θ₂) Φ Z D m (fun i=>(k i).val)‖≤
        C*Z^(m+15*η+π+eps)*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    have hsize:0<max 1 b₀*Z^D:=mul_pos hb (Real.rpow_pos_of_pos (zero_lt_one.trans hZp) D)
    have h0:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 0).val (k 0).property
    have h1:=hexp.2 (max 1 b₀*Z^D) D hsize le_rfl (k 1).val (k 1).property
    apply hw Z hZq' Dpool hD all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
      qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod Sc hdivc hfc cutoff
      (fun i x hx=>Set.Ioo_subset_Icc_self (cutoff_support i hx))
      D (exponent Z (k 0).val) (exponent Z (k 2).val) (exponent Z (k 1).val)
      (exponent Z (k 3).val) m r η τ hη.le hηsmall hτsmall
      (fun _=>by linarith) hlo hlog hprodj hprod hDeq hmargin₁ hmargin₂ hparent
      (by linarith [h0.2,h1.1]) (Finset.mem_filter.mp hk).2 c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂
      (fun x=>w x*outerCutoff cutoff (sourceRelative p x Z D (exponent Z (k 0).val)
        (exponent Z (k 2).val) (exponent Z (k 1).val) (exponent Z (k 3).val))) ?_
    intro x hx
    rw [norm_mul]
    have hmul {a b : ℝ} (ha : a ≤ 1) (hb₀ : 0 ≤ b) (hb : b ≤ 1) : a * b ≤ 1 :=
      (mul_le_of_le_one_left hb₀ ha).trans hb
    apply hmul (hweight x (Finset.mem_filter.mp hx).1) (by positivity)
    unfold outerCutoff
    simp only [norm_mul]
    exact hmul (hmul (hmul (cutoff_norm_le _ _) (by positivity)
      (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)) (by positivity) (cutoff_norm_le _ _)
  apply (norm_sum_le _ _).trans
  apply (Finset.sum_le_sum hnorm).trans
  rw [Finset.sum_const, nsmul_eq_mul]
  calc
    _≤(A*Z^loss)*(C*Z^(m+15*η+π+eps)*
        ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
          (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))):=
      mul_le_mul_of_nonneg_right (hcZ D m (4*η+τ) T hDcap hm le_rfl hT) (by positivity)
    _=_:=by rw [Real.rpow_add (zero_lt_one.trans hZp) (m+15*η+π+eps) loss];ring

end SevenEighths.InverseInitialRetainedSum

end

end OAI
end OAIOriginalModule1663

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialFiniteEnergy
Source SHA256: e0b57769bb736d8609df3c58c893c2f14cf7cbfdad055044bb65f2f06ac00e35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1664




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialFiniteEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

theorem finite_physical_bound
    (W₁ W₂:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs₁:Function.support W₁⊆Set.Icc a₀ b₀)(hs₂:Function.support W₂⊆Set.Icc a₀ b₀)
    (hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb₁:∀x,‖W₁ x‖≤B₀)(hb₂:∀x,‖W₂ x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hp:=poolPrimary_ne_zero F hF;
    let hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(S:Finset (Source (ι:=primePool F) 0)),
      (∀x∈S,x.divisor⊆x.common)→(∀x∈S,x.frequency≠0)→
      (∀x∈S,x.common⊆Finset.univ)→(∀x∈S,x.overlap⊆Finset.univ)→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(c₁ c₂ θ₁ θ₂:ℝ),1≤c₁→c₁≤bcap→1≤c₂→c₂≤bcap→
    ∀(w:Source (ι:=primePool F) 0→ℂ),(∀x∈S,‖w x‖≤1)→
      ‖physicalBlock p hp hcop hg (pointSource Finset.univ S) (w∘erasePoint) Ψ
        (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
        (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m‖≤
        C*Z^(m+15*η+π+eps+loss)*
          ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*degree)*
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*degree)) := by
  obtain ⟨J,Btree,hBtree,hretained⟩:=InverseInitialRetainedSum.retained_sum_bound
    W₁ W₂ a₀ b₀ bcap ha₀ hbcap hs₁ hs₂ hW₁ hW₂ Φ
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨ss,Ct,hCt,htail⟩:=InverseInitialDyadicTailBound.actual_high_mass_tail (2*cap+2) 1 τ hτ
  let tailC:=Ct*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ
  have htailC:0≤tailC:=by dsimp [tailC];positivity
  have hevent:∀ᶠZ:ℝ in atTop,max 1 b₀≤Z ∧ 64*(max 1 b₀)^2≤Z^η:=
    (eventually_ge_atTop (max 1 b₀)).and
      ((tendsto_rpow_atTop hη).eventually (eventually_ge_atTop (64*(max 1 b₀)^2)))
  obtain ⟨Zaux,haux⟩:=eventually_atTop.mp hevent
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨Cr,Zr,hCr,hZr,hretained⟩:=hretained q hq
  refine ⟨Cr+tailC,max Zr Zaux,by linarith,lt_max_of_lt_left hZr,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf hcommon hoverlap
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
    c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  have hZr':Zr≤Z:=(le_max_left _ _).trans hZ
  have hZp:1<Z:=hZr.trans_le hZr'
  obtain ⟨hbZ,h64⟩:=haux Z ((le_max_right _ _).trans hZ)
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hsize:max 1 b₀*Z^D≤Z^(2*cap+2):=by
    calc
      _≤Z*Z^D:=mul_le_mul_of_nonneg_right hbZ (Real.rpow_nonneg (by linarith) _)
      _=Z^(D+1):=by rw [Real.rpow_add (by linarith : 0<Z),Real.rpow_one];ring
      _≤_:=Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  have hs₁':Function.support (clippedSource W₁ c₁ θ₁)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₁ a₀ b₀ c₁ θ₁ ha₀ hc₁ hs₁ hx) (le_max_right 1 b₀)
  have hs₂':Function.support (clippedSource W₂ c₂ θ₂)⊆Set.Iic (max 1 b₀):=
    by
      intro x hx
      exact le_trans (clipped_support_upper W₂ a₀ b₀ c₂ θ₂ ha₀ hc₂ hs₂ hx) (le_max_right 1 b₀)
  obtain ⟨T,hT,hfreqcap⟩:=exists_source_frequency_cap p S
  have hsplit:=actual_physical_retained_tail p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ S hdiv hf w Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ
    Z D m (max 1 b₀) T (4*η+τ) hZp hs₁' hs₂' hfreqcap
  rw [hsplit]
  apply (norm_add_le _ _).trans
  have hret:=hretained Z hZr' Dpool hD all assigned hassigned hK lists Hslot coeff
    hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod S hdiv hf
    D m r T hm hT hprodj hprod hDeq hmargin₁ hmargin₂ hparent c₁ c₂ θ₁ θ₂ hc₁ hbc₁ hc₂ hbc₂ w hw
  let Sc:=cappedSource p S (fun _=>1) (physicalCaps (max 1 b₀) Z D T)
  have ht:=htail p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa) Ψ hΨ
    (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m η (max 1 b₀) 1 B₀ B₀
    hZp hη.le (by positivity) h64 (by linarith) hsize (by linarith) (by linarith)
    (by norm_num) hB₀ hB₀ (clipped_bound W₁ B₀ hb₁ c₁ θ₁) (clipped_bound W₂ B₀ hb₂ c₂ θ₂)
    hs₁' hs₂' Finset.univ Sc w
    (fun x hx=>hcommon x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hoverlap x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hdiv x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hf x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hw x (Finset.mem_filter.mp hx).1)
    (fun _=>1) (physicalCaps (max 1 b₀) Z D T) (by intros;norm_num)
    (fun x hx=>(Finset.mem_filter.mp hx).2)
  have hheight:1≤((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=
    one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith [norm_nonneg θ₁]))
      (one_le_pow₀ (by linarith [norm_nonneg θ₂]))
  have hpow:Z^(-1:ℝ)≤Z^(m+15*η+π+eps+loss):=
    Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)
  apply (add_le_add hret ht).trans
  change Cr*Z^(m+15*η+π+eps+loss)*_+(Ct*1*B₀*B₀*ss.sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ*Z^(-1:ℝ))≤_
  have hh:tailC*Z^(-1:ℝ)≤tailC*Z^(m+15*η+π+eps+loss)*
      ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤tailC*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left hpow htailC
      _≤_:=le_mul_of_one_le_right (by positivity) hheight
  convert add_le_add_left hh (Cr*Z^(m+15*η+π+eps+loss)*
    ((1+‖θ₁‖)^InverseClippingProfiles.momentOrder (4*J)*
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder (4*J))) using 1 <;> dsimp [tailC] <;> ring

end SevenEighths.InverseInitialFiniteEnergy

end

end OAI
end OAIOriginalModule1664

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialTotalEnergy
Source SHA256: 0ef6f457da3645cb613558815ec6f7d43e41ea445ede4a077bf0bea78e8c2e66
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1665




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalEnergy
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
theorem original_input_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(c θ:ℝ),1≤c→c≤bcap→
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z^m)*
        (‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists coeff)
            (clippedSource W c θ) Z D) u‖^2:ℝ)‖≤
        C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*degree)) := by
  have hsstar:Function.support (fun x=>star (W x))⊆Set.Icc a₀ b₀:=by
    intro x hx
    apply hs
    simpa only [Function.mem_support,star_ne_zero] using hx
  have hbStar:∀x,‖star (W x)‖≤B₀:=by intro x;simpa only [norm_star] using hb x
  obtain ⟨J,Btree,hBtree,hfinite⟩:=InverseInitialFiniteEnergy.finite_physical_bound
    (fun x=>star (W x)) W a₀ b₀ bcap ha₀ hbcap hsstar hs
    (Complex.conjCLE.contDiff.comp hW) hW Φ B₀ hB₀ hbStar hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨Cz,hCz,hzero⟩:=InverseInitialZeroMode.physical_marked_zero_bound
    loss cap (max 1 b₀) B₀ hloss hcap (by positivity) hB₀ Φ
  refine ⟨J,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨Cf,Z₀,hCf,hZ₀,hfinite⟩:=hfinite q hq
  refine ⟨Cf+Cz,Z₀,by linarith,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent c θ hc hbc
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hDcap:D≤cap:=by
    have hg:0≤assignedCenter assigned z:=Finset.sum_nonneg (fun i hi=>hz i (hassigned hi))
    rw [hDeq];linarith
  have hconj:(fun x=>star (clippedSource W c θ x))=clippedSource (fun x=>star (W x)) c (-θ):=
    funext (clippedSource_conjugate W c θ)
  have hn:=nonzero_frequency_norm_le p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m
    (Cf*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)))
    (by linarith : 0<Z) (by
      intro freqT hzero
      rw [hconj]
      have h:=hfinite Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        (finiteSource Finset.univ freqT)
        (finiteSource_divisor Finset.univ freqT) (finiteSource_nonzero Finset.univ freqT hzero)
        (fun x hx=>Finset.subset_univ _) (fun x hx=>Finset.subset_univ _)
        D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent
        c c (-θ) θ hc hbc hc hbc (fun _=>1) (by intros;norm_num)
      simpa only [Function.comp_def,norm_neg,pow_mul,pow_two,mul_pow] using h)
  have hz0:=hzero p hp hcop hg (InverseInitialRayAttachment.poolPrimary_injective F hFa)
    (poolPrimary_odd F hFa) (InverseInitialRayAttachment.poolPrimary_primary F hFa)
    Finset.univ Ψ hΨ (assignedElement assigned qelem) (all\assigned) lists coeff
    (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hac
    (clippedSource W c θ) (clipped_bound W B₀ hb c θ)
    (fun x hx=>le_trans (clipped_support_upper W a₀ b₀ c θ ha₀ hc hs hx) (le_max_right 1 b₀))
    Z D m hZp.le hDcap
  rw [original_input_zero_nonzero p hp hcop hg
    (InverseInitialRayAttachment.poolPrimary_injective F hFa) (poolPrimary_odd F hFa)
    (InverseInitialRayAttachment.poolPrimary_primary F hFa) Finset.univ Ψ
    (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
    (clippedSource W c θ) Φ Z D m (by linarith)]
  apply (norm_add_le _ _).trans
  have hh:1≤(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=one_le_pow₀ (by linarith [norm_nonneg θ])
  have hz1:Cz*Z^(m+loss)≤Cz*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*InverseClippingProfiles.momentOrder (4*J)):=by
    calc
      _≤Cz*Z^(m+15*η+π+eps+loss):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hZp.le (by linarith)) hCz.le
      _≤_:=le_mul_of_one_le_right (by positivity) hh
  change ‖physicalFrequency _ _ _ _ _ _ _ _ _ _ _ _ _ 0‖+_≤_
  exact (add_le_add (hz0.trans hz1) hn).trans_eq (by ring)

end SevenEighths.InverseInitialTotalEnergy

end

end OAI
end OAIOriginalModule1665

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseRawInputBound
Source SHA256: 52f0a30ffcc67c68da206d8a001f52da24f53f04010c72e190402f8c75f3bc18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1666


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.DetectorDictionaryInverseRawInputBound
open ConcretePrimeRowBridge ActualEisensteinCubic ConcreteTraceCRT CompletedGauss SecondPassArithmetic CanonicalQuadraticSieve CanonicalRowCompletion
open CanonicalCoefficientClass InverseMoment InverseInitialProfile InverseInitialRayAttachment
open InverseInitialQuotientGeometry InverseInitialProfileBounds
local notation "O"=>ActualEisensteinCubic.O

theorem raw_input_bound
    (W:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support W⊆Set.Icc a b)
    (Φ:𝓢(ℝ,ℂ))(gap eps π η τ loss:ℝ)
    (hgap:0<gap)(heps:0<eps)(hπ:0<π)(hη:0<η)(hηone:η≤1)
    (hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss):
    ∃J:ℕ,∃Btree:ℝ,1≤Btree ∧ ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^3≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let hg:=poolPrimary_good F hF;
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀ (r t : ℝ), (-2 : ℝ) ≤ r → r ≤ 1 - 2 * gap → 2 * r ≤ 3 - 2 * gap → r + 7 * η ≤ 2 →
    ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Z)*
      (‖((Z^(-r/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ 1 1 1
        (initialTest p (fun _=>1) (childLogTest W t) Z r) u‖^2:ℝ)‖≤
      C*Z^(1+15*η+π+eps+loss)*(1+‖t‖)^(2*J) := by
  have hB:0≤SchwartzMap.seminorm ℝ 0 0 W:=apply_nonneg _ _
  have hb:∀x,‖W x‖≤SchwartzMap.seminorm ℝ 0 0 W:=fun x=>by
    simpa only [pow_zero,one_mul,norm_iteratedFDeriv_zero] using W.le_seminorm ℝ 0 0 x
  obtain ⟨degree,Btree,hBtree,hbound⟩:=InverseInitialTotalEnergy.original_input_bound
    W a b 1 ha le_rfl hs (W.smooth ⊤) Φ _ hB hb 2 gap eps π η τ loss
    (by norm_num) hgap heps hπ hη hηone hηsmall hτ hτsmall hloss 0
  refine ⟨InverseClippingProfiles.momentOrder (4*degree),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,hbound⟩:=hbound q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hpool F hF
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance
  intro p hg Ψ hΨ hperiod r t hrlo hr₁ hr₂ hrcap
  have hZp:1<Z:=hZ₀.trans_le hZ
  have hpool':Btree*Z^((2:ℝ)+1)≤Dpool:=by norm_num;exact hpool
  have hp:=Real.one_le_rpow hZp.le hη.le
  have h:=hbound Z hZ Dpool hpool' (σ:=Fin 0) ∅ ∅ (by simp) (by simp)
    (fun _=>∅) (fun _=>1) (fun _ _=>0) (by simp) (by simp) (by simp) (by simp)
    (fun _=>1) (fun _=>0) (fun _=>1) (fun _=>1) (fun _ _=>0)
    (by simp) (by simp) (by simp) (by simp) Ψ hΨ hperiod r 1 r
    (by norm_num) (by norm_num) hrlo (by simpa using hp) (by simpa [assignedCenter] using hp)
    (by simp [assignedCenter]) (by simpa [assignedCenter] using hr₁)
    (by simpa [assignedCenter] using hr₂) (by simpa [assignedCenter] using hrcap)
    1 t le_rfl le_rfl
  simp only [Finset.sdiff_self,assignedElement,Finset.prod_empty] at h
  have hemark : primeMark (∅:Finset (Fin 0)) (fun _=> (∅:Finset (primePool F)))
      (fun _ _=> (0:ℂ))=(fun _=>1) := by
    funext A
    exact primeMark_empty _ _ A
  rw [hemark] at h
  simpa only [
    Real.rpow_one,←childLogTest_eq_clipped] using h

end SevenEighths.DetectorDictionaryInverseRawInputBound

end

end OAI
end OAIOriginalModule1666

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialInputRadial
Source SHA256: 27f303928101330b5ec21efbaddb384e402bf5abeb0387fb813935667b4ad493
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1667


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseInitialInputRadial
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic ConcreteTraceCRT
open InverseInitialConjugateEnergy
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem input_energy_summable (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(Y:ℝ)(hY:0<Y):
    Summable (fun u:O=>Φ (‖eisEmbedding u‖^2/Y)*
      (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)):=by
  let c:Finset ι→ℂ:=fun S=>a*supportMobius (fun i=>Ideal.span {p i}) S*
    secondInputCoefficient p hg Ψ j 1 1 test S
  have he (u:O):a*inputConjugateRow p hg pool Ψ j 1 1 test u=
      star (∑S∈pool.powerset,star (c S)*finiteSquarefreeRow (fun i=>Ideal.span {p i}) hg S u):=by
    simp only [inputConjugateRow,supportConjugateSum,Finset.mul_sum,star_sum,star_mul,star_star,c]
    apply Finset.sum_congr rfl
    intro S hS
    ring
  simp_rw [he,norm_star]
  exact finiteSquarefreeRow_smoothed_mean_square_summable (fun i=>Ideal.span {p i}) hg
    pool.powerset id (fun S=>star (c S)) Φ Y hY

theorem finite_rows_le_input_norm (pool:Finset ι)(Ψ:O→*ℂ)(j:O)(test:Finset ι→ℂ)
    (a:ℂ)(Φ:𝓢(ℝ,ℂ))(hΦ:∀x,0≤(Φ x).re)
    (hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (Y:ℝ)(hY:0<Y)(rows:Finset O)(hrows:∀u∈rows,‖eisEmbedding u‖^2≤Y):
    (∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)≤
      ‖∑'u:O,Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)‖:=by
  have hs:=input_energy_summable p hg pool Ψ j test a Φ Y hY
  have hr:=Complex.hasSum_re hs.hasSum
  have hfin:(∑u∈rows,‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2)=
      ∑u∈rows,(Φ (‖eisEmbedding u‖^2/Y)*
        (‖a*inputConjugateRow p hg pool Ψ j 1 1 test u‖^2:ℝ)).re:=by
    apply Finset.sum_congr rfl
    intro u hu
    rw [hone _ ⟨div_nonneg (sq_nonneg _) hY.le,(div_le_one hY).mpr (hrows u hu)⟩]
    simp only [one_mul,Complex.ofReal_re]
  rw [hfin]
  apply (hr.summable.sum_le_tsum rows (fun u _=>?_)).trans
  · rw [hr.tsum_eq]
    exact Complex.re_le_norm _
  · simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]
    exact mul_nonneg (hΦ _) (sq_nonneg _)

end SevenEighths.InverseInitialInputRadial

end

end OAI
end OAIOriginalModule1667

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialTotalRows
Source SHA256: 8f0d9b43992bcf5de5640f543fba63babf97ca5fea1cfc86cf42e9fc027e368a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1668


namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalRows
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
theorem original_input_rows_fourier_bound
    (W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(θ:ℝ),
      (∑u∈rows,‖((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)))
            (childLogTest W θ) Z D) u‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalEnergy.original_input_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  refine ⟨InverseClippingProfiles.momentOrder (4*J),Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨C,Z₀,hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y θ
  have hZp:1<Z:=hZ₀.trans_le hZ
  have he:=henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot
    (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P)) hdis hHs hPs
    (by intro i hi P hP;simpa only [norm_mul,FourierBridge.logPhase_norm,mul_one] using hac i hi P hP)
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent 1 θ le_rfl hbcap
  have hr:=InverseInitialInputRadial.finite_rows_le_input_norm p hg Finset.univ Ψ
    (assignedElement assigned qelem)
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P*FourierBridge.logPhase (-θ) (y i P))) (childLogTest W θ) Z D)
    ((Z^(-D/2):ℝ):ℂ) Φ hΦ hone (Z^m) (Real.rpow_pos_of_pos (by linarith) _) rows hrows
  apply hr.trans
  simpa only [InverseInitialProfileBounds.childLogTest_eq_clipped,pow_mul,pow_two,mul_pow] using he

end SevenEighths.InverseInitialTotalRows

end

end OAI
end OAIOriginalModule1668

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialTotalFourier
Source SHA256: ddde1532380e794d6583eb2d58ebf6ad8c84e9b1a4e672ca9f09eee1b3cace23
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1669




namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.InverseInitialTotalFourier
open ActualEisensteinCubic CompletedGauss ConcretePrimeRowBridge ConcreteTraceCRT
open CanonicalQuadraticSieve CanonicalRowCompletion CanonicalCoefficientClass
open InverseMoment InverseInitialArithmetic InverseInitialPhysicalMeasure InverseInitialProfile
open InverseInitialEnergyCallerSource InverseInitialEnergyCallerModes InverseInitialEnergyCallerWindows
open InverseInitialQuotientGeometry InverseInitialClippedColumns InverseInitialEnergyCallerState
open InverseInitialDyadicAssembly InverseInitialProfileBounds Filter
local notation "O"=>ActualEisensteinCubic.O

open InverseInitialPhysicalLimit InverseInitialPhysicalReassembly SecondPassArithmetic InverseInitialRayAttachment
open MeasureTheory FourierBridge JointLogSeparation InverseInitialOverlapFourier
theorem original_fourier_energy_bound
    (g:𝓢(ℝ,ℂ))(W:ℝ→ℂ)(a₀ b₀ bcap:ℝ)(ha₀:0<a₀)(hbcap:1≤bcap)
    (hs:Function.support W⊆Set.Icc a₀ b₀)
    (hW:ContDiff ℝ ∞ W)(Φ:𝓢(ℝ,ℂ))
    (hΦ:∀x,0≤(Φ x).re)(hone:∀x∈Set.Icc (0:ℝ) 1,Φ x=1)
    (B₀:ℝ)(hB₀:0≤B₀)(hb:∀x,‖W x‖≤B₀)
    (cap gap eps π η τ loss:ℝ)(hcap:0≤cap)(hgap:0<gap)(heps:0<eps)(hπ:0<π)
    (hη:0<η)(hηone:η≤1)(hηsmall:η≤gap/50)(hτ:0<τ)(hτsmall:τ≤gap/50)(hloss:0<loss)(K:ℕ):
    ∃degree:ℕ,∃Btree:ℝ,1≤Btree ∧
    ∀q:ℕ,q≠0→∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀Z:ℝ,Z₀≤Z→∀Dpool:ℕ,Btree*Z^(cap+1)≤Dpool→
    let F:=InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) Dpool;
    let hF:=InitialMeanSquare.outsideSquarefree_admissible (reflectionExcludedPrimes q) Dpool (reflectionExcludedPrimes_bad q);
    letI:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hF i];infer_instance;
    let p:=poolPrimary F;
    let _hp:=poolPrimary_ne_zero F hF;
    let _hcop:=poolPrimary_coprime F hF;
    let hg:=poolPrimary_good F hF;
    ∀{σ:Type}[DecidableEq σ](all assigned:Finset σ),assigned⊆all→all.card≤K→
    ∀(lists:σ→Finset (primePool F))(Hslot:σ→ℝ)(coeff:σ→primePool F→ℂ),
      (all:Set σ).PairwiseDisjoint lists→(∀i∈all\assigned,1≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,(P.val.absNorm:ℝ)≤Hslot i)→
      (∀i∈all\assigned,∀P∈lists i,‖coeff i P‖≤1)→
    ∀(qelem:σ→O)(z al bl:σ→ℝ)(primeW:σ→ℝ→ℂ),
      (∀i∈all,0≤z i)→(∀i∈assigned,qelem i≠0)→
      (∀i∈assigned,Function.support (primeW i)⊆Set.Icc (al i) (bl i))→
      (∀i∈assigned,primeW i ((Ideal.absNorm (Ideal.span {qelem i}):ℝ)/Z^(z i))≠0)→
    ∀Ψ:O→*ℂ,(∀u,‖Ψ u‖≤1)→FactorsModulo (fixedBaseConductor q) Ψ→
    ∀(D m r:ℝ),0≤m→m≤cap→-cap≤D→
      (∏i∈assigned,bl i)≤Z^η→
      (∏i∈all\assigned,Hslot i)≤Z^(assignedCenter (all\assigned) z+η)→
      D=r+assignedCenter all z-2*assignedCenter assigned z→
      r+2*assignedCenter all z≤m-2*gap→
      2*r+8*assignedCenter all z≤3*m-2*gap→
      r+assignedCenter all z+7*η≤cap→
    ∀(rows:Finset O),(∀u∈rows,‖eisEmbedding u‖^2≤Z^m)→
    ∀(y:σ→primePool F→ℝ)(xj θ:ℝ),
      (∑u∈rows,‖∫t:ℝ,density (frequencyTwist g θ) xj t*
        (((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
          (assignedElement assigned qelem) 1 1
          (initialTest p (primeMark (all\assigned) lists
            (fun i P=>coeff i P*FourierBridge.logPhase (-t) (y i P)))
            (childLogTest W t) Z D) u)‖^2)≤
        C*Z^(m+15*η+π+eps+loss)*((1+‖θ‖)^degree)^2 := by
  obtain ⟨J,Btree,hBtree,henergy⟩:=InverseInitialTotalRows.original_input_rows_fourier_bound
    W a₀ b₀ bcap ha₀ hbcap hs hW Φ hΦ hone B₀ hB₀ hb
    cap gap eps π η τ loss hcap hgap heps hπ hη hηone hηsmall hτ hτsmall hloss K
  obtain ⟨Cm,hCm,hmeasure⟩:=InverseInitialOverlapHeight.twisted_polynomial_measure_energy g J
  refine ⟨J+(volume:Measure ℝ).integrablePower,Btree,hBtree,?_⟩
  intro q hq
  obtain ⟨C,Z₀,hC,hZ₀,henergy⟩:=henergy q hq
  refine ⟨(Cm+1)*C,Z₀,mul_pos (by linarith) hC,hZ₀,?_⟩
  intro Z hZ Dpool hD F hFa
  let:∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=fun i=>by rw [poolPrimary_span F hFa i];infer_instance
  intro p hp hcop hg σ dec all assigned hassigned hK lists Hslot coeff hdis hHs hPs hac
    qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
    D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y xj θ
  have hZp:0<Z:=zero_lt_one.trans (hZ₀.trans_le hZ)
  let φ:O→ℝ→ℂ:=fun u t=>((Z^(-D/2):ℝ):ℂ)*inputConjugateRow p hg Finset.univ Ψ
    (assignedElement assigned qelem) 1 1
    (initialTest p (primeMark (all\assigned) lists
      (fun i P=>coeff i P*logPhase (-t) (y i P))) (childLogTest W t) Z D) u
  have ht:=hmeasure θ xj (fun u:rows=>φ u.val) (C*Z^(m+15*η+π+eps+loss))
    (by positivity)
    (fun u=>InverseInitialMarkedInputEnergy.marked_input_integrable p hg
      (frequencyTwist g θ) Finset.univ Ψ (assignedElement assigned qelem) u.val
      (all\assigned) lists coeff y W Z D xj)
    (fun t=>by
      apply (Finset.sum_coe_sort rows (fun u=>‖φ u t‖^2)).le.trans
      exact henergy Z hZ Dpool hD all assigned hassigned hK lists Hslot coeff
        hdis hHs hPs hac qelem z al bl primeW hz hqe hprimeW hprimeLive Ψ hΨ hperiod
        D m r hm hmcap hDlo hprodj hprod hDeq hmargin₁ hmargin₂ hparent rows hrows y t)
  apply (Finset.sum_coe_sort rows (fun u=>‖∫t:ℝ,density (frequencyTwist g θ) xj t*φ u t‖^2)).symm.le.trans
  apply ht.trans
  have hh:0≤C*Z^(m+15*η+π+eps+loss)*(1+‖θ‖)^(2*(J+(volume:Measure ℝ).integrablePower)):=by positivity
  have he:=mul_le_mul_of_nonneg_right (show Cm≤Cm+1 by linarith) hh
  convert he using 1 <;> simp only [pow_mul,pow_two,mul_pow] <;> ring

end SevenEighths.InverseInitialTotalFourier

end

end OAI
end OAIOriginalModule1669

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialInputReindex
Source SHA256: 16fecbeeb100ee0efd4833931deccf23e1e4dff5daba7c8ce83434c20bf34c1d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1670


namespace OAI

noncomputable section

open scoped Classical BigOperators
namespace SevenEighths.InverseInitialInputReindex
open ActualEisensteinCubic FirstCauchyArithmetic SecondPassArithmetic InverseMoment
open InverseInitialArithmetic
local notation "O"=>ActualEisensteinCubic.O

theorem input_puncture_span {ι:Type*}[DecidableEq ι](p:ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(j₁ j₂:O)(hspan:Ideal.span {j₁}=Ideal.span {j₂})
    (test:Finset ι→ℂ)(u:O):
    inputConjugateRow p hg pool Ψ j₁ 1 1 test u=
      inputConjugateRow p hg pool Ψ j₂ 1 1 test u:=by
  rw [initial_input_row p hg,initial_input_row p hg]
  unfold supportConjugateSum
  apply Finset.sum_congr rfl
  intro A hA
  dsimp only
  rw [rowCoprimeMask_eq_of_span_eq (fun i=>Ideal.span {p i}) A hspan]

theorem primeMark_subtype {σ ι:Type*}[DecidableEq σ][DecidableEq ι]
    (I:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:I=>L i.val) (fun i:I=>a i.val) A=
      primeMark I L a A:=by
  exact Finset.prod_coe_sort I (fun i=>primeSlot (L i) (a i) A)

theorem primeMark_remaining {σ ι:Type*}[Fintype σ][DecidableEq σ][DecidableEq ι]
    (J:Finset σ)(L:σ→Finset ι)(a:σ→ι→ℂ)(A:Finset ι):
    primeMark Finset.univ (fun i:{i:σ//i∉J}=>L i.val) (fun i:{i:σ//i∉J}=>a i.val) A=
      primeMark (Finset.univ\J) L a A:=by
  classical
  unfold primeMark
  exact (Finset.prod_subtype (Finset.univ\J) (by intro i;simp)
    (fun i=>primeSlot (L i) (a i) A)).symm

end SevenEighths.InverseInitialInputReindex

end

end OAI
end OAIOriginalModule1670

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.InitialOriginalHeight
Source SHA256: 1c330c524ea647b44df477aa7411602129b1724586a5131d84c694fd31c890ef
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1671


namespace OAI

noncomputable section

open scoped Classical SchwartzMap ContDiff FourierTransform
namespace SevenEighths.InverseInitialOriginalHeight
open InverseMoment InverseInitialProfile InverseInitialProfileBounds FourierBridge
open JointLogSeparation CompletedHeight

theorem child_eq_normTwisted (W:ℝ→ℂ)(θ:ℝ):childLogTest W θ=normTwistedSource W θ:=by
  rw [childLogTest_eq_clipped]
  funext x
  simp only [clippedSource,normTwistedSource,one_mul]

theorem child_support (W:ℝ→ℂ)(θ:ℝ):
    Function.support (childLogTest W θ)⊆Function.support W:=by
  rw [child_eq_normTwisted]
  exact normTwistedSource_support W θ

theorem child_smooth (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    ContDiff ℝ ∞ (childLogTest W θ):=by
  rw [child_eq_normTwisted]
  exact CanonicalRowCompletion.normTwistedSource_contDiff W a b ha hs hW θ

theorem logSchwartz_child (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(θ:ℝ):
    CubicReflectionKernel.logSchwartz (childLogTest W θ) a b ha
      ((child_support W θ).trans hs) (child_smooth W a b ha hs hW θ)=
    frequencyTwist (CubicReflectionKernel.logSchwartz W a b ha hs hW) θ:=by
  ext x
  simp only [CubicReflectionKernel.logSchwartz_apply,childLogTest,
    frequencyTwist_apply,Real.log_exp]
  ring

end SevenEighths.InverseInitialOriginalHeight

end

end OAI
end OAIOriginalModule1671

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstDiscarded
Source SHA256: ce820ae0836551937cd2f57fda8c38626c0128a5dc047d6263644f7d564323f9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1672



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscarded
open SevenEighths CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CanonicalQuadraticSieve
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFirstReduced
open CenteredMomentSupportedCorrelation
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

theorem actual_first_kernel_reference (I J E : Ideal O)
    (hI : I≠0) (hJ : J≠0) (hE : E≠0) (K X HN Tsec : ℝ)
    (hK : 0<K) (hX : 0<X)
    (hi : (Ideal.absNorm I:ℝ)≤Real.exp HN*X)
    (hj : (Ideal.absNorm J:ℝ)≤Real.exp HN*X)
    (hsec : firstNominalScale I J E K X≤Tsec) :
    kernelReference Tsec HN ≤
      K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)) := by
  simpa only [kernelReference,mul_one] using
    first_kernel_sector_lower I J E hI hJ hE K X 1 HN Tsec hK hX zero_le_one hi hj hsec

theorem canonical_discarded_first_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J E : Ideal O) (hI : Supported I) (hJ : Supported J), E≠0 →
      ∀ K X HN Tsec Z Csec ξ : ℝ, 0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      firstNominalScale I J E K X≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z < ξ/4) →
      ‖∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
          (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W
          ((K/((Ideal.absNorm E:ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
            (Ideal.absNorm (residualPart I J):ℝ)*(Ideal.absNorm (residualPart J I):ℝ)))*normValue h)‖ ≤
      (‖eisEmbedding (activeConductor I J)‖*(Ideal.absNorm (residualPart I J):ℝ)*
        (Ideal.absNorm (residualPart J I):ℝ))*
        (C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W I J E hI hJ hE K X HN Tsec Z Csec ξ hK hX hZ hCsec hi hj hsec hthreshold
  have hT : 0<Tsec := (firstNominalScale_pos I J E hE K X hK hX).trans_le hsec
  apply ht W Tsec Z Csec HN ξ _ _ hT hZ hCsec hthreshold
    (actual_first_kernel_reference I J E hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec)
    (by positivity)
  intro h
  apply (canonical_tripleFourier_norm_le I J hI hJ h).trans
  have ha := CenteredMomentTail.residueGauss_norm_le (residualGenerator I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (residualCharacter I J hI) (Ideal.Quotient.mk _ h)
  have hb := CenteredMomentTail.residueGauss_norm_le (residualGenerator J I)
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ))
    (residualCharacter J I hJ)⁻¹ (Ideal.Quotient.mk _ h)
  have ha' := ha.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span I J hI))
  have hb' := hb.trans_eq (congrArg (fun L : Ideal O => (Ideal.absNorm L:ℝ))
    (residualGenerator_span J I hJ))
  exact mul_le_mul (mul_le_mul_of_nonneg_left ha' (norm_nonneg _)) hb' (norm_nonneg _) (by positivity)

end SevenEighths.CenteredMomentFirstDiscarded

end

end OAI
end OAIOriginalModule1672

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstDiscardedEnergy
Source SHA256: 1889aa5f047902029c9ca315782104ab77adfc8f76b86cd8a615a2a42f3cd725
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1673


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstDiscardedEnergy
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson ConcretePrimeRowBridge
open CenteredMomentFirstReduced CenteredMomentSectorLocalization CenteredMomentCorrelation
open CenteredMomentCommonSupport CenteredMomentCanonicalFirst CenteredMomentSupportedCorrelation
open CenteredMomentFirstScale CenteredMomentFirstDiscarded CenteredMomentActive
open CenteredMomentCompleteCommon IdealMobiusDivisorSum
local notation "O" => ActualEisensteinCubic.O

theorem tripleRow_norm_le_one (a b r : O) (ha : a≠0) (hb : b≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (z : O) :
    ‖tripleRow a b r χa χb G z‖≤1 := by
  let := finite_quotient_span ha
  let := finite_quotient_span hb
  let : Fintype (Residue a) := Fintype.ofFinite _
  let : Fintype (Residue b) := Fintype.ofFinite _
  rw [tripleRow,norm_mul,norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_finite_character_le_one χa _)).trans
      (QuadraticInitialBound.norm_finite_character_le_one χb _))).trans (hG _)

theorem tripleFourier_norm_le_full (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
    (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
    (G : Residue r → ℂ) (hG : ∀ x,‖G x‖≤1) (h : O) :
    ‖tripleFourier a b r ha hb hr χa χb G h‖≤normValue (a*(b*r)) := by
  let := finite_quotient_span (mul_ne_zero ha (mul_ne_zero hb hr))
  let : Fintype (Residue (a*(b*r))) := Fintype.ofFinite _
  rw [tripleFourier,tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a*(b*r)),‖tripleResidue a b r χa χb G x*
      quotientTrace (a*(b*r)) (mul_ne_zero ha (mul_ne_zero hb hr)) (Ideal.Quotient.mk _ h*x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a*(b*r)),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [norm_mul,(quotientTrace _ _).norm_apply,mul_one,tripleResidue_mk]
      exact tripleRow_norm_le_one a b r ha hb χa χb G hG z
    _ = _ := by simp [normValue,Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem activeFunction_norm_le_one (I J : Ideal O) (hI : CanonicalQuadraticSieve.Supported I)
    (x : Residue (activeConductor I J)) : ‖activeFunction I J hI x‖≤1 := by
  obtain ⟨z,rfl⟩ := Ideal.Quotient.mk_surjective x
  calc
    _ = ‖finiteSexticRow (activePrime I J) (activeGood I J hI)
        (CenteredMomentCanonicalFirst.activeExponent I J) z‖ :=
      congrArg norm (principalSexticRow_mk (activePrime I J) (activeCoprime I J)
        (activeGood I J hI) (CenteredMomentCanonicalFirst.activeExponent I J)
        (activeConductor I J) (span_finitePrimeModulus _) z)
    _ ≤ 1 := QuadraticInitialBound.finiteSexticRow_norm_le_one _ _ _ z

theorem scaled_discarded_triple_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (Tsec Z Csec H ξ k : ℝ),
      0<Tsec → 1<Z → 1≤Csec → 0<k →
      (2*H/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ∀ (a b r : O) (ha : a≠0) (hb : b≠0) (hr : r≠0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ)
        (G : Residue r → ℂ), (∀ x,‖G x‖≤1) →
      kernelReference Tsec H≤k/normValue (a*(b*r)) →
      ‖((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
        (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
          tripleFourier a b r ha hb hr χa χb G h*
          paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h)‖ ≤
      k*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec H))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := actual_discarded_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro W Tsec Z Csec H ξ k hT hZ hCs hk hthreshold a b r ha hb hr χa χb G hG hscale
  have hN : 0<normValue (a*(b*r)) := norm_pos _
    (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr)))
  have hh := ht W Tsec Z Csec H ξ (k/normValue (a*(b*r))) (normValue (a*(b*r)))
    hT hZ hCs hthreshold hscale hN.le (tripleFourier a b r ha hb hr χa χb G)
    (tripleFourier_norm_le_full a b r ha hb hr χa χb G hG)
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (div_pos hk hN)]
  apply (mul_le_mul_of_nonneg_left hh (div_pos hk hN).le).trans_eq
  field_simp

def canonicalDiscardedTerm (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

theorem canonical_kernel_scale (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (E : Finset (CommonIndex I J)) (K : ℝ) :
    (K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/
      normValue (residualGenerator I J*(residualGenerator J I*activeConductor I J)) =
      K/((Ideal.absNorm (∏ P∈E,P.val):ℝ)*(Ideal.absNorm (Ideal.span {activeConductor I J}):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart I J):ℝ)*
        (Ideal.absNorm (CenteredMomentCompleteCommon.residualPart J I):ℝ)) := by
  rw [normValue_mul,normValue_mul]
  unfold normValue
  rw [primeSubsetGenerator,span_idealGenerator,residualGenerator_span I J hI,residualGenerator_span J I hJ,div_div]
  congr 1
  ring

theorem canonical_discarded_term_bound (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (E : Finset (CommonIndex I J)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ ≤
      K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := scaled_discarded_triple_bound A
  refine ⟨s,C,hC,?_⟩
  intro W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  have he : e≠0 := primeSubsetGenerator_ne_zero _ _
  have hE : (∏ P∈E,P.val)≠(0:Ideal O) := by
    have hh := Ideal.span_singleton_eq_bot.not.mpr he
    simpa only [e,primeSubsetGenerator,span_idealGenerator,Ideal.zero_eq_bot] using hh
  have hNe : 0<normValue e := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)
  have hNe1 : 1≤normValue e := by
    change (1:ℝ)≤(Ideal.absNorm (Ideal.span {e}):ℝ)
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr he))
  have hk := div_pos hK hNe
  have hkK : K/normValue e≤K := div_le_self hK.le hNe1
  have hT := (firstNominalScale_pos I J _ hE K X hK hX).trans_le hsec
  have hscale := actual_first_kernel_reference I J _ hI.1 hJ.1 hE K X HN Tsec hK hX hi hj hsec
  rw [← canonical_kernel_scale I J hI hJ E K] at hscale
  have hb := ht W Tsec Z Csec HN ξ (K/normValue e) hT hZ hCs hk hthreshold
    (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
    (supported_element_ne_zero _ (residualGenerator_supported I J hI))
    (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
    (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
    (activeFunction_norm_le_one I J hI) hscale
  have hm : ‖(UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
      tripleRow (residualGenerator I J) (residualGenerator J I) (activeConductor I J)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e‖≤1 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_ideal_moebius_le_one _)).trans
      (tripleRow_norm_le_one _ _ _ (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) _ _ _ (activeFunction_norm_le_one I J hI) e)
  change ‖_ * _‖≤_
  rw [norm_mul]
  apply (mul_le_mul hm hb (norm_nonneg _) zero_le_one).trans
  rw [one_mul]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hkK (by positivity)) (by positivity)

def inactiveSubsets (I J : Ideal O) : Finset (Finset (CommonIndex I J)) :=
  (principalSupport (Finset.univ : Finset (CommonIndex I J)) (leftExponent I J) (rightExponent I J)).powerset

theorem inactiveSubsets_card (I J : Ideal O) :
    (inactiveSubsets I J).card≤2^(primeSupport I).card := by
  rw [inactiveSubsets,Finset.card_powerset]
  apply Nat.pow_le_pow_right (by norm_num)
  calc
    _ ≤ (Finset.univ : Finset (CommonIndex I J)).card := Finset.card_le_card (Finset.subset_univ _)
    _ = (commonSupport I J).card := by simp [CommonIndex]
    _ ≤ _ := Finset.card_le_card Finset.inter_subset_left

def canonicalDiscardedPair (I J : Ideal O)
    (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ

theorem canonical_discarded_pair_bound (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (W : 𝓢(ℝ,ℂ)) (I J : Ideal O)
        (hI : CanonicalQuadraticSieve.Supported I) (hJ : CanonicalQuadraticSieve.Supported J)
        (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (Ideal.absNorm I:ℝ)≤Real.exp HN*X → (Ideal.absNorm J:ℝ)≤Real.exp HN*X →
      (∀ E∈inactiveSubsets I J,firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖canonicalDiscardedPair I J hI hJ W K Tsec Z ξ‖ ≤
      (Ideal.absNorm I:ℝ)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_term_bound A
  obtain ⟨D,hD,hsub⟩ := SquarefreeDivisorBound.prime_support_subsets_bound ε hε
  refine ⟨s,D*C,mul_pos hD hC,?_⟩
  intro W I J hI hJ K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj hsec hthreshold
  have hc : ((inactiveSubsets I J).card:ℝ)≤D*(Ideal.absNorm I:ℝ)^ε := by
    apply le_trans _ (hsub I hI.1)
    exact_mod_cast inactiveSubsets_card I J
  calc
    _ ≤ ∑ E∈inactiveSubsets I J,‖canonicalDiscardedTerm I J hI hJ E W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ _E∈inactiveSubsets I J,
        K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A) :=
      Finset.sum_le_sum (fun E hE => ht W I J hI hJ E K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec E hE) hthreshold)
    _ = ((inactiveSubsets I J).card:ℝ)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) := by simp
    _ ≤ (D*(Ideal.absNorm I:ℝ)^ε)*
        (K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^A)) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

end SevenEighths.CenteredMomentFirstDiscardedEnergy

end

end OAI
end OAIOriginalModule1673

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstTailAggregate
Source SHA256: 2a29ebe0b240ae84d3df4a987ebfbcbda7cc1ec8b2163e1f2a9fc981e7c80a24
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1674



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstTailAggregate
open ActualEisensteinCubic HeckeFamily CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentFirstDiscardedEnergy CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentSourceRow CenteredMomentHeckeExpansion CenteredMomentTwist
local notation "O" => ActualEisensteinCubic.O

theorem rowWeight_norm_le_one (η : Character) (m A z : O) (t : ℝ)
    (I : Ideal O) (hI : I≠0) : ‖rowWeight η m A z t I‖≤1 := by
  have hp := norm_real_imaginary_power (Ideal.absNorm I:ℝ) t (norm_pos I hI)
  norm_cast at hp
  change ‖(idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)‖≤1
  rw [norm_mul,norm_mul,hp,mul_one]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (idealCoeff_norm_le_one η I)).trans (idealRowHom_norm _ _)

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

theorem discarded_energy_bound (Adec : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ),0<C ∧
      ∀ (η : Character) (m A : O) (t : ℝ) (S : Finset (Ideal O))
        (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X HN Tsec Z Csec ξ : ℝ),
      0<K → 0<X → 1<Z → 1≤Csec →
      (∀ I∈S,(Ideal.absNorm I:ℝ)≤Real.exp HN*X) →
      (∀ I : supportedColumns S,∀ J : supportedColumns S,∀ E∈inactiveSubsets I J,
        firstNominalScale I J (∏ P∈E,P.val) K X≤Tsec) →
      (2*HN/Real.log Z+Real.log (4*Csec)/Real.log Z<ξ/4) →
      ‖discardedEnergy η m A t S c W K Tsec Z ξ‖ ≤
      (∑ I∈S,‖c I‖)^2*(Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec) := by
  obtain ⟨s,C,hC,ht⟩ := canonical_discarded_pair_bound Adec ε hε
  refine ⟨s,C,hC,?_⟩
  intro η m A t S c W K X HN Tsec Z Csec ξ hK hX hZ hCs hN hsec hthreshold
  let B := (Real.exp HN*X)^ε*K*(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 (kernelReference Tsec HN))^2*(1+Z^(ξ/4))^Adec)
  have hB : 0≤B := by dsimp only [B];positivity
  have hpair (I J : supportedColumns S) :
      ‖canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖≤B := by
    have hi := hN I (Finset.mem_filter.mp I.property).1
    have hj := hN J (Finset.mem_filter.mp J.property).1
    apply (ht W I J (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
      K X HN Tsec Z Csec ξ hK hX hZ hCs hi hj (hsec I J) hthreshold).trans
    apply div_le_div_of_nonneg_right _ (by positivity)
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (Nat.cast_nonneg _) hi hε.le) hK.le
  have hcoeff (I : supportedColumns S) : ‖c I*rowWeight η m A 1 t I‖≤‖c I‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) (rowWeight_norm_le_one η m A 1 t I (Finset.mem_filter.mp I.property).2.1)
  have hmass : (∑ I : supportedColumns S,‖c I‖)≤∑ I∈S,‖c I‖ := by
    rw [Finset.sum_coe_sort (supportedColumns S) (fun I => ‖c I‖)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _)
  have he : (∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B)=
      (∑ I : supportedColumns S,‖c I‖)^2*B := by
    rw [pow_two,Finset.sum_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.mul_sum,Finset.sum_mul]
  calc
    _ ≤ ∑ I : supportedColumns S,‖∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          canonicalDiscardedPair I J (Finset.mem_filter.mp I.property).2
            (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ‖ := norm_sum_le _ _
    _ ≤ ∑ I : supportedColumns S,∑ J : supportedColumns S,‖c I‖*‖c J‖*B := by
      apply Finset.sum_le_sum
      intro I hI
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro J hJ
      rw [norm_mul,norm_mul,norm_star]
      exact mul_le_mul (mul_le_mul (hcoeff I) (hcoeff J) (norm_nonneg _) (norm_nonneg _))
        (hpair I J) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = (∑ I : supportedColumns S,‖c I‖)^2*B := he
    _ ≤ (∑ I∈S,‖c I‖)^2*B := mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => norm_nonneg _)) hmass 2) hB
    _ = _ := by dsimp only [B];ring

end SevenEighths.CenteredMomentFirstTailAggregate

end

end OAI
end OAIOriginalModule1674

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstLocalization
Source SHA256: f862d62de682ef44c3731b043ebc330b16c2d935ed5836e6187258887ae51761
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1675



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

theorem weighted_fourier_summable (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c w : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (hw : ∀ h,‖w h‖≤1) :
    Summable (fun h : O => w h*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := paperRadialFourier_lattice_summable_norm W k hk
  simp_rw [← normValue_eq_embedding] at hs
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left B)
  intro h
  rw [norm_mul,norm_mul]
  exact mul_le_mul_of_nonneg_right
    ((mul_le_of_le_one_left (norm_nonneg _) (hw h)).trans (hc h)) (norm_nonneg _)

theorem retained_complex_norm (R q : ℝ) : ‖(retainedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (retainedWeight_nonneg R q)]
  exact (retainedWeight_bounds R q).2

theorem discarded_complex_norm (R q : ℝ) : ‖(discardedWeight R q:ℂ)‖≤1 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (discardedWeight_nonneg R q)]
  exact (discardedWeight_bounds R q).2

theorem lattice_fourier_split (W : 𝓢(ℝ,ℂ)) (k : ℝ) (hk : 0<k)
    (c : O → ℂ) (B : ℝ) (hc : ∀ h,‖c h‖≤B) (R : ℝ) :
    (∑' h : O,c h*paperRadialFourier W (k*normValue h))=
      c 0*paperRadialFourier W 0+
        (∑' h : O,(retainedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h))+
        (∑' h : O,(discardedWeight R (normValue h):ℂ)*c h*paperRadialFourier W (k*normValue h)) := by
  have hs := weighted_fourier_summable W k hk c (fun _ => 1) B hc (by simp)
  simp only [one_mul] at hs
  have hr := weighted_fourier_summable W k hk c (fun h => (retainedWeight R (normValue h):ℂ)) B hc
    (fun h => retained_complex_norm R _)
  have hd := weighted_fourier_summable W k hk c (fun h => (discardedWeight R (normValue h):ℂ)) B hc
    (fun h => discarded_complex_norm R _)
  rw [hs.tsum_eq_add_tsum_ite 0]
  have hzero : normValue (0:O)=0 := by simp [normValue]
  simp only [hzero,mul_zero]
  rw [add_assoc,← hr.tsum_add hd]
  congr 1
  apply tsum_congr
  intro h
  by_cases hh : h=0
  · subst h
    simp only [ite_true,hzero,
      retainedWeight_zero_nonpos R 0 le_rfl,discardedWeight_zero_nonpos R 0 le_rfl,
      Complex.ofReal_zero,zero_mul,add_zero]
  · rw [ite_eq_right hh]
    have hp : 0<normValue h := norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr hh)
    have he : (retainedWeight R (normValue h):ℂ)+(discardedWeight R (normValue h):ℂ)=1 := by
      exact_mod_cast retained_add_discarded R (normValue h) hp
    rw [← add_mul,← add_mul,he,one_mul]

def canonicalRetainedTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*∑' h : O,
      (retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*
        tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
          (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
          (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) h*
        paperRadialFourier W ((k/normValue (a*(b*r)))*normValue h))

def canonicalZeroTerm (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (E : Finset (CommonIndex I J)) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  let k := K/normValue e
  (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e*
    (((k/normValue (a*(b*r)):ℝ):ℂ)*
      (tripleFourier a b r (supported_element_ne_zero _ (residualGenerator_supported I J hI))
        (supported_element_ne_zero _ (residualGenerator_supported J I hJ)) (finitePrimeModulus_ne_zero _)
        (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) 0*paperRadialFourier W 0))

def canonicalRetainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K Tsec Z ξ

def canonicalZeroPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalZeroTerm I J hI hJ E W K

theorem reducedFirstSum_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      canonicalRetainedPair I J hI hJ W K Tsec Z ξ+canonicalDiscardedPair I J hI hJ W K Tsec Z ξ := by
  unfold reducedFirstSum canonicalZeroPair canonicalRetainedPair canonicalDiscardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K Tsec Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalRetainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K Tsec Z ξ

def zeroEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      canonicalZeroPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K

theorem finiteHeckeEnergy_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K Tsec Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K Tsec Z ξ+
        discardedEnergy η m A t S c W K Tsec Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_split _ _ _ _ W K Tsec Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstLocalization

end

end OAI
end OAIOriginalModule1675

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSectorLocalization
Source SHA256: a916b81173bd4adfc360250cd735bc841545ed7e213781ba678afcabbc652293
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1676


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.CenteredMomentFirstSectorLocalization
open ActualEisensteinCubic ConcreteTraceCRT EisensteinSchwartzPoisson
open CenteredMomentFirstDiscardedEnergy CenteredMomentSectorLocalization CenteredMomentFirstScale
open CenteredMomentCanonicalFirst CenteredMomentFirstReduced CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentSourceRow CenteredMomentFirstTailAggregate
open CanonicalQuadraticSieve HeckeFamily CenteredMomentHeckeExpansion CenteredMomentFirstEnergy
local notation "O" => ActualEisensteinCubic.O

open CenteredMomentFirstLocalization

def retainedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalRetainedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

def discardedPair (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ E∈inactiveSubsets I J,canonicalDiscardedTerm I J hI hJ E W K
    (firstNominalScale I J (∏ P∈E,P.val) K X) Z ξ

theorem reducedFirstSum_sector_split (I J : Ideal O) (hI : Supported I) (hJ : Supported J)
    (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) (hK : 0<K) :
    reducedFirstSum I J hI hJ W K=canonicalZeroPair I J hI hJ W K+
      retainedPair I J hI hJ W K X Z ξ+discardedPair I J hI hJ W K X Z ξ := by
  unfold reducedFirstSum canonicalZeroPair retainedPair discardedPair
  rw [← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  let Tsec:=firstNominalScale I J (∏ P∈E,P.val) K X
  dsimp only [canonicalZeroTerm,canonicalRetainedTerm,canonicalDiscardedTerm]
  simp_rw [← normValue_eq_embedding]
  let a := residualGenerator I J
  let b := residualGenerator J I
  let r := activeConductor I J
  have ha : a≠0 := supported_element_ne_zero _ (residualGenerator_supported I J hI)
  have hb : b≠0 := supported_element_ne_zero _ (residualGenerator_supported J I hJ)
  have hr : r≠0 := finitePrimeModulus_ne_zero _
  have he : primeSubsetGenerator (fun P : CommonIndex I J => P.val) E≠0 := primeSubsetGenerator_ne_zero _ _
  have hk : 0<(K/normValue (primeSubsetGenerator (fun P : CommonIndex I J => P.val) E))/normValue (a*(b*r)) :=
    div_pos (div_pos hK (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr he)))
      (norm_pos _ (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero ha (mul_ne_zero hb hr))))
  have hh := lattice_fourier_split W _ hk
    (tripleFourier a b r ha hb hr (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI))
    (normValue (a*(b*r)))
    (tripleFourier_norm_le_full a b r ha hb hr _ _ _ (activeFunction_norm_le_one I J hI))
    (frequencyRadius Tsec Z ξ)
  let e := primeSubsetGenerator (fun P : CommonIndex I J => P.val) E
  let k := (K/normValue e)/normValue (a*(b*r))
  let F := tripleFourier a b r ha hb hr (residualCharacter I J hI)
    (residualCharacter J I hJ)⁻¹ (activeFunction I J hI)
  let d := (UniqueFactorizationMonoid.moebius (∏ P∈E,P.val):ℂ)*
    tripleRow a b r (residualCharacter I J hI) (residualCharacter J I hJ)⁻¹ (activeFunction I J hI) e
  change d*((k:ℂ)*∑' h : O,F h*paperRadialFourier W ((K/normValue e)*normValue h/normValue (a*(b*r))))=
    d*((k:ℂ)*(F 0*paperRadialFourier W 0))+
      d*((k:ℂ)*∑' h : O,(retainedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))+
      d*((k:ℂ)*∑' h : O,(discardedWeight (frequencyRadius Tsec Z ξ) (normValue h):ℂ)*F h*paperRadialFourier W (k*normValue h))
  have heq (h : O) : (K/normValue e)*normValue h/normValue (a*(b*r))=k*normValue h := by dsimp [k];ring
  simp_rw [heq]
  rw [hh]
  ring

def retainedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      retainedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

def discardedEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K X Z ξ : ℝ) : ℂ :=
  ∑ I : supportedColumns S,∑ J : supportedColumns S,
    ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
      discardedPair I J (Finset.mem_filter.mp I.property).2
        (Finset.mem_filter.mp J.property).2 W K X Z ξ

theorem finiteHeckeEnergy_sector_localized (η : Character) (m A : O) (t : ℝ)
    (hmLam : ConcretePrimeRowBridge.goodLambda∣m) (hm2 : (2:O)∣m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ))
    (K X Z ξ : ℝ) (hK : 0<K) :
    finiteHeckeEnergy η m A t S c W K=
      zeroEnergy η m A t S c W K+retainedEnergy η m A t S c W K X Z ξ+
        discardedEnergy η m A t S c W K X Z ξ := by
  rw [finiteHeckeEnergy_reduced_poisson η m A t hmLam hm2 S c W K hK]
  simp_rw [reducedFirstSum_sector_split _ _ _ _ W K X Z ξ hK,mul_add,Finset.sum_add_distrib]
  rfl

end SevenEighths.CenteredMomentFirstSectorLocalization

end

end OAI
end OAIOriginalModule1676

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstCommonTransport
Source SHA256: 09f1238b1a21bab81f6f2047013d7c220ba8f0109f5f671f2a13b65962ad1eda
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1677



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstCommonTransport
open ActualEisensteinCubic ConcretePrimeRowBridge CanonicalQuadraticSieve
open CenteredMomentCanonicalFirst CenteredMomentCompleteCommon CenteredMomentActive
open CenteredMomentFirstSectorEnergy CompletedGauss
local notation "O"=>ActualEisensteinCubic.O

theorem extracted_support (I J:Ideal O):
    commonSupport (commonPart I J) (commonPart J I)=commonSupport I J:=by
  rw [commonSupport,commonPart_support,commonPart_support,commonSupport_comm J I,Finset.inter_self]

def commonEquiv (I J:Ideal O):CommonIndex I J ≃ CommonIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨P.val,by rw [extracted_support];exact P.property⟩
  invFun P:=⟨P.val,by rw [←extracted_support I J];exact P.property⟩
  left_inv _:=rfl
  right_inv _:=rfl

@[simp] theorem commonEquiv_val (I J:Ideal O)(P:CommonIndex I J):
    (commonEquiv I J P).val=P.val:=rfl

@[simp] theorem extracted_left (I J:Ideal O)(P:CommonIndex I J):
    leftExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=leftExponent I J P:=by
  simp only [leftExponent,commonEquiv_val,commonPart_valuation,ite_eq_left P.property]

@[simp] theorem extracted_right (I J:Ideal O)(P:CommonIndex I J):
    rightExponent (commonPart I J) (commonPart J I) (commonEquiv I J P)=rightExponent I J P:=by
  have hp:P.val∈commonSupport J I:=by rw [commonSupport_comm];exact P.property
  simp only [rightExponent,commonEquiv_val,commonPart_valuation,ite_eq_left hp]

def activeEquiv (I J:Ideal O):ActiveIndex I J ≃ ActiveIndex (commonPart I J) (commonPart J I) where
  toFun P:=⟨commonEquiv I J P.val,by
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using P.property⟩
  invFun P:=⟨(commonEquiv I J).symm P.val,by
    have hp:=P.property
    have he:(commonEquiv I J) ((commonEquiv I J).symm P.val)=P.val:=(commonEquiv I J).apply_symm_apply _
    rw [←he] at hp
    simpa only [ActiveIndex,CenteredMomentActive.activeSupport,Finset.mem_filter,Finset.mem_univ,true_and,extracted_left,extracted_right]
      using hp⟩
  left_inv P:=by apply Subtype.ext;exact (commonEquiv I J).symm_apply_apply _
  right_inv P:=by apply Subtype.ext;exact (commonEquiv I J).apply_symm_apply _

@[simp] theorem activeEquiv_prime (I J:Ideal O)(P:ActiveIndex I J):
    activePrime (commonPart I J) (commonPart J I) (activeEquiv I J P)=activePrime I J P:=rfl

@[simp] theorem activeEquiv_exponent (I J:Ideal O)(P:ActiveIndex I J):
    activeExponent (commonPart I J) (commonPart J I) (activeEquiv I J P)=activeExponent I J P:=by
  change netExponent (leftExponent _ _ (commonEquiv I J P.val))
    (rightExponent _ _ (commonEquiv I J P.val))=_
  rw [extracted_left,extracted_right]
  rfl

theorem activeConductor_extracted (I J:Ideal O):
    activeConductor (commonPart I J) (commonPart J I)=activeConductor I J:=by
  unfold activeConductor finitePrimeModulus
  congr 1
  exact (Fintype.prod_equiv (activeEquiv I J) _ _ (fun P=>by rw [activeEquiv_prime])).symm

theorem activeRow_extracted (I J:Ideal O)(hI:Supported I)(z:O):
    finiteSexticRow (activePrime (commonPart I J) (commonPart J I))
      (activeGood _ _ (commonPart_supported I J hI))
      (activeExponent (commonPart I J) (commonPart J I)) z=
    finiteSexticRow (activePrime I J) (activeGood I J hI) (activeExponent I J) z:=by
  unfold finiteSexticRow
  apply (Fintype.prod_equiv (activeEquiv I J) _ _ ?_).symm
  intro P
  rw [activeEquiv_exponent]
  rfl

theorem activeFunction_mk_extracted (I J:Ideal O)(hI:Supported I)(z:O):
