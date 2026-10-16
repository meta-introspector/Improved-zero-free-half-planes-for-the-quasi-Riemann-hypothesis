open CenteredMomentHeckeExpansion CenteredMomentHeckeColumnWindow CenteredMomentChildRows
open CenteredMomentSourceRow CenteredMomentSourceLiveColumn CenteredMomentAmplificationLiveMask
open CenteredMomentAddedZeroUniform CenteredMomentSourceProfileMass CenteredMomentSourceMass
open CenteredMomentCommonAllocationSum
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι]
local instance : DecidableEq (ι ⊕ Fin 2) := Classical.decEq _

theorem original_errors_to_children (η : Character) (m p : O)
    (hm : m≠0) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hPid : Prime (Ideal.span {p})) (hs : Supported (Ideal.span {p}))
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p})≠2)
    (hpp : goodLambda^2 ∣ p-1) (hmLam : goodLambda∣m) (hm2 : (2:O)∣m)
    (n : ℕ) (hn : n=0 ∨ n=5 ∨ n=6) :
    ∃ τ : RayCharacter → Character,
      (∀ χ,(τ χ).modulus.absNorm≤rowConductorBound (childCharacter η χ) m 1 (p^(2*errorMovingExponent n))) ∧
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

end SevenEighths.CenteredMomentAmplificationOriginalErrors

end

end OAI
end OAIOriginalModule1981

/-! Original module: OAI.NumberTheory.DirichletL.TraceCharacter
Source SHA256: 4589b073e682eaf08d284c02447ad938c1197c7f3879a06674886a1890cb2703
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1982



namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap

namespace SevenEighths.TraceCharacter

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT
open EisensteinSchwartzPoisson FiniteFourier

def traceCharacter (c : O) (hc : c ≠ 0) : AddChar (O ⧸ Ideal.span {c}) ℂ :=
  eisTraceModChar ShortDraftTrace.breveE
    ConcreteBreveE.breveE_period_coordinates c hc

theorem traceCharacter_mk (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      ShortDraftTrace.breveE (eisEmbedding x / (eisEmbedding c * eisLam)) := by
  simp only [traceCharacter, eisTraceModChar, IdealGaussCRT.traceModChar_mk]

theorem traceCharacter_eq_paperE (c : O) (hc : c ≠ 0) (x : O) :
    traceCharacter c hc (Ideal.Quotient.mk (Ideal.span {c}) x) =
      paperE (eisEmbedding x / eisEmbedding c) :=
  eisTraceModChar_eq_paperE c hc x

theorem traceCharacter_isPrimitive (c : O) (hc : c ≠ 0) :
    (traceCharacter c hc).IsPrimitive :=
  GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive c hc

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem residue_card :
    Fintype.card (O ⧸ Ideal.span {c}) = Ideal.absNorm (Ideal.span {c}) := by
  simp only [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

def gaussScalar (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussSum χ (traceCharacter c (NeZero.ne c))

theorem transform_nonunit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) (ha : ¬ IsUnit a) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) = 0 :=
  gaussSum_mulShift_nonunit_eq_zero χ hχ (traceCharacter c (NeZero.ne c)) ha

theorem transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    (∑ x : O ⧸ Ideal.span {c}, χ x * traceCharacter c (NeZero.ne c) (a * x)) =
      χ⁻¹ a * gaussScalar c χ :=
  transform_primitive_character χ hχ (traceCharacter c (NeZero.ne c)) a

theorem paper_transform_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (h : O) :
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      paperE (eisEmbedding (GaussianShiftedPartition.representative c x) *
        eisEmbedding h / eisEmbedding c)) =
      χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) * gaussScalar c χ := by
  simpa only [traceCharacter, eisTraceModChar_frequency] using
    transform_eq c χ hχ (Ideal.Quotient.mk (Ideal.span {c}) h)

theorem gaussScalar_norm_sq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ ^ 2 = (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  simpa only [gaussScalar, residue_card c] using
    primitive_gaussSum_norm_sq χ hχ (traceCharacter c (NeZero.ne c))
      (traceCharacter_isPrimitive c (NeZero.ne c))

theorem gaussScalar_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = Real.sqrt (Ideal.absNorm (Ideal.span {c}) : ℝ) := by
  rw [← gaussScalar_norm_sq c χ hχ, Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_norm_embedding (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    ‖gaussScalar c χ‖ = ‖eisEmbedding c‖ := by
  rw [gaussScalar_norm c χ hχ, ← eisEmbedding_norm_sq_eq_absNorm_span,
    Real.sqrt_sq (norm_nonneg _)]

theorem gaussScalar_ne_zero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : gaussScalar c χ ≠ 0 :=
  primitive_gaussSum_ne_zero χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c))

def normalizedGauss (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ :=
  gaussScalar c χ / (‖eisEmbedding c‖ : ℂ)

theorem normalizedGauss_norm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) : ‖normalizedGauss c χ‖ = 1 := by
  rw [normalizedGauss, norm_div, gaussScalar_norm_embedding c χ hχ,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _),
    div_self (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))]

theorem character_expansion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) (a : O ⧸ Ideal.span {c}) :
    χ a = (∑ x : O ⧸ Ideal.span {c}, χ⁻¹ x * traceCharacter c (NeZero.ne c) (a * x)) /
      gaussScalar c χ⁻¹ :=
  primitive_character_expansion χ hχ (traceCharacter c (NeZero.ne c))
    (traceCharacter_isPrimitive c (NeZero.ne c)) a

theorem primitive_paper_poisson (f : 𝓢(ℂ, ℂ))
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * f (eisEmbedding z)) =
      (gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperFourier f (eisEmbedding h / eisEmbedding c) := by
  have hp := actual_eisenstein_paper_poisson_trace f c (NeZero.ne c) χ
  change _ = (1 / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperFourier f (eisEmbedding h / eisEmbedding c) at hp
  simp_rw [transform_eq c χ hχ] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_one,
    eisEmbedding_norm_sq_eq_absNorm_span, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * gaussScalar c χ / (Ideal.absNorm (Ideal.span {c}) : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / (Ideal.absNorm (Ideal.span {c}) : ℝ)) := by
  have hp := actual_radial_paper_poisson_trace W scale hscale c (NeZero.ne c) χ
  change _ = (scale / ‖eisEmbedding c‖ ^ 2 : ℝ) • ∑' h : O,
    (∑ x : O ⧸ Ideal.span {c}, χ x *
      traceCharacter c (NeZero.ne c) (Ideal.Quotient.mk (Ideal.span {c}) h * x)) *
        paperRadialFourier W
          (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) at hp
  simp_rw [transform_eq c χ hχ, eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  rw [hp, ← tsum_mul_left]
  simp only [Complex.real_smul, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

theorem primitive_radial_paper_poisson_normalized (W : 𝓢(ℝ, ℂ)) (scale : ℝ)
    (hscale : 0 < scale) (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : IsPrimitiveOnIdeals χ) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * normalizedGauss c χ / (‖eisEmbedding c‖ : ℂ)) *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          paperRadialFourier W (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding c‖ ^ 2) := by
  have hp := primitive_radial_paper_poisson c W scale hscale χ hχ
  rw [← eisEmbedding_norm_sq_eq_absNorm_span c] at hp
  have hnorm : (Ideal.absNorm (Ideal.span {c}) : ℂ) = (‖eisEmbedding c‖ : ℂ) ^ 2 := by
    exact_mod_cast (eisEmbedding_norm_sq_eq_absNorm_span c).symm
  rw [hnorm] at hp
  rw [hp]
  congr 1
  rw [normalizedGauss]
  have hn : (‖eisEmbedding c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))
  field_simp

end SevenEighths.TraceCharacter

end

end OAI
end OAIOriginalModule1982

/-! Original module: OAI.NumberTheory.DirichletL.TraceConductor
Source SHA256: 8fa161f44ec9988d35ff37ec2ebaf5e8165cc84a35c647011961fd4f6266503d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1983



namespace OAI

noncomputable section

open scoped BigOperators SchwartzMap Classical

namespace SevenEighths.TraceConductor

abbrev O := ActualEisensteinCubic.O

open FiniteFourier CharacterTransport ConcretePrimeRowBridge
open ConcreteTraceCRT EisensteinSchwartzPoisson

structure PrimitivePresentation (M : Ideal O) (χ : MulChar (O ⧸ M) ℂ) where
  generator : O
  generator_ne_zero : generator ≠ 0
  character : MulChar (O ⧸ Ideal.span {generator}) ℂ
  primitive : IsPrimitiveOnIdeals character
  modulus_le : M ≤ Ideal.span {generator}
  norm_le : Ideal.absNorm (Ideal.span {generator}) ≤ M.absNorm
  source_mask : ∀ a : O, χ (Ideal.Quotient.mk M a) =
    if IsUnit (Ideal.Quotient.mk M a) then
      character (Ideal.Quotient.mk (Ideal.span {generator}) a) else 0

theorem exists_primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : Nonempty (PrimitivePresentation M χ) := by
  let : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient hM
  obtain ⟨K, φ, hMK, hK, hφ, hnorm, hmask⟩ :=
    ConductorPresentation.exists_primitive_presentation M χ
  let c := idealGenerator K
  let e : (O ⧸ Ideal.span {c}) ≃+* (O ⧸ K) :=
    Ideal.quotEquivOfEq (span_idealGenerator K)
  let θ := pullback e φ
  refine ⟨{
    generator := c
    generator_ne_zero := idealGenerator_ne_zero K hK
    character := θ
    primitive := primitive_pullback e φ hφ
    modulus_le := ?_
    norm_le := ?_
    source_mask := ?_ }⟩
  · simpa only [c, span_idealGenerator] using hMK
  · simpa only [c, span_idealGenerator] using hnorm
  · intro a
    simpa only [θ, pullback_apply, e, Ideal.quotEquivOfEq_mk] using hmask a

def primitivePresentation (M : Ideal O) (hM : M ≠ ⊥)
    (χ : MulChar (O ⧸ M) ℂ) : PrimitivePresentation M χ :=
  Classical.choice (exists_primitivePresentation M hM χ)

namespace PrimitivePresentation

variable {M : Ideal O} {χ : MulChar (O ⧸ M) ℂ}

def conductor (P : PrimitivePresentation M χ) : Ideal O := Ideal.span {P.generator}

theorem conductor_ne_bot (P : PrimitivePresentation M χ) : P.conductor ≠ ⊥ := by
  intro h
  exact P.generator_ne_zero (Ideal.span_singleton_eq_bot.mp h)

def gauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar P.generator P.character

theorem gauss_norm (P : PrimitivePresentation M χ) :
    ‖P.gauss‖ = Real.sqrt (P.conductor.absNorm : ℝ) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_norm P.generator P.character P.primitive

theorem gauss_ne_zero (P : PrimitivePresentation M χ) : P.gauss ≠ 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.gaussScalar_ne_zero P.generator P.character P.primitive

def fourier (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) : ℂ := by
  let : Finite (O ⧸ Ideal.span {P.generator}) := finite_quotient_span P.generator_ne_zero
  let : Fintype (O ⧸ Ideal.span {P.generator}) := Fintype.ofFinite _
  exact transform (TraceCharacter.traceCharacter P.generator P.generator_ne_zero) P.character a

theorem fourier_eq (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor) :
    P.fourier a = P.character⁻¹ a * P.gauss := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_eq P.generator P.character P.primitive a

theorem fourier_nonunit (P : PrimitivePresentation M χ) (a : O ⧸ P.conductor)
    (ha : ¬ IsUnit a) : P.fourier a = 0 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.transform_nonunit P.generator P.character P.primitive a ha

theorem source_sum_eq_masked (P : PrimitivePresentation M χ) (f : O → ℂ) :
    (∑' a : O, χ (Ideal.Quotient.mk M a) * f a) =
      ∑' a : O, (if IsUnit (Ideal.Quotient.mk M a) then
        P.character (Ideal.Quotient.mk P.conductor a) else 0) * f a := by
  apply tsum_congr
  intro a
  rw [P.source_mask]
  rfl

def normalizedGauss (P : PrimitivePresentation M χ) : ℂ := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss P.generator P.character

theorem normalizedGauss_norm (P : PrimitivePresentation M χ) :
    ‖P.normalizedGauss‖ = 1 := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.normalizedGauss_norm P.generator P.character P.primitive

theorem paper_poisson (P : PrimitivePresentation M χ) (f : 𝓢(ℂ, ℂ)) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) * f (eisEmbedding z)) =
      (P.gauss / (P.conductor.absNorm : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperFourier f (eisEmbedding h / eisEmbedding P.generator) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_paper_poisson P.generator f P.character P.primitive

theorem radial_paper_poisson (P : PrimitivePresentation M χ)
    (W : 𝓢(ℝ, ℂ)) (scale : ℝ) (hscale : 0 < scale) :
    (∑' z : O, P.character (Ideal.Quotient.mk P.conductor z) *
      W (‖eisEmbedding z‖ ^ 2 / scale)) =
      ((scale : ℂ) * P.normalizedGauss / (‖eisEmbedding P.generator‖ : ℂ)) *
        ∑' h : O, P.character⁻¹ (Ideal.Quotient.mk P.conductor h) *
          paperRadialFourier W
            (scale * ‖eisEmbedding h‖ ^ 2 / ‖eisEmbedding P.generator‖ ^ 2) := by
  let : NeZero P.generator := ⟨P.generator_ne_zero⟩
  exact TraceCharacter.primitive_radial_paper_poisson_normalized
    P.generator W scale hscale P.character P.primitive

end PrimitivePresentation

end SevenEighths.TraceConductor

end

end OAI
end OAIOriginalModule1983

/-! Original module: OAI.NumberTheory.DirichletL.GaussianTheta
Source SHA256: ae3496a86f536df3c5eb068eb006818cfe15c1de183946de06b1b46a250d1e8f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1984



namespace OAI

noncomputable section

open scoped BigOperators Classical FourierTransform

namespace SevenEighths.GaussianTheta

abbrev O := ActualEisensteinCubic.O

open ActualEisensteinCubic EisensteinEmbedding ConcreteTraceCRT EisensteinSchwartzPoisson

def gaussian (a : ℝ) (z : ℂ) : ℂ :=
  Complex.exp (-(Real.pi : ℂ) * (a : ℂ) * (‖z‖ : ℂ) ^ 2)

def coordinate (x y : ℝ) : ℂ := (x : ℂ) + (y : ℂ) * omega3

theorem omega3_re : omega3.re = -(1 / 2 : ℝ) := by norm_num [omega3]

theorem coordinate_norm_sq (x y : ℝ) :
    ‖coordinate x y‖ ^ 2 = RankTwoEisShift.Q x y := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [coordinate, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, omega3_re, omega3_im, zero_mul, zero_add,
    add_zero, sub_zero]
  unfold RankTwoEisShift.Q
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]

theorem exists_coordinate (w : ℂ) : ∃ x y : ℝ, w = coordinate x y := by
  let v := (basisEquiv omega3 omega3_im_ne_zero).symm w
  refine ⟨v.re, v.im, ?_⟩
  have h := (basisEquiv omega3 omega3_im_ne_zero).apply_symm_apply w
  simpa only [basisEquiv_apply, coordinate, mul_comm] using h.symm

theorem coordinate_dual_phase (x y : ℝ) (p : ℤ × ℤ) :
    paperE (coordinate x y * eisEmbedding (dualFrequencyEquiv p)) =
      RankTwoEisShift.dualPhase p.1 p.2 x y := by
  rw [paperE_eq_exp, dualFrequencyEquiv_coordinates]
  simp only [coordinate, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, omega3_re, omega3_im,
    zero_mul, zero_add, add_zero, sub_zero, complexPoint]
  unfold RankTwoEisShift.dualPhase
  congr 1
  have hs : (Real.sqrt 3 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  push_cast
  field_simp
  ring

theorem gaussian_coordinate_shift (a x y : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) +
      coordinate x y) = RankTwoEisShift.shifted a x y p := by
  have he : eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y =
      coordinate ((p.1 : ℝ) + x) ((p.2 : ℝ) + y) := by
    rw [eisEmbedding_eval]
    simp only [coordinate, Complex.ofReal_add, Complex.ofReal_intCast]
    ring
  rw [he]
  unfold gaussian RankTwoEisShift.shifted
  rw [← Complex.ofReal_pow, coordinate_norm_sq]
  congr 1
  push_cast
  ring

theorem gaussian_dual_coordinate (a : ℝ) (p : ℤ × ℤ) :
    gaussian a (eisEmbedding (dualFrequencyEquiv p)) =
      Complex.exp (((-Real.pi * a * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) := by
  unfold gaussian
  rw [← Complex.ofReal_pow, dualFrequencyEquiv_norm_sq]
  unfold RankTwoPoisson.eisQ
  congr 1
  push_cast
  ring

theorem shifted_prefactor (a : ℝ) (ha : 0 < a) :
    (1 / (a : ℂ) ^ (1 / 2 : ℂ)) *
      (1 / (((3 * a / 4 : ℝ) : ℂ)) ^ (1 / 2 : ℂ)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) := by
  have h := EisensteinGaussianPrefactor.complex_eta_times_prefactor a 1 ha (by norm_num)
  simp only [mul_one] at h
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  apply (mul_left_cancel₀ ha0)
  rw [← mul_assoc, h]
  push_cast
  field_simp

theorem shifted_lattice_poisson (a : ℝ) (ha : 0 < a) (w : ℂ) :
    (∑' z : O, gaussian a (eisEmbedding z + w)) =
      ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) *
        ∑' h : O, paperE (w * eisEmbedding h) *
          gaussian (4 / (3 * a)) (eisEmbedding h) := by
  obtain ⟨x, y, rfl⟩ := exists_coordinate w
  have hp := RankTwoEisShift.shifted_eisenstein_gaussian_poisson ha x y
  rw [shifted_prefactor a ha] at hp
  change (∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p) =
    ((2 / (Real.sqrt 3 * a) : ℝ) : ℂ) * ∑' p : ℤ × ℤ,
      Complex.exp (((-Real.pi * (4 / (3 * a)) * RankTwoPoisson.eisQ (p.1, -p.2) : ℝ) : ℂ)) *
        RankTwoEisShift.dualPhase p.1 p.2 x y at hp
  calc
    _ = ∑' p : ℤ × ℤ, gaussian a
        (eisEmbedding (ActualEisensteinCoordinates.eval p.1 p.2) + coordinate x y) :=
      (latticeCoordEquiv.symm.tsum_eq _).symm
    _ = ∑' p : ℤ × ℤ, RankTwoEisShift.shifted a x y p := by
      apply tsum_congr
      exact gaussian_coordinate_shift a x y
    _ = _ := by
      rw [hp]
      congr 1
      rw [← dualFrequencyEquiv.tsum_eq]
      apply tsum_congr
      intro p
      rw [coordinate_dual_phase, gaussian_dual_coordinate]
      exact mul_comm _ _

theorem gaussian_mul (a : ℝ) (z w : ℂ) :
    gaussian a (z * w) = gaussian (a * ‖z‖ ^ 2) w := by
  unfold gaussian
  rw [norm_mul]
  congr 1
  push_cast
  ring

theorem gaussian_summable (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => gaussian a (eisEmbedding z)) := by
  exact eis_gaussian_summable ha

theorem paperE_norm (z : ℂ) : ‖paperE z‖ = 1 := by
  rw [paperE_eq_exp, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im]

theorem weighted_gaussian_summable {R : Type*} [Fintype R]
    (q : O → R) (P : R → ℂ) (a : ℝ) (ha : 0 < a) :
    Summable (fun z : O => P (q z) * gaussian a (eisEmbedding z)) := by
  let C : ℝ := ∑ r : R, ‖P r‖
  have hP (r : R) : ‖P r‖ ≤ C :=
    Finset.single_le_sum (fun r _ => norm_nonneg (P r)) (Finset.mem_univ r)
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun z => norm_nonneg _) _
    ((gaussian_summable a ha).norm.mul_left C)
  intro z
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (hP _) (norm_nonneg _)

theorem gaussian_coset_poisson (a : ℝ) (ha : 0 < a) (c : O) (hc : c ≠ 0) (r : O) :
    (∑' z : O, gaussian a (eisEmbedding (r + c * z))) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, paperE (eisEmbedding r * eisEmbedding h / eisEmbedding c) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hc' := eisEmbedding_ne_zero hc
  have hscale : 0 < a * ‖eisEmbedding c‖ ^ 2 :=
    mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr hc'))
  have he (z : O) : eisEmbedding (r + c * z) =
      eisEmbedding c * (eisEmbedding z + eisEmbedding r / eisEmbedding c) := by
    rw [map_add, map_mul]
    field_simp
    ring
  simp_rw [he, gaussian_mul]
  rw [shifted_lattice_poisson _ hscale]
  congr 1
  apply tsum_congr
  intro h
  congr 2
  ring

theorem finite_gaussian_phase_sum {R : Type*} [Fintype R]
    (a : ℝ) (ha : 0 < a) (b : R → ℂ) (P : R → ℂ) (K : ℂ) :
    (∑ r : R, P r * (K * ∑' h : O,
      paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) =
      K * ∑' h : O, (∑ r : R, P r * paperE (b r * eisEmbedding h)) *
        gaussian a (eisEmbedding h) := by
  have hs (r : R) : Summable (fun h : O =>
      P r * (paperE (b r * eisEmbedding h) * gaussian a (eisEmbedding h))) := by
    apply Summable.mul_left
    apply Summable.of_norm
    simpa only [norm_mul, paperE_norm, one_mul] using (gaussian_summable a ha).norm
  simp_rw [mul_left_comm (P _) K, ← tsum_mul_left]
  rw [← Summable.tsum_finsetSum (fun r _ => (hs r).mul_left K)]
  apply tsum_congr
  intro h
  simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]

variable (c : O) [NeZero c]

local instance residueFinite : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span (NeZero.ne c)
local instance residueFintype : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _

theorem periodic_gaussian_poisson (P : O ⧸ Ideal.span {c} → ℂ)
    (a : ℝ) (ha : 0 < a) :
    (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        ∑' h : O, (∑ r : O ⧸ Ideal.span {c}, P r *
          TraceCharacter.traceCharacter c (NeZero.ne c)
            (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  rw [GaussianAbelPartition.tsum_periodic_weighted_partition
    (Ideal.Quotient.mk (Ideal.span {c})) P (fun z => gaussian a (eisEmbedding z))
    (weighted_gaussian_summable _ P a ha)]
  have hfiber (r : O ⧸ Ideal.span {c}) :=
    GaussianFiberEquiv.fiber_tsum c (NeZero.ne c) r
      (GaussianShiftedPartition.representative c r)
      (GaussianShiftedPartition.representative_spec c r)
      (fun z => gaussian a (eisEmbedding z))
  simp_rw [hfiber, gaussian_coset_poisson a ha c (NeZero.ne c)]
  have hd : 0 < 4 / (3 * (a * ‖eisEmbedding c‖ ^ 2)) := by
    exact div_pos (by norm_num) (mul_pos (by norm_num)
      (mul_pos ha (sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))))
  have h := finite_gaussian_phase_sum (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) hd
    (fun r => eisEmbedding (GaussianShiftedPartition.representative c r) / eisEmbedding c) P
    (((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ))
  simp_rw [TraceCharacter.traceCharacter, eisTraceModChar_frequency]
  convert h using 1 <;>
    congr 1 <;> (try ext r) <;>
    simp only [div_mul_eq_mul_div]

theorem primitive_gaussian_poisson (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (a : ℝ) (ha : 0 < a) :
    (∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian a (eisEmbedding z)) =
      ((2 / (Real.sqrt 3 * (a * ‖eisEmbedding c‖ ^ 2)) : ℝ) : ℂ) *
        TraceCharacter.gaussScalar c χ *
        ∑' h : O, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) h) *
          gaussian (4 / (3 * (a * ‖eisEmbedding c‖ ^ 2))) (eisEmbedding h) := by
  have hp := periodic_gaussian_poisson c χ a ha
  simp_rw [TraceCharacter.transform_eq c χ hχ] at hp
  rw [hp]
  simp_rw [← tsum_mul_left]
  apply tsum_congr
  intro h
  ring

def parameter (t : ℝ) : ℝ := 2 * t / (Real.sqrt 3 * ‖eisEmbedding c‖)

def theta (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) : ℂ :=
  ∑' z : O, χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
    gaussian (parameter c t) (eisEmbedding z)

theorem parameter_pos (t : ℝ) (ht : 0 < t) : 0 < parameter c t := by
  unfold parameter
  exact div_pos (mul_pos (by norm_num) ht)
    (mul_pos (Real.sqrt_pos.mpr (by norm_num))
      (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))))

theorem theta_summable (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : 0 < t) :
    Summable (fun z : O => χ (Ideal.Quotient.mk (Ideal.span {c}) z) *
      gaussian (parameter c t) (eisEmbedding z)) :=
  weighted_gaussian_summable _ χ _ (parameter_pos c t ht)

theorem parameter_dual (t : ℝ) (ht : 0 < t) :
    4 / (3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) = parameter c (1 / t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp
  ring_nf
  norm_num [Real.sq_sqrt]

theorem parameter_prefactor (t : ℝ) (ht : 0 < t) :
    2 / (Real.sqrt 3 * (parameter c t * ‖eisEmbedding c‖ ^ 2)) =
      1 / (‖eisEmbedding c‖ * t) := by
  have hn : ‖eisEmbedding c‖ ≠ 0 := norm_ne_zero_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hs : Real.sqrt 3 ≠ 0 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)).ne'
  unfold parameter
  field_simp

theorem theta_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ t = (TraceCharacter.normalizedGauss c χ / (t : ℂ)) *
      theta c χ⁻¹ (1 / t) := by
  have hp := primitive_gaussian_poisson c χ hχ (parameter c t) (parameter_pos c t ht)
  rw [parameter_dual c t ht, parameter_prefactor c t ht] at hp
  change theta c χ t =
    (((1 / (‖eisEmbedding c‖ * t) : ℝ) : ℂ) * TraceCharacter.gaussScalar c χ) *
      theta c χ⁻¹ (1 / t) at hp
  rw [hp]
  congr 1
  unfold TraceCharacter.normalizedGauss
  push_cast
  ring

def constantTerm (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) : ℂ := χ 0

omit [NeZero c] in
theorem constantTerm_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) :
    constantTerm c χ = if IsUnit c then 1 else 0 := by
  unfold constantTerm
  by_cases hu : IsUnit c
  · rw [ite_eq_left hu]
    have h10 : (1 : O ⧸ Ideal.span {c}) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [Ideal.span_singleton_eq_top.mpr hu]
      trivial
    rw [← h10, map_one]
  · rw [ite_eq_right hu]
    apply MulChar.map_nonunit
    intro hz
    have h10 := (isUnit_zero_iff.mp hz).symm
    have h1 : (1 : O) ∈ Ideal.span {c} := Ideal.Quotient.eq_zero_iff_mem.mp h10
    exact hu (Ideal.span_singleton_eq_top.mp ((Ideal.eq_top_iff_one _).mpr h1))

omit [NeZero c] in
theorem theta_zero_term (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) :
    χ (Ideal.Quotient.mk (Ideal.span {c}) (0 : O)) *
      gaussian (parameter c t) (eisEmbedding 0) = constantTerm c χ := by
  simp [gaussian, constantTerm]

theorem theta_inversion (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) (ht : 0 < t) :
    theta c χ (1 / t) = (TraceCharacter.normalizedGauss c χ * (t : ℂ)) * theta c χ⁻¹ t := by
  have h := theta_functional_equation c χ hχ (1 / t) (one_div_pos.mpr ht)
  simpa only [one_div, Complex.ofReal_inv, inv_inv, div_inv_eq_mul, one_mul] using h

theorem theta_root_nonzero (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hχ : FiniteFourier.IsPrimitiveOnIdeals χ) : TraceCharacter.normalizedGauss c χ ≠ 0 := by
  have h := TraceCharacter.normalizedGauss_norm c χ hχ
  intro hz
  rw [hz, norm_zero] at h
  exact zero_ne_one h

theorem embedding_unit_norm (u : Oˣ) : ‖eisEmbedding (u : O)‖ = 1 := by
  have h := eisEmbedding_norm_sq_eq_absNorm_span (u : O)
  rw [Ideal.span_singleton_eq_top.mpr u.isUnit, Ideal.absNorm_top, Nat.cast_one] at h
  nlinarith [norm_nonneg (eisEmbedding (u : O))]

omit [NeZero c] in

theorem theta_mul_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (u : Oˣ) :
    theta c χ t = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
  have h := u.mulLeft.tsum_eq (fun z : O =>
    χ (Ideal.Quotient.mk (Ideal.span {c}) z) * gaussian (parameter c t) (eisEmbedding z))
  calc
    theta c χ t = ∑' z : O,
        χ (Ideal.Quotient.mk (Ideal.span {c}) ((u : O) * z)) *
          gaussian (parameter c t) (eisEmbedding ((u : O) * z)) := h.symm
    _ = χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) * theta c χ t := by
      rw [theta, ← tsum_mul_left]
      apply tsum_congr
      intro z
      simp only [map_mul, gaussian, norm_mul, embedding_unit_norm, one_mul, mul_assoc]

omit [NeZero c] in

theorem theta_eq_zero_of_global_unit (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ)
    (u : Oˣ) (hu : χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) ≠ 1) :
    theta c χ t = 0 :=
  eq_zero_of_mul_eq_self_left hu (theta_mul_global_unit c χ t u).symm

omit [NeZero c] in
theorem global_unit_invariant_of_theta_ne_zero
    (χ : MulChar (O ⧸ Ideal.span {c}) ℂ) (t : ℝ) (ht : theta c χ t ≠ 0) :
    ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  by_contra hu
  exact ht (theta_eq_zero_of_global_unit c χ t u hu)

end SevenEighths.GaussianTheta

end

end OAI
end OAIOriginalModule1984

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Primitive
Source SHA256: 6f1f8df20ee09e62dcafc8cbcd966761d0114302684965732159fb570902a7c6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1985





namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.HeckePrimitive
open HeckeFamily

variable (c : O) [NeZero c]

private theorem span_ne_bot : Ideal.span ({c} : Set O) ≠ ⊥ := by
  simpa only [ne_eq, Ideal.span_singleton_eq_bot] using NeZero.ne c

private instance : Fintype (O ⧸ Ideal.span {c}) := by
  letI : Finite (O ⧸ Ideal.span {c}) := Ring.HasFiniteQuotients.finiteQuotient (span_ne_bot c)
  exact Fintype.ofFinite _

def character (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) : Character :=
  Character.ofResidue (Ideal.span {c}) (span_ne_bot c) χ hu

omit [NeZero c] in
theorem inverse_unit_trivial (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) :
    ∀ u : Oˣ, χ⁻¹ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1 := by
  intro u
  rw [MulChar.inv_apply_eq_inv', hu, inv_one]

def scale : ℝ := GaussianTheta.parameter c 1

theorem scale_pos : 0 < scale c := GaussianTheta.parameter_pos c 1 zero_lt_one

omit [NeZero c] in
theorem parameter_eq_scale_mul (t : ℝ) : GaussianTheta.parameter c t = scale c * t := by
  unfold scale GaussianTheta.parameter
  ring

theorem gaussianTheta_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1) (t : ℝ) :
    GaussianTheta.theta c χ t = HeckeTheta.theta (coefficients (character c χ hu))
      (scale c * t) := by
  unfold GaussianTheta.theta HeckeTheta.theta
  rw [← coordinateEquiv.tsum_eq]
  apply tsum_congr
  intro n
  rw [periodicCoeff_eq_elementCoeff]
  change χ (Ideal.Quotient.mk (Ideal.span {c}) (coordinateElement n.1 n.2)) *
      GaussianTheta.gaussian (GaussianTheta.parameter c t)
        (ConcreteTraceCRT.eisEmbedding (coordinateElement n.1 n.2)) = _
  congr 1
  unfold GaussianTheta.gaussian
  rw [Complex.ofReal_exp]
  congr 1
  rw [← Complex.ofReal_pow, ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span,
    ← normForm_eq_absNorm_span, parameter_eq_scale_mul]
  push_cast
  ring

def pair (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) : WeakFEPair ℂ :=
  PeriodicThetaRegularity.primitivePair
    (coefficients (character c χ hu))
    (coefficients (character c χ⁻¹ (inverse_unit_trivial c χ hu)))
    (scale c) (scale_pos c) (TraceCharacter.normalizedGauss c χ)
    (GaussianTheta.theta_root_nonzero c χ hp) (by
      intro t ht
      have h := GaussianTheta.theta_inversion c χ hp t ht
      rw [gaussianTheta_eq c χ hu,
        gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu)] at h
      simpa only [mul_one_div] using h)

@[simp] theorem pair_f (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).f t = GaussianTheta.theta c χ t :=
  (gaussianTheta_eq c χ hu t).symm

@[simp] theorem pair_g (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (t : ℝ) :
    (pair c χ hu hp).g t = GaussianTheta.theta c χ⁻¹ t :=
  (gaussianTheta_eq c χ⁻¹ (inverse_unit_trivial c χ hu) t).symm

def completedL (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (s : ℂ) : ℂ :=
  (pair c χ hu hp).Λ s / 6

theorem pair_completed_eq_right (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (hs : 1 < s.re) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s := by
  let w := coefficients (character c χ hu)
  have h := (pair c χ hu hp).hasMellin hs
  calc
    (pair c χ hu hp).Λ s =
        mellin (fun t => HeckeTheta.theta w (scale c * t) - w (0,0)) s := h.2.symm
    _ = (scale c : ℂ) ^ (-s) * mellin (fun t => HeckeTheta.theta w t - w (0,0)) s :=
      by simpa only [smul_eq_mul] using
        mellin_comp_mul_left (fun t => HeckeTheta.theta w t - w (0,0)) s (scale_pos c)
    _ = (scale c : ℂ) ^ (-s) * HeckeTheta.completed w s := by
      congr 1
      rw [← (HeckeTheta.pair_hasMellin w hs).2]
      unfold mellin
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro t ht
      dsimp only
      rw [HeckeTheta.theta_eq_pair w ht, HeckeTheta.pair_f₀]

theorem pair_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).Λ s = (scale c : ℂ) ^ (-s) *
      HeckeTheta.completed (coefficients (character c χ hu)) s :=
  HeckeMellinIdentity.scaled_eq (pair c χ hu hp)
    (HeckeTheta.pair (coefficients (character c χ hu))) rfl (HeckeTheta.pair_k _)
    (scale c) (scale_pos c) (fun _ hs => pair_completed_eq_right c χ hu hp hs) h0 h1

theorem symm_completed_eq (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    (pair c χ hu hp).symm.Λ s =
      (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv).Λ s := by
  apply HeckeMellinIdentity.eq_of_f (pair c χ hu hp).symm
    (pair c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv) rfl rfl _ rfl h0 h1
  intro t _
  change (pair c χ hu hp).g t = _
  rw [pair_g, pair_f]

theorem completedL_functional_equation (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ} (h0 : s ≠ 0) (h1 : s ≠ 1) :
    completedL c χ hu hp (1-s) = TraceCharacter.normalizedGauss c χ *
      completedL c χ⁻¹ (inverse_unit_trivial c χ hu) hp.inv s := by
  have h := (pair c χ hu hp).functional_equation s
  change (pair c χ hu hp).Λ (1-s) = TraceCharacter.normalizedGauss c χ *
    (pair c χ hu hp).symm.Λ s at h
  rw [symm_completed_eq c χ hu hp h0 h1] at h
  unfold completedL
  rw [h]
  ring

theorem completedL_eq_gamma_mul_LFunction (χ : MulChar (O ⧸ Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) (u : O)) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) {s : ℂ}
    (h0 : s ≠ 0) (h1 : s ≠ 1) (hΓ : Complex.Gamma s ≠ 0) :
    completedL c χ hu hp s = (scale c : ℂ)^(-s) * (Real.pi : ℂ)^(-s) *
      Complex.Gamma s * LFunction (character c χ hu) s := by
  unfold completedL
  rw [pair_completed_eq c χ hu hp h0 h1]
  unfold LFunction continuedLattice HeckeTheta.latticeL
  simp only [Complex.cpow_neg]
  have hπ : (Real.pi : ℂ)^s ≠ 0 := by
    exact (Complex.cpow_eq_zero_iff _ _).not.mpr (by simp [Real.pi_ne_zero])
  field_simp

end SevenEighths.HeckePrimitive

end

end OAI
end OAIOriginalModule1985

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ComparisonReflection
Source SHA256: 54b1c132fdfedee64fd85e504d70199abd664d82bc7b93eb1197a56475c96357
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1986




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive ActualEisensteinCubic ConcreteTraceCRT
open EisensteinSchwartzPoisson ConcretePrimeRowBridge GaussGeneratorTransport
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma residue_nontrivial (c : O) (χ : MulChar (O⧸Ideal.span {c}) ℂ) (hχ : χ≠1) :
    Nontrivial (O⧸Ideal.span {c}) := by
  by_contra h
  have : Subsingleton (O⧸Ideal.span {c}) := not_nontrivial_iff_subsingleton.mp h
  apply hχ
  ext x
  have hx : x=1 := Subsingleton.elim _ _
  simp [hx]

lemma residue_zero (c : O) [NeZero c] (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1) (hχ : χ≠1) :
    elementCoeff (character c χ hu) 0=0 := by
  let := residue_nontrivial c χ hχ
  change χ (Ideal.Quotient.mk (Ideal.span {c}) 0)=0
  rw [map_zero,χ.map_zero]

theorem radial_ideal_reindex (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hzero : elementCoeff η 0=0)
    (hs : Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X))) :
    (∑' z : O,elementCoeff η z*W (‖eisEmbedding z‖^2/X))=
      6*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  have h := UnrestrictedIdealReindex.tsum_unit_invariant_of_zero
    (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) hs
    (by rw [hzero,zero_mul])
    (fun u z => by rw [elementCoeff_unit_mul,norm_eisEmbedding_unit_mul])
  rw [h]
  congr 1
  apply tsum_congr
  intro I
  rw [eisEmbedding_norm_sq_eq_absNorm_span,span_idealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator η.modulus η.residue η.unit_trivial
    I.property (span_idealGenerator I.val)).symm

lemma bounded_radial_summable (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖)) :
    Summable (fun z : O => elementCoeff η z*W (‖eisEmbedding z‖^2/X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _) _ hs
  intro z
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  let : Finite (O⧸η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O⧸η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem primitive_plain_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    (∑' I : NI,idealCoeff (character c χ hu) I.val*W ((I.val.absNorm:ℝ)/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' I : NI,idealCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) I.val*
        paperRadialFourier W ((I.val.absNorm:ℝ)/(‖eisEmbedding c‖^2/X)) := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hQ : 0<‖eisEmbedding c‖^2 := sq_pos_of_pos hc
  have hχi : χ⁻¹≠1 := inv_ne_one.mpr hχ
  have hs : Summable (fun z : O => ‖W (‖eisEmbedding z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  have hd : Summable (fun z : O => ‖paperRadialFourier W
      (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X))‖) := by
    convert paperRadialFourier_lattice_summable_norm W (X/‖eisEmbedding c‖^2) (div_pos hX hQ) using 1
    funext z
    congr 2
    field_simp
  have he := TraceCharacter.primitive_radial_paper_poisson_normalized c W X hX χ hp
  have he' : (∑' z : O,elementCoeff (character c χ hu) z*W (‖eisEmbedding z‖^2/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))*
      ∑' z : O,elementCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) z*
        paperRadialFourier W (‖eisEmbedding z‖^2/(‖eisEmbedding c‖^2/X)) := by
    change (∑' z : O,χ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖eisEmbedding z‖^2/X))=_
    rw [he]
    congr 1
    apply tsum_congr
    intro z
    congr 2
    field_simp
  rw [radial_ideal_reindex _ W X (residue_zero c χ hu hχ) (bounded_radial_summable _ W X hs),
    radial_ideal_reindex _ (paperRadialFourier W) _ (residue_zero c χ⁻¹ _ hχi)
      (bounded_radial_summable _ (paperRadialFourier W) _ hd)] at he'
  linear_combination he'/6

lemma inverse_half_power (X : ℝ) (hX : 0≤X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

theorem primitive_normalized_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (character c χ hu) false W X 0 0=
      TraceCharacter.normalizedGauss c χ*
        HeckeDyadic.polynomial (character c χ⁻¹ (inverse_unit_trivial c χ hu)) false
          (paperRadialFourier W) (‖eisEmbedding c‖^2/X) 0 0 := by
  have hc : 0<‖eisEmbedding c‖ := norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c))
  have hY : 0<‖eisEmbedding c‖^2/X := div_pos (sq_pos_of_pos hc) hX
  rw [polynomial_plain _ _ _ hX,primitive_plain_reflection c χ hu hp hχ W X hX,
    polynomial_plain _ _ _ hY]
  have hs : Real.sqrt (‖eisEmbedding c‖^2/X)=‖eisEmbedding c‖/Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hc.le]
  have hx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn : (‖eisEmbedding c‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  have hfac : (Real.sqrt X:ℂ)⁻¹*((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖eisEmbedding c‖:ℂ))=
      TraceCharacter.normalizedGauss c χ*(Real.sqrt (‖eisEmbedding c‖^2/X):ℂ)⁻¹ := by
    rw [hs,Complex.ofReal_div]
    field_simp
    rw [hsq]
  rw [←mul_assoc,hfac,mul_assoc]

theorem reflected_profile_height_control (a b : ℝ) (ha : 0<a) (A K : ℕ) :
    ∃ n : ℕ,∀ (W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀t : ℝ,∀j : ℕ,j≤K → ∀x : ℝ,0≤x →
      (1+x)^A*‖LocalLogFourier.eulerDeriv
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) j x‖≤C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  obtain ⟨n,hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDbd⟩ := hn W hs hW
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t j hj x hx
  have hsame : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext y
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t y
  have hb := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) j hj x hx
  rw [hsame] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (hDbd t) hC.le).trans_eq (by ring))
end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end OAIOriginalModule1986

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedAnnuli
Source SHA256: 4a067e3fbaad129c3fac07ed6245a5dd7084f5c99f96dbaab430f6686b5f555d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1987



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.CenteredMomentReflectedAnnuli
open Set EisensteinSchwartzPoisson CenteredMomentSectorLocalization
open CenteredMomentComparisonReflection LocalLogFourier

def logWindow (v : ℝ) : ℂ := (annulus (Real.exp v) : ℂ)

theorem logWindow_smooth : ContDiff ℝ ∞ logWindow :=
  Complex.ofRealCLM.contDiff.comp (annulus_smooth.comp Real.contDiff_exp)

theorem logWindow_support : Function.support logWindow ⊆ Icc (-Real.log 4) 0 := by
  intro v hv
  have hn : annulus (Real.exp v) ≠ 0 := by simpa [logWindow] using hv
  have hlow : 1/4 < Real.exp v := lt_of_not_ge (fun h => hn (annulus_zero_low _ h))
  have hhigh : Real.exp v < 1 := lt_of_not_ge (fun h => hn (annulus_zero_high _ h))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  constructor
  · exact (Real.exp_lt_exp.mp (hl ▸ hlow)).le
  · exact (Real.exp_lt_one_iff.mp hhigh).le

theorem logWindow_tsupport : tsupport logWindow ⊆ Icc (-Real.log 4) 0 :=
  closure_minimal logWindow_support isClosed_Icc

theorem logWindow_compact : HasCompactSupport logWindow :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc logWindow_support

def logWindowSchwartz : 𝓢(ℝ,ℂ) := logWindow_compact.toSchwartzMap logWindow_smooth

theorem logWindow_derivative_window (i : ℕ) (v : ℝ)
    (hi : ‖iteratedFDeriv ℝ i logWindow v‖ ≠ 0) :
    1/4 ≤ Real.exp v ∧ |v| ≤ Real.log 4 := by
  have hv := logWindow_tsupport (support_iteratedFDeriv_subset i (norm_ne_zero_iff.mp hi))
  have hl : Real.exp (-Real.log 4) = (1/4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0:ℝ)<4)]
    norm_num
  refine ⟨hl ▸ Real.exp_le_exp.mpr hv.1, abs_le.mpr ⟨hv.1,?_⟩⟩
  exact hv.2.trans (Real.log_nonneg (by norm_num))

theorem logWindow_derivative_bound (K : ℕ) :
    ∃ C : ℝ, 0<C ∧ ∀ i≤K, ∀v : ℝ, ‖iteratedFDeriv ℝ i logWindow v‖≤C := by
  let C := 1+∑ i∈Finset.range (K+1), SchwartzMap.seminorm ℝ 0 i logWindowSchwartz
  have hsum := Finset.sum_nonneg (s:=Finset.range (K+1))
    (fun i _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 i) logWindowSchwartz)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro i hi v
  have hb := SchwartzMap.le_seminorm' ℝ 0 i logWindowSchwartz v
  have hc := Finset.single_le_sum (s:=Finset.range (K+1))
    (f:=fun j=>SchwartzMap.seminorm ℝ 0 j logWindowSchwartz)
    (fun j _ => apply_nonneg (SchwartzMap.seminorm ℝ 0 j) logWindowSchwartz)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  change ‖iteratedDeriv i logWindowSchwartz v‖≤C
  simpa only [pow_zero, one_mul] using hb.trans (by dsimp [C];linarith)

def reflected (W : ℝ→ℂ) (t : ℝ) : ℝ→ℂ :=
  paperRadialFourier (CompletedHeight.normTwistedSource W t)

theorem reflected_smooth (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (t : ℝ) :
    ContDiffOn ℝ ∞ (reflected W t) (Ioi 0) := by
  have he : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext x
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t x
  unfold reflected
  rw [←he]
  exact paperRadialFourier_contDiffOn _

def annularProfile (F : ℝ→ℂ) (s x : ℝ) : ℂ := (annulus x:ℂ)*F (s*x)

def logProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  positiveLogProfile logWindow (reflected W t) s logWindow_compact logWindow_smooth
    (reflected_smooth W a b ha hs hW t) hs0

@[simp] theorem logProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t v : ℝ) :
    logProfile W a b ha hs hW s hs0 t v =
      annularProfile (reflected W t) s (Real.exp v) := rfl

theorem logProfile_tsupport (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W)
    (s : ℝ) (hs0 : 0<s) (t : ℝ) :
    tsupport (logProfile W a b ha hs hW s hs0 t) ⊆ Icc (-Real.log 4) 0 := by
  apply closure_minimal _ isClosed_Icc
  intro v hv
  apply logWindow_support
  intro hz
  exact hv (by change logWindow v*reflected W t (s*Real.exp v)=0;rw [hz,zero_mul])

theorem logProfile_finite_seminorm (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀s : ℝ, ∀hs0 : 0<s, ∀t : ℝ,
      H.sup (schwartzSeminormFamily ℝ ℝ ℂ) (logProfile W a b ha hs hW s hs0 t) ≤
        C*(1+‖t‖)^J/(1+s)^B := by
  let K := H.sup Prod.snd
  obtain ⟨CW,hCW,hwin⟩ := logWindow_derivative_bound K
  obtain ⟨J,hJ⟩ := reflected_profile_height_control a b ha B K
  let D := 1+∑z∈H,(Real.log 4)^z.1*
    (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)
  have hlog : 0≤Real.log 4 := Real.log_nonneg (by norm_num)
  have hD : 0<D := by
    have hn : 0≤∑z∈H,(Real.log 4)^z.1*
        (∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW) := by positivity
    dsimp [D];linarith
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hEuler⟩ := hJ W hs hW
  refine ⟨D*CF/(1/4:ℝ)^B,by positivity,?_⟩
  intro s hs0 t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hzK : z.2≤K := Finset.le_sup hz
  have hb := positive_log_uniform_seminorm logWindow (reflected W t)
    s (1/4) (Real.log 4) CW (CF*(1+‖t‖)^J) B z.2 z.1
    logWindow_compact logWindow_smooth (reflected_smooth W a b ha hs hW t)
    hs0 (by norm_num) (by norm_num) hlog hCW.le (by positivity)
    (fun i hi v => hwin i (hi.trans hzK) v)
    (fun v hv => by obtain ⟨i,hi,hn⟩:=hv;exact logWindow_derivative_window i v hn)
    (fun i hi x hx => hEuler t i (hi.trans hzK) x hx.le)
  have hd : (Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW)≤D := by
    have h := Finset.single_le_sum (s:=H)
      (f:=fun z=>(Real.log 4)^z.1*(∑i∈Finset.range (z.2+1),(z.2.choose i:ℝ)*CW))
      (fun z _ => by positivity) hz
    dsimp [D];linarith
  have hb' : (1/4:ℝ)^B*(1+s)^B*
      SchwartzMap.seminorm ℝ z.1 z.2 (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J) := by
    apply hb.trans
    rw [←Finset.sum_mul, ←mul_assoc]
    exact mul_le_mul_of_nonneg_right hd (by positivity)
  have hb'' : SchwartzMap.seminorm ℝ z.1 z.2
      (logProfile W a b ha hs hW s hs0 t) ≤
      D*(CF*(1+‖t‖)^J)/((1/4:ℝ)^B*(1+s)^B) :=
    (le_div_iff₀ (by positivity)).mpr
      (by simpa only [mul_comm, mul_left_comm, mul_assoc] using hb')
  exact hb''.trans_eq (by ring)

theorem annularProfile_support (F : ℝ→ℂ) (s : ℝ) :
    Function.support (annularProfile F s) ⊆ Icc (1/4) 1 := by
  intro x hx
  constructor
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_low x (le_of_not_ge hn)])
  · by_contra hn
    exact hx (by simp [annularProfile,annulus_zero_high x (le_of_not_ge hn)])

theorem annularProfile_zero (F : ℝ→ℂ) (s x : ℝ)
    (hx : x≤1/4 ∨ 1≤x) : annularProfile F s x=0 := by
  rcases hx with hx|hx
  · simp [annularProfile,annulus_zero_low x hx]
  · simp [annularProfile,annulus_zero_high x hx]

theorem annular_partition (F : ℝ→ℂ) (x : ℝ) (hx : 0<x) :
    (∑' n : ℤ,annularProfile F (dyadicScale n) (x/dyadicScale n))=F x := by
  have he (n : ℤ) : annularProfile F (dyadicScale n) (x/dyadicScale n)=
      (dyadicWeight n x:ℂ)*F x := by
    simp [annularProfile,dyadicWeight,mul_div_cancel₀,ne_of_gt (dyadicScale_pos n)]
  simp_rw [he]
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition x hx]
  simp

theorem normalized_annular_term (η : HeckeFamily.Character) (F : ℝ→ℂ)
    (s Y : ℝ) (hs : 0<s) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(annulus (x/s):ℂ)*F x) Y 0 0=
      (Real.sqrt s:ℂ)*HeckeDyadic.polynomial η false (annularProfile F s) (s*Y) 0 0 := by
  rw [polynomial_plain _ _ _ hY,polynomial_plain _ _ _ (mul_pos hs hY)]
  have he (x : ℝ) : (annulus ((x/Y)/s):ℂ)*F (x/Y)=
      annularProfile F s (x/(s*Y)) := by
    unfold annularProfile
    congr 2 <;> field_simp
  simp_rw [he]
  rw [Real.sqrt_mul hs.le,Complex.ofReal_mul]
  have hs' : (Real.sqrt s:ℂ)≠0 := by exact_mod_cast (ne_of_gt (Real.sqrt_pos.2 hs))
  field_simp

def annularMass (B : ℕ) (n : ℤ) : ℝ :=
  Real.sqrt (dyadicScale n)/(1+dyadicScale n)^B

theorem annularMass_nonneg (B : ℕ) (n : ℤ) : 0≤annularMass B n := by
  have hp := dyadicScale_pos n
  unfold annularMass
  positivity

lemma sqrt_nat_pow (x : ℝ) (hx : 0≤x) (j : ℕ) :
    Real.sqrt (x^j)=(Real.sqrt x)^j := by
  induction j with
  | zero => simp
  | succ j ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx j),ih,pow_succ]

theorem annularMass_lower_bound (B j : ℕ) :
    annularMass B (-(j:ℤ))≤(Real.sqrt (1/2:ℝ))^j := by
  have hx := dyadicScale_pos (-(j:ℤ))
  have hd : 1≤(1+dyadicScale (-(j:ℤ)))^B := one_le_pow₀ (by linarith)
  have he : dyadicScale (-(j:ℤ))=(1/2:ℝ)^j := by
    simp [dyadicScale,zpow_neg,inv_pow]
  calc
    annularMass B (-(j:ℤ))≤Real.sqrt (dyadicScale (-(j:ℤ))) :=
      div_le_self (Real.sqrt_nonneg _) hd
    _=(Real.sqrt (1/2:ℝ))^j := by rw [he,sqrt_nat_pow _ (by norm_num)]

theorem annularMass_upper_bound (B A j : ℕ) (hAB : A+1≤B) :
    annularMass B (j:ℤ)≤((2:ℝ)^A)⁻¹^j := by
  have hx : 1≤dyadicScale (j:ℤ) := by
    simp only [dyadicScale,zpow_natCast]
    exact one_le_pow₀ (by norm_num)
  have hp : 0<dyadicScale (j:ℤ) := dyadicScale_pos _
  have hd : dyadicScale (j:ℤ)^(A+1)≤(1+dyadicScale (j:ℤ))^B :=
    (pow_le_pow_left₀ hp.le (by linarith) _).trans
      (pow_le_pow_right₀ (by linarith) hAB)
  have hb : annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := by
    unfold annularMass
    exact div_le_div₀ hp.le (Real.sqrt_le_self_iff.mpr (Or.inr hx))
      (by positivity) hd
  calc
    annularMass B (j:ℤ)≤dyadicScale (j:ℤ)/dyadicScale (j:ℤ)^(A+1) := hb
    _=((2:ℝ)^A)⁻¹^j := by
      rw [pow_succ,mul_comm (dyadicScale (j:ℤ)^A),div_mul_cancel_left₀ (ne_of_gt hp)]
      simp only [dyadicScale,zpow_natCast,←pow_mul,inv_pow]
      rw [Nat.mul_comm]

lemma nonnegative_geometric_tail (f : ℕ→ℝ) (q : ℝ) (hq0 : 0≤q) (hq1 : q<1)
    (hf : ∀j,0≤f j) (hb : ∀j,f j≤q^j) (L : ℕ) :
    Summable (fun j=>f (j+L)) ∧ (∑'j:ℕ,f (j+L))≤q^L/(1-q) := by
  have hg : Summable (fun j:ℕ=>q^(j+L)) := by
    simpa only [pow_add] using (summable_geometric_of_lt_one hq0 hq1).mul_right (q^L)
  have hs := Summable.of_nonneg_of_le (fun j=>hf (j+L)) (fun j=>hb (j+L)) hg
  refine ⟨hs,(hs.tsum_le_tsum (fun j=>hb (j+L)) hg).trans_eq ?_⟩
  simp_rw [pow_add]
  rw [tsum_mul_right,tsum_geometric_of_lt_one hq0 hq1]
  ring

theorem annularMass_lower_tail (B L : ℕ) :
    Summable (fun j:ℕ=>annularMass B (-((j+L:ℕ):ℤ))) ∧
      (∑'j:ℕ,annularMass B (-((j+L:ℕ):ℤ)))≤
        (Real.sqrt (1/2:ℝ))^L/(1-Real.sqrt (1/2:ℝ)) := by
  apply nonnegative_geometric_tail (fun j=>annularMass B (-(j:ℤ)))
    (Real.sqrt (1/2:ℝ)) (Real.sqrt_nonneg _)
    (by simpa using (Real.sqrt_lt_sqrt (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)))
    (fun j=>annularMass_nonneg _ _) (annularMass_lower_bound B) L

theorem annularMass_upper_tail (B A L : ℕ) (hA : 1≤A) (hAB : A+1≤B) :
    Summable (fun j:ℕ=>annularMass B ((j+L:ℕ):ℤ)) ∧
      (∑'j:ℕ,annularMass B ((j+L:ℕ):ℤ))≤
        (((2:ℝ)^A)⁻¹)^L/(1-((2:ℝ)^A)⁻¹) := by
  have hp : 1<(2:ℝ)^A := by
    calc
      1<(2:ℝ)^1 := by norm_num
      _≤(2:ℝ)^A := pow_le_pow_right₀ (by norm_num) hA
  apply nonnegative_geometric_tail (fun j=>annularMass B (j:ℤ))
    ((2:ℝ)^A)⁻¹ (by positivity) (inv_lt_one_of_one_lt₀ hp)
    (fun j=>annularMass_nonneg _ _) (fun j=>annularMass_upper_bound B A j hAB) L

theorem annularMass_summable (B : ℕ) (hB : 2≤B) : Summable (annularMass B) := by
  apply Summable.of_nat_of_neg
  · simpa only [Nat.add_zero] using (annularMass_upper_tail B 1 0 (by omega) hB).1
  · simpa only [Nat.add_zero] using (annularMass_lower_tail B 0).1

theorem logProfile_dyadic_seminorm_sum (a b : ℝ) (ha : 0<a)
    (H : Finset (ℕ×ℕ)) (B : ℕ) (hB : 2≤B) :
    ∃ J : ℕ, ∀ W : ℝ→ℂ, ∀ hs : Function.support W⊆Icc a b,
      ∀hW : ContDiff ℝ ∞ W, ∃C : ℝ, 0<C ∧ ∀t : ℝ,
      Summable (fun n:ℤ=>Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)) ∧
      (∑'n:ℤ,Real.sqrt (dyadicScale n)*
        H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
          (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t))≤
        C*(1+‖t‖)^J := by
  obtain ⟨J,hJ⟩ := logProfile_finite_seminorm a b ha H B
  refine ⟨J,?_⟩
  intro W hs hW
  obtain ⟨CF,hCF,hbound⟩ := hJ W hs hW
  have hmass := annularMass_summable B hB
  have hmass0 : 0≤∑'n:ℤ,annularMass B n := tsum_nonneg (annularMass_nonneg B)
  refine ⟨CF*(1+∑'n:ℤ,annularMass B n),by positivity,?_⟩
  intro t
  let f := fun n:ℤ=>Real.sqrt (dyadicScale n)*
    H.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (logProfile W a b ha hs hW (dyadicScale n) (dyadicScale_pos n) t)
  have hf0 : ∀n,0≤f n := fun n=>
    mul_nonneg (Real.sqrt_nonneg _) (apply_nonneg _ _)
  have hb : ∀n,f n≤(CF*(1+‖t‖)^J)*annularMass B n := by
    intro n
    have h := mul_le_mul_of_nonneg_left (hbound _ (dyadicScale_pos n) t)
      (Real.sqrt_nonneg (dyadicScale n))
    exact h.trans_eq (by unfold annularMass;ring)
  have hg := hmass.mul_left (CF*(1+‖t‖)^J)
  have hf := Summable.of_nonneg_of_le hf0 hb hg
  refine ⟨hf,(hf.tsum_le_tsum hb hg).trans ?_⟩
  rw [tsum_mul_left]
  nlinarith [show 0≤CF*(1+‖t‖)^J by positivity]

end SevenEighths.CenteredMomentReflectedAnnuli

end

end OAI
end OAIOriginalModule1987

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionDeletion
Source SHA256: 1a84677ea26cd8c5d0656488bb08e6972f8204b1078f2e5707c652db06a8936a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1988



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectionDeletion
open HeckeFamily CenteredMomentComparisonReflection UniqueFactorizationMonoid
open IdealMobiusDivisorSum EisensteinSchwartzPoisson ConcreteTraceCRT
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def norm (I : NI) : ℝ := I.val.absNorm
lemma norm_pos (I : NI) : 0 < norm I := CompletedGauss.nonzeroIdeal_norm_pos I

def outside (S : Finset (Ideal O)) (I : Ideal O) : Prop := ∀ P ∈ S, ¬ P ∣ I
abbrev SmoothIdeal (S : Finset (Ideal O)) := {I : NI // primeSupport I.val ⊆ S}
abbrev OutsideIdeal (S : Finset (Ideal O)) := {I : NI // outside S I.val}

def extract (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∈ S)).prod
def residual (S : Finset (Ideal O)) (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (· ∉ S)).prod
lemma extract_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (extract S I) = (normalizedFactors I).filter (· ∈ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_factors (S : Finset (Ideal O)) (I : Ideal O) :
    normalizedFactors (residual S I) = (normalizedFactors I).filter (· ∉ S) :=
  normalizedFactors_prod_eq_self_of_subset
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma extract_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : extract S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma residual_ne_zero (S : Finset (Ideal O)) (I : Ideal O) : residual S I ≠ 0 :=
  prod_ne_zero_of_subset_normalizedFactors
    (fun _ h => (Multiset.mem_filter.mp h).1)
lemma reconstruct (S : Finset (Ideal O)) (I : NI) :
    extract S I.val * residual S I.val = I.val := by
  rw [extract, residual, ← Multiset.prod_add, Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self I.property
lemma extract_smooth (S : Finset (Ideal O)) (I : Ideal O) :
    primeSupport (extract S I) ⊆ S := by
  intro P hP
  have hh : P ∈ normalizedFactors I ∧ P ∈ S := by
    simpa only [primeSupport, extract_factors, Multiset.mem_toFinset, Multiset.mem_filter] using hP
  exact hh.2
lemma outside_iff_factors (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ normalizedFactors I.val, P ∉ S := by
  constructor
  · intro h P hP hPS
    exact h P hPS (dvd_of_mem_normalizedFactors hP)
  · intro h P hPS hd
    exact h P ((mem_normalizedFactors_iff I.property).mpr ⟨hS P hPS, hd⟩) hPS
lemma residual_outside (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : Ideal O) :
    outside S (residual S I) := by
  rw [outside_iff_factors S hS ⟨_, residual_ne_zero S I⟩, residual_factors]
  intro P hP
  exact (Multiset.mem_filter.mp hP).2
lemma split_product (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (D : SmoothIdeal S) (J : OutsideIdeal S) :
    extract S (D.val.val * J.val.val) = D.val.val ∧
      residual S (D.val.val * J.val.val) = J.val.val := by
  have hd : (normalizedFactors D.val.val).filter (· ∈ S) = normalizedFactors D.val.val :=
    Multiset.filter_eq_self.mpr (fun P hP => D.property (Multiset.mem_toFinset.mpr hP))
  have hj : (normalizedFactors J.val.val).filter (· ∈ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact (outside_iff_factors S hS J.val).mp J.property P hP
  have hd' : (normalizedFactors D.val.val).filter (· ∉ S) = 0 := by
    apply Multiset.filter_eq_nil.mpr
    intro P hP
    exact not_not.mpr (D.property (Multiset.mem_toFinset.mpr hP))
  have hj' : (normalizedFactors J.val.val).filter (· ∉ S) = normalizedFactors J.val.val :=
    Multiset.filter_eq_self.mpr ((outside_iff_factors S hS J.val).mp J.property)
  simp only [extract, residual, normalizedFactors_mul D.val.property J.val.property,
    Multiset.filter_add, hd, hj, hd', hj', add_zero, zero_add,
    Ideal.prod_normalizedFactors_eq_self D.val.property,
    Ideal.prod_normalizedFactors_eq_self J.val.property, and_self]

def splitEquiv (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    NI ≃ SmoothIdeal S × OutsideIdeal S where
  toFun I := (⟨⟨extract S I.val, extract_ne_zero S I.val⟩, extract_smooth S I.val⟩,
    ⟨⟨residual S I.val, residual_ne_zero S I.val⟩, residual_outside S hS I.val⟩)
  invFun p := ⟨p.1.val.val * p.2.val.val, mul_ne_zero p.1.val.property p.2.val.property⟩
  left_inv I := Subtype.ext (reconstruct S I)
  right_inv p := by
    obtain ⟨hd, hj⟩ := split_product S hS p.1 p.2
    exact Prod.ext (Subtype.ext (Subtype.ext hd)) (Subtype.ext (Subtype.ext hj))

lemma outside_iff_coprime (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) (I : NI) :
    outside S I.val ↔ ∀ P ∈ S, IsCoprime I.val P := by
  have he (P : Ideal O) (hP : Prime P) : primeSupport P = {P} := by
    simp only [primeSupport]
    have hf : normalizedFactors P = {P} := by
      simpa using normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
        (by intro Q hQ; simpa only [Multiset.mem_singleton.mp hQ] using hP)
    simp [hf]
  simp only [outside]
  apply forall_congr'
  intro P
  apply forall_congr'
  intro hP
  rw [← IdealCoprimeSieveOperator.primeSupport_disjoint_iff I.property (hS P hP).ne_zero,
    he P (hS P hP), Finset.disjoint_singleton_right]
  simp only [primeSupport, Multiset.mem_toFinset,
    mem_normalizedFactors_iff I.property, hS P hP, true_and]

lemma deleted_coefficient (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (I : NI) :
    idealCoeff (η.excludePrimes S hS) I.val =
      if outside S I.val then idealCoeff η I.val else 0 := by
  rw [idealCoeff_excludePrimes, outside_iff_coprime S hS I]
  split_ifs <;> rfl

def DecayTwo (F : ℝ → ℂ) : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x → x^2 * ‖F x‖ ≤ C

lemma schwartz_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo W := by
  refine ⟨SchwartzMap.seminorm ℝ 2 0 W, apply_nonneg _ _, ?_⟩
  intro x hx
  simpa only [Real.norm_eq_abs, abs_of_pos hx] using
    SchwartzMap.norm_pow_mul_le_seminorm ℝ W 2 x

lemma reflected_decayTwo (W : 𝓢(ℝ,ℂ)) : DecayTwo (paperRadialFourier W) := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_source_weighted_bound 2
  refine ⟨C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W, by positivity, ?_⟩
  intro x hx
  exact (mul_le_mul_of_nonneg_right (by nlinarith : x^2 ≤ (1+x)^2)
    (norm_nonneg _)).trans (hb W x hx.le)

lemma inverse_norm_sq_summable : Summable (fun I : NI => (norm I ^ 2)⁻¹) := by
  have h := CompletedGauss.nonzeroIdeal_norm_rpow_summable 2 (by norm_num)
  convert h using 1
  funext I
  rw [Real.rpow_neg (by positivity), Real.rpow_two]
  rfl

lemma radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun I : NI => ‖F (norm I / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  apply (inverse_norm_sq_summable.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  have hx := div_pos (norm_pos I) hX
  have h : ‖F (norm I / X)‖ ≤ C / (norm I / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma plain_summable (η : Character) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => idealCoeff η I.val * F (norm I / X)) := by
  apply Summable.of_norm
  apply (radial_summable_norm F hF X hX).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro I
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)

lemma pair_radial_summable_norm (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : NI × NI => ‖F (norm p.1 * norm p.2 / X)‖) := by
  obtain ⟨C,hC,hb⟩ := hF
  have hs := inverse_norm_sq_summable.mul_of_nonneg inverse_norm_sq_summable
    (fun I => by positivity) (fun I => by positivity)
  apply (hs.mul_left (C*X^2)).of_nonneg_of_le (fun _ => norm_nonneg _)
  intro p
  have hx := div_pos (mul_pos (norm_pos p.1) (norm_pos p.2)) hX
  have h : ‖F (norm p.1 * norm p.2 / X)‖ ≤ C / (norm p.1 * norm p.2 / X)^2 :=
    (le_div_iff₀ (sq_pos_of_pos hx)).mpr (by nlinarith [hb _ hx])
  exact h.trans_eq (by field_simp)

lemma restricted_pair_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun p : SmoothIdeal S × OutsideIdeal S =>
      idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) := by
  have hi : Function.Injective (fun p : SmoothIdeal S × OutsideIdeal S => (p.1.val,p.2.val)) := by
    intro p q h
    exact Prod.ext (Subtype.ext (congrArg Prod.fst h)) (Subtype.ext (congrArg Prod.snd h))
  apply ((pair_radial_summable_norm F hF X hX).comp_injective hi).of_norm_bounded
  intro p
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)

lemma outside_plain_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) =
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / X) := by
  have he := tsum_subtype {I : NI | outside S I.val}
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  change (∑' I : OutsideIdeal S, idealCoeff η I.val.val * F (norm I.val / X)) = _ at he
  rw [he]
  apply tsum_congr
  intro I
  rw [deleted_coefficient]
  by_cases hI : outside S I.val <;> simp [Set.indicator, hI]

lemma restoration_inner (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (D : SmoothIdeal S) :
    (∑' J : OutsideIdeal S, idealCoeff η (D.val.val * J.val.val) *
      F (norm D.val * norm J.val / X)) =
    idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  rw [← outside_plain_tsum η S hS F, ← tsum_mul_left]
  apply tsum_congr
  intro J
  rw [map_mul, mul_assoc]
  congr 2
  field_simp

lemma restoration_plain_summable (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  exact (restricted_pair_summable η S F hF X hX).prod.congr
    (fun D => restoration_inner η S hS F X D)

theorem restoration_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0 < X) :
    (∑' I : NI, idealCoeff η I.val * F (norm I / X)) =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val *
        ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val)) := by
  have he := (splitEquiv S hS).symm.tsum_eq
    (fun I : NI => idealCoeff η I.val * F (norm I / X))
  have hp := (restricted_pair_summable η S F hF X hX).tsum_prod
  have hpoint (p : SmoothIdeal S × OutsideIdeal S) :
      norm ((splitEquiv S hS).symm p) = norm p.1.val * norm p.2.val := by
    change (Ideal.absNorm (p.1.val.val * p.2.val.val) : ℝ) = _
    rw [map_mul, Nat.cast_mul]
    rfl
  simp only [hpoint] at he
  rw [← he]
  change (∑' p : SmoothIdeal S × OutsideIdeal S,
    idealCoeff η (p.1.val.val * p.2.val.val) * F (norm p.1.val * norm p.2.val / X)) = _
  rw [hp]
  exact tsum_congr (fun D => restoration_inner η S hS F X D)

lemma normalization_factor (X N : ℝ) (hX : 0<X) (hN : 0<N) :
    (Real.sqrt N : ℂ)⁻¹ * (Real.sqrt (X/N) : ℂ)⁻¹ = (Real.sqrt X : ℂ)⁻¹ := by
  rw [Real.sqrt_div hX.le, Complex.ofReal_div]
  have hn : (Real.sqrt N : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hN).ne'
  field_simp

lemma normalized_restoration_term (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X : ℝ) (hX : 0<X) (D : SmoothIdeal S) :
    idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val.val *
      ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D.val))]
  change idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
    ((Real.sqrt (X / norm D.val) : ℂ)⁻¹ *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) = _
  have h := normalization_factor X (norm D.val) hX (norm_pos D.val)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val.val *
    ∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F (norm I / (X / norm D.val))) * h

theorem normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false F X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false F (X / norm D.val) 0 0 := by
  constructor
  · apply ((restoration_plain_summable η S hS F hF X hX).mul_left (Real.sqrt X : ℂ)⁻¹).congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm
  · rw [polynomial_plain _ _ _ hX]
    change (Real.sqrt X : ℂ)⁻¹ * (∑' I : NI, idealCoeff η I.val * F (norm I / X)) = _
    rw [restoration_plain η S hS F hF X hX, ← tsum_mul_left]
    apply tsum_congr
    intro D
    exact (normalized_restoration_term η S hS F X hX D).symm

theorem reflected_normalized_restoration (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    Summable (fun D : SmoothIdeal S => idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
      HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) X 0 0 =
      ∑' D : SmoothIdeal S, idealCoeff η D.val.val / (Real.sqrt (norm D.val) : ℂ) *
        HeckeDyadic.polynomial (η.excludePrimes S hS) false (paperRadialFourier W) (X / norm D.val) 0 0 :=
  normalized_restoration η S hS _ (reflected_decayTwo W) X hX

def outsideSum (η : Character) (S : Finset (Ideal O)) (F : ℝ → ℂ) (X : ℝ) : ℂ :=
  ∑' I : NI, (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)

lemma outsideSum_summable (η : Character) (S : Finset (Ideal O))
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    Summable (fun I : NI => (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X)) := by
  apply (radial_summable_norm F hF X hX).of_norm_bounded
  intro I
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η I.val)
  · simp

lemma outside_mul_prime (S : Finset (Ideal O)) (hS : ∀ Q ∈ S, Prime Q)
    (P : Ideal O) (hP : Prime P) (hPS : P ∉ S) (I : Ideal O) :
    outside S (P*I) ↔ outside S I := by
  have hn (Q : Ideal O) (hQ : Q ∈ S) : ¬ Q ∣ P := by
    intro hd
    have he : Q = P := associated_iff_eq.mp (((hS Q hQ).dvd_prime_iff_associated hP).mp hd)
    exact hPS (he ▸ hQ)
  simp only [outside]
  apply forall_congr'
  intro Q
  apply forall_congr'
  intro hQ
  rw [(hS Q hQ).dvd_mul, not_or, and_iff_right (hn Q hQ)]

lemma prime_shift_tsum (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (X : ℝ) :
    (∑' I : NI, if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) =
    idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  let f : NI → ℂ := fun I => if P ∣ I.val then
    (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0
  let g : NI → ℂ := fun I => idealCoeff η P *
    ((if outside S I.val then idealCoeff η I.val else 0) * F (norm I / (X / (P.absNorm : ℝ))))
  let e : NI → NI := fun I => ⟨P*I.val, mul_ne_zero hP.ne_zero I.property⟩
  have he (I : NI) : f (e I) = g I := by
    have hn : norm (e I) = (P.absNorm : ℝ) * norm I := by
      simp only [norm, e, map_mul, Nat.cast_mul]
    simp only [f, e, dvd_mul_right, ite_true, outside_mul_prime S hS P hP hPS,
      map_mul, g]
    change (if outside S I.val then idealCoeff η P * idealCoeff η I.val else 0) *
      F (norm (e I) / X) = _
    rw [hn]
    by_cases ho : outside S I.val
    · simp only [ho, ite_true, mul_assoc]
      congr 2
      rw [div_div_eq_mul_div, mul_comm]
    · simp [ho]
  have hi : Function.Injective e := by
    intro I J hij
    exact Subtype.ext (mul_left_cancel₀ hP.ne_zero (congrArg Subtype.val hij))
  have hsum : (∑' I, f I) = ∑' I, g I := by
    apply tsum_eq_tsum_of_ne_zero_bij (fun I : Function.support g => e I.val)
    · exact hi.comp Subtype.val_injective
    · intro I hI
      have hd : P ∣ I.val := by
        by_contra hn
        exact hI (by simp [f, hn])
      obtain ⟨J,hJ⟩ := hd
      have hj : J ≠ 0 := by intro hz; exact I.property (by rw [hJ,hz,mul_zero])
      have hei : e ⟨J,hj⟩ = I := Subtype.ext hJ.symm
      have hg : g ⟨J,hj⟩ ≠ 0 := by rw [← he, hei]; exact hI
      exact ⟨⟨⟨J,hj⟩,hg⟩,hei⟩
    · intro I; exact he I.val
  change (∑' I, f I) = _
  rw [hsum, tsum_mul_left]
  rfl

lemma outsideSum_insert (η : Character) (S : Finset (Ideal O))
    (hS : ∀ Q ∈ S, Prime Q) (P : Ideal O) (hP : Prime P) (hPS : P ∉ S)
    (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η (insert P S) F X = outsideSum η S F X -
      idealCoeff η P * outsideSum η S F (X / (P.absNorm : ℝ)) := by
  have hs := outsideSum_summable η S F hF X hX
  have hd : Summable (fun I : NI => if P ∣ I.val then
      (if outside S I.val then idealCoeff η I.val else 0) * F (norm I / X) else 0) := by
    exact hs.indicator {I : NI | P ∣ I.val}
  rw [← prime_shift_tsum η S hS P hP hPS F X]
  simp only [outsideSum]
  rw [← hs.tsum_sub hd]
  apply tsum_congr
  intro I
  have hi : outside (insert P S) I.val = (¬ P ∣ I.val ∧ outside S I.val) := by
    simp [outside, Finset.mem_insert]
  rw [hi]
  by_cases hp : P ∣ I.val <;> by_cases ho : outside S I.val <;>
    simp [hp, ho]

lemma subset_product_nonzero (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    (∏ P ∈ S, P) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun P hP => (hS P hP).ne_zero)
lemma subset_product_norm_pos (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P) :
    0 < (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero S hS))

theorem finite_deletion_plain (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    outsideSum η S F X = ∑ D ∈ S.powerset, (-1 : ℂ)^D.card * idealCoeff η (∏ P ∈ D, P) *
      (∑' I : NI, idealCoeff η I.val * F (norm I / (X / (Ideal.absNorm (∏ P ∈ D, P) : ℝ)))) := by
  induction S using Finset.induction_on generalizing X with
  | empty => simp [outsideSum, outside]
  | @insert P S hPS ih =>
    have hP := hS P (Finset.mem_insert_self _ _)
    have hSS : ∀ Q ∈ S, Prime Q := fun Q hQ => hS Q (Finset.mem_insert_of_mem hQ)
    have hn : 0 < (P.absNorm : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP.ne_zero)
    rw [outsideSum_insert η S hSS P hP hPS F hF X hX,
      ih hSS X hX, ih hSS (X / (P.absNorm : ℝ)) (div_pos hX hn),
      Finset.sum_powerset_insert hPS, Finset.mul_sum]
    rw [sub_eq_add_neg]
    congr 1
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro D hD
    have hPD : P ∉ D := fun h => hPS ((Finset.mem_powerset.mp hD) h)
    rw [Finset.card_insert_of_notMem hPD, Finset.prod_insert hPD, map_mul,
      map_mul, Nat.cast_mul, pow_succ]
    have hh : X / ((P.absNorm : ℝ) * (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ)) =
        (X / (P.absNorm : ℝ)) / (Ideal.absNorm (∏ Q ∈ D,Q) : ℝ) := by rw [div_div]
    rw [hh]
    ring

lemma normalized_dilation_term (η : Character) (F : ℝ → ℂ) (X : ℝ)
    (hX : 0<X) (D : NI) :
    idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
      HeckeDyadic.polynomial η false F (X / norm D) 0 0 =
    (Real.sqrt X : ℂ)⁻¹ * (idealCoeff η D.val *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) := by
  rw [polynomial_plain _ _ _ (div_pos hX (norm_pos D))]
  change idealCoeff η D.val / (Real.sqrt (norm D) : ℂ) *
    ((Real.sqrt (X / norm D) : ℂ)⁻¹ *
      ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) = _
  have h := normalization_factor X (norm D) hX (norm_pos D)
  rw [div_eq_mul_inv]
  linear_combination (idealCoeff η D.val *
    ∑' I : NI, idealCoeff η I.val * F (norm I / (X / norm D))) * h

theorem normalized_finite_deletion (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (-1 : ℂ)^D.card *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [polynomial_plain _ _ _ hX]
  have he : (∑' I : NI, idealCoeff (η.excludePrimes S hS) I.val * F ((I.val.absNorm : ℝ) / X)) =
      outsideSum η S F X := by
    apply tsum_congr
    intro I
    rw [deleted_coefficient]
    rfl
  rw [he, finite_deletion_plain η S hS F hF X hX, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D hD
  have hDS : ∀ P ∈ D, Prime P := fun P hP => hS P ((Finset.mem_powerset.mp hD) hP)
  have ht := normalized_dilation_term η F X hX ⟨∏P∈D,P, subset_product_nonzero D hDS⟩
  dsimp only [norm] at ht
  dsimp only [norm]
  linear_combination -(-1 : ℂ)^D.card * ht

lemma subset_product_moebius (D : Finset (Ideal O)) (hD : ∀ P ∈ D, Prime P) :
    (moebius (∏ P ∈ D,P) : ℂ) = (-1 : ℂ)^D.card := by
  have hf : normalizedFactors (∏ P ∈ D,P) = D.val := by
    simpa using normalizedFactors_prod_of_prime (m := D.val) hD
  have hs : Squarefree (∏ P ∈ D,P) := by
    rw [squarefree_iff_nodup_normalizedFactors (subset_product_nonzero D hD), hf]
    exact D.nodup
  rw [hs.moebius_eq, factors_eq_normalizedFactors, hf]
  simp

theorem normalized_finite_deletion_moebius (η : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (hF : DecayTwo F) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial (η.excludePrimes S hS) false F X 0 0 =
      ∑ D ∈ S.powerset, (moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)) *
        HeckeDyadic.polynomial η false F (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ)) 0 0 := by
  rw [normalized_finite_deletion η S hS F hF X hX]
  apply Finset.sum_congr rfl
  intro D hD
  rw [subset_product_moebius D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))]

def reflectedTerm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P) : ℝ) * norm H.val) : ℂ) *
    HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
      (Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val)) 0 0

lemma reflectedTerm_eq (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H =
      ((moebius (∏ P ∈ D,P) : ℂ) *
        (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ))) *
      (idealCoeff ηi H.val.val / (Real.sqrt (norm H.val) : ℂ) *
        HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
          ((Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val) 0 0) := by
  have hs : Q * (Ideal.absNorm (∏ P ∈ D,P) : ℝ) / (X * norm H.val) =
      (Q / (X / (Ideal.absNorm (∏ P ∈ D,P) : ℝ))) / norm H.val := by
    simp only [div_div_eq_mul_div, div_div]
  unfold reflectedTerm
  rw [hs, Real.sqrt_mul (Nat.cast_nonneg _), Complex.ofReal_mul]
  ring

theorem deletion_reflection (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S, Prime P) (W F : ℝ → ℂ) (hW : DecayTwo W) (hF : DecayTwo F)
    (G : ℂ) (Q : ℝ) (hQ : 0<Q)
    (hreflect : ∀ Y : ℝ, 0<Y → HeckeDyadic.polynomial η false W Y 0 0 =
      G * HeckeDyadic.polynomial ηi false F (Q/Y) 0 0)
    (X : ℝ) (hX : 0<X) :
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS F X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      G * ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, reflectedTerm η ηi S hS F X Q D H := by
  have hnorm (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      0 < (Ideal.absNorm (∏ P ∈ D,P) : ℝ) :=
    subset_product_norm_pos D (fun P hP => hS P ((Finset.mem_powerset.mp hD) hP))
  constructor
  · intro D hD
    have hs := (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
      (div_pos hQ (div_pos hX (hnorm D hD)))).1
    exact (hs.mul_left ((moebius (∏ P ∈ D,P) : ℂ) *
      (idealCoeff η (∏ P ∈ D,P) / (Real.sqrt (Ideal.absNorm (∏ P ∈ D,P) : ℝ) : ℂ)))).congr
      (fun H => (reflectedTerm_eq η ηi S hS F X Q D H).symm)
  · rw [normalized_finite_deletion_moebius η S hS W hW X hX, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro D hD
    rw [hreflect _ (div_pos hX (hnorm D hD)),
      (normalized_restoration ηi S hS F hF (Q/(X/(Ideal.absNorm (∏ P ∈ D,P) : ℝ)))
        (div_pos hQ (div_pos hX (hnorm D hD)))).2]
    rw [mul_left_comm]
    congr 1
    rw [← tsum_mul_left]
    apply tsum_congr
    intro H
    rw [reflectedTerm_eq]

theorem primitive_deleted_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖eisEmbedding c‖^2
    (∀ D ∈ S.powerset, Summable (reflectedTerm η ηi S hS (paperRadialFourier W) X Q D)) ∧
    HeckeDyadic.polynomial (η.excludePrimes S hS) false W X 0 0 =
      TraceCharacter.normalizedGauss c χ *
        ∑ D ∈ S.powerset, ∑' H : SmoothIdeal S,
          reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H := by
  dsimp only
  apply deletion_reflection _ _ S hS W (paperRadialFourier W)
    (schwartz_decayTwo W) (reflected_decayTwo W) _ _ _
    (fun Y hY => primitive_normalized_reflection c χ hu hp hχ W Y hY) X hX
  exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (NeZero.ne c)))

theorem primitive_deleted_reflection_absolute (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk (Ideal.span {c}) u.val) = 1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ ≠ 1)
    (S : Finset (Ideal O)) (hS : ∀ P ∈ S, Prime P)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0<X) :
    let η := HeckePrimitive.character c χ hu
    let ηi := HeckePrimitive.character c χ⁻¹ (HeckePrimitive.inverse_unit_trivial c χ hu)
    let Q := ‖eisEmbedding c‖^2
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,
      ‖reflectedTerm η ηi S hS (paperRadialFourier W) X Q D H‖) := by
  dsimp only
  exact summable_sum (fun D hD =>
    ((primitive_deleted_reflection c χ hu hp hχ S hS W X hX).1 D hD).norm)

end SevenEighths.CenteredMomentReflectionDeletion

end

end OAI
end OAIOriginalModule1988

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalReflection
Source SHA256: 88c7ffebcec9fec0072da228342b8867b56634b07b9a4fe45f956b8231336305
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1989




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalReflection
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentNaturalPrimitive
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local instance : IsPrincipalIdealRing O := IsCyclotomicExtension.Rat.three_pid K

lemma polynomial_coeff_congr (χ ψ : Character)
    (h : ∀I,idealCoeff χ I=idealCoeff ψ I) (W : ℝ→ℂ) (X : ℝ) :
    HeckeDyadic.polynomial χ false W X 0 0=HeckeDyadic.polynomial ψ false W X 0 0 := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [h]

lemma inverse_deletion_coeff (χ ψ : Character) (S : Finset (Ideal O))
    (hS : ∀P∈S,Prime P) (h : ∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I)
    (I : Ideal O) : idealCoeff χ.inverse I=idealCoeff (ψ.inverse.excludePrimes S hS) I := by
  rw [idealCoeff_inverse_conj,h,idealCoeff_excludePrimes,idealCoeff_excludePrimes,
    idealCoeff_inverse_conj]
  split_ifs <;> simp

theorem primitive_character_deleted (ψ : Character)
    (hp : FiniteFourier.IsPrimitiveOnIdeals ψ.residue) (hn : ψ.residue≠1) :
    ∃G : ℂ,‖G‖=1 ∧ ∀(S : Finset (Ideal O))(hS : ∀P∈S,Prime P)
      (W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
      (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
        X (ψ.modulus.absNorm:ℝ) D)) ∧
      HeckeDyadic.polynomial (ψ.excludePrimes S hS) false W X 0 0=
        G*∑D∈S.powerset,∑'H : SmoothIdeal S,
          reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  rcases ψ with ⟨M,hM,χ,hu,p,hp0,hpm⟩
  obtain ⟨c,hc⟩ := Submodule.IsPrincipal.principal M
  change M=Ideal.span {c} at hc
  subst M
  have hc0 : c≠0 := by simpa only [ne_eq,Ideal.span_singleton_eq_bot] using hM
  let : NeZero c := ⟨hc0⟩
  refine ⟨TraceCharacter.normalizedGauss c χ,TraceCharacter.normalizedGauss_norm c χ hp,?_⟩
  intro S hS W X hX
  have hh := primitive_deleted_reflection c χ hu hp hn S hS W X hX
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span] at hh
  exact hh

theorem original_natural_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      let hS := redundantSet_prime χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      (∀I,idealCoeff χ I=idealCoeff (ψ.excludePrimes S hS) I) ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        (∀D∈S.powerset,Summable (reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W)
          X (ψ.modulus.absNorm:ℝ) D)) ∧
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            reflectedTerm ψ ψ.inverse S hS (paperRadialFourier W) X (ψ.modulus.absNorm:ℝ) D H := by
  obtain ⟨ψ,hmod,hprim,hne,hsq,hcop,hdvd,hnorm,hcoeff⟩ := exists_natural_primitive χ
  obtain ⟨G,hG,hreflection⟩ := primitive_character_deleted ψ hprim (hne hn)
  refine ⟨ψ,G,hprim,hne hn,hG,hnorm,hcop,hcoeff,?_⟩
  intro W X hX
  have hh := hreflection _ (redundantSet_prime χ.modulus ψ.modulus) W X hX
  exact ⟨hh.1,(polynomial_coeff_congr χ _ hcoeff W X).trans hh.2⟩

theorem original_inverse_reflection (χ : Character) (hn : χ.residue≠1) :
    ∃(ψ : Character)(G : ℂ),FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧ ψ.residue≠1 ∧ ‖G‖=1 ∧
      let S := redundantSet χ.modulus ψ.modulus
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀(W : 𝓢(ℝ,ℂ))(X : ℝ),0<X →
        HeckeDyadic.polynomial χ false W X 0 0=
          G*∑D∈S.powerset,∑'H : SmoothIdeal S,
            (UniqueFactorizationMonoid.moebius (∏P∈D,P):ℂ)*idealCoeff ψ (∏P∈D,P)*
              idealCoeff ψ.inverse H.val.val /
              (Real.sqrt ((Ideal.absNorm (∏P∈D,P):ℝ)*norm H.val):ℂ)*
              HeckeDyadic.polynomial χ.inverse false (paperRadialFourier W)
                ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)) 0 0 := by
  obtain ⟨ψ,G,hprim,hne,hG,hnorm,hcop,hcoeff,hreflect⟩ := original_natural_reflection χ hn
  refine ⟨ψ,G,hprim,hne,hG,hnorm,?_⟩
  intro W X hX
  rw [(hreflect W X hX).2]
  congr 1
  apply Finset.sum_congr rfl
  intro D hD
  apply tsum_congr
  intro H
  unfold reflectedTerm
  rw [←polynomial_coeff_congr χ.inverse _
    (inverse_deletion_coeff χ ψ _ (redundantSet_prime χ.modulus ψ.modulus) hcoeff)]

end SevenEighths.CenteredMomentNaturalReflection

end

end OAI
end OAIOriginalModule1989

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedSeries
Source SHA256: 269aefaefad76d9792471893415586ce061cf52d8a88a85c7753aad4155e9e62
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1990



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedSeries
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

def dyadicIdealTerm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) : ℂ :=
  idealCoeff η I.val*(dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F ((I.val.absNorm:ℝ)/Y)

lemma dyadicIdealTerm_norm (η : Character) (F : ℝ→ℂ) (Y : ℝ) (I : NI) (n : ℤ) :
    ‖dyadicIdealTerm η F Y I n‖=
      dyadicWeight n ((I.val.absNorm:ℝ)/Y)*‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖ := by
  unfold dyadicIdealTerm
  rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (dyadicWeight_bounds _ _).1,norm_mul]
  ring

lemma dyadic_ideal_absolute (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun p : NI×ℤ=>‖dyadicIdealTerm η F Y p.1 p.2‖) := by
  apply (summable_prod_of_nonneg (fun _=>norm_nonneg _)).mpr
  simp_rw [dyadicIdealTerm_norm]
  constructor
  · intro I
    exact (dyadicWeight_summable _).mul_right _
  · simp_rw [tsum_mul_right]
    have he (I : NI) : (∑'n : ℤ,dyadicWeight n ((I.val.absNorm:ℝ)/Y))=1 :=
      dyadicWeight_partition _ (div_pos (HeckeDyadic.norm_pos I) hY)
    simp_rw [he,one_mul]
    exact (plain_summable η F hF Y hY).norm

lemma dyadic_ideal_partition (η : Character) (F : ℝ→ℂ) (Y : ℝ) (hY : 0<Y) (I : NI) :
    (∑'n : ℤ,dyadicIdealTerm η F Y I n)=idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y) := by
  have he (n : ℤ) : dyadicIdealTerm η F Y I n=
      (dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*(idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    unfold dyadicIdealTerm
    ring
  simp_rw [he]
  have hp : 0<(I.val.absNorm:ℝ)/Y := div_pos (HeckeDyadic.norm_pos I) hY
  rw [tsum_mul_right,←Complex.ofReal_tsum,dyadicWeight_partition _ hp]
  simp

theorem normalized_annular_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false F Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have habs := dyadic_ideal_absolute η F hF Y hY
  have hs := habs.of_norm
  have he (n : ℤ) : (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,dyadicIdealTerm η F Y I n := by
    rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
      polynomial_plain _ _ _ hY]
    congr 1
    apply tsum_congr
    intro I
    simp only [dyadicIdealTerm,dyadicWeight]
    ring
  simp_rw [he]
  refine ⟨hs.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η F Y hY]
  congr 1
  rw [hs.tsum_comm]
  exact tsum_congr (fun I=>(dyadic_ideal_partition η F Y hY I).symm)

theorem actual_reflected_annular_series (η : Character) (W : 𝓢(ℝ,ℂ))
    (Y : ℝ) (hY : 0<Y) :
    Summable (fun n : ℤ=>(Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
        (dyadicScale n*Y) 0 0) ∧
    HeckeDyadic.polynomial η false (paperRadialFourier W) Y 0 0=
      ∑'n : ℤ,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile (paperRadialFourier W) (dyadicScale n))
          (dyadicScale n*Y) 0 0 := by
  exact normalized_annular_series η _ (reflected_decayTwo W) Y hY

end SevenEighths.CenteredMomentReflectedSeries

end

end OAI
end OAIOriginalModule1990

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectedTruncation
Source SHA256: a58e26a4689f63838bb7276945fc29c5cd3f1e28e743ee197069230aad629fd1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1991


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentReflectedTruncation
open HeckeFamily CenteredMomentSectorLocalization CenteredMomentReflectedAnnuli
open CenteredMomentComparisonReflection CenteredMomentReflectionDeletion
open CenteredMomentReflectedSeries EisensteinSchwartzPoisson
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

theorem normalized_subseries (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (Y : ℝ) (hY : 0<Y) (A : Set ℤ) :
    Summable (fun n : ℤ=>if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0) ∧
    HeckeDyadic.polynomial η false
      (fun x=>(∑'n : ℤ,if n∈A then dyadicWeight n x else 0:ℝ)*F x) Y 0 0=
      ∑'n : ℤ,if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0 := by
  have hs := (dyadic_ideal_absolute η F hF Y hY).of_norm
  have hi : Summable (fun p : NI×ℤ=>if p.2∈A then dyadicIdealTerm η F Y p.1 p.2 else 0) :=
    hs.indicator {p : NI×ℤ | p.2∈A}
  have he (n : ℤ) : (if n∈A then (Real.sqrt (dyadicScale n):ℂ)*
      HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 else 0)=
      (Real.sqrt Y:ℂ)⁻¹*∑'I : NI,if n∈A then dyadicIdealTerm η F Y I n else 0 := by
    split_ifs with hn
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      congr 1
      apply tsum_congr
      intro I
      simp only [dyadicIdealTerm,dyadicWeight]
      ring
    · simp
  simp_rw [he]
  refine ⟨hi.prod_symm.prod.mul_left _,?_⟩
  rw [tsum_mul_left,polynomial_plain η _ Y hY]
  congr 1
  rw [hi.tsum_comm]
  apply tsum_congr
  intro I
  have ht (n : ℤ) : (if n∈A then dyadicIdealTerm η F Y I n else 0)=
      ((if n∈A then dyadicWeight n ((I.val.absNorm:ℝ)/Y) else 0:ℝ):ℂ)*
        (idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
    split_ifs <;> simp only [dyadicIdealTerm,Complex.ofReal_zero,zero_mul] ; ring
  simp_rw [ht]
  rw [tsum_mul_right,←Complex.ofReal_tsum]
  ring

def retainedAnnuli (R Y : ℝ) (hY : 0<Y) : Finset ℤ :=
  (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).toFinset

lemma retainedAnnuli_mem (R Y : ℝ) (hY : 0<Y) (n : ℤ) :
    n∈retainedAnnuli R Y hY ↔ Retained R n ∧ ∃q : ℝ,Y⁻¹≤q ∧ dyadicWeight n q≠0 := by
  exact (finite_retained_above R (Y⁻¹) (inv_pos.mpr hY)).mem_toFinset

lemma original_norm_lower (I : NI) (Y : ℝ) (hY : 0<Y) :
    Y⁻¹≤(I.val.absNorm:ℝ)/Y := by
  have hn : (1:ℝ)≤I.val.absNorm := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property))
  simpa only [one_div] using div_le_div_of_nonneg_right hn hY.le

theorem retained_finite_series (η : Character) (F : ℝ→ℂ) (hF : DecayTwo F)
    (R Y : ℝ) (hY : 0<Y) :
    HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=
      ∑n∈retainedAnnuli R Y hY,(Real.sqrt (dyadicScale n):ℂ)*
        HeckeDyadic.polynomial η false (annularProfile F (dyadicScale n)) (dyadicScale n*Y) 0 0 := by
  have hh := (normalized_subseries η F hF Y hY {n | Retained R n}).2
  change HeckeDyadic.polynomial η false (fun x=>(retainedWeight R x:ℂ)*F x) Y 0 0=_ at hh
  rw [hh,tsum_eq_sum (s:=retainedAnnuli R Y hY)]
  · apply Finset.sum_congr rfl
    intro n hn
    simp only [Set.mem_ofPred_eq,ite_eq_left ((retainedAnnuli_mem R Y hY n).mp hn).1]
  · intro n hn
    split_ifs with hr
    · rw [←normalized_annular_term η F (dyadicScale n) Y (dyadicScale_pos n) hY,
        polynomial_plain _ _ _ hY]
      have hz (I : NI) : dyadicWeight n ((I.val.absNorm:ℝ)/Y)=0 := by
        by_contra hne
        exact hn ((retainedAnnuli_mem R Y hY n).mpr ⟨hr,_,original_norm_lower I Y hY,hne⟩)
      have he (I : NI) : idealCoeff η I.val*
          ((annulus (((I.val.absNorm:ℝ)/Y)/dyadicScale n):ℂ)*F ((I.val.absNorm:ℝ)/Y))=0 := by
        change idealCoeff η I.val*((dyadicWeight n ((I.val.absNorm:ℝ)/Y):ℂ)*F _)=0
        rw [hz,Complex.ofReal_zero,zero_mul,mul_zero]
      simp_rw [he,tsum_zero,mul_zero]
    · rfl

end SevenEighths.CenteredMomentReflectedTruncation

end

end OAI
end OAIOriginalModule1991

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionMass
Source SHA256: 552ba9aa43b0765a049cdb1003396d63341bd445d3112ca625cdbf388261510c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1992


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion HeckeFamily UniqueFactorizationMonoid
open IdealMobiusDivisorSum
local notation "O" => HeckeFamily.O

def weight (I : Ideal O) : ℝ := (Real.sqrt (I.absNorm : ℝ))⁻¹
lemma weight_nonneg (I : Ideal O) : 0 ≤ weight I := by unfold weight; positivity
lemma weight_mul (I J : Ideal O) : weight (I*J) = weight I * weight J := by
  simp only [weight, map_mul, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg _), mul_inv_rev]
  ring
lemma weight_one : weight (1 : Ideal O) = 1 := by simp [weight]
lemma weight_pow (I : Ideal O) (n : ℕ) : weight (I^n) = weight I ^ n := by
  induction n with
  | zero => simpa only [pow_zero] using weight_one
  | succ n ih => rw [pow_succ,weight_mul,ih,pow_succ]
lemma weight_prod (S : Finset (Ideal O)) (f : Ideal O → Ideal O) :
    weight (∏ P ∈ S,f P) = ∏ P ∈ S,weight (f P) := by
  induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty] using weight_one
  | @insert P S h ih => simp only [Finset.prod_insert h,weight_mul,ih]
lemma prime_weight_lt_one (P : Ideal O) (hP : Prime P) : weight P < 1 := by
  have h : (1:ℝ) < P.absNorm := by
    have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩
    exact_mod_cast (by omega : 1 < P.absNorm)
  have hs : 1 < Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.lt_sqrt (by norm_num)]
    simpa using h
  exact inv_lt_one_of_one_lt₀ hs

def exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) (P : S) : ℕ :=
  (normalizedFactors I.val.val).count P.val
lemma reconstruct_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    (∏ P : S,P.val ^ exponents S I P) = I.val.val := by
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P)]
  exact (Finset.prod_multiset_count_of_subset (normalizedFactors I.val.val) S I.property).symm.trans
    (Ideal.prod_normalizedFactors_eq_self I.val.property)
lemma exponents_injective (S : Finset (Ideal O)) : Function.Injective (exponents S) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  rw [← reconstruct_exponents S I,← reconstruct_exponents S J,h]
lemma weight_exponents (S : Finset (Ideal O)) (I : SmoothIdeal S) :
    weight I.val.val = ∏ P : S,weight P.val ^ exponents S I P := by
  conv_lhs => rw [← reconstruct_exponents S I]
  simp only [exponents]
  rw [Finset.prod_coe_sort S (fun P => P ^ (normalizedFactors I.val.val).count P),
    Finset.prod_coe_sort S (fun P => weight P ^ (normalizedFactors I.val.val).count P), weight_prod]
  simp only [weight_pow]

lemma hasSum_geometric_pi {α : Type*} [Fintype α] (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (hr1 : ∀ a, r a < 1) :
    HasSum (fun n : α → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹) := by
  classical
  apply Fintype.induction_empty_option (P := fun β _ => ∀ (r : β → ℝ),
    (∀ a, 0 ≤ r a) → (∀ a, r a < 1) →
    HasSum (fun n : β → ℕ => ∏ a,r a ^ n a) (∏ a,(1-r a)⁻¹)) ?_ ?_ ?_ α r hr hr1
  · intro α β _ e ih r hr hr1
    let : Fintype α := Fintype.ofEquiv β e.symm
    have h := ih (r ∘ e) (fun a => hr (e a)) (fun a => hr1 (e a))
    let E : (β → ℕ) ≃ (α → ℕ) := Equiv.arrowCongr e.symm (Equiv.refl ℕ)
    have he := E.hasSum_iff.mpr h
    convert he using 1
    · funext n
      exact (e.prod_comp (fun b => r b ^ n b)).symm
    · exact (e.prod_comp (fun b => (1-r b)⁻¹)).symm
  · intro r _ _
    simp
  · intro α _ ih r hr hr1
    have h0 := hasSum_geometric_of_lt_one (hr none) (hr1 none)
    have ht := ih (fun a => r (some a)) (fun a => hr (some a)) (fun a => hr1 (some a))
    have hs := h0.summable.mul_of_nonneg ht.summable (fun n => pow_nonneg (hr none) n)
      (fun n => Finset.prod_nonneg (fun a _ => pow_nonneg (hr (some a)) (n a)))
    have hp := h0.mul ht hs
    have he := (Equiv.piOptionEquivProd (β := fun _ : Option α => ℕ)).hasSum_iff.mpr hp
    simpa only [Function.comp_def, Fintype.prod_option, Equiv.piOptionEquivProd_apply] using he

lemma smooth_summable (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    Summable (fun I : SmoothIdeal S => weight I.val.val) := by
  have hs := (hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))).summable
  exact (hs.comp_injective (exponents_injective S)).congr (fun I => (weight_exponents S I).symm)

lemma smooth_mass_le_euler (S : Finset (Ideal O)) (hS : ∀ P ∈ S,Prime P) :
    (∑' I : SmoothIdeal S,weight I.val.val) ≤ ∏ P ∈ S,(1-weight P)⁻¹ := by
  have hh := hasSum_geometric_pi (fun P : S => weight P.val)
    (fun P => weight_nonneg P.val) (fun P => prime_weight_lt_one P.val (hS P.val P.property))
  have h := Summable.tsum_le_tsum_of_inj (exponents S) (exponents_injective S)
    (fun n _ => Finset.prod_nonneg (fun P _ => pow_nonneg (weight_nonneg P.val) (n P)))
    (fun I => (weight_exponents S I).le) (smooth_summable S hS) hh.summable
  rw [hh.tsum_eq,Finset.prod_coe_sort S (fun P => (1-weight P)⁻¹)] at h
  exact h

lemma deletion_mass (S : Finset (Ideal O)) :
    (∑ D ∈ S.powerset, weight (∏ P ∈ D,P)) = ∏ P ∈ S,(1+weight P) := by
  simp_rw [weight_prod]
  exact (Finset.prod_one_add S).symm

def localMass (P : Ideal O) : ℝ := (1+weight P)/(1-weight P)
lemma localMass_nonneg (P : Ideal O) (hP : Prime P) : 0 ≤ localMass P := by
  exact div_nonneg (by linarith [weight_nonneg P]) (sub_pos.mpr (prime_weight_lt_one P hP)).le
lemma prime_weight_le (P : Ideal O) (hP : Prime P) : weight P ≤ 3/4 := by
  have hn : (2:ℝ) ≤ P.absNorm := by
    exact_mod_cast (SmoothMobiusCorrection.prime_norm_two_le ⟨P,hP⟩ : 2 ≤ P.absNorm)
  have hs : 4/3 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    nlinarith
  rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
  nlinarith
lemma localMass_le_seven (P : Ideal O) (hP : Prime P) : localMass P ≤ 7 := by
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith [prime_weight_le P hP]
lemma localMass_le_three (P : Ideal O) (hP : Prime P) (hn : (4:ℝ) ≤ P.absNorm) :
    localMass P ≤ 3 := by
  have hs : 2 ≤ Real.sqrt (P.absNorm : ℝ) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]
    linarith
  have hw : weight P ≤ 1/2 := by
    rw [weight,inv_eq_one_div,div_le_iff₀ (by linarith : 0 < Real.sqrt (P.absNorm : ℝ))]
    linarith
  apply (div_le_iff₀ (sub_pos.mpr (prime_weight_lt_one P hP))).mpr
  linarith

theorem euler_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P),
      (∏ P ∈ S,localMass P) ≤ C * (Ideal.absNorm (∏ P ∈ S,P) : ℝ)^ε := by
  obtain ⟨B,hB⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop hε).eventually (Filter.eventually_ge_atTop (3:ℝ)))
  let K : ℕ := ⌈max 4 B⌉₊
  let smallIdeals := ConcretePrimeRowBridge.idealsUpTo K
  have hK : max 4 B ≤ (K:ℝ) := Nat.le_ceil _
  refine ⟨(7:ℝ)^smallIdeals.card,by positivity,?_⟩
  intro S hS
  have hpoint (P : Ideal O) (hP : P ∈ S) :
      localMass P ≤ (if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε := by
    have hn : (1:ℝ) ≤ P.absNorm := by
      have hh : 2 ≤ P.absNorm := SmoothMobiusCorrection.prime_norm_two_le ⟨P,hS P hP⟩
      exact_mod_cast (by omega : 1 ≤ P.absNorm)
    have he : 1 ≤ (P.absNorm:ℝ)^ε := Real.one_le_rpow hn hε.le
    by_cases hp : P ∈ smallIdeals
    · simp only [ite_eq_left hp]
      exact (localMass_le_seven P (hS P hP)).trans (by nlinarith)
    · have hpk : (K:ℝ) < P.absNorm := by
        have hh : ¬ P.absNorm ≤ K := by
          intro h
          apply hp
          exact ConcretePrimeRowBridge.mem_idealsUpTo.mpr ⟨by exact_mod_cast hn,h⟩
        exact_mod_cast Nat.lt_of_not_ge hh
      have h4 : (4:ℝ) ≤ P.absNorm := (le_max_left _ _).trans (hK.trans hpk.le)
      have hb : B ≤ (P.absNorm:ℝ) := (le_max_right _ _).trans (hK.trans hpk.le)
      simp only [ite_eq_right hp,one_mul]
      exact (localMass_le_three P (hS P hP) h4).trans (hB _ hb)
  have hc : (S.filter (· ∈ smallIdeals)).card ≤ smallIdeals.card :=
    Finset.card_le_card (fun P hP => (Finset.mem_filter.mp hP).2)
  calc
    (∏ P ∈ S,localMass P) ≤ ∏ P ∈ S,((if P ∈ smallIdeals then 7 else 1)*(P.absNorm:ℝ)^ε) :=
      Finset.prod_le_prod₀ (fun P hP => localMass_nonneg P (hS P hP)) hpoint
    _ = (7:ℝ)^(S.filter (· ∈ smallIdeals)).card * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
      rw [Finset.prod_mul_distrib,← Finset.prod_filter]
      simp only [Finset.prod_const,Real.finsetProd_rpow S _ (fun _ _ => Nat.cast_nonneg _) ε,
        map_prod,Nat.cast_prod]
    _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc) (Real.rpow_nonneg (by positivity) _)

def coefficient (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (H : SmoothIdeal S) : ℂ :=
  (moebius (∏ P ∈ D,P) : ℂ) * idealCoeff η (∏ P ∈ D,P) * idealCoeff ηi H.val.val /
    (Real.sqrt ((Ideal.absNorm (∏ P ∈ D,P):ℝ) * norm H.val) : ℂ)

lemma coefficient_norm_le (η ηi : Character) (S : Finset (Ideal O))
    (D : Finset (Ideal O)) (hD : ∀ P ∈ D,Prime P) (H : SmoothIdeal S) :
    ‖coefficient η ηi S D H‖ ≤ weight (∏ P ∈ D,P) * weight H.val.val := by
  rw [coefficient,subset_product_moebius D hD]
  simp only [norm_div,norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  have h : ‖idealCoeff η (∏ P ∈ D,P)‖ * ‖idealCoeff ηi H.val.val‖ ≤ 1 :=
    (mul_le_mul (idealCoeff_norm_le_one η _) (idealCoeff_norm_le_one ηi _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  apply (div_le_div_of_nonneg_right h (Real.sqrt_nonneg _)).trans_eq
  simp only [CenteredMomentReflectionDeletion.norm,weight,Real.sqrt_mul (Nat.cast_nonneg _),one_div,mul_inv_rev]
  ring

lemma coefficient_summable_norm (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (fun H : SmoothIdeal S => ‖coefficient η ηi S D H‖) := by
  apply ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P))).of_nonneg_of_le
    (fun _ => norm_nonneg _)
  exact fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hD hP)) H

lemma coefficient_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (D : Finset (Ideal O)) (hD : D ⊆ S) :
    Summable (coefficient η ηi S D) := (coefficient_summable_norm η ηi S hS D hD).of_norm

lemma coefficient_mass_le_euler (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
      ∏ P ∈ S,localMass P := by
  have hD (D : Finset (Ideal O)) (hD : D ∈ S.powerset) :
      (∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        weight (∏ P ∈ D,P) * (∏ P ∈ S,(1-weight P)⁻¹) := by
    have hsub := Finset.mem_powerset.mp hD
    apply ((coefficient_summable_norm η ηi S hS D hsub).tsum_le_tsum
      (fun H => coefficient_norm_le η ηi S D (fun P hP => hS P (hsub hP)) H)
      ((smooth_summable S hS).mul_left (weight (∏ P ∈ D,P)))).trans
    rw [tsum_mul_left]
    exact mul_le_mul_of_nonneg_left (smooth_mass_le_euler S hS) (weight_nonneg _)
  apply (Finset.sum_le_sum hD).trans_eq
  rw [← Finset.sum_mul,deletion_mass,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro P _
  exact (div_eq_mul_inv _ _).symm

lemma coefficient_mass_summable (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) :
    Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) := by
  exact summable_sum (fun D hD => coefficient_summable_norm η ηi S hS D (Finset.mem_powerset.mp hD))

theorem reflection_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (_hS : ∀ P ∈ S,Prime P)
      (η ηi : Character),
      Summable (fun H : SmoothIdeal S => ∑ D ∈ S.powerset,‖coefficient η ηi S D H‖) ∧
      (∑ D ∈ S.powerset, ∑' H : SmoothIdeal S, ‖coefficient η ηi S D H‖) ≤
        C * (Ideal.absNorm (∏ P ∈ S,P):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩ := euler_mass_subpower ε hε
  exact ⟨C,hC,fun S hS η ηi => ⟨coefficient_mass_summable η ηi S hS,
    (coefficient_mass_le_euler η ηi S hS).trans (hbound S hS)⟩⟩

def unitSmooth (S : Finset (Ideal O)) : SmoothIdeal S :=
  ⟨⟨1,one_ne_zero⟩,by
    change (normalizedFactors (1 : Ideal O)).toFinset ⊆ S
    rw [normalizedFactors_one]
    exact Finset.empty_subset _⟩
lemma coefficient_empty_unit (η ηi : Character) (S : Finset (Ideal O)) :
    coefficient η ηi S ∅ (unitSmooth S) = 1 := by
  have hm : (moebius (1 : Ideal O) : ℂ) = 1 := by
    simpa only [Finset.prod_empty,Finset.card_empty,pow_zero] using
      subset_product_moebius ∅ (by simp)
  change (moebius (1 : Ideal O) : ℂ) * idealCoeff η 1 * idealCoeff ηi 1 /
    (Real.sqrt ((Ideal.absNorm (1 : Ideal O) : ℝ) * (Ideal.absNorm (1 : Ideal O) : ℝ)) : ℂ) = 1
  rw [hm,map_one,map_one,map_one]
  norm_num

lemma reflectedTerm_eq_coefficient (η ηi : Character) (S : Finset (Ideal O))
    (hS : ∀ P ∈ S,Prime P) (F : ℝ → ℂ) (X Q : ℝ)
    (D : Finset (Ideal O)) (H : SmoothIdeal S) :
    reflectedTerm η ηi S hS F X Q D H = coefficient η ηi S D H *
      HeckeDyadic.polynomial (ηi.excludePrimes S hS) false F
        (Q * (Ideal.absNorm (∏ P ∈ D,P):ℝ)/(X*norm H.val)) 0 0 := rfl

end SevenEighths.CenteredMomentReflectionMass
end

end OAI
end OAIOriginalModule1992

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonMaskExpansion
Source SHA256: 7a7905cbf1da98804584b9a6d53749e29138c32d8384c3ad370c7ad5c38379f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1993


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentCommonMaskExpansion
open HeckeFamily CenteredMomentReflectionDeletion CenteredMomentReflectionMass
open UniqueFactorizationMonoid
local notation "O" => HeckeFamily.O

def naturalSlot (χ : Character) (pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℂ :=
  (Real.sqrt P:ℂ)⁻¹ * ∑ I∈pool,idealCoeff χ I*β I

def profileSlot (χ : Character) (pool : Finset (Ideal O))
    (ν : Ideal O→ℂ) (W : ℝ→ℂ) (P : ℝ) : ℂ :=
  naturalSlot χ pool (fun I=>ν I*W ((I.absNorm:ℝ)/P)) P

lemma outside_prime (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) : outside R I ↔ I∉R := by
  constructor
  · intro h hi
    exact h I hi dvd_rfl
  · intro h J hj hd
    have he : J=I := (prime_dvd_prime_iff_eq (hR J hj) hI).mp hd
    exact h (he ▸ hj)

lemma deleted_prime (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (I : Ideal O) (hI : Prime I) :
    idealCoeff (χ.excludePrimes R hR) I = if I∈R then 0 else idealCoeff χ I := by
  have h:=deleted_coefficient χ R hR ⟨I,hI.ne_zero⟩
  simpa only [outside_prime R hR I hI,ite_not] using h

theorem naturalSlot_delete (χ : Character) (R : Finset (Ideal O)) (hR : ∀ I∈R,Prime I)
    (pool : Finset (Ideal O)) (hp : ∀ I∈pool,Prime I) (β : Ideal O→ℂ) (P : ℝ) :
    naturalSlot (χ.excludePrimes R hR) pool β P =
      naturalSlot χ pool β P - naturalSlot χ (pool∩R) β P := by
  unfold naturalSlot
  have hinter : pool∩R=pool.filter (fun I=>I∈R) := by ext I;simp
  rw [←mul_sub,hinter,Finset.sum_filter,←Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro I hi
  rw [deleted_prime χ R hR I (hp I hi)]
  by_cases h:I∈R <;> simp [h]

lemma prod_sub_expansion {α : Type*} [DecidableEq α] (F : Finset α) (a b : α→ℂ) :
    (∏i∈F,(a i-b i))=∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,b i)*(∏i∈F\J,a i) := by
  have he : (∏i∈F,(a i-b i))=∏i∈F,((-b i)+a i) := by
    apply Finset.prod_congr rfl
    intro i hi
    ring
  rw [he,Finset.prod_add]
  simp only [Finset.prod_neg]

def plainCoefficient (χ : Character) (D : Finset (Ideal O)) : ℂ :=
  (moebius (∏I∈D,I):ℂ)*(idealCoeff χ (∏I∈D,I)/(Real.sqrt (Ideal.absNorm (∏I∈D,I):ℝ):ℂ))

variable {α : Type*} [DecidableEq α]

def signedCoefficient (χ : Character) (R D₁ D₂ : Finset (Ideal O))
    (J : Finset α) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℂ :=
  plainCoefficient χ D₁*plainCoefficient χ D₂*(-1:ℂ)^J.card*
    ∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i)

theorem simultaneous_deletion (χ : Character) (R : Finset (Ideal O))
    (hR : ∀ I∈R,Prime I) (W₁ W₂ : 𝓢(ℝ,ℂ)) (X₁ X₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (F : Finset α)
    (pool : α→Finset (Ideal O)) (hp : ∀i∈F,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) :
    HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₁ X₁ 0 0 *
      HeckeDyadic.polynomial (χ.excludePrimes R hR) false W₂ X₂ 0 0 *
      (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i)) =
    ∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      signedCoefficient χ R D₁ D₂ J pool β P *
        (HeckeDyadic.polynomial χ false W₁ (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial χ false W₂ (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
  have hs : (∏i∈F,naturalSlot (χ.excludePrimes R hR) (pool i) (β i) (P i))=
      ∑J∈F.powerset,(-1:ℂ)^J.card*(∏i∈J,naturalSlot χ (pool i∩R) (β i) (P i))*
        (∏i∈F\J,naturalSlot χ (pool i) (β i) (P i)) := by
    have hh:=prod_sub_expansion F (fun i=>naturalSlot χ (pool i) (β i) (P i))
      (fun i=>naturalSlot χ (pool i∩R) (β i) (P i))
    exact (Finset.prod_congr rfl (fun i hi=>naturalSlot_delete χ R hR (pool i) (hp i hi) (β i) (P i))).trans hh
  rw [normalized_finite_deletion_moebius χ R hR W₁ (schwartz_decayTwo W₁) X₁ hX₁,
    normalized_finite_deletion_moebius χ R hR W₂ (schwartz_decayTwo W₂) X₂ hX₂,hs]
  rw [Finset.sum_mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  dsimp only [signedCoefficient,plainCoefficient]
  ring

def slotMass (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) : ℝ :=
  (Real.sqrt P)⁻¹ * ∑I∈pool∩R,‖β I‖

lemma slotMass_nonneg (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    0≤slotMass R pool β P := by unfold slotMass;positivity

lemma naturalSlot_norm (χ : Character) (R pool : Finset (Ideal O)) (β : Ideal O→ℂ) (P : ℝ) :
    ‖naturalSlot χ (pool∩R) β P‖≤slotMass R pool β P := by
  rw [naturalSlot,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Real.sqrt_nonneg _))
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hi
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one χ I)

lemma plainCoefficient_norm (χ : Character) (D : Finset (Ideal O))
    (hD : ∀I∈D,Prime I) : ‖plainCoefficient χ D‖≤weight (∏I∈D,I) := by
  rw [plainCoefficient,subset_product_moebius D hD]
  simp only [norm_mul,norm_pow,norm_neg,norm_one,one_pow,one_mul,norm_div,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_div_of_nonneg_right (idealCoeff_norm_le_one χ _) (Real.sqrt_nonneg _)).trans_eq
    (by simp only [weight,one_div])

lemma slot_point_mass (I : Ideal O) (hI : Prime I) (β : Ideal O→ℂ)
    (P b M : ℝ) (hP : 0<P) (hM : 0≤M) (hβ : ‖β I‖≤M)
    (hs : β I≠0 → (I.absNorm:ℝ)≤b*P) :
    (Real.sqrt P)⁻¹*‖β I‖≤(Real.sqrt (max 1 b)*M)*weight I := by
  by_cases hz : β I=0
  · simp only [hz,norm_zero,mul_zero]
    exact mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hM) (weight_nonneg _)
  have hN : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI.ne_zero)
  have hB : 0≤max 1 b := le_trans zero_le_one (le_max_left _ _)
  have hsqrt : Real.sqrt (I.absNorm:ℝ)≤Real.sqrt (max 1 b)*Real.sqrt P := by
    rw [←Real.sqrt_mul hB]
    exact Real.sqrt_le_sqrt ((hs hz).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hP.le))
  have hi : (Real.sqrt P)⁻¹≤Real.sqrt (max 1 b)*weight I := by
    rw [weight,←div_eq_mul_inv,inv_eq_one_div,
      div_le_div_iff₀ (Real.sqrt_pos.mpr hP) (Real.sqrt_pos.mpr hN)]
    simpa using hsqrt
  calc
    _≤(Real.sqrt (max 1 b)*weight I)*M :=
      mul_le_mul hi hβ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (weight_nonneg _))
    _=_ := by ring

lemma slotMass_bound (R pool : Finset (Ideal O)) (hp : ∀I∈pool,Prime I)
    (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    slotMass R pool β P≤(Real.sqrt (max 1 b)*M)*∑I∈R,weight I := by
  unfold slotMass
  rw [Finset.mul_sum]
  calc
    _≤∑I∈pool∩R,(Real.sqrt (max 1 b)*M)*weight I :=
      Finset.sum_le_sum (fun I hi=>slot_point_mass I (hp I (Finset.mem_inter.mp hi).1)
        β P b M hP hM (hβ I (Finset.mem_inter.mp hi).1) (hs I (Finset.mem_inter.mp hi).1))
    _=(Real.sqrt (max 1 b)*M)*∑I∈pool∩R,weight I := (Finset.mul_sum _ _ _).symm
    _≤_ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right (fun I hi hn=>weight_nonneg I))
      (mul_nonneg (Real.sqrt_nonneg _) hM)

lemma one_add_sum_weight (R : Finset (Ideal O)) :
    1+∑I∈R,weight I≤∏I∈R,(1+weight I) := by
  induction R using Finset.induction_on with
  | empty => simp
  | @insert I R hi ih =>
    rw [Finset.sum_insert hi,Finset.prod_insert hi]
    have hw:=weight_nonneg I
    have hs:0≤∑J∈R,weight J:=Finset.sum_nonneg (fun J _=>weight_nonneg J)
    nlinarith

lemma deletion_le_euler (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    (∏I∈R,(1+weight I))≤∏I∈R,localMass I := by
  apply Finset.prod_le_prod₀ (fun I hi=>by linarith [weight_nonneg I])
  intro I hi
  apply (le_div_iff₀ (sub_pos.mpr (prime_weight_lt_one I (hR I hi)))).mpr
  have h:=weight_nonneg I
  nlinarith

lemma euler_ge_one (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I) :
    1≤∏I∈R,localMass I :=
  (show 1≤∏I∈R,(1+weight I) by
    linarith [Finset.sum_nonneg (s:=R) (fun I _=>weight_nonneg I),one_add_sum_weight R]).trans
    (deletion_le_euler R hR)

lemma one_add_slotMass (R pool : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (hp : ∀I∈pool,Prime I) (β : Ideal O→ℂ) (P b M : ℝ) (hP : 0<P) (hM : 0≤M)
    (hβ : ∀I∈pool,‖β I‖≤M) (hs : ∀I∈pool,β I≠0 → (I.absNorm:ℝ)≤b*P) :
    1+slotMass R pool β P≤max 1 (Real.sqrt (max 1 b)*M)*(∏I∈R,localMass I) := by
  have ha:=slotMass_bound R pool hp β P b M hP hM hβ hs
  have hb:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hc:=le_max_left 1 (Real.sqrt (max 1 b)*M)
  have hd:=le_max_right 1 (Real.sqrt (max 1 b)*M)
  have he:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
  nlinarith

def coefficientMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*∏i∈J,slotMass R (pool i) (β i) (P i)

omit [DecidableEq α] in
lemma signedCoefficient_norm (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤coefficientMajorant R D₁ D₂ J pool β P := by
  simp only [signedCoefficient,norm_mul,norm_pow,norm_neg,norm_one,one_pow,mul_one,norm_prod]
  apply mul_le_mul
  · exact mul_le_mul (plainCoefficient_norm χ D₁ (fun I hi=>hR I (hD₁ hi)))
      (plainCoefficient_norm χ D₂ (fun I hi=>hR I (hD₂ hi))) (norm_nonneg _) (weight_nonneg _)
  · exact Finset.prod_le_prod₀ (fun i _=>norm_nonneg _) (fun i _=>naturalSlot_norm χ R (pool i) (β i) (P i))
  · positivity
  · exact mul_nonneg (weight_nonneg _) (weight_nonneg _)

omit [DecidableEq α] in
lemma majorant_mass (R : Finset (Ideal O)) (F : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      coefficientMajorant R D₁ D₂ J pool β P)=
      (∏I∈R,(1+weight I))^2*(∏i∈F,(1+slotMass R (pool i) (β i) (P i))) := by
  simp only [coefficientMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

def uniformMajorant (R D₁ D₂ : Finset (Ideal O)) (J : Finset α) (b M : α→ℝ) : ℝ :=
  weight (∏I∈D₁,I)*weight (∏I∈D₂,I)*
    ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)

omit [DecidableEq α] in
lemma uniformMajorant_nonneg (R D₁ D₂ : Finset (Ideal O)) (J : Finset α)
    (b M : α→ℝ) (hM : ∀i∈J,0≤M i) :
    0≤uniformMajorant R D₁ D₂ J b M := by
  apply mul_nonneg (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_nonneg (fun i hi=>mul_nonneg
    (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
    (Finset.sum_nonneg (fun I _=>weight_nonneg I)))

omit [DecidableEq α] in
lemma signedCoefficient_uniform (χ : Character) (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (D₁ D₂ : Finset (Ideal O)) (hD₁ : D₁⊆R) (hD₂ : D₂⊆R) (J : Finset α)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P b M : α→ℝ)
    (hp : ∀i∈J,∀I∈pool i,Prime I) (hP : ∀i∈J,0<P i) (hM : ∀i∈J,0≤M i)
    (hβ : ∀i∈J,∀I∈pool i,‖β i I‖≤M i)
    (hs : ∀i∈J,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) :
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖≤uniformMajorant R D₁ D₂ J b M := by
  apply (signedCoefficient_norm χ R hR D₁ D₂ hD₁ hD₂ J pool β P).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (weight_nonneg _) (weight_nonneg _))
  exact Finset.prod_le_prod₀ (fun i _=>slotMass_nonneg _ _ _ _)
    (fun i hi=>slotMass_bound R (pool i) (hp i hi) (β i) (P i) (b i) (M i)
      (hP i hi) (hM i hi) (hβ i hi) (hs i hi))

omit [DecidableEq α] in
lemma uniformMajorant_mass (R : Finset (Ideal O)) (F : Finset α) (b M : α→ℝ) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)=
      (∏I∈R,(1+weight I))^2*
        ∏i∈F,(1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)) := by
  simp only [uniformMajorant,←Finset.mul_sum]
  rw [←Finset.prod_one_add]
  simp only [←Finset.sum_mul]
  rw [←Finset.sum_mul_sum,deletion_mass]
  ring

omit [DecidableEq α] in
lemma uniformMajorant_mass_le (R : Finset (Ideal O)) (hR : ∀I∈R,Prime I)
    (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i) :
    (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)) * (∏I∈R,localMass I)^(2+F.card) := by
  rw [uniformMajorant_mass]
  have hE:=euler_ge_one R hR
  have hp (i : α) (hi : i∈F) :
      1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
        max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
    have ha:1+∑I∈R,weight I≤∏I∈R,localMass I:=(one_add_sum_weight R).trans (deletion_le_euler R hR)
    have hb:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have hc:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
    nlinarith
  calc
    _≤(∏I∈R,localMass I)^2*
        ∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I) := by
      apply mul_le_mul
      · exact pow_le_pow_left₀ (Finset.prod_nonneg (fun I _=>by linarith [weight_nonneg I]))
          (deletion_le_euler R hR) 2
      · exact Finset.prod_le_prod₀ (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I)))) hp
      · exact Finset.prod_nonneg (fun i hi=>add_nonneg zero_le_one
          (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
            (Finset.sum_nonneg (fun I _=>weight_nonneg I))))
      · exact sq_nonneg _
    _=_ := by rw [Finset.prod_mul_distrib,Finset.prod_const,pow_add];ring

omit [DecidableEq α] in

theorem uniform_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I),
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,uniformMajorant R D₁ D₂ J b M)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  let n:ℕ:=2+F.card
  have hn:(0:ℝ)<n:=by dsimp [n];positivity
  let δ:ℝ:=ε/n
  have hδ:0<δ:=div_pos hε hn
  obtain ⟨C₀,hC₀,hbound⟩:=euler_mass_subpower δ hδ
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0<A:=Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨A*C₀^n,mul_pos hA (pow_pos hC₀ n),?_⟩
  intro R hR
  have he:0≤∏I∈R,localMass I:=(euler_ge_one R hR).trans' zero_le_one
  have hr:0≤(Ideal.absNorm (∏I∈R,I):ℝ):=Nat.cast_nonneg _
  have hpow:((Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hr]
    congr 1
    dsimp [δ]
    exact div_mul_cancel₀ _ hn.ne'
  calc
    _≤A*(∏I∈R,localMass I)^n:=uniformMajorant_mass_le R hR F b M hM
    _≤A*(C₀*(Ideal.absNorm (∏I∈R,I):ℝ)^δ)^n:=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ he (hbound R hR) n) hA.le
    _=_:=by rw [mul_pow,hpow];ring

omit [DecidableEq α] in

theorem signed_mass_subpower (F : Finset α) (b M : α→ℝ) (hM : ∀i∈F,0≤M i)
    (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖β i I‖≤M i) →
      (∀i∈F,∀I∈pool i,β i I≠0 → (I.absNorm:ℝ)≤b i*P i) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs
  apply le_trans _ (hbound R hR)
  apply Finset.sum_le_sum
  intro D₁ hD₁
  apply Finset.sum_le_sum
  intro D₂ hD₂
  apply Finset.sum_le_sum
  intro J hJ
  have hj:=Finset.mem_powerset.mp hJ
  exact signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
    (Finset.mem_powerset.mp hD₂) J pool β P b M
    (fun i hi=>hp i (hj hi)) (fun i hi=>hP i (hj hi)) (fun i hi=>hM i (hj hi))
    (fun i hi=>hβ i (hj hi)) (fun i hi=>hs i (hj hi))

lemma profile_bounds (pool : Finset (Ideal O)) (ν : Ideal O→ℂ) (W : ℝ→ℂ)
    (P b M : ℝ) (hP : 0<P) (hν : ∀I∈pool,‖ν I‖≤1)
    (hW : ∀x,‖W x‖≤M) (hs : Function.support W⊆Set.Iic b) :
    (∀I∈pool,‖ν I*W ((I.absNorm:ℝ)/P)‖≤M) ∧
      (∀I∈pool,ν I*W ((I.absNorm:ℝ)/P)≠0 → (I.absNorm:ℝ)≤b*P) := by
  constructor
  · intro I hi
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hν I hi)).trans (hW _)
  · intro I hi hn
    exact (div_le_iff₀ hP).mp (hs (right_ne_zero_of_mul hn))

omit [DecidableEq α] in

theorem profile_signed_mass_subpower (F : Finset α) (b M : α→ℝ)
    (hM : ∀i∈F,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ (R : Finset (Ideal O)) (_hR : ∀I∈R,Prime I)
      (χ : Character) (pool : α→Finset (Ideal O)) (ν : α→Ideal O→ℂ)
      (W : α→ℝ→ℂ) (P : α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I) → (∀i∈F,0<P i) →
      (∀i∈F,∀I∈pool i,‖ν i I‖≤1) → (∀i∈F,∀x,‖W i x‖≤M i) →
      (∀i∈F,Function.support (W i)⊆Set.Iic (b i)) →
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool
          (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P‖)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
  obtain ⟨C,hC,hbound⟩:=signed_mass_subpower F b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro R hR χ pool ν W P hp hP hν hW hs
  exact hbound R hR χ pool (fun i I=>ν i I*W i ((I.absNorm:ℝ)/P i)) P hp hP
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).1)
    (fun i hi=>(profile_bounds (pool i) (ν i) (W i) (P i) (b i) (M i)
      (hP i hi) (hν i hi) (hW i hi) (hs i hi)).2)

end SevenEighths.CenteredMomentCommonMaskExpansion

end

end OAI
end OAIOriginalModule1993

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonMaskEnergy
Source SHA256: 4cac2632a3141729667a2b4b43bbdddf5719f80516525ad74d5028da4dbe0e53
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1994




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentCommonMaskEnergy
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentNaturalRowSource
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation CenteredMomentLattice
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
local notation "O" => HeckeFamily.O

theorem finite_shared_energy {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a f : ι→κ→ℂ) (ρ : κ→ℝ) (hρ : ∀j,0≤ρ j)
    (ha : ∀i j,‖a i j‖≤ρ j) (E : ℝ) (hE : 0≤E)
    (hf : ∀j,(∑i,‖f i j‖^2)≤E) :
    (∑i,‖∑j,a i j*f i j‖^2)≤(∑j,ρ j)^2*E := by
  have hb (j : κ) : (∑i,‖a i j*f i j‖^2)≤(ρ j*Real.sqrt E)^2 := by
    calc
      _≤∑i,(ρ j)^2*‖f i j‖^2 := Finset.sum_le_sum (fun i _=>by
        rw [norm_mul,mul_pow]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (ha i j) 2) (sq_nonneg _))
      _=(ρ j)^2*(∑i,‖f i j‖^2) := (Finset.mul_sum _ _ _).symm
      _≤(ρ j)^2*E := mul_le_mul_of_nonneg_left (hf j) (sq_nonneg _)
      _=_ := by rw [mul_pow,Real.sq_sqrt hE]
  have hh := CompletedGauss.finite_tsum_energy_bound
    (fun j i=>a i j*f i j) (fun j=>ρ j*Real.sqrt E)
    (fun j=>mul_nonneg (hρ j) (Real.sqrt_nonneg _)) (summable_of_hasFiniteSupport (Set.toFinite _)) hb
  simpa only [tsum_fintype,←Finset.sum_mul,mul_pow,Real.sq_sqrt hE] using hh.2

lemma triple_sum {τ : Type*} {υ : Type*} {ξ : Type*} {A : Type*} [AddCommMonoid A]
    (S : Finset τ) (T : Finset υ) (U : Finset ξ)
    [Fintype ({x // x∈S}×{x // x∈T}×{x // x∈U})]
    (g : τ→υ→ξ→A) :
    (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑x∈S,∑y∈T,∑z∈U,g x y z := by
  have hh : (∑j : {x // x∈S}×{x // x∈T}×{x // x∈U},g j.1.val j.2.1.val j.2.2.val)=
      ∑j∈S×ˢ(T×ˢU),g j.1 j.2.1 j.2.2 := by
    apply Finset.sum_bij (fun j _=>(j.1.val,j.2.1.val,j.2.2.val))
    · intro j _
      exact Finset.mem_product.mpr ⟨j.1.property,Finset.mem_product.mpr ⟨j.2.1.property,j.2.2.property⟩⟩
    · intro i _ j _ h
      apply Prod.ext
      · exact Subtype.ext (congrArg Prod.fst h)
      · apply Prod.ext
        · exact Subtype.ext (congrArg (fun x=>x.2.1) h)
        · exact Subtype.ext (congrArg (fun x=>x.2.2) h)
    · intro j hj
      obtain ⟨h1,h23⟩:=Finset.mem_product.mp hj
      obtain ⟨h2,h3⟩:=Finset.mem_product.mp h23
      exact ⟨(⟨j.1,h1⟩,⟨j.2.1,h2⟩,⟨j.2.2,h3⟩),Finset.mem_univ _,rfl⟩
    · intro j _
      rfl
  simpa only [Finset.sum_product] using hh

theorem actual_shared_energy {α : Type*} [DecidableEq α]
    (F : Finset α) (b M : α→ℝ) (hM : ∀j∈F,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hmass⟩:=uniform_mass_subpower F b M hM (ε/2) (by positivity)
  refine ⟨C^2,sq_pos_of_pos hC,?_⟩
  intro ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE he
  let κ := {D : Finset (Ideal O) // D∈R.powerset} ×
    {D : Finset (Ideal O) // D∈R.powerset} × {J : Finset α // J∈F.powerset}
  let a (i : ι) (j : κ) := signedCoefficient (χ i) R j.1.val j.2.1.val j.2.2.val (pool i) (β i) (P i)
  let f (i : ι) (j : κ) := HeckeDyadic.polynomial (χ i) false (W₁ i)
    (X₁ i/(Ideal.absNorm (∏I∈j.1.val,I):ℝ)) 0 0 *
    HeckeDyadic.polynomial (χ i) false (W₂ i)
    (X₂ i/(Ideal.absNorm (∏I∈j.2.1.val,I):ℝ)) 0 0 *
    ∏k∈F\j.2.2.val,naturalSlot (χ i) (pool i k) (β i k) (P i k)
  let ρ (j : κ) := uniformMajorant R j.1.val j.2.1.val j.2.2.val b M
  have hρ (j : κ) : 0≤ρ j := uniformMajorant_nonneg _ _ _ _ _ _
    (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
  have ha (i : ι) (j : κ) : ‖a i j‖≤ρ j := by
    exact signedCoefficient_uniform (χ i) R hR _ _
      (Finset.mem_powerset.mp j.1.property) (Finset.mem_powerset.mp j.2.1.property)
      _ (pool i) (β i) (P i) b M
      (fun k hk=>hp i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hP i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hM k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hβ i k (Finset.mem_powerset.mp j.2.2.property hk))
      (fun k hk=>hs i k (Finset.mem_powerset.mp j.2.2.property hk))
  have hh:=finite_shared_energy a f ρ hρ ha E hE
    (fun j=>he j.1.val j.1.property j.2.1.val j.2.1.property j.2.2.val j.2.2.property)
  have hid (i : ι) : (∑j,a i j*f i j)=
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
      HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
      ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>signedCoefficient (χ i) R D₁ D₂ J (pool i) (β i) (P i)*
        (HeckeDyadic.polynomial (χ i) false (W₁ i) (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
         HeckeDyadic.polynomial (χ i) false (W₂ i) (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
         ∏k∈F\J,naturalSlot (χ i) (pool i k) (β i k) (P i k)))).trans
      (simultaneous_deletion (χ i) R hR (W₁ i) (W₂ i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
        F (pool i) (hp i) (β i) (P i)).symm
  have hm : (∑j,ρ j)≤C*(Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2) := by
    exact (triple_sum R.powerset R.powerset F.powerset
      (fun D₁ D₂ J=>uniformMajorant R D₁ D₂ J b M)).trans_le (hmass R hR)
  have hr : ((Ideal.absNorm (∏I∈R,I):ℝ)^(ε/2))^2=(Ideal.absNorm (∏I∈R,I):ℝ)^ε := by
    rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num
  simp_rw [hid] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_right
    (pow_le_pow_left₀ (Finset.sum_nonneg (fun j _=>hρ j)) hm 2) hE).trans_eq
      (by rw [mul_pow,hr]))

lemma sqrt_inverse_cpow (X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹=(X:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hX.le (1/2:ℝ))

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    HeckeDyadic.polynomial χ false W X 0 0=(Real.sqrt X:ℂ)⁻¹*idealSum χ W X := by
  rw [sqrt_inverse_cpow X hX]
  unfold HeckeDyadic.polynomial idealSum
  congr 1
  have he:=tsum_subtype_eq_of_support_subset
    (s:={I : Ideal O | I≠0}) (f:=fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi;subst I;exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=_ at he
  simpa only [HeckeDyadic.summand,HeckeDyadic.coefficient,Bool.false_eq_true,ite_false,
    HeckeDyadic.norm,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,
    neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

def heightCoefficient (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) : ℂ :=
  β I*(I.absNorm:ℂ)^(Complex.I*t)

lemma heightCoefficient_norm (β : Ideal O→ℂ) (t : ℝ) (I : Ideal O) (hI : I≠0) :
    ‖heightCoefficient β t I‖=‖β I‖ := by
  have hn : (0:ℝ)<I.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  rw [heightCoefficient,norm_mul]
  have hp : ‖(I.absNorm:ℂ)^(Complex.I*t)‖=1 := by
    simpa using Complex.norm_cpow_eq_rpow_re_of_pos hn (Complex.I*t)
  rw [hp,mul_one]

lemma normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X : ℝ) (hX : 0<X) :
    (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X=
      (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
        (normPowerProfile W a b ha hs hW t) X 0 0 := by
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX,plain_zero_height _ _ X hX]
  ring

theorem original_positive_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (hP : ∀i,0<P i) (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t) X₁ 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₂ 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  rw [F.masked_positive R hR,twistedIdealSum_scale _ W₁ a₁ b₁ ha₁ hs₁ hW₁ t X₁ hX₁,
    twistedIdealSum_scale _ W₂ a₂ b₂ ha₂ hs₂ hW₂ t X₂ hX₂,
    plain_zero_height _ _ X₁ hX₁,plain_zero_height _ _ X₂ hX₂]
  have hn : (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹=
      (Real.sqrt X₁:ℂ)⁻¹*(Real.sqrt X₂:ℂ)⁻¹*∏i,(Real.sqrt (P i):ℂ)⁻¹ := by
    rw [Real.sqrt_mul (mul_pos hX₁ hX₂).le,Real.sqrt_mul hX₁.le,
      Real.sqrt_prod _ (fun i _=>(hP i).le),Complex.ofReal_mul,Complex.ofReal_mul,
      Complex.ofReal_prod,mul_inv_rev,mul_inv_rev,Finset.prod_inv_distrib]
    ring
  have hc (i : α) : (∑I∈pool i,β i I*idealCoeff (excluded F.character R) I*(I.absNorm:ℂ)^(Complex.I*t))=
      ∑I∈pool i,idealCoeff (excluded F.character R) I*heightCoefficient (β i) t I := by
    apply Finset.sum_congr rfl
    intro I hI
    unfold heightCoefficient
    ring
  simp_rw [hc]
  simp only [naturalSlot,Finset.prod_mul_distrib]
  rw [hn]
  ring

lemma deleted_height_phase (X N t : ℝ) (hX : 0<X) (hN : 0<N) :
    (X:ℂ)^(Complex.I*t)=(N:ℂ)^(Complex.I*t)*((X/N:ℝ):ℂ)^(Complex.I*t) := by
  have hh:=Complex.mul_cpow_ofReal_nonneg hN.le (div_nonneg hX.le hN.le) (Complex.I*t)
  rw [←Complex.ofReal_mul,show N*(X/N)=X by field_simp] at hh
  exact hh

lemma positive_height_phase_norm (X t : ℝ) (hX : 0<X) : ‖(X:ℂ)^(Complex.I*t)‖=1 := by
  simpa using Complex.norm_cpow_eq_rpow_re_of_pos hX (Complex.I*t)

lemma deleted_normalized_twisted_plain (χ : Character) (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (t X N : ℝ) (hX : 0<X) (hN : 0<N) :
    (X:ℂ)^(Complex.I*t)*HeckeDyadic.polynomial χ false
      (normPowerProfile W a b ha hs hW t) (X/N) 0 0=
      (N:ℂ)^(Complex.I*t)*((Real.sqrt (X/N):ℂ)⁻¹*twistedIdealSum χ W t (X/N)) := by
  rw [normalized_twisted_plain χ W a b ha hs hW t (X/N) (div_pos hX hN),
    deleted_height_phase X N t hX hN]
  ring

theorem original_positive_deletion {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ((X₁:ℂ)^(Complex.I*t)*(X₂:ℂ)^(Complex.I*t))*
        ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
          signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          (HeckeDyadic.polynomial χ false (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
            (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
           HeckeDyadic.polynomial χ false (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t)
            (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
           ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_normalized (naturalRow η z hz) R hR W₁ W₂ a₁ b₁ a₂ b₂
    ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P hP t X₁ X₂ hX₁ hX₂]
  congr 1
  exact simultaneous_deletion (naturalRow η z hz).character (CompletedGauss.primeSupport R)
    (support_prime R) (normPowerProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ t)
    (normPowerProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ t) X₁ X₂ hX₁ hX₂ Finset.univ pool
    (fun i _=>hp i) (fun i=>heightCoefficient (β i) t) P

theorem original_retained_normalized {α : Type*} [Fintype α] [DecidableEq α]
    {η : Character} {z : O} (F : NaturalRow η z) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hr₁ : 1≤X₁*b₁) (hr₂ : 1≤X₂*b₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      (((clippedScale X₁):ℂ)^(Complex.I*t)*((clippedScale X₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₁ a₁ b₁ ha₁ hs₁ hW₁ X₁ hX₁ hr₁ t) (clippedScale X₁) 0 0 *
         HeckeDyadic.polynomial (excluded F.character R) false
          (retainedProfile W₂ a₂ b₂ ha₂ hs₂ hW₂ X₂ hX₂ hr₂ t) (clippedScale X₂) 0 0 *
         ∏i,naturalSlot (excluded F.character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  exact original_positive_normalized F R hR (dilated W₁ (clipDilation X₁))
    (dilated W₂ (clipDilation X₂)) (a₁/max 1 b₁) b₁ (a₂/max 1 b₂) b₂
    (div_pos ha₁ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (div_pos ha₂ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    (dilated_support W₁ a₁ b₁ (max 1 b₁) (clipDilation X₁) ha₁ (le_max_left _ _)
      (clipDilation_ge_one X₁ hX₁) (clipDilation_le b₁ X₁ hX₁ hr₁) hs₁)
    (dilated_support W₂ a₂ b₂ (max 1 b₂) (clipDilation X₂) ha₂ (le_max_left _ _)
      (clipDilation_ge_one X₂ hX₂) (clipDilation_le b₂ X₂ hX₂ hr₂) hs₂)
    (dilated_contDiff W₁ hW₁ _) (dilated_contDiff W₂ hW₂ _) pool β P hP t
    _ _ (by unfold clippedScale;positivity) (by unfold clippedScale;positivity)

theorem original_retained_zero {α : Type*} [Fintype α]
    (η : Character) (m A z : O) (W₁ W₂ : ℝ→ℂ) (b₁ b₂ : ℝ)
    (hs₁ : Function.support W₁⊆Set.Iic b₁) (hs₂ : Function.support W₂⊆Set.Iic b₂)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂)
    (hz : X₁*b₁<1 ∨ X₂*b₂<1) :
    retainedPositiveRow η m A z W₁ W₂ pool β P t X₁ X₂=0 := by
  unfold retainedPositiveRow positiveSlotRow
  rw [←clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  rcases hz with h|h
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h]
    simp
  · rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h]
    simp

theorem original_positive_energy {α : Type*} [Fintype α] [DecidableEq α]
    (b M : α→ℝ) (hM : ∀j,0≤M j) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)(R : Ideal O),R≠0 →
      ∀(W₁ W₂ : ι→ℝ→ℂ)(a₁ b₁ a₂ b₂ : ι→ℝ)
        (ha₁ : ∀i,0<a₁ i)(ha₂ : ∀i,0<a₂ i)
        (hs₁ : ∀i,Function.support (W₁ i)⊆Set.Icc (a₁ i) (b₁ i))
        (hs₂ : ∀i,Function.support (W₂ i)⊆Set.Icc (a₂ i) (b₂ i))
        (hW₁ : ∀i,ContDiff ℝ ∞ (W₁ i))(hW₂ : ∀i,ContDiff ℝ ∞ (W₂ i))
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)
        (t X₁ X₂ : ι→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,∀I∈pool i j,Prime I) → (∀i j,0<P i j) →
      (∀i j,∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      let χ:=fun i=>(naturalRow (η i) (z i) (hz i)).character
      let S:=CompletedGauss.primeSupport R
      (∀D₁∈S.powerset,∀D₂∈S.powerset,∀J∈(Finset.univ : Finset α).powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false
          (normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈Finset.univ\J,naturalSlot (χ i) (pool i j) (heightCoefficient (β i j) (t i)) (P i j)‖^2)≤E) →
      (∑i,‖positiveSlotRow (η i)
        (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
        1 (z i) (W₁ i) (W₂ i) (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i)‖^2)≤
        C*(Ideal.absNorm (∏I∈S,I):ℝ)^ε*E := by
  obtain ⟨C,hC,hbound⟩:=actual_shared_energy (Finset.univ : Finset α) b M (fun j _=>hM j) ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂ pool β P t X₁ X₂
    hX₁ hX₂ hp hP hβ hs E hE
  dsimp only
  intro hchild
  have hh:=hbound (CompletedGauss.primeSupport R) (support_prime R)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>normPowerProfile (W₁ i) (a₁ i) (b₁ i) (ha₁ i) (hs₁ i) (hW₁ i) (t i))
    (fun i=>normPowerProfile (W₂ i) (a₂ i) (b₂ i) (ha₂ i) (hs₂ i) (hW₂ i) (t i))
    X₁ X₂ pool (fun i j=>heightCoefficient (β i j) (t i)) P hX₁ hX₂
    (fun i j _=>hp i j) (fun i j _=>hP i j)
    (fun i j _ I hi=>by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=>hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι) := original_positive_normalized (naturalRow (η i) (z i) (hz i)) R hR
    (W₁ i) (W₂ i) (a₁ i) (b₁ i) (a₂ i) (b₂ i) (ha₁ i) (ha₂ i) (hs₁ i) (hs₂ i)
    (hW₁ i) (hW₂ i) (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  simp_rw [he,norm_mul,positive_height_phase_norm _ _ (hX₁ _),
    positive_height_phase_norm _ _ (hX₂ _),one_mul]
  simpa only [excluded,norm_mul] using hh

theorem original_positive_deletion_height {α : Type*} [Fintype α] [DecidableEq α]
    (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (W₁ W₂ : ℝ→ℂ) (a₁ b₁ a₂ b₂ : ℝ) (ha₁ : 0<a₁) (ha₂ : 0<a₂)
    (hs₁ : Function.support W₁⊆Set.Icc a₁ b₁) (hs₂ : Function.support W₂⊆Set.Icc a₂ b₂)
    (hW₁ : ContDiff ℝ ∞ W₁) (hW₂ : ContDiff ℝ ∞ W₂)
    (pool : α→Finset (Ideal O)) (hp : ∀i,∀I∈pool i,Prime I)
    (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    let χ:=(naturalRow η z hz).character
    let S:=CompletedGauss.primeSupport R
    positiveSlotRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z W₁ W₂ pool β P t X₁ X₂=
      ∑D₁∈S.powerset,∑D₂∈S.powerset,∑J∈(Finset.univ : Finset α).powerset,
        (signedCoefficient χ S D₁ D₂ J pool (fun i=>heightCoefficient (β i) t) P *
          ((Ideal.absNorm (∏I∈D₁,I):ℂ)^(Complex.I*t)*
           (Ideal.absNorm (∏I∈D₂,I):ℂ)^(Complex.I*t))) *
        (((Real.sqrt (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₁ t (X₁/(Ideal.absNorm (∏I∈D₁,I):ℝ))) *
         ((Real.sqrt (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ)):ℂ)⁻¹ *
          twistedIdealSum χ W₂ t (X₂/(Ideal.absNorm (∏I∈D₂,I):ℝ))) *
         ∏i∈Finset.univ\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)) := by
  dsimp only
  rw [original_positive_deletion η z hz R hR W₁ W₂ a₁ b₁ a₂ b₂ ha₁ ha₂ hs₁ hs₂ hW₁ hW₂
    pool hp β P hP t X₁ X₂ hX₁ hX₂]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D₁ hD₁
  apply Finset.sum_congr rfl
  intro D₂ hD₂
  apply Finset.sum_congr rfl
  intro J hJ
  have hN₁:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₁
    (fun I hi=>support_prime R I (Finset.mem_powerset.mp hD₁ hi))
  have hN₂:=CenteredMomentReflectionDeletion.subset_product_norm_pos D₂
    (fun I hi=>support_prime R I (Finset.mem_powerset.mp hD₂ hi))
  have h1:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₁ a₁ b₁ ha₁ hs₁ hW₁
    t X₁ (Ideal.absNorm (∏I∈D₁,I):ℝ) hX₁ hN₁
  have h2:=deleted_normalized_twisted_plain (naturalRow η z hz).character W₂ a₂ b₂ ha₂ hs₂ hW₂
    t X₂ (Ideal.absNorm (∏I∈D₂,I):ℝ) hX₂ hN₂
  convert congrArg (fun q : ℂ=>
    signedCoefficient (naturalRow η z hz).character (CompletedGauss.primeSupport R) D₁ D₂ J pool
      (fun i=>heightCoefficient (β i) t) P * q *
      ∏i∈Finset.univ\J,naturalSlot (naturalRow η z hz).character (pool i) (heightCoefficient (β i) t) (P i))
    (congrArg₂ (fun x y : ℂ=>x*y) h1 h2) using 1 <;> push_cast <;> ring

end SevenEighths.CenteredMomentCommonMaskEnergy

end

end OAI
end OAIOriginalModule1994

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AllocatedNaturalSource
Source SHA256: b2dcf790d4b8c2d013c039119eca3c064d33afca72214a3a5585995ee0a436f3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1995





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentAllocatedNaturalSource
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentCommonMaskEnergy
open CenteredMomentNaturalRowSource CenteredMomentRetainedEnergy CenteredMomentRetainedProfile
open CenteredMomentHeckeTwist CenteredMomentHeckeVolume CenteredMomentHeckeCancellation
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained
local notation "O" => HeckeFamily.O

structure Plain where
  W : ℝ→ℂ
  a : ℝ
  b : ℝ
  a_pos : 0<a
  support : Function.support W⊆Set.Icc a b
  smooth : ContDiff ℝ ∞ W

def Plain.profile (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) : 𝓢(ℝ,ℂ) :=
  if h : 1≤U*V.b then retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t else 0

lemma Plain.profile_retained (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : 1≤U*V.b) :
    V.profile U hU t=retainedProfile V.W V.a V.b V.a_pos V.support V.smooth U hU h t := by
  simp [Plain.profile,h]

lemma Plain.profile_zero (V : Plain) (U : ℝ) (hU : 0<U) (t : ℝ) (h : U*V.b<1) :
    V.profile U hU t=0 := by simp [Plain.profile,not_le.mpr h]

lemma polynomial_zero (χ : Character) (X : ℝ) :
    HeckeDyadic.polynomial χ false (0 : 𝓢(ℝ,ℂ)) X 0 0=0 := by
  simp [HeckeDyadic.polynomial,HeckeDyadic.summand]

theorem retained_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    {α : Type*} [Fintype α] [DecidableEq α] (V₁ V₂ : Plain)
    (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t U₁ U₂ : ℝ) (hU₁ : 0<U₁) (hU₂ : 0<U₂) :
    retainedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z V₁.W V₂.W pool β P t U₁ U₂=
      (((clippedScale U₁):ℂ)^(Complex.I*t)*((clippedScale U₂):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile U₁ hU₁ t) (clippedScale U₁) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile U₂ hU₂ t) (clippedScale U₂) 0 0 *
         ∏i,naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i)) := by
  by_cases h₁ : 1≤U₁*V₁.b
  · by_cases h₂ : 1≤U₂*V₂.b
    · rw [V₁.profile_retained U₁ hU₁ t h₁,V₂.profile_retained U₂ hU₂ t h₂]
      exact original_retained_normalized (naturalRow η z hz) R hR _ _ _ _ _ _ V₁.a_pos V₂.a_pos
        V₁.support V₂.support V₁.smooth V₂.smooth pool β P hP t U₁ U₂ hU₁ hU₂ h₁ h₂
    · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
        (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
        (Or.inr (lt_of_not_ge h₂)),V₂.profile_zero U₂ hU₂ t (lt_of_not_ge h₂),polynomial_zero]
      simp
  · rw [original_retained_zero η _ 1 z V₁.W V₂.W V₁.b V₂.b
      (fun _ h=>(V₁.support h).2) (fun _ h=>(V₂.support h).2) pool β P t U₁ U₂ hU₁ hU₂
      (Or.inl (lt_of_not_ge h₁)),V₁.profile_zero U₁ hU₁ t (lt_of_not_ge h₁),polynomial_zero]
    simp

variable {α : Type*} [Fintype α] [DecidableEq α]

def rawScale (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) (X : ℝ) (j : Fin 2) : ℝ :=
  X/Ideal.absNorm (selectedPlain D a j)

lemma rawScale_pos (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X : ℝ) (hX : 0<X) (j : Fin 2) : 0<rawScale D a X j := by
  apply div_pos hX
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (selectedDivisor_ne_zero D Finset.univ a _))

lemma raw_same_product (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (X₁ X₂ Y₁ Y₂ : ℝ) (h : X₁*X₂=Y₁*Y₂) :
    rawScale D a X₁ 0*rawScale D a X₂ 1=rawScale D a Y₁ 0*rawScale D a Y₂ 1 := by
  simp only [rawScale,div_mul_div_comm,h]

theorem allocated_normalized (η : Character) (z : O) (hz : z≠0) (R : Ideal O) (hR : R≠0)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ) (hP : ∀i,0<P i)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) :
    allocatedPositiveRow η (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 z t pool β P D a V₁.W V₂.W X₁ X₂=
      (((clippedScale (rawScale D a X₁ 0)):ℂ)^(Complex.I*t)*
       ((clippedScale (rawScale D a X₂ 1)):ℂ)^(Complex.I*t))*
        (HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t) (clippedScale (rawScale D a X₁ 0)) 0 0 *
         HeckeDyadic.polynomial (excluded (naturalRow η z hz).character R) false
          (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t) (clippedScale (rawScale D a X₂ 1)) 0 0 *
         ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
           (pool i) (heightCoefficient (β i) t) (P i)) := by
  have h:=retained_normalized η z hz R hR V₁ V₂
    (fun i : liveIndices D a=>pool i) (fun i : liveIndices D a=>β i) (fun i : liveIndices D a=>P i)
    (fun i=>hP i) t _ _ (rawScale_pos D a X₁ hX₁ 0) (rawScale_pos D a X₂ hX₂ 1)
  have hp': (∏i : liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i))=
      ∏i∈liveIndices D a,naturalSlot (excluded (naturalRow η z hz).character R)
      (pool i) (heightCoefficient (β i) t) (P i) := Finset.prod_coe_sort (liveIndices D a) (fun i : α=>naturalSlot (excluded (naturalRow η z hz).character R) (pool i) (heightCoefficient (β i) t) (P i))
  rw [hp'] at h
  exact h

omit [Fintype α] [DecidableEq α] in

theorem slot_controls (ν : α→Ideal O→ℂ) (W : α→ℝ→ℂ) (P b M : α→ℝ)
    (hP : ∀i,0<P i) (hν : ∀i I,‖ν i I‖≤1)
    (hW : ∀i x,‖W i x‖≤M i) (hs : ∀i,Function.support (W i)⊆Set.Iic (b i)) :
    (∀i I,‖ν i I*W i ((I.absNorm:ℝ)/P i)‖≤M i) ∧
    (∀i I,ν i I*W i ((I.absNorm:ℝ)/P i)≠0 → (I.absNorm:ℝ)≤b i*P i) := by
  constructor
  · intro i I
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right (hν i I) (norm_nonneg _)).trans (by simpa using hW i _)
  · intro i I hn
    exact (div_le_iff₀ (hP i)).mp (hs i (right_ne_zero_of_mul hn))

def SharedBound (F : Finset α) (b M : α→ℝ) (C ε : ℝ) : Prop :=
    ∀{ι : Type*} [Fintype ι],
      ∀(R : Finset (Ideal O))(hR : ∀I∈R,Prime I)(χ : ι→Character)
        (W₁ W₂ : ι→𝓢(ℝ,ℂ))(X₁ X₂ : ι→ℝ)
        (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ),
      (∀i,0<X₁ i) → (∀i,0<X₂ i) →
      (∀i j,j∈F → ∀I∈pool i j,Prime I) → (∀i j,j∈F → 0<P i j) →
      (∀i j,j∈F → ∀I∈pool i j,‖β i j I‖≤M j) →
      (∀i j,j∈F → ∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
      ∀E : ℝ,0≤E →
      (∀D₁∈R.powerset,∀D₂∈R.powerset,∀J∈F.powerset,
        (∑i,‖HeckeDyadic.polynomial (χ i) false (W₁ i)
          (X₁ i/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
          HeckeDyadic.polynomial (χ i) false (W₂ i)
          (X₂ i/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
          ∏j∈F\J,naturalSlot (χ i) (pool i j) (β i j) (P i j)‖^2)≤E) →
      (∑i,‖HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₁ i) (X₁ i) 0 0 *
        HeckeDyadic.polynomial ((χ i).excludePrimes R hR) false (W₂ i) (X₂ i) 0 0 *
        ∏j∈F,naturalSlot ((χ i).excludePrimes R hR) (pool i j) (β i j) (P i j)‖^2)≤
        C*(Ideal.absNorm (∏I∈R,I):ℝ)^ε*E

theorem uniform_shared (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀F : Finset α,SharedBound F b M C ε := by
  have he (F : Finset α) : ∃C : ℝ,0<C ∧ SharedBound F b M C ε :=
    actual_shared_energy F b M (fun i _=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑F : Finset α,C F
  have hsum : 0≤∑F : Finset α,C F:=Finset.sum_nonneg (fun F _=>(hC F).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro F ι _ R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C F≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ F)
    dsimp [B]
    linarith
  exact (hb F R hR χ W₁ W₂ X₁ X₂ pool β P hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

lemma primeSupport_product_radical (R : Ideal O) (hR : R≠0) :
    (∏I∈CompletedGauss.primeSupport R,I)=R.radical := by
  ext x
  change x∈(∏I∈CompletedGauss.primeSupport R,I) ↔ ∃n : ℕ,x^n∈R
  simp_rw [←Ideal.span_singleton_le_iff_mem,←Ideal.dvd_iff_le,←Ideal.span_singleton_pow]
  exact (UniqueFactorizationMonoid.exists_dvd_pow_iff_radical_dvd hR).symm

def child (χ : Character) (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2)))
    (V₁ V₂ : Plain) (pool : α→Finset (Ideal O)) (β : α→Ideal O→ℂ) (P : α→ℝ)
    (t X₁ X₂ : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (D₁ D₂ : Finset (Ideal O)) (J : Finset α) : ℂ :=
  HeckeDyadic.polynomial χ false (V₁.profile _ (rawScale_pos D a X₁ hX₁ 0) t)
    (clippedScale (rawScale D a X₁ 0)/(Ideal.absNorm (∏I∈D₁,I):ℝ)) 0 0 *
  HeckeDyadic.polynomial χ false (V₂.profile _ (rawScale_pos D a X₂ hX₂ 1) t)
    (clippedScale (rawScale D a X₂ 1)/(Ideal.absNorm (∏I∈D₂,I):ℝ)) 0 0 *
  ∏i∈liveIndices D a\J,naturalSlot χ (pool i) (heightCoefficient (β i) t) (P i)

def AllocatedBound (b M : α→ℝ) (C ε : ℝ) : Prop :=
  ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (α⊕Fin 2))),
  ∀{ι : Type*} [Fintype ι],∀(η : ι→Character)(z : ι→O)(hz : ∀i,z i≠0)
    (R : Ideal O),R≠0 → ∀(V₁ V₂ : ι→Plain)
    (pool : ι→α→Finset (Ideal O))(β : ι→α→Ideal O→ℂ)(P : ι→α→ℝ)(t X₁ X₂ : ι→ℝ)
    (hX₁ : ∀i,0<X₁ i)(hX₂ : ∀i,0<X₂ i),
    (∀i j,∀I∈pool i j,Prime I) → (∀i j,0<P i j) →
    (∀i j,∀I∈pool i j,‖β i j I‖≤M j) →
    (∀i j,∀I∈pool i j,β i j I≠0 → (I.absNorm:ℝ)≤b j*P i j) →
    ∀E : ℝ,0≤E →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (η i) (z i) (hz i)).character D a (V₁ i) (V₂ i)
         (pool i) (β i) (P i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i) D₁ D₂ J‖^2)≤E) →
    (∑i,‖allocatedPositiveRow (η i)
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (z i) (t i) (pool i) (β i) (P i) D a (V₁ i).W (V₂ i).W (X₁ i) (X₂ i)‖^2)≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*E

theorem allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ AllocatedBound b M C ε := by
  obtain ⟨C,hC,hbound⟩:=uniform_shared b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hh:=hbound (liveIndices D a) (CompletedGauss.primeSupport R) (support_prime R)
    (fun i=>(naturalRow (η i) (z i) (hz i)).character)
    (fun i=>(V₁ i).profile _ (rawScale_pos D a (X₁ i) (hX₁ i) 0) (t i))
    (fun i=>(V₂ i).profile _ (rawScale_pos D a (X₂ i) (hX₂ i) 1) (t i))
    (fun i=>clippedScale (rawScale D a (X₁ i) 0)) (fun i=>clippedScale (rawScale D a (X₂ i) 1))
    pool (fun i j=>heightCoefficient (β i j) (t i)) P
    (fun _=>by unfold clippedScale;positivity) (fun _=>by unfold clippedScale;positivity)
    (fun i j _=>hp i j) (fun i j _=>hP i j)
    (fun i j _ I hi=>by rw [heightCoefficient_norm _ _ _ (hp i j I hi).ne_zero];exact hβ i j I hi)
    (fun i j _ I hi hn=>hs i j I hi (left_ne_zero_of_mul hn)) E hE hchild
  have he (i : ι):=allocated_normalized (η i) (z i) (hz i) R hR D a (V₁ i) (V₂ i)
    (pool i) (β i) (P i) (hP i) (t i) (X₁ i) (X₂ i) (hX₁ i) (hX₂ i)
  have hphase (U t : ℝ) : ‖((clippedScale U):ℂ)^(Complex.I*t)‖=1 :=
    positive_height_phase_norm _ _ (by unfold clippedScale;positivity)
  simp_rw [he,norm_mul,hphase,one_mul]
  rw [←primeSupport_product_radical R hR]
  simpa only [SharedBound,excluded,norm_mul] using hh

theorem uniform_allocated_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
      AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε := by
  have he (T : Finset α) : ∃C : ℝ,0<C ∧ AllocatedBound (fun i : T=>b i) (fun i : T=>M i) C ε :=
    allocated_energy (fun i : T=>b i) (fun i : T=>M i) (fun i=>hM i) ε hε
  choose C hC hb using he
  let B : ℝ:=1+∑T : Finset α,C T
  have hsum : 0≤∑T : Finset α,C T:=Finset.sum_nonneg (fun T _=>(hC T).le)
  refine ⟨B,by dsimp [B];linarith,?_⟩
  intro T D a ι _ η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild
  have hCB : C T≤B := by
    have hh:=Finset.single_le_sum (fun G _=>(hC G).le) (Finset.mem_univ T)
    dsimp [B]
    linarith
  exact (hb T D a η z hz R hR V₁ V₂ pool β P t X₁ X₂ hX₁ hX₂ hp hP hβ hs E hE hchild).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCB (Real.rpow_nonneg (Nat.cast_nonneg _) _)) hE)

theorem natural_nonprincipal_width (η : Character) (z : O) (hz : z≠0)
    (Q R : Ideal O) (hR : R≠0)
    (hex : ¬CenteredExceptionalProfile.FixedInducingRow η Q
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R) 1 z)
    (Z m q Cz : ℝ) (hZ : 0<Z) (hCz : 0≤Cz)
    (hη : (η.modulus.absNorm:ℝ)≤Z^m) (hrow : ((Ideal.span {z}).absNorm:ℝ)≤Cz*Z^q) :
    (naturalRow η z hz).character.residue≠1 ∧
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤(fixedConductorFactor:ℝ)*Cz*Z^(m+q) :=
  ⟨(naturalRow η z hz).nonprincipal hz Q R hR hex,
    (naturalRow η z hz).modulus_power_bound Z m q Cz hZ hCz hη hrow⟩

structure Slots (α : Type*) (b M : α→ℝ) where
  pool : α→Finset (Ideal O)
  ν : α→Ideal O→ℂ
  W : α→ℝ→ℂ
  P : α→ℝ
  prime : ∀i,∀I∈pool i,Prime I
  P_pos : ∀i,0<P i
  ν_bound : ∀i I,‖ν i I‖≤1
  W_bound : ∀i x,‖W i x‖≤M i
  support : ∀i,Function.support (W i)⊆Set.Iic (b i)

def Slots.coefficient {b M : α→ℝ} (s : Slots α b M) (i : α) (I : Ideal O) : ℂ :=
  s.ν i I*s.W i ((I.absNorm:ℝ)/s.P i)

omit [Fintype α] [DecidableEq α] in
lemma Slots.controls {b M : α→ℝ} (s : Slots α b M) :
    (∀i I,‖s.coefficient i I‖≤M i) ∧
    (∀i I,s.coefficient i I≠0 → (I.absNorm:ℝ)≤b i*s.P i) :=
  slot_controls s.ν s.W s.P b M s.P_pos s.ν_bound s.W_bound s.support

structure Row (α : Type*) (b M : α→ℝ) where
  η : Character
  z : O
  z_ne : z≠0
  plain₁ : Plain
  plain₂ : Plain
  slots : Slots α b M
  t : ℝ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ
  X₁_pos : 0<X₁
  X₂_pos : 0<X₂
  Y₁_pos : 0<Y₁
  Y₂_pos : 0<Y₂
  same_product : X₁*X₂=Y₁*Y₂

lemma Row.extracted_same_product {b M : α→ℝ} (s : Row α b M)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (α⊕Fin 2))) :
    rawScale D a s.X₁ 0*rawScale D a s.X₂ 1=rawScale D a s.Y₁ 0*rawScale D a s.Y₂ 1 :=
  raw_same_product D a _ _ _ _ s.same_product

theorem uniform_paired_nuW_energy (b M : α→ℝ) (hM : ∀i,0≤M i) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀T : Finset α,
    ∀(D : Ideal O)(a : Allocation D (Finset.univ : Finset (T⊕Fin 2))),
    ∀{ι : Type*} [Fintype ι],∀s : ι→Row T (fun i=>b i) (fun i=>M i),
    ∀(R : Ideal O),R≠0 → ∀E₁ E₂ : ℝ,0≤E₁ → 0≤E₂ →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).X₁ (s i).X₂ (s i).X₁_pos (s i).X₂_pos D₁ D₂ J‖^2)≤E₁) →
    (∀D₁∈(CompletedGauss.primeSupport R).powerset,
     ∀D₂∈(CompletedGauss.primeSupport R).powerset,∀J∈(liveIndices D a).powerset,
       (∑i,‖child (naturalRow (s i).η (s i).z (s i).z_ne).character D a
         (s i).plain₁ (s i).plain₂ (s i).slots.pool (s i).slots.coefficient (s i).slots.P
         (s i).t (s i).Y₁ (s i).Y₂ (s i).Y₁_pos (s i).Y₂_pos D₁ D₂ J‖^2)≤E₂) →
    (∑i,(‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).X₁ (s i).X₂‖^2+
      ‖allocatedPositiveRow (s i).η
      (CenteredMomentSecondHeightFamily.fixedBadMask*ConcretePrimeRowBridge.idealGenerator R)
      1 (s i).z (s i).t (s i).slots.pool (s i).slots.coefficient (s i).slots.P D a
      (s i).plain₁.W (s i).plain₂.W (s i).Y₁ (s i).Y₂‖^2))≤
      C*(Ideal.absNorm R.radical:ℝ)^ε*(E₁+E₂) := by
  obtain ⟨C,hC,hbound⟩:=uniform_allocated_energy b M hM ε hε
  refine ⟨C,hC,?_⟩
  intro T D a ι _ s R hR E₁ E₂ hE₁ hE₂ hleft hright
  have hl:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).X₁) (fun i=>(s i).X₂) (fun i=>(s i).X₁_pos) (fun i=>(s i).X₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₁ hE₁ hleft
  have hr:=hbound T D a (fun i=>(s i).η) (fun i=>(s i).z) (fun i=>(s i).z_ne) R hR
    (fun i=>(s i).plain₁) (fun i=>(s i).plain₂) (fun i=>(s i).slots.pool)
    (fun i=>(s i).slots.coefficient) (fun i=>(s i).slots.P) (fun i=>(s i).t)
    (fun i=>(s i).Y₁) (fun i=>(s i).Y₂) (fun i=>(s i).Y₁_pos) (fun i=>(s i).Y₂_pos)
    (fun i=>(s i).slots.prime) (fun i=>(s i).slots.P_pos)
    (fun i j I _=>(s i).slots.controls.1 j I) (fun i j I _=>(s i).slots.controls.2 j I)
    E₂ hE₂ hright
  rw [Finset.sum_add_distrib,mul_add]
  exact add_le_add hl hr

def inputSlots (s : CenteredMomentCommonRadialData.Input α) : Slots α s.hi s.M where
  pool:=s.slots
  ν:=s.ν
  W:=s.W
  P:=s.P
  prime:=s.prime
  P_pos:=s.P_pos
  ν_bound:=s.ν_bound
  W_bound:=s.W_bound
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma inputSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) :
    (inputSlots s).coefficient=s.toData.coefficient := rfl

def commonSlots (s : CenteredMomentCommonRadialData.Input α) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    Slots (CenteredMomentCommonProfile.liveIndices B.val) (fun i=>s.hi i) (fun i=>s.M i) where
  pool:=fun i=>s.slots i
  ν:=fun i=>s.ν i
  W:=fun i=>s.W i
  P:=fun i=>s.P i
  prime:=fun i=>s.prime i
  P_pos:=fun i=>s.P_pos i
  ν_bound:=fun i=>s.ν_bound i
  W_bound:=fun i=>s.W_bound i
  support:=fun i _ hx=>(s.support i hx).2

omit [DecidableEq α] in
lemma commonSlots_coefficient (s : CenteredMomentCommonRadialData.Input α) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    (commonSlots s C B).coefficient=(CenteredMomentCommonRadialData.commonData s C R B).coefficient := rfl

end SevenEighths.CenteredMomentAllocatedNaturalSource

end

end OAI
end OAIOriginalModule1995

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionTails
Source SHA256: d643a6ee4d63f28899efd4a43922b4d81b65f4b92daa5df79b69ea83f11b527a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1996



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentComparisonReflection
open HeckeFamily EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O
local notation "NI" => UnrestrictedIdealReindex.NonzeroIdeal

lemma ideal_norm_rpow_summable (B : ℕ) (hB : 2≤B) :
    Summable (fun I : NI=>(I.val.absNorm:ℝ)^(-(B:ℝ))) := by
  have hb : (1:ℝ)<B := by exact_mod_cast (by omega : 1<B)
  have hs := (CubicEisenstein.fullIdealWeight_summable_norm (B:ℂ)
    (by simpa using hb)).comp_injective
      (Subtype.val_injective : Function.Injective (fun I : NI=>I.val))
  apply hs.congr
  intro I
  rw [Function.comp_apply,CubicEisenstein.fullIdealWeight,ite_eq_right I.property]
  change ‖((I.val.absNorm:ℝ):ℂ)^(-(B:ℂ))‖=_
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hi]
  simp

lemma plain_term_rapid_bound (η : Character) (F : ℝ→ℂ) (B : ℕ) (D Y : ℝ)
    (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) (I : NI) :
    ‖idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤
      (D*Y^B)*(I.val.absNorm:ℝ)^(-(B:ℝ)) := by
  have hi : 0<(I.val.absNorm:ℝ) := HeckeDyadic.norm_pos I
  have hx : 0<(I.val.absNorm:ℝ)/Y := div_pos hi hY
  have hb : ‖F ((I.val.absNorm:ℝ)/Y)‖≤D/((I.val.absNorm:ℝ)/Y)^B :=
    (le_div_iff₀ (pow_pos hx B)).mpr (by simpa only [mul_comm] using hF _ hx)
  calc
    _≤‖F ((I.val.absNorm:ℝ)/Y)‖:=by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η _)
    _≤D/((I.val.absNorm:ℝ)/Y)^B:=hb
    _=_:=by
      rw [Real.rpow_neg hi.le,Real.rpow_natCast,div_pow]
      field_simp

theorem plain_rapid_summable (η : Character) (F : ℝ→ℂ) (B : ℕ) (hB : 2≤B)
    (D Y : ℝ) (hY : 0<Y) (hF : ∀x : ℝ,0<x → x^B*‖F x‖≤D) :
    Summable (fun I : NI=>idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=>norm_nonneg _)
    (plain_term_rapid_bound η F B D Y hY hF)
    ((ideal_norm_rpow_summable B hB).mul_left (D*Y^B))

theorem plain_rapid_bound (B : ℕ) (hB : 2≤B) :
    ∃C : ℝ,0<C ∧ ∀(η : Character)(F : ℝ→ℂ)(D Y : ℝ),0≤D → 0<Y →
      (∀x : ℝ,0<x → x^B*‖F x‖≤D) →
      ‖HeckeDyadic.polynomial η false F Y 0 0‖≤C*D*(Y^B/Real.sqrt Y) := by
  let C := 1+∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ))
  have hs := ideal_norm_rpow_summable B hB
  have hnon : 0≤∑' I : NI,(I.val.absNorm:ℝ)^(-(B:ℝ)) :=
    tsum_nonneg (fun I=>Real.rpow_nonneg (HeckeDyadic.norm_pos I).le _)
  refine ⟨C,by dsimp [C];linarith,?_⟩
  intro η F D Y hD hY hF
  have ht := plain_rapid_summable η F B hB D Y hY hF
  have hh := ht.norm.tsum_le_tsum (plain_term_rapid_bound η F B D Y hY hF)
    (hs.mul_left (D*Y^B))
  rw [tsum_mul_left] at hh
  have hb : ‖∑' I : NI,idealCoeff η I.val*F ((I.val.absNorm:ℝ)/Y)‖≤D*Y^B*C := by
    exact (norm_tsum_le_tsum_norm ht.norm).trans (hh.trans
      (mul_le_mul_of_nonneg_left (by dsimp [C];linarith) (by positivity)))
  rw [polynomial_plain η F Y hY,norm_mul,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (Real.sqrt_nonneg Y)]
  calc
    _≤(Real.sqrt Y)⁻¹*(D*Y^B*C):=mul_le_mul_of_nonneg_left hb (by positivity)
    _=C*D*(Y^B/Real.sqrt Y):=by ring

theorem actual_reflected_absolute_bound (a b : ℝ) (ha : 0<a) (B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y : ℝ),0<Y →
      ‖HeckeDyadic.polynomial η false
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y) := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha B 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y hY
  have hf : ∀x : ℝ,0<x → x^B*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) B)
      (norm_nonneg _)).trans hh
  exact (hKb η _ (D*(1+‖t‖)^n) Y (by positivity) hY hf).trans_eq (by ring)

lemma discarded_rapid_control (F : ℝ→ℂ) (A B : ℕ) (D R : ℝ)
    (hD : 0≤D) (hR : 0<R) (hF : ∀x : ℝ,0<x → x^(B+A)*‖F x‖≤D) :
    ∀x : ℝ,0<x → x^B*‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤D/R^A := by
  intro x hx
  by_cases hz : CenteredMomentSectorLocalization.discardedWeight R x=0
  · simp only [hz,Complex.ofReal_zero,zero_mul,norm_zero,mul_zero]
    positivity
  have hRx := (CenteredMomentSectorLocalization.discardedWeight_support R x hz).le
  have hw := CenteredMomentSectorLocalization.discardedWeight_bounds R x
  have hnorm : ‖(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*F x‖≤‖F x‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg hw.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hw.2
  apply (mul_le_mul_of_nonneg_left hnorm (pow_nonneg hx.le B)).trans
  apply (le_div_iff₀ (pow_pos hR A)).mpr
  calc
    _≤(x^B*‖F x‖)*x^A :=mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR.le hRx A) (by positivity)
    _=x^(B+A)*‖F x‖ :=by rw [pow_add];ring
    _≤D :=hF x hx

theorem actual_reflected_discarded_bound (a b : ℝ) (ha : 0<a) (A B : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀(W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0<C ∧ ∀(η : Character)(t Y R : ℝ),0<Y → 0<R →
      ‖HeckeDyadic.polynomial η false
        (fun x=>(CenteredMomentSectorLocalization.discardedWeight R x:ℂ)*
          paperRadialFourier (CompletedHeight.normTwistedSource W t) x) Y 0 0‖≤
        C*(1+‖t‖)^n*(Y^B/Real.sqrt Y)/R^A := by
  obtain ⟨n,hn⟩ := reflected_profile_height_control a b ha (B+A) 0
  obtain ⟨K,hK,hKb⟩ := plain_rapid_bound B hB
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDb⟩ := hn W hs hW
  refine ⟨K*D,mul_pos hK hD,?_⟩
  intro η t Y R hY hR
  have hf : ∀x : ℝ,0<x → x^(B+A)*‖paperRadialFourier (CompletedHeight.normTwistedSource W t) x‖≤D*(1+‖t‖)^n := by
    intro x hx
    have hh := hDb t 0 (by omega) x hx.le
    simp only [LocalLogFourier.eulerDeriv,iteratedDeriv_zero,Real.exp_zero,mul_one] at hh
    exact (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx.le (by linarith : x≤1+x) (B+A))
      (norm_nonneg _)).trans hh
  have hm := discarded_rapid_control _ A B (D*(1+‖t‖)^n) R (by positivity) hR hf
  exact (hKb η _ ((D*(1+‖t‖)^n)/R^A) Y (by positivity) hY hm).trans_eq (by ring)

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end OAIOriginalModule1996

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ReflectionLength
Source SHA256: 311471b5418905c3d829edf91e10f51625399590244843e216d95d3f2b3855ca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1997


namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.CenteredMomentComparisonReflection

lemma nonempty_clipped_scale (S B q : ℝ) (hS : 0<S) (hq : 1≤q)
    (hsupport : q/S≤B) : max 1 S≤max 1 B*S := by
  have hh : 1≤B*S := hq.trans ((div_le_iff₀ hS).mp hsupport)
  apply max_le
  · exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hS.le)
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right (le_max_left 1 B) hS.le

lemma reflected_scale_bound (Z M n xi C Q R d h s : ℝ)
    (hZ : 1<Z) (_hC : 0≤C) (hQ : 0≤Q) (hd : 0≤d) (_hs : 0≤s)
    (hcap : Q*R≤C*Z^M) (hdR : d≤R) (hh : 1≤h) (hsmax : s≤Z^(xi/2)) :
    s*(Q*d/(Z^n*h))≤C*Z^(M-n+xi/2) := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hn : 0<Z^n := Real.rpow_pos_of_pos hz _
  have hp : Q*d≤C*Z^M := (mul_le_mul_of_nonneg_left hdR hQ).trans hcap
  have hy : Q*d/(Z^n*h)≤C*Z^M/Z^n := by
    calc
      _≤Q*d/Z^n := div_le_div_of_nonneg_left (mul_nonneg hQ hd) hn (by nlinarith)
      _≤C*Z^M/Z^n := div_le_div_of_nonneg_right hp hn.le
  calc
    _≤Z^(xi/2)*(C*Z^M/Z^n) := mul_le_mul hsmax hy (by positivity) (by positivity)
    _=C*Z^(M-n+xi/2) := by
      rw [Real.rpow_add hz,Real.rpow_sub hz]
      ring

theorem eventually_reflected_length (C B box xi : ℝ) (hC : 0<C)
    (hbox : 1≤box) (hxi : 0<xi) :
    ∀ᶠ Z : ℝ in atTop,1<Z ∧ ∀(M n Q R d h s q : ℝ),
      0<Q → 0<d → 0<s → Q*R≤C*Z^M → d≤R → 1≤h →
      s≤Z^(xi/2) → 1≤q → q/(s*(Q*d/(Z^n*h)))≤B →
      let declared := Real.logb Z (box*max 1 (s*(Q*d/(Z^n*h))))
      0≤declared ∧ declared≤M-n+xi := by
  have hc := (tendsto_rpow_atTop (show 0<xi/2 by linarith)).eventually
    (eventually_ge_atTop (C*max 1 B*box))
  filter_upwards [eventually_gt_atTop (1:ℝ),hc] with Z hZ hconst
  refine ⟨hZ,?_⟩
  intro M n Q R d h s q hQ hd hs hcap hdR hh hsm hq hsupport
  have hz : 0<Z := zero_lt_one.trans hZ
  have hp : 0<s*(Q*d/(Z^n*h)) := by positivity
  have hraw := reflected_scale_bound Z M n xi C Q R d h s hZ hC.le hQ.le hd.le hs.le hcap hdR hh hsm
  have hclip := nonempty_clipped_scale _ B q hp hq hsupport
  have hT : 1≤box*max 1 (s*(Q*d/(Z^n*h))) := by
    calc
      (1:ℝ)=1*1 :=by ring
      _≤box*max 1 (s*(Q*d/(Z^n*h))) :=
        mul_le_mul hbox (le_max_left _ _) (by norm_num) (by linarith)
  constructor
  · exact Real.logb_nonneg hZ hT
  · apply (Real.logb_le_iff_le_rpow hZ (zero_lt_one.trans_le hT)).mpr
    calc
      _≤box*(max 1 B*(C*Z^(M-n+xi/2))) :=
        mul_le_mul_of_nonneg_left (hclip.trans
          (mul_le_mul_of_nonneg_left hraw (le_max_of_le_left (by norm_num)))) (by linarith)
      _=(C*max 1 B*box)*Z^(M-n+xi/2) :=by ring
      _≤Z^(xi/2)*Z^(M-n+xi/2) :=mul_le_mul_of_nonneg_right hconst (by positivity)
      _=Z^(M-n+xi) :=by rw [←Real.rpow_add hz];congr 1;ring

end SevenEighths.CenteredMomentComparisonReflection

end

end OAI
end OAIOriginalModule1997

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonMaskChildCapacity
Source SHA256: e773d97165326c8236860ba4c893c39c316e6e5415c794c70218f71603437689
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1998



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.CenteredMomentCommonMaskChildCapacity
open HeckeFamily HeckeDyadic CenteredMomentComparisonReflection
local notation "O" => HeckeFamily.O

lemma polynomial_nonzero_support (χ : Character) (W : ℝ→ℂ) (X sigma t b : ℝ)
    (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) : 1≤b*X := by
  by_contra hh
  have hb : b*X<1:=lt_of_not_ge hh
  apply hn
  unfold polynomial
  have hzero : ∀I : NonzeroIdeal,summand χ false W X sigma t I=0 := by
    intro I
    have hW : W (norm I/X)=0 := by
      by_contra hW
      have hu:=hs hW
      have hle : norm I≤b*X:=(div_le_iff₀ hX).mp hu
      have hi : 1≤norm I := by
        change 1≤(I.val.absNorm:ℝ)
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr I.property)
      linarith
    simp only [summand,hW,mul_zero,zero_mul]
  simp only [hzero,tsum_zero,mul_zero]

lemma actual_clipped_log (χ : Character) (W : ℝ→ℂ) (Z X sigma t b : ℝ)
    (hZ : 1<Z) (hX : 0<X) (hs : Function.support W⊆Set.Iic b)
    (hn : polynomial χ false W X sigma t≠0) :
    0≤Real.logb Z (max 1 X) ∧
      Real.logb Z (max 1 X)≤Real.logb Z X+Real.logb Z (max 1 b) := by
  have hB : 0<max 1 b:=zero_lt_one.trans_le (le_max_left _ _)
  have hclip : max 1 X≤max 1 b*X := by
    apply max_le
