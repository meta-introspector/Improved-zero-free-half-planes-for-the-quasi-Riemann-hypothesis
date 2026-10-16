    ring
  cases negative <;>
    simp only [firstBareCubeCoefficient,cubeLogCoefficient,cubeMinusCoefficient,cubePlusCoefficient,
      firstPassColumnMinus,firstPassColumnPlus,logTwistMinus,logTwistPlus,
      Bool.false_eq_true,ite_false,ite_true,ht] <;> ring

theorem firstCommonColumn_original_labels
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) d) negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
        dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_eq_rayIdealRow p hp hg hinj F D _ negative χ ω X t hX h,
    firstBareCubeCoefficient_window p hp hg hcop B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f)
      (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) t d,
    rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv]
  rfl

theorem firstCommonColumn_marked_priority {σ : Type*} [DecidableEq σ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (ω : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U)) c f) d)
      negative χ ω X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d f D *
        ∑ r : FirstCoreIndex,firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
          ∑ J ∈ slots.powerset,primeMark J lists a (A∪D) *
            firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
              (fun U => primeMark (slots\J) (fun i => lists i\(A∪D)) a U*H U)
              (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t)
              (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U))
    ω X t hX c d f h]
  rw [marked_dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B A v ε₁ ε₂
    negative χ Ψ m slots lists a H (fun u => ω (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) c d (-t)]
  simp_rw [firstCoreInputRow_marked_priority]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0541

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstFamilyEnergy
Source SHA256: fe1604b81a27d0ba1914eb2b6f9a97fe86a970b7c5eaa3a023c6e43790bce099
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0542


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFamilySeparatedRow (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  ∑ x∈source,w x*firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x)
    ω₁ ω₂ (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z

def firstFamilyEnergy (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) : ℝ :=
  ∑ x∈source,‖w x‖*firstBlockEnergy p hg F (selector x) (C x) negative ω X t (h x)

theorem firstFamilyEnergy_nonneg (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (ω : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) :
    0 ≤ firstFamilyEnergy p hg source F selector C w negative ω X t h :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _)
    (firstBlockEnergy_nonneg p hg F (selector x) (C x) negative ω X t (h x)))

theorem first_family_cauchy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) :
    let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
    ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      Real.sqrt (firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7) (H 7) h)*
      Real.sqrt (firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8) (H 8) h) := by
  dsimp only
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  let weight (j : κ × (RayCharacter × RayCharacter) × Finset ι) : ℂ :=
    w j.1*firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)*
      firstOuterPhase H (firstCommonOuterLog p (A₁ j.1) (A₂ j.1) (C j.1) (R j.1)
        (d j.1) (h j.1) j.2.2 s)
  have hn (j : κ × (RayCharacter × RayCharacter) × Finset ι) :
      ‖weight j‖ = ‖w j.1‖*‖firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)‖ := by
    simp only [weight,norm_mul,firstOuterPhase_norm,mul_one]
  have hc := DescentWeightedCauchy.weighted_cauchy
    (source ×ˢ ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset)) weight
    (fun j => firstCommonColumn p hg F j.2.2 (C₂ j.1) false j.2.1.2 ω₂ (s 8) (H 8) (h j.1))
    (fun j => firstCommonColumn p hg F j.2.2 (C₁ j.1) true j.2.1.1 ω₁ (s 7) (H 7) (h j.1))
  simp only [hn,Finset.sum_product] at hc
  have he : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      weight (x,r,D)*firstCommonColumn p hg F D (C₂ x) false r.2 ω₂ (s 8) (H 8) (h x)*
        star (firstCommonColumn p hg F D (C₁ x) true r.1 ω₁ (s 7) (H 7) (h x))) =
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z := by
    simp only [firstFamilySeparatedRow,firstBlockedSeparatedRow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro D hD
    dsimp only [weight,firstBlockOuterWeight,H]
    ring
  rw [he] at hc
  have hleft : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₁ x) true r.1 ω₁ (s 7) (H 7) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7) (H 7) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,ite_true]
  have hright : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₂ x) false r.2 ω₂ (s 8) (H 8) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8) (H 8) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,Bool.false_eq_true,ite_false]
  rw [hleft,hright] at hc
  exact hc.trans_eq (mul_comm _ _)

theorem first_family_integral_of_energy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    B*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      B*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact hh.trans_eq (by rw [←sq,Real.sq_sqrt]; unfold tripleHeight coordinateHeight; positivity)
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),B*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul B)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0542

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstFreshEnergy
Source SHA256: faad3a2ca6704c6cae99572f778799805bad0bd55ddff0e68314dbc5f19b4df7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0543


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_fresh_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B,0 < v j)
      (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
      (ω : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ source,Squarefree x.1) →
      (∀ x ∈ source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z ∈ rows,z ≠ 0) → (∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x ∈ source,‖w x‖ ≤ M) →
      (∑ x ∈ source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator x.1)) d)
        negative χ ω X t x.2‖^2) ≤
      M*K*Y^ε * ∑ z ∈ rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
        (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := SquarefreeDivisorBound.first_element_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F D B v ε₁ ε₂ hv negative χ C ω X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply le_trans _ (hpush source rows (dilationLabel p B v ε₁ ε₂) w
    (dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
      (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)) M Y hM hY hs hmap hrows hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ C ω X t hX c d (ConcretePrimeRowBridge.idealGenerator x.1) x.2]
  simp only [norm_mul]
  have hr0 : ‖supportRay p χ D‖ ≤ 1 := FiniteRayExpansion.norm_char_le_one χ _
  have hr : ‖if negative then star (supportRay p χ D) else supportRay p χ D‖ ≤ 1 := by
    cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,norm_star]
      using hr0
  have hb := beforeDilationLabel_norm_le_one (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂
    negative c d (ConcretePrimeRowBridge.idealGenerator x.1) D
  calc
    _ ≤ ‖beforeDilationLabel (fun i => Ideal.span {p i}) hg p B v ε₁ ε₂ negative c d
        (ConcretePrimeRowBridge.idealGenerator x.1) D‖ *
        ‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ C
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (x.2*(ConcretePrimeRowBridge.idealGenerator x.1)^2*dilationLabel p B v ε₁ ε₂)‖ :=
      mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hr
    _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hb

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0543

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOldEnergy
Source SHA256: cd06cd85ad0c6ddaa88be7bac30cd15e01e6544efbe57853b2e19410c7913e37
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0544



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem firstBlockOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (selector : Finset ι → ℂ) (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) :
    ‖firstBlockOuterWeight p selector r D h‖ ≤ ‖crossCoeff r.1 r.2‖*‖selector D‖ := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  have hm : ‖supportMobius (fun i => Ideal.span {p i}) D‖ = 1 := by
    have hs := congrArg norm (supportMobius_sq _ hprime hinj D)
    simp only [norm_mul,norm_one] at hs
    nlinarith [norm_nonneg (supportMobius (fun i => Ideal.span {p i}) D)]
  have hc : ‖rowCoprimeMask (fun i => Ideal.span {p i}) D h‖ ≤ 1 := by
    unfold rowCoprimeMask
    split_ifs <;> norm_num
  simp only [firstBlockOuterWeight,norm_mul,hm,mul_one]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc

def firstOldLabelCoefficient (hp : ∀ i,p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (c d : Eis) (f : Ideal Eis) : Finset ι → ℂ :=
  firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
    (originalLabelColumn p hg B ε₁ ε₂ negative C c (ConcretePrimeRowBridge.idealGenerator f)) d

theorem first_block_old_label_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
      (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ j∈B,0 < v j) → ∀ (negative : Bool) (C : Finset ι → ℂ)
      (ω : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * firstBlockEnergy p hg F selector
        (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
        negative ω X t x.2) ≤
      M*K*Y^ε * ∑ r : RayCharacter × RayCharacter, ∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖) *
          ∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => ω (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F B selector v ε₁ ε₂ hv negative C ω X t hX c d
    source rows w M Y hM hY hs hmap hrows hnorm hw
  calc
    _ = ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,∑ x∈source,
        ‖w x‖*‖firstBlockOuterWeight p selector r D x.2‖*
          ‖firstCommonColumn p hg F D
            (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
            negative (if negative then r.1 else r.2) ω X t x.2‖^2 := by
      simp only [firstBlockEnergy,Finset.mul_sum,← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          (M*K*Y^ε*∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => ω (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ x∈source,
            ‖w x‖*‖firstCommonColumn p hg F D
              (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
              negative (if negative then r.1 else r.2) ω X t x.2‖^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro x hx
          have hh := mul_le_mul_of_nonneg_left
            (firstBlockOuterWeight_norm_le p hinj selector r D x.2) (norm_nonneg (w x))
          exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
            (if negative then r.1 else r.2) C ω X t hX c d source rows w M Y
              hM hY hs hmap hrows hnorm hw) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring_nf

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0544

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstRetainedPhysical
Source SHA256: fcc51679a2f02469aa0382e30943f29ae2c48cf87b034d0d98747c2c28562aca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0545



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstCubePhysicalMode (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (d h : O) : ℂ :=
  (K:ℂ)*cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d h *
    firstPhysicalCommonRows p hg (pool\(b.support∪C))
      (cubeMinusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁) d)
      (cubePlusCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) d)
      (fun x=>star (W₁ x)) W₂ Φ
      (‖eisEmbedding (aLabel p b.support b.rightBit)‖^2)
      (‖eisEmbedding (aLabel p b.support b.leftBit)‖^2)
      (primeProductNorm p C)
      (primeProductNorm p (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)) K d h

theorem canonical_retained_physical
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (T : Finset ι→Finset O) :
    canonicalCubeDualFinite p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun U=>H₁ U*W₁ (primeProductNorm p U)) (fun U=>H₂ U*W₂ (primeProductNorm p U)) Φ K T =
    canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ f *
      ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
        ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂
          W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h := by
  unfold canonicalCubeDualFinite
  apply congrArg
  apply Finset.sum_congr rfl
  intro D hD
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro h hh
  have he := canonical_first_kernel_physical p hp hcop hg hinj hc hpr pool b hb C hC
    Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h
  change (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) D)‖^2:ℂ)⁻¹ * _ =
    firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W₁ W₂ Φ K _ h at he
  rw [←Complex.ofReal_pow,primeSubsetGenerator_norm_eq_productNorm] at he
  rw [div_eq_mul_inv,mul_assoc,he]

theorem canonical_first_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (hb : b.Admissible)
    (C : Finset ι) (hC : Disjoint C b.support)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ : O) (f : Ideal O) (hf : f≠0) (H₁ H₂ : Finset ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) (R : Finset ι→ℝ)
    (hR : ∀ D,0≤R D) :
    let fgen := ConcretePrimeRowBridge.idealGenerator f
    let H₁' := fun U=>H₁ U*W₁ (primeProductNorm p U)
    let H₂' := fun U=>H₂ U*W₂ (primeProductNorm p U)
    let T := fun D=>childFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit f) (R D)
    canonicalCubeBeforePoisson p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K =
      canonicalCubeDualZero p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K +
      (canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ fgen *
        ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          (UniqueFactorizationMonoid.moebius (∏i∈D,Ideal.span {p i}):ℂ)*
          ∑ h∈(T D).erase 0,firstCubePhysicalMode p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁ H₂
            W₁ W₂ Φ K (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h) +
      canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K T := by
  intro fgen H₁' H₂' T
  rw [canonicalCubeBeforePoisson_split p hp hcop hg hinj hc pool b C Ψ₁ Ψ₂ m₁ m₂ fgen H₁' H₂' Φ K hK T]
  · rw [canonical_retained_physical p hp hcop hg hinj hc hpr pool b hb C hC]
  · intro D hD
    apply (mem_childFrequencyBall _ (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ f hf) _ _).mpr
    simpa only [mul_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0)] using hR D

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0545

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstToSecond
Source SHA256: 7c5734b267b920b4cc152aa3ae0ad16fc442aa379865856dfe16ea14164716f6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0546


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def firstFreshSecondPoisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) : ℂ :=
  ∑ G ∈ (F\D).powerset, ∑ U ∈ ((F\D)\G).powerset, ∑ V ∈ ((F\D)\G).powerset,
    if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
      (m*b0Label p B v ε₁ ε₂) (c*jLabel p B v ε₁ ε₂) d
      (firstCoreTest H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
      maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0

theorem firstFreshSecondPoisson_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) (hY : 0 < Y) :
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y =
    ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
      if Disjoint U V then overlapPairWeight p hg (firstCoreTwist negative χ Ψ r)
        ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
        (firstCoreTest H (fun u => ω (Real.exp u))
          (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
        maskedSecondDual p hg hp hinj G U V rowMajorant Y else 0 := by
  unfold firstFreshSecondPoisson
  rw [← firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y hY]
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y]
  simp_rw [inputConjugateRow_fixed_pool p hg hinj F D]
  exact inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F
    (firstCoreTwist negative χ Ψ r) ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i)
    (c*jLabel p B v ε₁ ε₂) d
    (firstCoreTest H (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D) rowMajorant Y hY

theorem first_fresh_core_energy_to_second
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X : ℝ) (c d : Eis) (t : ℝ)
    (rows : Finset Eis) (Y : ℝ) (hY : 0 < Y)
    (hrows : ∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y)
    (hΨ : ‖Ψ (∏ i∈D,p i)‖ ≤ 1) :
    (∑ z∈rows,‖dilatedCoreRow p hp hcop hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) ≤
    (32*512) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y).re := by
  calc
    _ ≤ ∑ z∈rows,(32*512) * ∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
            (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact dilatedCoreRow_sq_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d (-t) z hΨ
    _ = (32*512) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
        ∑ z∈rows,‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
          (fun u => ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact firstCoreInputRow_finite_le_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => ω (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d r (-t) rows Y hY hrows

theorem first_fresh_old_labels_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) →
      ∀ (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), (∀ j∈B,0 < v j) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis),
      ‖Ψ (∏ i∈D,p i)‖ ≤ 1 → ∀ (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hp hg hcop B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H)
            c (ConcretePrimeRowBridge.idealGenerator x.1)) d)
        negative χ ω X t x.2‖^2) ≤
      M*K*Y^ε * ((32*512)*∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d r t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F D B v ε₁ ε₂ hv negative χ Ψ m hΨ H ω X t hX
    c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative χ
    (multiplicativeCoreColumn p Ψ m H) ω X t hX c d source rows w M Y hM hY.le
      hs hmap hrows hnorm hw).trans
  exact mul_le_mul_of_nonneg_left
    (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative χ
      Ψ m H ω X c d t rows Y hY hnorm hΨ) (by positivity)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0546

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstFamilyToSecond
Source SHA256: 0f508500f50f1772da9adf295051613e14d257566444a080a4813cfe152d343b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0547




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_family_original_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) →
      ∀ (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ i∈B,0 < v i) → ∀ (negative : Bool) (Ψ : Eis →* ℂ) (m : Eis),
      (∀ a,‖Ψ a‖ ≤ 1) → ∀ (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x∈rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      firstFamilyEnergy p hg source F (fun _ => selector)
        (fun x => firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m H) c d x.1) w negative ω X t Prod.snd ≤
      M*K*Y^ε * ((32*512)*
        ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
          (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H ω X c d core t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_block_old_label_energy ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B selector v ε₁ ε₂ hv negative Ψ m hΨ
    H ω X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  have h := hpush p hp hinj hcop hg F B selector v ε₁ ε₂ hv negative
    (multiplicativeCoreColumn p Ψ m H) ω X t hX c d source rows w M Y hM hY.le
    hs hmap hrows hnorm hw
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ((32*512)*∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H ω X c d core t Y).re) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_left
        (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative
          (if negative then r.1 else r.2) Ψ m H ω X c d t rows Y hY hnorm (hΨ _)) (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro core hcore
      ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0547

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstCanonicalEnergy
Source SHA256: dbaea81735b617413e1f83c759e6202e89fd87c59263a715fb79aa36eff206d3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0548



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def retainedCubeWeight (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) : ℂ :=
  a x * canonicalCubeOuter p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator x.1) *
    cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2

theorem retainedCubeWeight_norm
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) :
    ‖retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a x‖≤‖a x‖ := by
  simp only [retainedCubeWeight,norm_mul]
  calc
    _ ≤ ‖a x‖*1*1 := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left
          (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _) (norm_nonneg _))
        (cubeBaseFactor_norm_le_one p hp hcop hg hc _ _ _ _ _ _)
        (norm_nonneg _) (by positivity)
    _ = _ := by ring

include hp in
theorem retained_physical_row_support (b : CubeCoordinates ι) (x : Ideal O×O) (hx : x.1≠0)
    (Y : ℝ) (hcut : x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) x ∈
        nonzeroChildFrequencyBall 1 Y := by
  have hh := (mem_nonzeroChildFrequencyBall _
    (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ x.1 hx) _ _).mp hcut
  apply (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ _).mpr
  simpa only [one_mul,firstPhysicalMultiplier_row] using hh

theorem retained_cube_energy_to_second (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (source : Finset (Ideal O×O)) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ x∈source,Squarefree x.1) → (∀ x∈source,x.1≠0) → (∀ x∈source,‖a x‖≤Γ) →
      (∀ x∈source,x.2∈nonzeroChildFrequencyBall
        (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) →
      ∀ (negative : Bool) (H : Finset ι→ℂ) (selector : Finset ι→ℂ)
        (ω : ℝ→ℂ) (X t : ℝ),0<X →
      let Ψ := if negative then Ψ₁ else Ψ₂
      let m := if negative then m₁ else m₂
      let Hshift := fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)
      let w := retainedCubeWeight p hp hcop hg b C Ψ₁ Ψ₂ m₁ m₂ d a
      firstFamilyEnergy p hg source F (fun _=>selector)
        (fun x=>firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (multiplicativeCoreColumn p Ψ m Hshift)
          (∏i∈C,p i) d x.1) w negative ω X t Prod.snd ≤
      Γ*K*Y^ε*((32*512)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
          (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m Hshift ω X (∏i∈C,p i) d core t Y).re) := by
  obtain ⟨K,hK,hstep⟩ := first_family_original_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a source Γ Y hΓ hY
    hs hn ha hcut negative H selector ω X t hX Ψ m Hshift w
  apply hstep p hp hinj hcop hg hc hpr F b.support selector _ _ _ b.support_pos negative Ψ m
    (by intro u; cases negative
        · exact hΨ₂ u
        · exact hΨ₁ u) Hshift ω X t hX (∏i∈C,p i) d source
    (nonzeroChildFrequencyBall 1 Y) w Γ Y hΓ hY hs
  · intro x hx
    exact retained_physical_row_support p hp b x (hn x hx) Y (hcut x hx)
  · intro z hz
    exact (Finset.mem_erase.mp hz).1
  · intro z hz
    have hb := ((mem_nonzeroChildFrequencyBall 1 one_ne_zero Y z).mp hz).2
    simpa only [one_mul,eisEmbedding_norm_sq_eq_absNorm_span] using hb
  · intro x hx
    exact (retainedCubeWeight_norm p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a x).trans (ha x hx)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0548

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstPriorityEnergy
Source SHA256: 7c8981fb0426afb6c010b57ef99dd08c1ffbb1cb73e5092c4da42ed5ff7834b5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0549



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem first_fresh_real_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (H : Finset ι→ℂ) (ω : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H ω X c d core height Y).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re *
      ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
        (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2 := by
  unfold firstFreshSecondPoisson
  rw [←firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) rowMajorant Y hY,
    rowMajorant_tsum_eq_sum _ Y hY]
  let P := fun z=>firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z
  change (∑ z∈rowMajorantBall Y,rowMajorant (‖eisEmbedding z‖^2/Y)*(‖P z‖^2 : ℝ)).re =
    ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re*‖P z‖^2
  simp only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero]

lemma priority_norm_sum_sq {α : Type*} (s : Finset α) (f : α→ℂ) :
    ‖∑ i∈s,f i‖^2≤(s.card:ℝ)*∑ i∈s,‖f i‖^2 := by
  have hnorm := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le s f) 2
  apply hnorm.trans
  simpa using Finset.sum_mul_sq_le_sq_mul_sq s (fun _=>(1:ℝ)) (fun i=>‖f i‖)

theorem first_fresh_priority_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B A : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (H : Finset ι→ℂ) (ω : ℝ→ℂ) (X : ℝ) (c d : Eis)
    (core : FirstCoreIndex) (height Y : ℝ) (hY : 0<Y) :
    (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (fun U=>primeMark slots lists a (A∪U)*H U) ω X c d core height Y).re ≤
    (2:ℝ)^slots.card * ∑ J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2 *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
        (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U) ω X c d core height Y).re := by
  rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ ω X c d core height Y hY]
  calc
    _ ≤ ∑ z∈rowMajorantBall Y,(rowMajorant (‖eisEmbedding z‖^2/Y)).re *
        ((slots.powerset.card:ℝ)*∑ J∈slots.powerset,
          ‖primeMark J lists a (A∪D) * firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
            (fun U=>primeMark (slots\J) (fun i=>lists i\(A∪D)) a U*H U)
            (fun u=>ω (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d core (-height) z‖^2) := by
      apply Finset.sum_le_sum
      intro z hz
      apply mul_le_mul_of_nonneg_left _ (rowMajorant_nonneg _)
      rw [firstCoreInputRow_marked_priority]
      exact priority_norm_sum_sq _ _
    _ = _ := by
      simp_rw [first_fresh_real_energy p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m _ ω X c d core height Y hY]
      simp only [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,Finset.mul_sum,norm_mul,mul_pow]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro J hJ
      apply Finset.sum_congr rfl
      intro z hz
      ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0549

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstUnequalEnergy
Source SHA256: 084475efdffc4293ef8cc545bbe8600e031b16b749412da46741f3806533fffc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0550


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels FirstCauchyArithmetic RayFourExpansion
open JointLogSeparation FourierBridge MeasureTheory
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_family_integral_of_two_energies (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B₁ B₂ : ℝ) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true ω₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B₁*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false ω₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B₂*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
    (Real.sqrt B₁*Real.sqrt B₂)*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z‖ ≤
      (Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w ω₁ ω₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    apply hh.trans_eq
    rw [Real.sqrt_mul hB₁,Real.sqrt_mul hB₂]
    calc
      _=(Real.sqrt B₁*Real.sqrt B₂)*(Real.sqrt (tripleHeight J z.1*coordinateHeight J z.2))^2:=by ring
      _= _:=by rw [Real.sq_sqrt];unfold tripleHeight coordinateHeight;positivity
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),(Real.sqrt B₁*Real.sqrt B₂)*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul _)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _
end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0550

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FreshWindows
Source SHA256: 8707fe7459c41fa07770c526028fab106fc4921dbe680d00d29594e2f46eee9e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0551



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem fresh_ratio_of_source_support (W : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n) (hw : W (g*v*n) ≠ 0) :
    n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)) := by
  have hgp : 0 < g := hg₀.trans_le hg.1
  have hvp : 0 < v := hv₀.trans_le hv.1
  have hghi : 0 < g₁ := hgp.trans_le hg.2
  have hvhi : 0 < v₁ := hvp.trans_le hv.2
  have hsource := hs hw
  constructor
  · apply (div_le_iff₀ (mul_pos hghi hvhi)).mpr
    calc
      a ≤ g*v*n := hsource.1
      _ ≤ (g₁*v₁)*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.2 hv.2 hvp.le hghi.le) hn
      _ = _ := by ring
  · apply (le_div_iff₀ (mul_pos hg₀ hv₀)).mpr
    calc
      _ = (g₀*v₀)*n := by ring
      _ ≤ g*v*n := mul_le_mul_of_nonneg_right
        (mul_le_mul hg.1 hv.1 hv₀.le hgp.le) hn
      _ ≤ b := hsource.2

theorem fresh_window_eq_one (W ω : ℝ → ℂ) (a b g₀ g₁ v₀ v₁ g v n : ℝ)
    (hs : Function.support W ⊆ Set.Icc a b)
    (hg₀ : 0 < g₀) (hv₀ : 0 < v₀) (hg : g ∈ Set.Icc g₀ g₁)
    (hv : v ∈ Set.Icc v₀ v₁) (hn : 0 ≤ n)
    (hω : ∀ n ∈ Set.Icc (a/(g₁*v₁)) (b/(g₀*v₀)), ω n = 1)
    (hw : W (g*v*n) ≠ 0) : ω n = 1 :=
  hω n (fresh_ratio_of_source_support W a b g₀ g₁ v₀ v₁ g v n hs hg₀ hv₀ hg hv hn hw)

theorem secondChildKernelPair_insert_fresh {ι : Type*} [DecidableEq ι]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (K : Finset ι → Finset ι → ℂ) (ω₁ ω₂ : Finset ι → ℂ)
    (hω : ∀ N ∈ (F \ V).powerset, ∀ M ∈ (F \ V).powerset,
      K (V ∪ N) (V ∪ M) ≠ 0 → ω₁ (V ∪ N) = 1 ∧ ω₂ (V ∪ M) = 1) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (ω₁ S)*ω₂ T*K S T) := by
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  by_cases hK : K (V ∪ N) (V ∪ M) = 0
  · simp only [hK,mul_zero]
  · obtain ⟨h1,h2⟩ := hω N hN M hM hK
    simp only [h1,h2,star_one,one_mul]

theorem secondChildKernelPair_separated_marked {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F V A₁ A₂ : Finset ι) (Ψ₁ Ψ₂ : Eis →* ℂ) (m r c d e k₁ k₂ : Eis)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) :
    secondChildKernelPair p hp hcop hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (fun S T => star (primeMark slots₁ lists₁ a₁ (A₁ ∪ S)*W₁ (primeProductNorm p S/X₁)) *
        (primeMark slots₂ lists₂ a₂ (A₂ ∪ T)*W₂ (primeProductNorm p T/X₂))) =
      star (canonicalMarkedSplit p hp hcop hg F V A₁ Ψ₁ m r c d e k₁ slots₁ lists₁ a₁ W₁ X₁) *
        canonicalMarkedSplit p hp hcop hg F V A₂ Ψ₂ m r c d e k₂ slots₂ lists₂ a₂ W₂ X₂ := by
  have hs (Ψ : Eis →* ℂ) (A : Finset ι) (k : Eis) (slots : Finset σ)
      (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :=
    secondChildSum_marked_fixed_pool p hp hcop hg F V A Ψ m r c d e k slots lists a W X
  unfold canonicalMarkedSplit
  rw [← hs Ψ₁ A₁ k₁ slots₁ lists₁ a₁ W₁ X₁, ← hs Ψ₂ A₂ k₂ slots₂ lists₂ a₂ W₂ X₂]
  unfold secondChildKernelPair secondChildSum
  rw [star_sum, Finset.sum_mul]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  simp only [secondChildColumn,star_mul,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0551

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalSplit
Source SHA256: 492f36705f4e097efd0f95e670d7ffb3cd2d9322f89ff64525d2bf53731f2d24
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0552



namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def reopenedPhysicalSourceSum (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (source : CubeCoordinates ι→Finset ι→Ideal O→ℂ) : ℂ :=
  ∑ b∈reopenedCubeFamily Q,∑ C∈(pool\b.support).powerset,∑ I∈labels,
    reopenedPairCoefficient β b C I*source b C I

def reopenedPhysicalCutoff (b : CubeCoordinates ι) (I : Ideal O)
    (R : Finset ι→ℝ) (D : Finset ι) : Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit I) (R D)

def reopenedPhysicalRetained (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ : O→*ℂ) (m : O) (I : Ideal O)
    (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (R : Finset ι→ℝ) : ℂ :=
  canonicalCubeOuter p hp hcop hg b C Ψ Ψ m m (idealGenerator I)*
    ∑ D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      (UniqueFactorizationMonoid.moebius (∏ i∈D,Ideal.span {p i}):ℂ)*
      ∑ h∈(reopenedPhysicalCutoff p b I R D).erase 0,
        firstCubePhysicalMode p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
          (mark b.rightExponent) (mark b.leftExponent) W W Φ K
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h

theorem original_reopened_physical_split
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ))
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    (∑ I∈labels,∑' z:O,Φ (‖eisEmbedding z‖^2/K)*
      (‖varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z‖^2:ℝ)) =
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W Φ K (R b C I)) +
    reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) Φ K
        (reopenedPhysicalCutoff p b I (R b C I))) := by
  rw [varying_reopened_smoothed_source p hp hcop hg hinj hpr pool Q hQ labels β Ψ m]
  · unfold varyingCanonicalSourceTotal reopenedPhysicalSourceSum
    simp only [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    apply Finset.sum_congr rfl
    intro C hC
    apply Finset.sum_congr rfl
    intro I hI
    have hCb : Disjoint C b.support := by
      exact Finset.disjoint_left.mpr (fun i hi hib=>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hib)
    have he := canonical_first_physical_split p hp hcop hg hinj hc hpr pool b
      (reopenedCubeFamily_admissible Q b hb) C hCb Ψ Ψ m m I (hlabels I hI)
      (mark I b.rightExponent) (mark I b.leftExponent) W W Φ K hK (R b C I) (hR b hb C hC I hI)
    dsimp only at he
    rw [he]
    simp only [reopenedPhysicalRetained]
    rw [show reopenedPhysicalCutoff p b I (R b C I) =
      (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent
        b.leftBit b.rightBit I) (R b C I D)) from rfl]
    ring
  · exact hK

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0552

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedPhysicalEnergy
Source SHA256: fab0845e7573005dec03a1a12f79b081ffaf187c2c0571d71cd267272d928645
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0553


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
open ConcretePrimeRowBridge (idealGenerator)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem rowFamilyEnergy_le_of_full_split (labels : Finset (Ideal O))
    (P : Ideal O→O→ℂ) (K : ℝ) (hK : 0<K) (A B C : ℂ)
    (he : (∑ I∈labels,∑' z:O,rowMajorant (‖eisEmbedding z‖^2/K)*(‖P I z‖^2:ℝ))=A+B+C) :
    CanonicalRowCompletion.rowFamilyEnergy labels P K ≤ ‖A‖+‖B‖+‖C‖ := by
  unfold CanonicalRowCompletion.rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_eq_sub _ K hK,Finset.sum_sub_distrib,Complex.sub_re]
  rw [he]
  have hn : 0≤(∑ I∈labels,((‖P I 0‖^2:ℝ):ℂ)).re := by
    simp only [Complex.re_sum,Complex.ofReal_re]
    exact Finset.sum_nonneg (fun I hI=>sq_nonneg _)
  simp only [Complex.add_re]
  linarith [Complex.re_le_norm A,Complex.re_le_norm B,Complex.re_le_norm C]

theorem original_reopened_physical_energy
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (hQ : ∀ v∈Q,v.support⊆pool)
    (labels : Finset (Ideal O)) (hlabels : ∀ I∈labels,I≠0)
    (β : Ideal O→(ι→₀ℕ)→ℂ) (Ψ : O→*ℂ) (m : O)
    (mark : Ideal O→(ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ)
    (K : ℝ) (hK : 0<K) (R : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (hR : ∀ b∈reopenedCubeFamily Q,∀ C∈(pool\b.support).powerset,∀ I∈labels,∀ D,0≤R b C I D) :
    CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (idealGenerator I)
        (fun v U=>mark I v U*W (primeProductNorm p U)) z) K ≤
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K)‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      reopenedPhysicalRetained p hp hcop hg pool b C Ψ m I (mark I) W rowMajorant K (R b C I))‖ +
    ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
      canonicalCubeDualTail p hp hcop hg pool b C Ψ Ψ m m (idealGenerator I)
        (fun U=>mark I b.rightExponent U*W (primeProductNorm p U))
        (fun U=>mark I b.leftExponent U*W (primeProductNorm p U)) rowMajorant K
        (reopenedPhysicalCutoff p b I (R b C I)))‖ := by
  apply rowFamilyEnergy_le_of_full_split labels _ K hK
  exact original_reopened_physical_split p hp hcop hg hinj hc hpr pool Q hQ labels hlabels
    β Ψ m mark W rowMajorant K hK R hR

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0553

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSeparatedColumns
Source SHA256: 404792d499c4c84f7ba86188afcdf0f1c89dfa665917d7254bc9183d210a10c7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0554



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondOuterPhase (h y : Fin 6 → ℝ) : ℂ :=
  logPhase (h 0) (y 0) * logPhase (h 1) (y 1) *
    logPhase (h 2) (y 2) * logPhase (h 3) (y 3)

def childLogTest (ω : ℝ → ℂ) (h : ℝ) (y : ℝ) : ℂ :=
  ω y * logPhase h (Real.log y)

lemma second_mode_split (y : Fin 6 → ℝ) (t : Frequency) (u : Fin 6 → ℝ) :
    pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t u =
      secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u) y *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 4) (y 4) *
        logPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t u 5) (y 5) := by
  rw [pureProfileMode_height]
  simp only [Fin.prod_univ_succ, secondOuterPhase]
  simp only [Fin.succ,  Fin.val_mk]
  norm_num
  ring

lemma secondOuterPhase_norm (h y : Fin 6 → ℝ) : ‖secondOuterPhase h y‖ = 1 := by
  simp only [secondOuterPhase,norm_mul,logPhase_norm,mul_one]

lemma second_fresh_scale {ι : Type*} [DecidableEq ι] (p : ι → Eis)
    (hp : ∀ i, p i ≠ 0) (V N : Finset ι) (hVN : Disjoint V N) (X : ℝ) :
    primeProductNorm p (V ∪ N)/(primeProductNorm p V*X) = primeProductNorm p N/X := by
  rw [primeProductNorm_union p V N hVN]
  field_simp [(primeProductNorm_pos p hp V).ne']

theorem actual_second_columns_separated {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (X : ℝ) (h₁ h₂ : ℝ) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X)) * ω₂ (primeProductNorm p M/X)) *
        logPhase h₁ (Real.log (primeProductNorm p N/X)) *
        logPhase h₂ (Real.log (primeProductNorm p M/X))) =
    star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
      slots₁ lists₁ a₁ (childLogTest ω₁ (-h₁)) (primeProductNorm p x.overlap*X)) *
      canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
      x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
      slots₂ lists₂ a₂ (childLogTest ω₂ h₂) (primeProductNorm p x.overlap*X) := by
  rw [← secondChildKernelPair_separated_marked]
  unfold secondChildKernelPair
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint x.overlap N := by
    apply Finset.disjoint_left.mpr
    intro i hi hiN
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hN) hiN)).2 hi
  have hVM : Disjoint x.overlap M := by
    apply Finset.disjoint_left.mpr
    intro i hi hiM
    exact (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hM) hiM)).2 hi
  dsimp only
  rw [second_fresh_scale p hp x.overlap N hVN,second_fresh_scale p hp x.overlap M hVM]
  simp only [secondActualCoefficient,childLogTest,secondChildColumn,
    star_mul,SecondPassIntegration.logPhase_conjugate,neg_neg,mul_one]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0554

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondFreshAssembly
Source SHA256: b8350b05562cf133bb6e6044bf828a182e87097eff8dc387a019024f6c149933
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0555



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSeparatedPair (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) : ℂ :=
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  secondOuterPhase h
    (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
  star (canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedLeft x.rayLeft
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor x.frequency
    slots₁ lists₁ a₁ (childLogTest ω₁ (-h 4)) (primeProductNorm p x.overlap*X₀)) *
  canonicalMarkedSplit p hp hcop hg F x.overlap x.extractedRight x.rayRight
    x.puncture x.quotient x.oldLabel x.oldDivisor x.divisor (-x.frequency)
    slots₂ lists₂ a₂ (childLogTest ω₂ (h 5)) (primeProductNorm p x.overlap*X₀)

theorem actual_second_full_mode_columns (F : Finset ι) (x : SecondProfileData ι)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (v : Frequency × (Fin 6 → ℝ)) :
    (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
      secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
        (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2) =
      secondSeparatedPair p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope v.1 v.2
  let O := secondOuterPhase h (secondRelativeLog (secondActualNorms p x ∅ ∅) G₀ E₀ V₀ K₀ X₀)
  calc
    _ = O * (∑ N ∈ (F \ x.overlap).powerset, ∑ M ∈ (F \ x.overlap).powerset,
        secondActualCoefficient p hp hcop hg x slots₁ slots₂ lists₁ lists₂ a₁ a₂ N M *
          (star (ω₁ (primeProductNorm p N/X₀)) * ω₂ (primeProductNorm p M/X₀)) *
          logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
          logPhase (h 5) (Real.log (primeProductNorm p M/X₀))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hm : pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
          (secondRelativeLog (secondActualNorms p x N M) G₀ E₀ V₀ K₀ X₀) v.1 v.2 =
          O * logPhase (h 4) (Real.log (primeProductNorm p N/X₀)) *
            logPhase (h 5) (Real.log (primeProductNorm p M/X₀)) := by
        rw [second_mode_split]
        simp [secondOuterPhase,secondRelativeLog,secondRelativeNorm,secondActualNorms,O,h]
      rw [hm]
      ring
    _ = _ := by
      rw [actual_second_columns_separated]
      simp only [secondSeparatedPair,h,O,mul_assoc]

theorem actualSecondFreshRows_integral {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (g : Fin 6 → 𝓢(ℝ,ℂ)) (b₁ b₂ b₃ : 𝓢(ℝ,ℂ))
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), fullProfileDensity g b₁ b₂ b₃ v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        fullProfileDensity g b₁ b₂ b₃ v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← full_density_finite_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0555

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDensityAssembly
Source SHA256: 6b251c73dddb74ef18f815ad81fe5092f31db86adb018b24b6cdd887e0ce8f0c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0556



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondFreshRows_integral_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

theorem actualSecondFreshRows_normalized_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density) (normalization : ℂ)
    (he : ∀ j ∈ secondProfileIndices source F x,
      normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    normalization * (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  rw [actualSecondProfileRows_eq_indexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ j.2.1 j.2.2) *
        (normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
          (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2)) := by ring
    _ = _ := by rw [he j hj]; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0556

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondGenerator
Source SHA256: 5961388c09167b0b6c5a01fc08ea44454db70fcb14bb60634bd8f001f6d50391
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0557



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondUnitFrequency (u v : Eisˣ) (k : Eis) : Eis := ((u^4*v:Eisˣ):Eis)*k

lemma secondUnitFrequency_injective (u v : Eisˣ) : Function.Injective (secondUnitFrequency u v) := by
  intro a b hab
  exact mul_left_cancel₀ (Units.ne_zero (u^4*v)) hab

lemma secondUnitFrequency_norm (u v : Eisˣ) (k : Eis) :
    ‖ConcreteTraceCRT.eisEmbedding (secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding k‖ :=
  GaussGeneratorTransport.norm_eisEmbedding_unit_mul (u^4*v) k

lemma secondUnitFrequency_neg (u v : Eisˣ) (k : Eis) :
    secondUnitFrequency u v (-k) = -secondUnitFrequency u v k := by
  simp only [secondUnitFrequency,mul_neg]

variable {ι σ : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondCanonical_generator_transport
    (F : Finset ι) (Ψ : Eis →* ℂ) (m label d e k : Eis)
    (L D E : Ideal Eis) (u v : Eisˣ)
    (hl : label = (u:Eis)*primaryGenerator L)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E))
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m label (d*e*k) slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m (primaryGenerator L)
        (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k) slots lists a W X := by
  rw [hl,finiteCanonicalMarkedRow_label_transfer,hd]
  congr 1
  unfold secondUnitFrequency
  change (u:Eis)^4*((v:Eis)*(primaryGenerator D*primaryGenerator E)*k) =
    primaryGenerator D*primaryGenerator E*(((u:Eis)^4*(v:Eis))*k)
  ring

theorem secondCanonical_row_norm (D E : Ideal Eis) (u v : Eisˣ) (d e k : Eis)
    (hd : d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E)) :
    ‖ConcreteTraceCRT.eisEmbedding
      (primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k)‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*e*k)‖ := by
  rw [hd]
  have hl : primaryGenerator D*primaryGenerator E*secondUnitFrequency u v k =
      ((u^4*v:Eisˣ):Eis)*(primaryGenerator D*primaryGenerator E*k) := by
    unfold secondUnitFrequency
    ring
  rw [hl,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]
  have hr : (v:Eis)*(primaryGenerator D*primaryGenerator E)*k =
      (v:Eis)*(primaryGenerator D*primaryGenerator E*k) := by ring
  rw [hr,GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem exists_second_generator_sectors (label d e : Eis) (L D E : Ideal Eis)
    (hl : Ideal.span {label} = L) (hd : Ideal.span {d} = D) (he : Ideal.span {e} = E)
    (hL : primaryGenerator L ≠ 0) (hD : primaryGenerator D ≠ 0) (hE : primaryGenerator E ≠ 0) :
    ∃ u v : Eisˣ, label = (u:Eis)*primaryGenerator L ∧
      d*e = (v:Eis)*(primaryGenerator D*primaryGenerator E) := by
  obtain ⟨u,hu⟩ := generator_eq_unit_primary L label hl hL
  have hspan : Ideal.span {d*e} = D*E := by
    rw [← Ideal.span_singleton_mul_span_singleton,hd,he]
  obtain ⟨v,hv⟩ := generator_eq_unit_primary (D*E) (d*e) hspan
    (by rw [primaryGenerator_mul]; exact mul_ne_zero hD hE)
  exact ⟨u,v,hu,by simpa only [primaryGenerator_mul] using hv⟩

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0557

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSourceProfile
Source SHA256: 318b3910e4fe4b173fec50adac20e0b02af1d5f6d9b1731e8f71388ab660e38c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0558


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def expansionProfileData (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (A₁ A₂ : Finset ι) (x : SecondExpansionData ι) : SecondProfileData ι where
  common := x.sourceCommon
  overlap := x.overlap
  extractedLeft := A₁ ∪ x.sourceCommon
  extractedRight := A₂ ∪ x.sourceCommon
  rayLeft := secondRayMinus Ψ z
  rayRight := secondRayPlus Ψ z
  puncture := m
  quotient := secondExpansionQuotient p x
  oldLabel := c
  oldDivisor := d
  divisor := primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor
  frequency := x.frequency

def expansionProfileWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (Y : ℝ) (x : SecondExpansionData ι) : ℂ :=
  (Y : ℂ) * (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondTotalWeight p hp hcop hg Ψ Ψ m (secondExpansionQuotient p x) c d
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (z,x.overlap)

theorem secondExpansionSource_marked_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    ∑ x ∈ source, expansionProfileWeight p hp hcop hg Ψ m c d z Y x *
      actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  unfold secondExpansionSource
  apply Finset.sum_congr rfl
  intro x hx
  have he := hE x hx
  have hc := weighted_secondRayChild_congr_off_common p hp hcop hg hinj hpr
    x.sourceCommon x.divisor he F x.overlap Ψ Ψ m c d x.frequency z
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ (x.sourceCommon ∪ U)) *
        W₁ (primeProductNorm p (x.sourceCommon ∪ U)/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ (x.sourceCommon ∪ U)) *
        W₂ (primeProductNorm p (x.sourceCommon ∪ U)/X)) Φ Y)
    (secondSourcePairKernel p (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ ((A₁ ∪ x.sourceCommon) ∪ U) *
        W₁ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ ((A₂ ∪ x.sourceCommon) ∪ U) *
        W₂ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X)) Φ Y)
    (by
      intro S T hGS hGT
      simp only [secondSourcePairKernel,primeProductNorm_union p x.sourceCommon S hGS,
        primeProductNorm_union p x.sourceCommon T hGT,Finset.union_assoc])
  dsimp only at hc
  rw [← secondExpansionQuotient_of_subset p x he] at hc
  rw [hc]
  simp only [expansionProfileWeight,actualSecondProfileRow,expansionProfileData,
    secondSourceCommonCoefficient,Complex.ofReal_pow]
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0558

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSourceTuples
Source SHA256: 94f77b8ccfe1da4b313ab4f6db3ab39f974e004eb031ae98e636102a81df050c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0559



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic CompletedGauss FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure SecondOriginalSource (ι : Type*) (Jo Jn : ℕ) where
  q0 : Ideal Eis
  quotient : Ideal Eis
  J : Ideal Eis
  C : Ideal Eis
  s : Ideal Eis
  b1 : Ideal Eis
  A1 : Ideal Eis
  A2 : Ideal Eis
  dK : Ideal Eis
  J2 : Ideal Eis
  b2 : Ideal Eis
  common : Finset ι
  divisor : Finset ι
  overlap : Finset ι
  frequency : Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def originalSecondTuple {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) : SecondTuple Jo Jn where
  outer := ⟨x.q0,x.quotient,sourceIdeal p (x.common \ x.divisor)⟩
  core := ![x.J,x.C,sourceIdeal p x.divisor,x.s,x.b1,x.A1,x.A2,x.dK]
  commonResidual := sourceIdeal p x.overlap
  cubeResidual := x.J2
  secondCube := x.b2
  extractedCommon := sourceIdeal p x.common
  frequency := secondUnitFrequency u v x.frequency
  oldAssigned := x.oldAssigned
  newAssigned := fun i => sourcePrime p (x.newAssigned i)

structure SecondOriginalValid {Jo Jn : ℕ} (x : SecondOriginalSource ι Jo Jn) : Prop where
  j_split : x.s*x.J2 = x.J
  b_split : x.b1*x.b2 = x.q0^2*x.J2^2*x.s
  a1 : x.A1 ∣ (x.b1*x.b2).radical
  a2 : x.A2 ∣ (x.b1*x.b2).radical
  first_divisor : x.dK ∣ x.C*(x.b1*x.b2).radical
  first_generator : primaryGenerator x.dK ≠ 0
  second_subset : x.divisor ⊆ x.common
  old_support : ∀ i, (x.oldAssigned i).val ∣ x.q0*x.J*x.C*x.quotient
  new_support : ∀ i, x.newAssigned i ∈ x.common ∪ x.overlap

theorem originalSecondTuple_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : SecondOriginalSource ι Jo Jn) (hx : SecondOriginalValid x) :
    Valid (originalSecondTuple p u v x)
      (secondChild (originalSecondTuple p u v x)).1
      (secondChild (originalSecondTuple p u v x)).2.1
      (secondChild (originalSecondTuple p u v x)).2.2 := by
  have hproduct : sourceIdeal p x.divisor * sourceIdeal p (x.common \ x.divisor) =
      sourceIdeal p x.common := by
    rw [←sourceIdeal_union p x.divisor (x.common \ x.divisor)
      (Finset.disjoint_left.mpr (fun i hi hj => (Finset.mem_sdiff.mp hj).2 hi)),
      Finset.union_sdiff_of_subset hx.second_subset]
  refine ⟨rfl,rfl,hx.j_split,hx.b_split,hx.a1,hx.a2,hx.first_divisor,?_,hx.first_generator,?_,rfl,?_,?_⟩
  · exact hproduct
  · change primaryGenerator (sourceIdeal p x.divisor) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · intro i
    apply (hx.old_support i).trans
    change x.q0*x.J*x.C*x.quotient ∣
      x.q0*(x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*x.quotient
    refine ⟨sourceIdeal p x.divisor*sourceIdeal p x.overlap,?_⟩
    ring
  · intro i
    change (sourcePrime p (x.newAssigned i)).val ∣
      (x.J*x.C*sourceIdeal p x.divisor*sourceIdeal p x.overlap)*sourceIdeal p (x.common \ x.divisor)
    have hslot : (sourcePrime p (x.newAssigned i)).val ∣
        sourceIdeal p x.common*sourceIdeal p x.overlap := by
      rcases Finset.mem_union.mp (hx.new_support i) with hi|hi
      · exact dvd_mul_of_dvd_left (source_prime_dvd p x.common _ hi) _
      · exact dvd_mul_of_dvd_right (source_prime_dvd p x.overlap _ hi) _
    apply hslot.trans
    refine ⟨x.J*x.C,?_⟩
    rw [←hproduct]
    ring

theorem originalSecondTuple_injective
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) :
    Function.Injective (originalSecondTuple (Jo:=Jo) (Jn:=Jn) p u v) := by
  intro x y hxy
  have hi := sourceIdeal_injective p hinj
  have hcore (i : Fin 8) := congrArg (fun z : SecondTuple Jo Jn => z.core i) hxy
  apply SecondOriginalSource.ext
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.q0) hxy
  · exact congrArg (fun z : SecondTuple Jo Jn => z.outer.quotient) hxy
  · exact hcore 0
  · exact hcore 1
  · exact hcore 3
  · exact hcore 4
  · exact hcore 5
  · exact hcore 6
  · exact hcore 7
  · exact congrArg SecondTuple.cubeResidual hxy
  · exact congrArg SecondTuple.secondCube hxy
  · exact hi (congrArg SecondTuple.extractedCommon hxy)
  · exact hi (hcore 2)
  · exact hi (congrArg SecondTuple.commonResidual hxy)
  · exact secondUnitFrequency_injective u v (congrArg SecondTuple.frequency hxy)
  · exact congrArg SecondTuple.oldAssigned hxy
  · funext i
    apply hinj
    exact congrArg (fun z : SecondTuple Jo Jn => (z.newAssigned i).val) hxy

theorem original_second_source_fiber_bound (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (SecondOriginalSource ι Jo Jn))
    (hs : ∀ x ∈ source, SecondOriginalValid x)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let S := source.filter (fun x => secondChild (originalSecondTuple p u v x) = (γ,f,k))
  have hv : ∀ y ∈ S.image (originalSecondTuple p u v), Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    have hh := originalSecondTuple_valid p hp hpr u v x (hs x hxs)
    simpa only [he] using hh
  have hb := valid_tuple_card_le_slot_cap (S.image (originalSecondTuple p u v))
    γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_of_injective S (originalSecondTuple_injective p hinj u v)] at hb
  exact hb

theorem originalSecondTuple_row_norm {Jo Jn : ℕ} (u v : Eisˣ)
    (x : SecondOriginalSource ι Jo Jn) (d e : Eis)
    (hde : d*e = (v:Eis)*(primaryGenerator x.dK*primaryGenerator (sourceIdeal p x.divisor))) :
    ‖ConcreteTraceCRT.eisEmbedding (secondChild (originalSecondTuple p u v x)).2.2‖ =
      ‖ConcreteTraceCRT.eisEmbedding (d*e*x.frequency)‖ := by
  exact secondCanonical_row_norm x.dK (sourceIdeal p x.divisor) u v d e x.frequency hde

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0559

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CubeSource
Source SHA256: e5154ae07a363fa1a4c6b33510e57ae854ef21ebfa30d3936f639cdabaf27450
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0560


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero sourceIdeal_union sourceIdeal_injective sourcePrime source_prime_dvd)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

lemma sourceIdeal_isRadical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i}))) (S : Finset ι) :
    (sourceIdeal p S).IsRadical := by
  change (Ideal.span {∏ i ∈ S,p i}).IsRadical
  rw [FiniteGaussPhase.span_finset_prod]
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty]; exact fun _ _ => by simp
  | @insert a S ha ih =>
    rw [Finset.prod_insert ha,Ideal.mul_eq_inf_of_isCoprime]
    · exact (inferInstance : (Ideal.span {p a}).IsPrime).isRadical.inf ih
    · apply IsCoprime.prod_right
      intro b hb
      exact hcop (fun he => ha (he.symm ▸ hb))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma cubeRadical_span_dvd_product (B : Finset ι) (v : ι → ℕ)
    (hv : ∀ i ∈ B, 0 < v i) :
    sourceIdeal p B ∣ Ideal.span {primeProduct p B v} := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i) ∣ primeProduct p B v
  unfold primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  exact dvd_pow_self _ (Nat.ne_of_gt (hv i hi))

theorem cubeSupport_dvd_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B : Finset ι) (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p B ∣
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  apply Ideal.dvd_iff_le.mpr
  apply (sourceIdeal_isRadical p hcop B).radical_le_iff.mpr
  apply Ideal.dvd_iff_le.mp
  rw [Ideal.span_singleton_mul_span_singleton,←primeProduct_add]
  exact cubeRadical_span_dvd_product p B _ hv

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma aLabel_dvd_cubeSupport (B : Finset ι) (ε : ι → Bool) :
    Ideal.span {aLabel p B ε} ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  unfold aLabel primeProduct
  change (∏ i ∈ B,p i^bit (ε i)) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases hh : ε i <;> simp [bit]

theorem firstMask_dvd_cube_radical
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (B C D : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v₁ v₂ : ι → ℕ) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    sourceIdeal p D ∣ sourceIdeal p C *
      (Ideal.span {primeProduct p B v₁}*Ideal.span {primeProduct p B v₂}).radical := by
  have hd := InverseInitialArithmetic.sourceIdeal_dvd p D (C∪B) hD
  rw [sourceIdeal_union p C B hCB] at hd
  exact hd.trans (mul_dvd_mul_left _ (cubeSupport_dvd_radical p hcop B v₁ v₂ hv))

def cubeSecondSource {Jo Jn : ℕ} (B C D G E V : Finset ι)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι) :
    SecondOriginalSource ι Jo Jn where
  q0 := Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  quotient := t
  J := Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  C := sourceIdeal p C
  s := Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)}
  b1 := Ideal.span {primeProduct p B v₁}
  A1 := Ideal.span {aLabel p B ε₁}
  A2 := Ideal.span {aLabel p B ε₂}
  dK := sourceIdeal p D
  J2 := Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  common := G
  divisor := E
  overlap := V
  frequency := k
  oldAssigned := oldAssigned
  newAssigned := newAssigned

theorem cubeSecondSource_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣
      Ideal.span {b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} *
      Ideal.span {jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂} * sourceIdeal p C * t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) := by
  constructor
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i+v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂} = _
    rw [Ideal.span_singleton_mul_span_singleton,←jLabel_eq_squarefree_mul_j2]
    rfl
  · have hb := congrArg (fun a : Eis => (Ideal.span {a} : Ideal Eis))
      (cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv)
    simpa only [cubeSecondSource,pow_two,←Ideal.span_singleton_mul_span_singleton] using hb
  · exact (aLabel_dvd_cubeSupport p B ε₁).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact (aLabel_dvd_cubeSupport p B ε₂).trans (cubeSupport_dvd_radical p hcop B v₁ v₂ hv)
  · exact firstMask_dvd_cube_radical p hcop B C D hCB hD v₁ v₂ hv
  · change primaryGenerator (sourceIdeal p D) ≠ 0
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  · exact hE
  · exact hold
  · exact hnew

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem oldSlot_dvd_reconstructed_support
    (B C : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) (P t : Ideal Eis)
    (hP : P ∣ sourceIdeal p B*sourceIdeal p C*t) :
    P ∣ Ideal.span {b0Label p B v ε₁ ε₂}*
      Ideal.span {jLabel p B v ε₁ ε₂}*sourceIdeal p C*t := by
  have hb := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv)
  change sourceIdeal p B ∣ Ideal.span {jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂} at hb
  rw [←Ideal.span_singleton_mul_span_singleton,mul_comm (Ideal.span {jLabel p B v ε₁ ε₂})] at hb
  exact hP.trans (mul_dvd_mul_right (mul_dvd_mul_right hb _) _)

theorem cubeSecondSource_valid_original_slots (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (B C D G E V : Finset ι) (hCB : Disjoint C B)
    (hD : D ⊆ C∪B) (hE : E ⊆ G)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i)
    (t : Ideal Eis) (k : Eis)
    (oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal) (newAssigned : Fin Jn → ι)
    (hold : ∀ i, (oldAssigned i).val ∣ sourceIdeal p B*sourceIdeal p C*t)
    (hnew : ∀ i, newAssigned i ∈ G∪V) :
    SecondOriginalValid (cubeSecondSource p B C D G E V v₁ v₂ ε₁ ε₂ t k oldAssigned newAssigned) :=
  cubeSecondSource_valid p hp hpr hcop B C D G E V hCB hD hE v₁ v₂ ε₁ ε₂ hv t k
    oldAssigned newAssigned
    (fun i => oldSlot_dvd_reconstructed_support p B C _ ε₁ ε₂ hv _ t (hold i)) hnew

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0560

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CubeSupportNorm
Source SHA256: 7ec7296bc56e76d605ceae00a1d4e52eda155b287538545c7a63a79ee7620db6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0561



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseInitialArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀ i,p i≠0)

include hp in
theorem cube_whole_support_norm (b : CubeCoordinates ι) :
    primeProductNorm p b.support≤
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2*
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2 := by
  have hd := cubeRadical_span_dvd_product p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.support_pos
  have hne : (Ideal.span {primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i)}:Ideal O)≠0 :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hn := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hne))
    (Ideal.absNorm_dvd_absNorm_of_le (Ideal.dvd_iff_le.mp hd))
  have he : (Ideal.absNorm (sourceIdeal p b.support):ℝ)=primeProductNorm p b.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (eisEmbedding_norm_sq_eq_absNorm_span (∏i∈b.support,p i)).symm
  have hh : primeProductNorm p b.support≤
      ‖eisEmbedding (primeProduct p b.support (fun i=>b.leftExponent i+b.rightExponent i))‖^2 := by
    rw [eisEmbedding_norm_sq_eq_absNorm_span,←he]
    exact_mod_cast hn
  simpa only [primeProduct_add,map_mul,norm_mul,mul_pow] using hh

include hp in
theorem cube_whole_support_dyad (b : CubeCoordinates ι) (B : ℝ) (hB : 0≤B)
    (hl : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hr : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p b.support≤B^2 :=
  (cube_whole_support_norm p hp b).trans ((mul_le_mul hl hr (sq_nonneg _) hB).trans_eq (pow_two B).symm)

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0561

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstMarkedZeroSource
Source SHA256: 44254b46ca334005b29157ed15476d5be02f5797918b254683a3a660d5a0c3b3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0562



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem full_marked_first_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (coeff:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ)
      (extra₁ extra₂ : CubeCoordinates ι→Finset ι)
      (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
      (W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ L K B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖coeff b D I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤L) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤L) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,coeff b D I*
        canonicalCubeDualZero p hp hcop hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W K‖≤
      C*B^(1+ε)*L*F*Γ*((B^2*L)^ε)^2*(G₁*G₂ * |K| * ‖paperRadialFourier W 0‖) := by
  obtain ⟨Cz,hCz,hzero⟩ := full_variable_first_zero_bound ε hε
  obtain ⟨Cm,hCm,hmark⟩ := whole_cube_marked_test_uniform ε hε
  refine ⟨Cz*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    test₁ test₂ extra₁ extra₂ slots lists a W Γ G₁ G₂ L K B F
    hΓ hG₁ hG₂ hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff hslots ha
    he₁ he₂ htest₁ htest₂ hs₁ hs₂
  have hB0 : 0≤B := le_trans zero_le_one hB
  have hextra (extra : CubeCoordinates ι→Finset ι) (he : ∀b∈bs,extra b⊆b.support)
      (b : CubeCoordinates ι) (hb : b∈bs) : primeProductNorm p (extra b)≤B^2 :=
    (primeProductNorm_mono p hp (he b hb)).trans (cube_whole_support_dyad p hp b B hB0 (hb₁ b hb) (hb₂ b hb))
  have ht₁ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₁ b∪U)*test₁ b U‖≤Cm*(B^2*L)^ε*G₁ :=
    hmark p hp hcop slots lists a hslots ha (extra₁ b) (test₁ b) (B^2) G₁ L
      (sq_nonneg _) hG₁ hL.le (hextra extra₁ he₁ b hb) (htest₁ b hb) (hs₁ b hb)
  have ht₂ (b : CubeCoordinates ι) (hb : b∈bs) :
      ∀U,‖primeMark slots lists a (extra₂ b∪U)*test₂ b U‖≤Cm*(B^2*L)^ε*G₂ :=
    hmark p hp hcop slots lists a hslots ha (extra₂ b) (test₂ b) (B^2) G₂ L
      (sq_nonneg _) hG₂ hL.le (hextra extra₂ he₂ b hb) (htest₂ b hb) (hs₂ b hb)
  have hh := hzero p hp hcop hg hinj hc pool bs labels coeff Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists a (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists a (extra₂ b∪U)*test₂ b U) W
    Γ (Cm*(B^2*L)^ε*G₁) (Cm*(B^2*L)^ε*G₂) L K B F
    hΓ (by positivity) (by positivity) hL hB hF hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF hcoeff ht₁ ht₂
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2)
  exact hh.trans_eq (by ring)

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0562

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstTailAggregation
Source SHA256: fc48523d615700440adfe9de099966981f6f1337c5a52e49a4fcd020718ccf1b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0563



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
section
variable {ι:Type*} [DecidableEq ι]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def firstLocalPhysicalTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K:ℝ) (T:Finset ι→Finset O) (D:Finset ι):ℂ :=
  ∑'h:{h:O // h∉T D},actualFirstKernel p hp hcop hg (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
    (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂) W (fun _=>1) (fun _=>1) 1 1 K
    (primeSubsetGenerator (fun i=>Ideal.span {p i}) D) h.val

theorem cube_tail_support_test (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
    (K L:ℝ) (T:Finset ι→Finset O)
    (hs:∀U,H₁ U≠0→primeProductNorm p U≤L) (hC:¬primeProductNorm p C≤L) :
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T=0 := by
  have hz (U:Finset ι):H₁ ((b.rightDivisor∪C)∪U)=0:=by
    by_contra h
    exact hC ((primeProductNorm_mono p hp
      (Finset.Subset.trans Finset.subset_union_right Finset.subset_union_left)).trans (hs _ h))
  have hcoef (U:Finset ι):canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁ U=0:=by
    simp only [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,ite_true,hz,mul_zero,zero_mul]
  simp only [canonicalCubeDualTail,actualFirstKernel,threeGaussRowFactor,hcoef,mul_zero,
    star_zero,zero_mul,ite_self,Finset.sum_const_zero,tsum_zero]

end

theorem full_first_tail_from_local (ε:ℝ) (hε:0<ε) :
    ∃Ctail:ℝ,0<Ctail ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (H₁ H₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (K B L F Γ E:ℝ)
      (T:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→Finset O),
      1≤B → 0<L → 1≤F → 0≤Γ → 0≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (∀b∈bs,∀U,H₁ b U≠0→primeProductNorm p U≤L) →
      (∀b∈bs,∀C∈boundedPrimeSupports p (pool\b.support) L,∀I∈labels,
        ∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I) D‖≤E) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I)‖≤
        Ctail*B^(4+ε)*L^2*F*Γ*E := by
  obtain ⟨Cb,hCb,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨Cb*128^3,by positivity,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ H₁ H₂ W K B L F Γ E T
    hB hL hF hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha hs hlocal
  have hBp:0<B:=zero_lt_one.trans_le hB
  have hlabel:(labels.card:ℝ)≤128*F:=DescentFiberCost.finite_ideal_count_real labels F hF hI0 hIF
  have hbcount:(bs.card:ℝ)≤Cb*B^(1+ε)*B:=by
    apply hcount p hp hinj bs B B hB hBp.le hadm hb₁ hb₂
    intro b hb
    have hn:primeProductNorm p (cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)≤B^2:=
      (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans
        (cube_whole_support_dyad p hp b B hBp.le (hb₁ b hb) (hb₂ b hb))
    change ‖eisEmbedding (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i)‖^2≤B^2 at hn
    nlinarith [norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit,p i))]
  let z (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):ℂ:=
    canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (ConcretePrimeRowBridge.idealGenerator I) (H₁ b) (H₂ b) W K (T b C I)
  have hblock (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels):
      ‖z b C I‖≤128*(L*B^2)*E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    dsimp only [z,canonicalCubeDualTail]
    rw [norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) (canonicalCubeOuter_norm_le_one p hp hcop hg hc b C
      Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)).trans
    calc
      _≤∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,E:=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro D hD
        rw [norm_mul]
        exact (mul_le_mul (sourceMobiusDivisor_norm_le_one p hp D)
          (hlocal b hb C hC I hI D hD) (norm_nonneg _) zero_le_one).trans_eq (one_mul E)
      _= ((C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.card:ℝ)*E:=by simp
      _≤_:=mul_le_mul_of_nonneg_right (cubeSourceDivisors_card p hp hinj b C B L hBp hL hCB
        (hb₁ b hb) (hb₂ b hb) (Finset.mem_filter.mp hC).2) hE
  have hcommon (b:CubeCoordinates ι) (hb:b∈bs):
      ‖∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤
      (128*L)*(128*F)*Γ*(128*(L*B^2)*E):=by
    have heq:(∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I)=
        ∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,a b C I*z b C I:=by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro C hC hnot
      have hn:¬primeProductNorm p C≤L:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
      apply Finset.sum_eq_zero
      intro I hI
      rw [show z b C I=0 from cube_tail_support_test p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ _
        (H₁ b) (H₂ b) W K L (T b C I) (hs b hb) hn,mul_zero]
    rw [heq]
    calc
      _≤∑C∈boundedPrimeSupports p (pool\b.support) L,∑I∈labels,Γ*(128*(L*B^2)*E):=by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro C hC
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro I hI
        rw [norm_mul]
        exact mul_le_mul (ha b hb C (Finset.mem_filter.mp hC).1 I hI) (hblock b hb C hC I hI) (norm_nonneg _) hΓ
      _= ((boundedPrimeSupports p (pool\b.support) L).card:ℝ)*(labels.card:ℝ)*Γ*(128*(L*B^2)*E):=by simp;ring
      _≤_:=by gcongr;exact boundedPrimeSupports_card_positive p hp hinj _ _ hL
  change ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*z b C I‖≤_
  calc
    _≤∑b∈bs,(128*L)*(128*F)*Γ*(128*(L*B^2)*E):=
      (norm_sum_le _ _).trans (Finset.sum_le_sum hcommon)
    _= (bs.card:ℝ)*((128*L)*(128*F)*Γ*(128*(L*B^2)*E)):=by simp
    _≤(Cb*B^(1+ε)*B)*((128*L)*(128*F)*Γ*(128*(L*B^2)*E)):=by gcongr
    _= _:=by
      have he:B^(1+ε)*B*B^2=B^(4+ε):=by
        calc
          _=B^(1+ε)*B^(1:ℝ)*B^(2:ℝ):=by rw [Real.rpow_one,Real.rpow_two]
          _=B^((1+ε)+1+2):=by rw [←Real.rpow_add hBp,←Real.rpow_add hBp]
          _= _:=by congr 1;ring
      calc
        _=(Cb*128^3)*(B^(1+ε)*B*B^2)*L^2*F*Γ*E:=by ring
        _= _:=by rw [he]

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0563

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstRapidPhysicalTail
Source SHA256: 1b12b909f2d140241ff831082cf16f9cb35e45c6900b742b9fe0f489383bc78e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0564



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem first_whole_cube_rapid_physical_tail (ε:ℝ) (hε:0<ε)
    (Mmax Fmax eta tau saving:ℝ) (hMm:0≤Mmax) (hFm:0≤Fmax)
    (heta:0≤eta) (htau:0<tau) :
    ∃ (s:Finset (ℕ×ℕ)) (Ct Cm:ℝ),0<Ct ∧ 0<Cm ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι) (C D extra₁ extra₂:Finset ι)
      (f:Ideal O) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (test₁ test₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (E G₁ G₂ Z M r ell V B j:ℝ) (delta:Finset ι→ℝ),
      b.Admissible → Disjoint C b.support →
      D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit →
      f≠0 → 0≤E → 0≤G₁ → 0≤G₂ → 1≤Z → 0≤M → M≤Mmax →
      0≤ell → 0≤V → -eta≤r → r+3*ell+V≤Fmax →
      primeProductNorm p C≤Z^(r+eta) →
      primeProductNorm p extra₁≤E → primeProductNorm p extra₂≤E →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖test₁ U‖≤G₁) → (∀U,‖test₂ U‖≤G₂) →
      (∀U,test₁ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀U,test₂ U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta) →
      ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta) →
      (Ideal.absNorm f:ℝ)≤Z^(V+eta) → primeProductNorm p D≤Z^(delta D+eta) →
      Z^(B-eta)≤primeProductNorm p C →
      Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2 →
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (ConcretePrimeRowBridge.idealGenerator f)
        (fun U=>primeMark slots lists a (extra₁∪U)*test₁ U)
        (fun U=>primeMark slots lists a (extra₂∪U)*test₂ U) W (Z^M)
        (fun D=>childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent
          b.rightExponent b.leftBit b.rightBit f)
          (Z^(firstPhysicalHeight M r ell V (delta D) B j+12*eta+tau))) D‖≤
      65536*(Cm*(E*Z^(r+eta))^ε*G₁)*(Cm*(E*Z^(r+eta))^ε*G₂)*
        (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=choose_actual_first_tail_order Mmax Fmax eta tau saving hMm hFm heta htau
  obtain ⟨s,Ct,Cm,hCt,hCm,htail⟩:=first_whole_cube_canonical_tail ε hε order
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool b C D extra₁ extra₂ f Ψ₁ Ψ₂ m₁ m₂ slots lists a
    test₁ test₂ W E G₁ G₂ Z M r ell V B j delta hb hCB hD hf hE hG₁ hG₂ hZ hM hMmax
    hell hV hr hwhole hC he₁ he₂ hΨ₁ hΨ₂ hslots ha ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hlocal:=htail p hp hinj hcop hg hc pool b hb C D hCB f hf Ψ₁ Ψ₂ hΨ₁ hΨ₂
    m₁ m₂ extra₁ extra₂ E slots lists a hE he₁ he₂ hslots ha test₁ test₂ W G₁ G₂ Z M r ell V
    (delta D) B j eta tau hG₁ hG₂ hz ht₁ ht₂ hs₁ hs₂ hb₁ hb₂ hF hdelta hBlo hj
  dsimp only at hlocal
  apply hlocal.trans
  exact horder p hp b C D hCB hD Z M r ell V
    (Cm*(E*Z^(r+eta))^ε*G₁) (Cm*(E*Z^(r+eta))^ε*G₂)
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hM hMmax hell hV hr hwhole (by positivity) (by positivity) (by positivity) hb₁ hb₂ hC

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0564

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstFullRapidTail
Source SHA256: 5fef305bebe7c3afcb956fb524a35f1482ef1c6ab4f9b60c8fa19f2727b12887
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0565


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def firstExactPhysicalCutoff {ι:Type*} [DecidableEq ι] (p:ι→O)
    (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O) (Z M r ell V eta tau:ℝ) (D:Finset ι):Finset O :=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (Z^(firstPhysicalHeight M r ell V (Real.logb Z (primeProductNorm p D))
      (Real.logb Z (primeProductNorm p C))
      (Real.logb Z (‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau))

theorem full_first_whole_marked_rapid_tail (Mmax Fmax eta tau saving:ℝ)
    (hMm:0≤Mmax) (hFm:0≤Fmax) (heta:0≤eta) (htau:0<tau) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
      (slots:Finset σ) (lists:σ→Finset ι) (weights:σ→ι→ℂ)
      (extra₁ extra₂:CubeCoordinates ι→Finset ι)
      (test₁ test₂:CubeCoordinates ι→Finset ι→ℂ) (W:𝓢(ℝ,ℂ))
      (Z M r ell V Γ G₁ G₂:ℝ),
      1<Z → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤r → r+3*ell+V≤Fmax →
      0≤Γ → 0≤G₁ → 0≤G₂ →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta)) →
      (∀b∈bs,‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta)) →
      (∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖weights i k‖≤1) →
      (∀b∈bs,extra₁ b⊆b.support) → (∀b∈bs,extra₂ b⊆b.support) →
      (∀b∈bs,∀U,‖test₁ b U‖≤G₁) → (∀b∈bs,∀U,‖test₂ b U‖≤G₂) →
      (∀b∈bs,∀U,test₁ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      (∀b∈bs,∀U,test₂ b U≠0→primeProductNorm p U≤Z^(r+eta)) →
      ‖∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
        canonicalCubeDualTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
          (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
          (firstExactPhysicalCutoff p b C I Z M r ell V eta tau)‖≤
      Ctail*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  let saving':=saving+4*Fmax+14*eta
  obtain ⟨s,Ct,Cm,hCt,hCm,hloc⟩:=first_whole_cube_rapid_physical_tail 1 (by norm_num)
    Mmax Fmax eta tau saving' hMm hFm heta htau
  obtain ⟨Ca,hCa,hagg⟩:=full_first_tail_from_local 1 (by norm_num)
  refine ⟨s,Ca*65536*Cm^2*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ slots lists weights extra₁ extra₂
    test₁ test₂ W Z M r ell V Γ G₁ G₂ hZ hM hMmax hell hV hr hwhole hΓ hG₁ hG₂ hΨ₁ hΨ₂
    hadm hb₁ hb₂ hI0 hIF ha hslots hw he₁ he₂ ht₁ ht₂ hs₁ hs₂
  have hz:0<Z:=zero_lt_one.trans hZ
  let B:=Z^(ell+eta)
  let L:=Z^(r+eta)
  let E:=65536*(Cm*(B^2*L)*G₁)*(Cm*(B^2*L)*G₂)*
    (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving')
  have hB:1≤B:=Real.one_le_rpow hZ.le (by linarith)
  have hL:0<L:=Real.rpow_pos_of_pos hz _
  have hE:0≤E:=by dsimp [E,B,L];positivity
  have hextra (extra:CubeCoordinates ι→Finset ι) (he:∀b∈bs,extra b⊆b.support)
      (b:CubeCoordinates ι) (hb:b∈bs):primeProductNorm p (extra b)≤B^2:=
    (primeProductNorm_mono p hp (he b hb)).trans
      (cube_whole_support_dyad p hp b B (zero_le_one.trans hB) (hb₁ b hb) (hb₂ b hb))
  have hlocal (b:CubeCoordinates ι) (hb:b∈bs) (C:Finset ι)
      (hC:C∈boundedPrimeSupports p (pool\b.support) L) (I:Ideal O) (hI:I∈labels)
      (D:Finset ι) (hD:D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset):
      ‖firstLocalPhysicalTail p hp hcop hg pool b C Ψ₁ Ψ₂ m₁ m₂ (ConcretePrimeRowBridge.idealGenerator I)
        (fun U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
        (fun U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M)
        (firstExactPhysicalCutoff p b C I Z M r ell V eta tau) D‖≤E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    have hupper (x:ℝ) (hx:0<x):x≤Z^(Real.logb Z x+eta):=by
      conv_lhs=>rw [←Real.rpow_logb hz (ne_of_gt hZ) hx]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hlower (x:ℝ) (hx:0<x):Z^(Real.logb Z x-eta)≤x:=by
      conv_rhs=>rw [←Real.rpow_logb hz (ne_of_gt hZ) hx]
      exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
    have hjpos:0<‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2:=
      SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
    have he:=hloc p hp hinj hcop hg hc pool b C D (extra₁ b) (extra₂ b) I Ψ₁ Ψ₂ m₁ m₂
      slots lists weights (test₁ b) (test₂ b) W (B^2) G₁ G₂ Z M r ell V
      (Real.logb Z (primeProductNorm p C))
      (Real.logb Z (‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))
      (fun D=>Real.logb Z (primeProductNorm p D))
      (hadm b hb) hCB (Finset.mem_powerset.mp hD) (hI0 I hI) (sq_nonneg _) hG₁ hG₂ hZ.le hM hMmax
      hell hV hr hwhole (Finset.mem_filter.mp hC).2 (hextra extra₁ he₁ b hb) (hextra extra₂ he₂ b hb)
      hΨ₁ hΨ₂ hslots hw (ht₁ b hb) (ht₂ b hb) (hs₁ b hb) (hs₂ b hb) (hb₁ b hb) (hb₂ b hb) (hIF I hI)
      (hupper _ (primeProductNorm_pos p hp D)) (hlower _ (primeProductNorm_pos p hp C)) (hlower _ hjpos)
    simpa only [firstLocalPhysicalTail,firstExactPhysicalCutoff,Real.rpow_one,E,L] using he
  have he:=hagg p hp hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M) B L (Z^(V+eta)) Γ E
    (fun b C I=>firstExactPhysicalCutoff p b C I Z M r ell V eta tau)
    hB hL (Real.one_le_rpow hZ.le (by linarith)) hΓ hE hΨ₁ hΨ₂ hadm hb₁ hb₂ hI0 hIF ha
    (fun b hb U hU=>hs₁ b hb U (mul_ne_zero_iff.mp hU).2) hlocal
  apply he.trans
  have hexp:B^9*L^4*Z^(V+eta)*Z^(-saving')≤Z^(-saving):=by
    dsimp [B,L]
    rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,
      ←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    dsimp [saving']
    norm_num
    linarith
  have hm:=mul_le_mul_of_nonneg_left hexp
    (show 0≤Ca*65536*Cm^2*Ct*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) from by positivity)
  convert hm using 1
  · dsimp only [E]
    norm_num
    ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0565

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ReopenedZeroEnergy
Source SHA256: 9779e9afd5c6385f34a1d17809838ebada30e94fa7c887ca67ea9722a94c4020
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0566



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_reopened_marked_zero_bound (ε : ℝ) (hε : 0<ε) :
    ∃ C:ℝ,0<C ∧ ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (Q:Finset (ι→₀ℕ)) (labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ) (Ψ:O→*ℂ) (m:O)
      (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (W:ℝ→ℂ) (Φ:𝓢(ℝ,ℂ)) (Γ G L K B F:ℝ),
      0≤Γ → 0≤G → 0<L → 1≤B → 1≤F →
      (∀u,‖Ψ u‖≤1) →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ) →
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀U,‖W (primeProductNorm p U)‖≤G) →
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤L) →
      ‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m
          (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ K)‖≤
      C*B^(1+ε)*L*F*Γ^2*((B^2*L)^ε)^2*(G^2*|K| *‖paperRadialFourier Φ 0‖) := by
  obtain ⟨C,hC,he⟩ := full_marked_first_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G L K B F
    hΓ hG hL hB hF hΨ hQ hn hFlabels hβ hslots ha hW hs
  have hb := reopenedCubeFamily_cube_norms p Q B hQ
  have hcoeff := reopenedPairCoefficient_bound Q labels β Γ hΓ hβ
  have hh := he p hp hcop hg hinj hc pool (reopenedCubeFamily Q) labels
    (reopenedPairCoefficient β) Ψ Ψ m m (fun _ U=>W (primeProductNorm p U))
    (fun _ U=>W (primeProductNorm p U))
    (fun b=>b.rightExponent.support) (fun b=>b.leftExponent.support)
    slots lists a Φ (Γ^2) G G L K B F (sq_nonneg _) hG hG hL hB hF hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun b hb'=> (hb b hb').1) (fun b hb'=> (hb b hb').2)
    hn hFlabels (fun b hb C hC I hI=>hcoeff b hb C I hI) hslots ha
    (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hs) (fun _ _=>hs)
  simpa only [reopenedPhysicalSourceSum,Finset.union_comm,pow_two] using hh

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0566

/-! Original module: OAI.NumberTheory.DirichletL.Descent.OriginalZeroPhysical
Source SHA256: 949656ab2d5edb66aec022425b8ccd6a95459ef0aad484800bcdf8677b7646b5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0567



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_first_zero_physical (ε:ℝ)(hε:0<ε):
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
      (Z M r ell V eta Γ G:ℝ),1<Z→0≤ell+eta→0≤V+eta→0≤Γ→0≤G→
      (∀u,‖Ψ u‖≤1)→
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀U,‖W (primeProductNorm p U)‖≤G)→
      (∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta))→
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun b C I=>
        canonicalCubeDualZero p hp hcop hg pool b C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>primeMark slots lists a (U∪b.rightExponent.support)*W (primeProductNorm p U))
          (fun U=>primeMark slots lists a (U∪b.leftExponent.support)*W (primeProductNorm p U)) Φ (Z^M))‖≤
        C*Γ^2*G^2*‖paperRadialFourier Φ 0‖*Z^(M-ell+3*eta+ε*(5*ell+2*r+7*eta)):=by
  obtain ⟨C,hC,he⟩:=original_reopened_marked_zero_bound ε hε
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Z M r ell V eta Γ G
    hZ hell hV hΓ hG hΨ hQ hn hlabels hβ hslots ha hW hs
  have hz:0<Z:=zero_lt_one.trans hZ
  have hb:=he p hp hcop hg hinj hc pool Q labels β Ψ m slots lists a W Φ Γ G
    (Z^(r+eta)) (Z^M) (Z^(ell+eta)) (Z^(V+eta)) hΓ hG
    (Real.rpow_pos_of_pos hz _) (Real.one_le_rpow hZ.le hell) (Real.one_le_rpow hZ.le hV)
    hΨ hQ hn hlabels hβ hslots ha hW hs
  apply (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hz.le _)).trans
  apply le_of_eq
  rw [abs_of_pos (Real.rpow_pos_of_pos hz M)]
  have hp2 (x:ℝ):(Z^x)^2=Z^(2*x):=by rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;ring
  rw [hp2,←Real.rpow_add hz,←Real.rpow_mul hz.le,←Real.rpow_mul hz.le,hp2]
  calc
    _=(C*Γ^2*G^2*‖paperRadialFourier Φ 0‖)*
      (Z^(-r-2*ell-V)*Z^((ell+eta)*(1+ε))*Z^(r+eta)*Z^(V+eta)*
        Z^(2*((2*(ell+eta)+(r+eta))*ε))*Z^M):=by ring
    _=_:=by
      rw [←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz,←Real.rpow_add hz]
      congr 2
      ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0567

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSourceEncoding
Source SHA256: 942fc0fa022ee005d084f787b993689f4f775ae0b259cba5016b4deec7c7d662
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0568


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_injective)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

@[ext] structure MarkedSecondSource (ι : Type*) (Jo Jn : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  second : SecondExpansionData ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal
  newAssigned : Fin Jn → ι

variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def markedSecondOriginal {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : SecondOriginalSource ι Jo Jn :=
  cubeSecondSource p x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit
    x.quotient x.second.frequency x.oldAssigned x.newAssigned

theorem markedSecondOriginal_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} :
    Set.InjOn (markedSecondOriginal (Jo:=Jo) (Jn:=Jn) p) {x | x.cube.Admissible} := by
  intro x hx y hy hxy
  have hc : x.cube = y.cube := by
    apply cubeDivisorKey_injective_on_product p hp hinj hx hy
    · simpa only [markedSecondOriginal,cubeSecondSource,cubeProductIdeal] using
        congrArg (fun z : SecondOriginalSource ι Jo Jn => z.b1*z.b2) hxy
    · funext i
      fin_cases i
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.b1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A1 hxy
      · simpa [markedSecondOriginal,cubeSecondSource,cubeDivisorKey] using
          congrArg SecondOriginalSource.A2 hxy
  apply MarkedSecondSource.ext hc
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.C hxy)
  · exact sourceIdeal_injective p hinj (congrArg SecondOriginalSource.dK hxy)
  · apply SecondExpansionData.ext
    · exact congrArg SecondOriginalSource.common hxy
    · exact congrArg SecondOriginalSource.divisor hxy
    · exact congrArg SecondOriginalSource.overlap hxy
    · exact congrArg SecondOriginalSource.frequency hxy
  · exact congrArg SecondOriginalSource.quotient hxy
  · exact congrArg SecondOriginalSource.oldAssigned hxy
  · exact congrArg SecondOriginalSource.newAssigned hxy

theorem markedSecondTuple_injOn (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i})) {Jo Jn : ℕ} (u v : Eisˣ) :
    Set.InjOn (fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x))
      {x | x.cube.Admissible} := by
  intro x hx y hy he
  exact markedSecondOriginal_injOn p hp hinj hx hy
    (originalSecondTuple_injective p hinj u v he)

theorem markedSecondOriginal_valid (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap) :
    SecondOriginalValid (markedSecondOriginal p x) :=
  cubeSecondSource_valid_original_slots p hp hpr hcop x.cube.support x.firstCommon x.firstDivisor
    x.second.sourceCommon x.second.divisor x.second.overlap hCB hD hE
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit x.cube.support_pos
    x.quotient x.second.frequency x.oldAssigned x.newAssigned hold hnew

theorem actual_marked_second_source_fiber (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (ha : ∀ x ∈ source, x.cube.Admissible)
    (hCB : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support)
    (hD : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon)
    (hold : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient)
    (hnew : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap)
    (γ : OuterTriple) (f : Ideal Eis) (k : Eis)
    (hf : f ≠ 0) (hq : γ.q0 ≠ 0) (ht : γ.quotient ≠ 0) (hr : γ.residual ≠ 0)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K) :
    (source.filter (fun x => secondChild (originalSecondTuple p u v (markedSecondOriginal p x)) = (γ,f,k))).card ≤
      (IdealMobiusDivisorSum.idealDivisors f).card^(9+4*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.q0).card^(5+2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.quotient).card^(2*K) *
      (IdealMobiusDivisorSum.idealDivisors γ.residual).card^(2*K) := by
  classical
  let encode := fun x : MarkedSecondSource ι Jo Jn => originalSecondTuple p u v (markedSecondOriginal p x)
  let S := source.filter (fun x => secondChild (encode x) = (γ,f,k))
  have hvalid : ∀ x ∈ source,
      Valid (encode x) (secondChild (encode x)).1 (secondChild (encode x)).2.1 (secondChild (encode x)).2.2 := by
    intro x hx
    exact originalSecondTuple_valid p hp hpr u v (markedSecondOriginal p x)
      (markedSecondOriginal_valid p hp hpr hcop x (hCB x hx) (hD x hx) (hE x hx) (hold x hx) (hnew x hx))
  have hv : ∀ y ∈ S.image encode, Valid y γ f k := by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hxs,he⟩ := Finset.mem_filter.mp hx
    simpa only [he] using hvalid x hxs
  have hi : Set.InjOn encode (S : Set (MarkedSecondSource ι Jo Jn)) := by
    intro x hx y hy he
    exact markedSecondTuple_injOn p hp hinj u v
      (ha x (Finset.mem_filter.mp hx).1) (ha y (Finset.mem_filter.mp hy).1) he
  have hb := valid_tuple_card_le_slot_cap (S.image encode) γ f k hf hq ht hr hv K ho hn
  rw [Finset.card_image_iff.mpr hi] at hb
  exact hb

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0568

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondFixedFamily
Source SHA256: 4f737ebfc1300337b3355eee490837537f437a9938b87300941a416c68e1356a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0569


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem secondChildColumn_drop_puncture (Ψ : Eis →* ℂ) (m d f k : Eis)
    (hd : d ∣ m*f) (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hp hcop hg Ψ (m*d) f k H S =
      secondChildColumn p hp hcop hg Ψ m f k H S := by
  by_cases hz : ∃ i ∈ S, d ∈ Ideal.span {p i}
  · obtain ⟨i,hi,hdI⟩ := hz
    have hr : m*f ∈ Ideal.span {p i} := by
      obtain ⟨a,ha⟩ := hd
      rw [ha]
      exact Ideal.mul_mem_right _ _ hdI
    have hl : (m*d)*f ∈ Ideal.span {p i} := by
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hdI)
    rw [secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ (m*d) f k H S i hi hl,
      secondChildColumn_zero_of_mask_label_mem p hp hcop hg Ψ m f k H S i hi hr]
  · have hm : rowCoprimeMask (fun i => Ideal.span {p i}) S d = 1 := by
      simp only [rowCoprimeMask,ite_eq_right hz]
    simp only [secondChildColumn,FirstPassCubeLabels.mask_mul _ hg S,hm,mul_one]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_drop_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m d f k : Eis) (hd : d ∣ m*f)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ (m*d) f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_drop_puncture p hp hcop hg Ψ m d f k hd]

theorem canonicalMarkedSplit_original_lists (F V A : Finset ι) (Ψ : Eis →* ℂ)
    (m r c d e k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hA : ∀ i ∈ A, (m*r)*(c*e*∏ j ∈ V,p j) ∈ Ideal.span {p i}) :
    canonicalMarkedSplit p hp hcop hg F V A Ψ m r c d e k slots lists a W X =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hp hcop hg F Ψ (m*r)
          (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) := by
  unfold canonicalMarkedSplit
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F A Ψ (m*r)
    (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) hA]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_first_divisor_dvd_child
    (B C D V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (m r e : Eis) :
    primeSubsetGenerator (fun i => Ideal.span {p i}) D ∣
      ((m*b0Label p B v ε₁ ε₂)*r)*
        (((∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂)*e*∏ i ∈ V,p i) := by
  have hd := poisson_mask_generator_dvd p D (C∪B) hD
  rw [Finset.prod_union hCB] at hd
  have hb := cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv
  change (∏ i ∈ B,p i) ∣ jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂ at hb
  apply (hd.trans (mul_dvd_mul_left (∏ i ∈ C,p i) hb)).trans
  refine ⟨m*r*e*∏ i ∈ V,p i,?_⟩
  ring

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_extracted_support_killed
    (B C G E V A : Finset ι) (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i) (m : Eis) :
    ∀ i ∈ A,
      ((m*b0Label p B v ε₁ ε₂)*secondMaskQuotient p E G hEG)*
        (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*
          primeSubsetGenerator (fun j => Ideal.span {p j}) E*∏ j ∈ V,p j) ∈ Ideal.span {p i} := by
  let r := secondMaskQuotient p E G hEG
  let e := primeSubsetGenerator (fun j => Ideal.span {p j}) E
  let T := ((m*b0Label p B v ε₁ ε₂)*r)*
    (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*e*∏ j ∈ V,p j)
  have hb : (∏ j ∈ B,p j) ∣ T := by
    apply (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv).trans
    refine ⟨m*r*(∏ j ∈ C,p j)*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hc : (∏ j ∈ C,p j) ∣ T := by
    refine ⟨m*b0Label p B v ε₁ ε₂*r*jLabel p B v ε₁ ε₂*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hg' : (∏ j ∈ G,p j) ∣ T := by
    rw [secondMaskQuotient_spec p E G hEG]
    refine ⟨m*b0Label p B v ε₁ ε₂*(∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂*∏ j ∈ V,p j,?_⟩
    dsimp [T,r,e]
    ring
  intro i hi
  apply Ideal.mem_span_singleton.mpr
  change p i ∣ T
  rcases Finset.mem_union.mp (hA hi) with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact (Finset.dvd_prod_of_mem p hi).trans hb
    · exact (Finset.dvd_prod_of_mem p hi).trans hc
  · exact (Finset.dvd_prod_of_mem p hi).trans hg'

theorem actual_second_split_fixed_family
    (F B C D G E V A : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (Ψ : Eis →* ℂ) (m k : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
    let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
    let r := secondMaskQuotient p E G hEG
    let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
    canonicalMarkedSplit p hp hcop hg F V A Ψ
      (m*b0Label p B v ε₁ ε₂*d) r c d e k slots lists a W (primeProductNorm p V*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hp hcop hg F Ψ ((m*b0Label p B v ε₁ ε₂)*r)
          (c*e*∏ i ∈ V,p i) (d*e*k) (slots\J) lists a W X := by
  dsimp only
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) D
  let e := primeSubsetGenerator (fun i => Ideal.span {p i}) E
  let r := secondMaskQuotient p E G hEG
  let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
  have hd := actual_first_divisor_dvd_child p B C D V hCB hD v ε₁ ε₂ hv m r e
  have hk := actual_second_extracted_support_killed p B C G E V A hEG hA v ε₁ ε₂ hv m
  have hm : (m*b0Label p B v ε₁ ε₂*d)*r = ((m*b0Label p B v ε₁ ε₂)*r)*d := by ring
  have hX : primeProductNorm p V*X/primeProductNorm p V = X := by
    field_simp [(primeProductNorm_pos p hp V).ne']
  unfold canonicalMarkedSplit
  rw [show m*b0Label p B v ε₁ ε₂*primeSubsetGenerator (fun i => Ideal.span {p i}) D *
      secondMaskQuotient p E G hEG = ((m*b0Label p B v ε₁ ε₂)*r)*d from hm]
  rw [hX]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_drop_puncture p hp hcop hg F Ψ _ d _ _ hd]
  rw [finiteCanonicalMarkedRow_restore_lists p hp hcop hg F A Ψ _ _ _ (slots\J) lists a W X hk]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0569

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondVaryingDensity
Source SHA256: d909a354f2c4215230c42cf49ff81de5efb69dc9ca6a6032f5187fe3a955d140
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0570



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory FourierBridge JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actualSecondVaryingFreshRows_integral_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (he : ∀ j ∈ secondProfileIndices source F x,
      secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  have hindexed : (∑ j∈source,w j*actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ∑ j∈secondProfileIndices source F x,
        (w j.1*secondActualCoefficient p hp hcop hg (x j.1) slots₁ slots₂
          (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2)*
        secondNormProfile (fun z=>star (W₁ (z/(G₀*V₀*X₀))))
          (fun z=>W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _=>1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
    simp_rw [actualSecondProfileRow_eq_whole]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hindexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [he j hj]
  ring

theorem actualSecondVaryingFreshRows_normalized_density {κ : Type*}
    (source : Finset κ) (F : Finset ι) (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y G₀ E₀ V₀ K₀ X₀ : ℝ)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density) (normalization : ℂ)
    (he : ∀ j ∈ secondProfileIndices source F x,
      normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
        (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y (secondActualNorms p (x j.1) j.2.1 j.2.2) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ *
        (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀)) *
        ∫ v : Frequency × (Fin 6 → ℝ), density v *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2) :
    normalization * (∑ j ∈ source, w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ((E₀*V₀*X₀ : ℝ):ℂ)⁻¹ * ∫ v : Frequency × (Fin 6 → ℝ),
        density v *
          ∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
            slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v := by
  have hindexed : (∑ j∈source,w j*actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
      ∑ j∈secondProfileIndices source F x,
        (w j.1*secondActualCoefficient p hp hcop hg (x j.1) slots₁ slots₂
          (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2)*
        secondNormProfile (fun z=>star (W₁ (z/(G₀*V₀*X₀))))
          (fun z=>W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _=>1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2) := by
    simp_rw [actualSecondProfileRow_eq_whole]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  rw [hindexed]
  have hc (v : Frequency × (Fin 6 → ℝ)) :
      (∑ j ∈ source, w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ v) =
      ∑ j ∈ secondProfileIndices source F x,
        ((w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
          slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
          (star (ω₁ (primeProductNorm p j.2.1/X₀)) * ω₂ (primeProductNorm p j.2.2/X₀))) *
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope
            (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀) v.1 v.2 := by
    simp_rw [← actual_second_full_mode_columns]
    simp only [secondProfileIndices,Finset.sum_sigma,Finset.sum_product,Finset.mul_sum,mul_assoc]
  simp_rw [hc]
  rw [← density_finite_sum _ density hDensity]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    _ = (w j.1 * secondActualCoefficient p hp hcop hg (x j.1)
        slots₁ slots₂ (lists₁ j.1) (lists₂ j.1) a₁ a₂ j.2.1 j.2.2) *
        (normalization * secondNormProfile (fun z => star (W₁ (z/(G₀*V₀*X₀))))
          (fun z => W₂ (z/(G₀*V₀*X₀))) Φ (fun _ _ => 1) Y
          (secondActualNorms p (x j.1) j.2.1 j.2.2)) := by ring
    _ = _ := by rw [he j hj]; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0570

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondWeights
Source SHA256: a2ec9883783ff00a8fe7d0cf1a4c3c7ab0c73439526bad747dd6813298fad228
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0571


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondSignedSourceWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    (UniqueFactorizationMonoid.moebius (∏ i ∈ x.divisor, Ideal.span {p i}) : ℂ) *
    secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap

theorem expansionProfileWeight_eq_signed (Ψ : Eis →* ℂ) (m c d : Eis)
    (z : SecondRayIndex) (Y : ℝ) (x : SecondExpansionData ι) :
    expansionProfileWeight p hp hcop hg Ψ m c d z Y x =
      (Y : ℂ)*secondRayCoefficient z*secondSignedSourceWeight p hp hcop hg Ψ m c d z x := by
  simp only [expansionProfileWeight,secondSignedSourceWeight,secondTotalWeight]
  ring

theorem secondSignedSourceWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) :
    ‖secondSignedSourceWeight p hp hcop hg Ψ m c d z x‖ ≤ 1 := by
  have hinput : ‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖^2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ (norm_nonneg _)
      ((secondInputCoefficient_norm_le p hg Ψ m c d x.sourceCommon).trans (hΨ _)) 2
  have hμ := QuadraticInitialBound.norm_ideal_moebius_le_one
    (∏ i ∈ x.divisor,Ideal.span {p i})
  have hcommon := secondCommonWeight_norm_le p hp hcop hg hinj hc
    (secondRayMinus Ψ z) (secondRayPlus Ψ z) m (secondExpansionQuotient p x) c d
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor) x.frequency (-x.frequency) x.overlap
  have hc1 : ‖secondCommonWeight p hp hcop hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d (primeSubsetGenerator (fun i => Ideal.span {p i}) x.divisor)
      x.frequency (-x.frequency) x.overlap‖ ≤ 1 := by
    apply hcommon.trans
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((secondRayMinus_norm_le Ψ z _).trans (hΨ _))).trans
      ((secondRayPlus_norm_le Ψ z _).trans (hΨ _))
  simp only [secondSignedSourceWeight,norm_mul,Complex.norm_real,Real.norm_eq_abs]
  rw [abs_of_nonneg (sq_nonneg (‖secondInputCoefficient p hg Ψ m c d (fun _ => 1) x.sourceCommon‖))]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    ((mul_le_of_le_one_left (norm_nonneg _) hinput).trans hμ)).trans hc1

theorem secondExpansionSource_signed_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x ∈ source, secondSignedSourceWeight p hp hcop hg Ψ m c d z x *
        actualSecondProfileRow p hp hcop hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [secondExpansionSource_marked_profile p hp hcop hg hinj hpr (hE := hE)]
  simp only [expansionProfileWeight_eq_signed,Finset.mul_sum,mul_assoc]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0571

/-! Original module: OAI.NumberTheory.DirichletL.Descent.TripleMass
Source SHA256: 8341aac4081ab8f0e3db9a735e307d9984a8c41ba7c36e2af510a1494eefd49d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0572


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def tripleDivisorWeight (K : ℕ) (γ : OuterTriple) : ℝ :=
  ((idealDivisors γ.q0).card : ℝ)^(5+2*K) *
    ((idealDivisors γ.quotient).card : ℝ)^(2*K) *
    ((idealDivisors γ.residual).card : ℝ)^(2*K)

lemma tripleDivisorWeight_nonneg (K : ℕ) (γ : OuterTriple) :
    0 ≤ tripleDivisorWeight K γ := by unfold tripleDivisorWeight; positivity

theorem ideal_divisor_power_small (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : Ideal Eis, I ≠ 0 →
      ((idealDivisors I).card : ℝ)^j ≤ C*(Ideal.absNorm I : ℝ)^ε := by
  have hj : 0 < (j+1 : ℝ) := by positivity
  obtain ⟨C,hC,hb⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/(j+1)) (div_pos hε hj)
  refine ⟨C^(j+1), by positivity, ?_⟩
  intro I hI
  have hcard : (1 : ℝ) ≤ (idealDivisors I).card := by
    exact_mod_cast InverseInitialFibers.divisor_card_pos I hI
  calc
    _ ≤ ((idealDivisors I).card : ℝ)^(j+1) := pow_le_pow_right₀ hcard (by omega)
    _ ≤ (C*(Ideal.absNorm I : ℝ)^(ε/(j+1)))^(j+1) :=
      pow_le_pow_left₀ (by positivity) (hb I hI) _
    _ = C^(j+1)*(Ideal.absNorm I : ℝ)^ε := by
      rw [mul_pow]
      congr 1
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1
      push_cast
      field_simp

theorem tripleDivisorWeight_small (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ γ : OuterTriple,
      γ.q0 ≠ 0 → γ.quotient ≠ 0 → γ.residual ≠ 0 →
      tripleDivisorWeight K γ ≤
        C*((Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient*Ideal.absNorm γ.residual)^ε := by
  obtain ⟨Cq,hCq,hq⟩ := ideal_divisor_power_small (5+2*K) ε hε
  obtain ⟨Ct,hCt,ht⟩ := ideal_divisor_power_small (2*K) ε hε
  refine ⟨Cq*Ct*Ct, by positivity, ?_⟩
  intro γ hq0 ht0 hr0
  unfold tripleDivisorWeight
  calc
    _ ≤ (Cq*(Ideal.absNorm γ.q0 : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.quotient : ℝ)^ε) *
        (Ct*(Ideal.absNorm γ.residual : ℝ)^ε) := by
      gcongr
      · exact hq γ.q0 hq0
      · exact ht γ.quotient ht0
      · exact ht γ.residual hr0
    _ = _ := by
      rw [Real.mul_rpow (by positivity : 0 ≤ (Ideal.absNorm γ.q0 : ℝ)*Ideal.absNorm γ.quotient)
        (by positivity), Real.mul_rpow (by positivity) (by positivity)]
      ring

theorem outerTriple_card (Γ : Finset OuterTriple) (B T R : ℝ)
    (hB : 1 ≤ B) (hT : 1 ≤ T) (hR : 1 ≤ R)
    (hzero : ∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hnorm : ∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
      (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) :
    (Γ.card : ℝ) ≤ 128^3*B*T*R := by
  let f : OuterTriple → Ideal Eis × Ideal Eis × Ideal Eis := fun γ => (γ.q0,γ.quotient,γ.residual)
  have hf : Function.Injective f := by
    intro γ δ h
    exact OuterTriple.ext (congrArg Prod.fst h)
      (congrArg (fun z => z.2.1) h) (congrArg (fun z => z.2.2) h)
  have hc := DescentFiberCost.fixed_triple_count (Γ.image f) B T R hB hT hR
    (fun x hx => by obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hx; exact hzero γ hγ)
    (fun x hx => by obtain ⟨γ,hγ,rfl⟩ := Finset.mem_image.mp hx; exact hnorm γ hγ)
  simpa only [Finset.card_image_of_injective _ hf] using hc

theorem triple_normalized_mass (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Γ : Finset OuterTriple) (B T R : ℝ),
      1 ≤ B → 1 ≤ T → 1 ≤ R →
      (∀ γ ∈ Γ, γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0) →
      (∀ γ ∈ Γ, (Ideal.absNorm γ.q0 : ℝ) ≤ B ∧
        (Ideal.absNorm γ.quotient : ℝ) ≤ T ∧ (Ideal.absNorm γ.residual : ℝ) ≤ R) →
      (B*T*R)⁻¹ * (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤ C*(B*T*R)^ε := by
  obtain ⟨C,hC,hb⟩ := tripleDivisorWeight_small K ε hε
  refine ⟨128^3*C, by positivity, ?_⟩
  intro Γ B T R hB hT hR hz hn
  have hpos : 0 < B*T*R := by positivity
  have hw : ∀ γ ∈ Γ, tripleDivisorWeight K γ ≤ C*(B*T*R)^ε := by
    intro γ hγ
    obtain ⟨hq,ht,hr⟩ := hz γ hγ
    apply (hb γ hq ht hr).trans
    gcongr
    · exact (hn γ hγ).1
    · exact (hn γ hγ).2.1
    · exact (hn γ hγ).2.2
  have hs : (∑ γ ∈ Γ, tripleDivisorWeight K γ) ≤
      (128^3*B*T*R)*(C*(B*T*R)^ε) := by
    calc
      _ ≤ ∑ _γ ∈ Γ, C*(B*T*R)^ε := Finset.sum_le_sum hw
      _ = (Γ.card : ℝ)*(C*(B*T*R)^ε) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right (outerTriple_card Γ B T R hB hT hR hz hn) (by positivity)
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hpos.le)).trans_eq
  field_simp

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0572

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondCauchy
Source SHA256: 75b77ad9dda6c5186e52d326d3ff7f1af97f1d57858ef745acab14a4936be3c5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0573



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open SevenEighths.InverseSecondFibers IdealMobiusDivisorSum CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

def secondLabelEnergy (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : ℝ :=
  ∑ f ∈ labels, ((idealDivisors f).card : ℝ)^(9+4*K) *
    ∑ k ∈ rows, ‖F (γ,f,k)‖^2

lemma secondLabelEnergy_nonneg (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (F : SecondChild → ℂ) (γ : OuterTriple) : 0 ≤ secondLabelEnergy K labels rows F γ := by
  unfold secondLabelEnergy; positivity

theorem second_weighted_count {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  have hF := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw F
  have hG := second_energy_projection source oldLists newLists keep hvalid labels rows hf houter hchild
    K ho hn (fun x => ‖w x‖) hw G
  apply (DescentWeightedCauchy.weighted_cauchy (originalSource source oldLists newLists keep)
    w (F ∘ secondChild) (G ∘ secondChild)).trans
  exact mul_le_mul (Real.sqrt_le_sqrt hF) (Real.sqrt_le_sqrt hG)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem second_weighted_count_of_child_bound {Jo Jn : ℕ} (source : Finset (SecondTuple Jo Jn))
    (oldLists : Fin Jo → Finset SmoothMobiusCorrection.PrimeIdeal)
    (newLists : Fin Jn → Finset SmoothMobiusCorrection.PrimeIdeal)
    (keep : SecondTuple Jo Jn → Prop)
    (hvalid : ∀ x ∈ originalSource source oldLists newLists keep,
      Valid x (secondChild x).1 (secondChild x).2.1 (secondChild x).2.2)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hf : ∀ f ∈ labels, f ≠ 0)
    (houter : ∀ γ ∈ sourceTriples source oldLists newLists keep,
      γ.q0 ≠ 0 ∧ γ.quotient ≠ 0 ∧ γ.residual ≠ 0)
    (hchild : ∀ x ∈ originalSource source oldLists newLists keep,
      (secondChild x).2.1 ∈ labels ∧ (secondChild x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : SecondTuple Jo Jn → ℂ)
    (hw : ∀ x ∈ originalSource source oldLists newLists keep, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) (E : ℝ) (hE : 0 ≤ E)
    (hF : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows F γ ≤ E)
    (hG : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows G γ ≤ E) :
    ‖∑ x ∈ originalSource source oldLists newLists keep,
      w x * F (secondChild x) * star (G (secondChild x))‖ ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
  have hb (P : SecondChild → ℂ)
      (hP : ∀ γ ∈ sourceTriples source oldLists newLists keep, secondLabelEnergy K labels rows P γ ≤ E) :
      (∑ γ ∈ sourceTriples source oldLists newLists keep,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows P γ) ≤
      E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro γ hγ
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hP γ hγ) (tripleDivisorWeight_nonneg K γ)
  apply (second_weighted_count source oldLists newLists keep hvalid labels rows hf houter hchild K ho hn w hw F G).trans
  calc
    _ ≤ Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) *
      Real.sqrt (E * ∑ γ ∈ sourceTriples source oldLists newLists keep, tripleDivisorWeight K γ) :=
      mul_le_mul (Real.sqrt_le_sqrt (hb F hF)) (Real.sqrt_le_sqrt (hb G hG))
        (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = _ := Real.mul_self_sqrt (mul_nonneg hE (Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ)))

def secondCanonicalPolynomial {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) : ℂ :=
  finiteCanonicalMarkedRow p hp hcop hg pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

theorem secondCanonicalPolynomial_actual_columns {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
    (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i - 1)
    (pool : Finset ι) (Ψ : OuterTriple → Eis →* ℂ) (puncture : OuterTriple → Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg pool Ψ puncture slots lists a W X c =
      ∑ U ∈ pool.powerset,
        columnWeight (CanonicalRowCompletion.rowTwist (Ψ c.1) (puncture c.1)
          (primaryGenerator c.2.1) c.2.2) (Ideal.span {∏ i ∈ U, p i}) *
        (primeMark slots lists a U * W c.1 (FirstPassCubeLabels.primeProductNorm p U / X)) :=
  finiteCanonicalMarkedRow_actual_columns p hp hcop hg hpr pool (Ψ c.1) (puncture c.1)
    (primaryGenerator c.2.1) c.2.2 slots lists a (W c.1) X

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0573

/-! Original module: OAI.NumberTheory.DirichletL.Descent.ActualSecondEnergy
Source SHA256: c92a48e22ecf4f5853f90f36a3167bfe72a2d825d3ba7aa32bdc49678b18aa1f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0574



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers IdealMobiusDivisorSum
open InverseInitialArithmetic (sourceIdeal sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondChild {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) : SecondChild :=
  secondChild (originalSecondTuple p u v (markedSecondOriginal p x))

def actualSecondTriples {Jo Jn : ℕ} (u v : Eisˣ)
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Finset OuterTriple :=
  source.image (fun x => (actualSecondChild p u v x).1)

theorem actualSecondChild_nonzero (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) (ht : x.quotient ≠ 0) :
    (actualSecondChild p u v x).2.1 ≠ 0 ∧
    (actualSecondChild p u v x).1.q0 ≠ 0 ∧
    (actualSecondChild p u v x).1.quotient ≠ 0 ∧
    (actualSecondChild p u v x).1.residual ≠ 0 := by
  have hj : Ideal.span {jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  have hb : Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} ≠ (0 : Ideal Eis) :=
    Ideal.span_singleton_eq_bot.not.mpr (primeProduct_ne_zero p hp _ _)
  change _ ≠ 0 ∧ _ ≠ 0 ∧ x.quotient ≠ 0 ∧ _ ≠ 0
  refine ⟨?_,hb,ht,sourceIdeal_ne_zero p hp _⟩
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hj (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)) (sourceIdeal_ne_zero p hp _)

structure ActualSecondSourceConditions {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn)) : Prop where
  admissible : ∀ x ∈ source, x.cube.Admissible
  common_disjoint : ∀ x ∈ source, Disjoint x.firstCommon x.cube.support
  first_divisor : ∀ x ∈ source, x.firstDivisor ⊆ x.firstCommon∪x.cube.support
  second_divisor : ∀ x ∈ source, x.second.divisor ⊆ x.second.sourceCommon
  old_support : ∀ x ∈ source, ∀ i, (x.oldAssigned i).val ∣
      sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*x.quotient
  new_support : ∀ x ∈ source, ∀ i, x.newAssigned i ∈ x.second.sourceCommon∪x.second.overlap
  quotient_nonzero : ∀ x ∈ source, x.quotient ≠ 0

theorem actual_second_fiber_weight (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source) (c : SecondChild)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) :
    ∑ x ∈ source with actualSecondChild p u v x = c, w x ≤ secondDivisorWeight K c := by
  by_cases he : (source.filter (fun x => actualSecondChild p u v x = c)).Nonempty
  · obtain ⟨x,hx⟩ := he
    obtain ⟨hx,he⟩ := Finset.mem_filter.mp hx
    obtain ⟨hf,hq,ht,hr⟩ := actualSecondChild_nonzero p hp u v x (hs.quotient_nonzero x hx)
    rw [he] at hf hq ht hr
    have hcard := actual_marked_second_source_fiber p hp hpr hcop hinj u v source
      hs.admissible hs.common_disjoint hs.first_divisor hs.second_divisor hs.old_support hs.new_support
      c.1 c.2.1 c.2.2 hf hq ht hr K ho hn
    calc
      _ ≤ ∑ _x ∈ source with actualSecondChild p u v _x = c, (1 : ℝ) :=
        Finset.sum_le_sum (fun x hx => hw x (Finset.mem_filter.mp hx).1)
      _ = ((source.filter (fun x => actualSecondChild p u v x = c)).card : ℝ) := by simp
      _ ≤ _ := by
        dsimp only [secondDivisorWeight,actualSecondChild]
        exact_mod_cast hcard
  · rw [Finset.not_nonempty_iff_eq_empty.mp he]
    simp only [Finset.sum_empty]
    unfold secondDivisorWeight
    positivity

theorem actual_second_energy_projection (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℝ) (hw : ∀ x ∈ source, w x ≤ 1) (F : SecondChild → ℂ) :
    ∑ x ∈ source, w x * ‖F (actualSecondChild p u v x)‖^2 ≤
      ∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ := by
  have hm : ∀ x ∈ source, actualSecondChild p u v x ∈
      actualSecondTriples p u v source ×ˢ (labels ×ˢ rows) := by
    intro x hx
    exact Finset.mem_product.mpr ⟨Finset.mem_image.mpr ⟨x,hx,rfl⟩,Finset.mem_product.mpr (hchild x hx)⟩
  have hb := fiber_energy_bound source (actualSecondTriples p u v source ×ˢ (labels ×ˢ rows))
    (actualSecondChild p u v) w (secondDivisorWeight K) (fun c => ‖F c‖^2) hm
    (fun _ _ => sq_nonneg _) (fun c _ => actual_second_fiber_weight p hp hpr hcop hinj u v source hs c K ho hn w hw)
  apply hb.trans_eq
  simp only [Finset.sum_product,secondDivisorWeight,tripleDivisorWeight,secondLabelEnergy,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro γ hγ
  apply Finset.sum_congr rfl
  intro f hf
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem actual_second_weighted_count (hp : ∀ i, p i ≠ 0)
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn))
    (hs : ActualSecondSourceConditions p source)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hn : Jn ≤ 2*K)
    (w : MarkedSecondSource ι Jo Jn → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x * F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v source,
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  apply (DescentWeightedCauchy.weighted_cauchy source w (F ∘ actualSecondChild p u v)
    (G ∘ actualSecondChild p u v)).trans
  exact mul_le_mul
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw F))
    (Real.sqrt_le_sqrt (actual_second_energy_projection p hp hpr hcop hinj u v source hs labels rows hchild K ho hn (fun x => ‖w x‖) hw G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0574

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondCanonicalChild
Source SHA256: aef441f5a193227b8368b50350fcad1d5c31448c868dd2a9b5c886ef209c120b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0575



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem primaryGenerator_primeProduct
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1) (S : Finset ι) (v : ι → ℕ) :
    primaryGenerator (Ideal.span {primeProduct p S v}) = primeProduct p S v := by
  apply primaryGenerator_span _ (primeProduct_ne_zero p hp S v)
  unfold primeProduct
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have hpow : ConcretePrimeRowBridge.goodLambda^2 ∣ p i^v i-1 := by
      simpa only [one_pow] using (hpr i).trans (sub_dvd_pow_sub_pow (p i) 1 (v i))
    have he : p i^v i*(∏ j ∈ S,p j^v j)-1 =
        (p i^v i-1)*(∏ j ∈ S,p j^v j)+((∏ j ∈ S,p j^v j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hpow _) ih

def actualSecondPuncture (m : Eis) (γ : OuterTriple) : Eis :=
  (m*primaryGenerator γ.q0)*primaryGenerator γ.residual

def actualSecondRawLabel {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  ((∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * ∏ i ∈ x.second.overlap,p i

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_mask_span (F : Finset ι) (Ψ : Eis →* ℂ)
    (m₁ m₂ f k : Eis) (he : Ideal.span {m₁}=Ideal.span {m₂})
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hp hcop hg F Ψ m₁ f k slots lists a W X =
      finiteCanonicalMarkedRow p hp hcop hg F Ψ m₂ f k slots lists a W X :=
  fixedChildRow_congr_mask_span p hp hcop hg F Ψ he _ f k

theorem actual_second_puncture_span
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) :
    Ideal.span {((m*b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
      secondExpansionQuotient p x.second)} =
    Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} := by
  change Ideal.span {(m*b0Label p _ _ _ _)*secondExpansionQuotient p x.second} =
    Ideal.span {(m*primaryGenerator (Ideal.span {b0Label p _ _ _ _}))*
      primaryGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor))}
  rw [show primaryGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr,secondExpansionQuotient_of_subset p x.second hE]
  simp only [←Ideal.span_singleton_mul_span_singleton,secondMaskQuotient_span,
    FiniteGaussPhase.span_finset_prod]

theorem actual_second_generator_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    ∃ u v : Eisˣ,
      actualSecondRawLabel p x = (u:Eis)*primaryGenerator (actualSecondChild p u v x).2.1 ∧
      primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor =
        (v:Eis)*(primaryGenerator (sourceIdeal p x.firstDivisor)*primaryGenerator (sourceIdeal p x.second.divisor)) := by
  let L := (markedSecondOriginal p x).J * sourceIdeal p x.firstCommon *
    sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap
  have hs (S : Finset ι) : Ideal.span {primeSubsetGenerator (fun i => Ideal.span {p i}) S} = sourceIdeal p S := by
    simp only [primeSubsetGenerator,ConcretePrimeRowBridge.span_idealGenerator,sourceIdeal]
    exact (FiniteGaussPhase.span_finset_prod S p).symm
  have hl : Ideal.span {actualSecondRawLabel p x} = L := by
    unfold actualSecondRawLabel L
    simp only [←Ideal.span_singleton_mul_span_singleton,hs,sourceIdeal,markedSecondOriginal,cubeSecondSource]
    ring
  have hgp (S : Finset ι) : primaryGenerator (sourceIdeal p S) ≠ 0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hL : primaryGenerator L ≠ 0 := by
    dsimp only [L]
    rw [primaryGenerator_mul,primaryGenerator_mul,primaryGenerator_mul]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (hgp _)) (hgp _)) (hgp _)
    change primaryGenerator (Ideal.span {jLabel p _ _ _ _}) ≠ 0
    rw [show primaryGenerator (Ideal.span {jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryGenerator_primeProduct p hp hpr _ _]
    exact primeProduct_ne_zero p hp _ _
  obtain ⟨u,v,hu,hv⟩ := exists_second_generator_sectors (actualSecondRawLabel p x)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor)
    (primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor)
    L (sourceIdeal p x.firstDivisor) (sourceIdeal p x.second.divisor)
    hl (hs _) (hs _) hL (hgp _) (hgp _)
  exact ⟨u,v,hu,hv⟩

theorem actual_second_canonical_child
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
    finiteCanonicalMarkedRow p hp hcop hg F Ψ
      ((m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)*secondExpansionQuotient p x.second)
      (actualSecondRawLabel p x)
      (primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor *
        primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor * k)
      slots lists a W X =
    secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
      slots lists a (fun _ => W) X
      (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hu,hv⟩ := actual_second_generator_sectors p hp hpr x
  refine ⟨u,v,?_⟩
  intro F Ψ m k slots lists a W X
  rw [secondCanonical_generator_transport p hp hcop hg F Ψ _ _ _ _ _ _ _ _ u v hu hv]
  exact finiteCanonicalMarkedRow_mask_span p hp hcop hg F Ψ _ _ _ _
    (actual_second_puncture_span p hp hpr x hE u v m) slots lists a W X

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0575

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondCanonicalSplit
Source SHA256: 13b7be853fc428ca8a2c6b921794ca60eefbc2e28ebe14740d0fbbe0976ef678
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0576



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def actualMarkedSecondProfileData {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) (A₁ A₂ : Finset ι) : SecondProfileData ι :=
  let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  expansionProfileData p Ψ (m*b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit*d)
    c d z A₁ A₂ x.second

theorem actual_second_split_child_uniform
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (A : Finset ι), A ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon →
      ∀ (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
      let d := primeSubsetGenerator (fun i => Ideal.span {p i}) x.firstDivisor
      let e := primeSubsetGenerator (fun i => Ideal.span {p i}) x.second.divisor
      let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
      canonicalMarkedSplit p hp hcop hg F x.second.overlap A Ψ
        (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit*d)
        (secondExpansionQuotient p x.second) c d e k slots lists a W
        (primeProductNorm p x.second.overlap*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪x.second.overlap) *
        secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
          (slots\J) lists a (fun _ => W) X
          (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hchild⟩ := actual_second_canonical_child p hp hcop hg hpr (σ:=σ) x hE
  refine ⟨u,v,?_⟩
  intro F Ψ m k A hA slots lists a W X
  dsimp only
  rw [secondExpansionQuotient_of_subset p x.second hE]
  rw [actual_second_split_fixed_family p hp hcop hg F x.cube.support x.firstCommon
    x.firstDivisor x.second.sourceCommon x.second.divisor x.second.overlap A hCB hD hE hA
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    x.cube.support_pos Ψ m k slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simpa only [actualSecondRawLabel,secondExpansionQuotient_of_subset p x.second hE] using
    hchild F Ψ m k (slots\J) lists a W X

theorem actual_second_separated_pair_canonical
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hp hcop hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}}) := by
  obtain ⟨u,v,hsplit⟩ := actual_second_split_child_uniform p hp hcop hg hpr (σ:=σ) x hCB hD hE
  refine ⟨u,v,?_⟩
  intro F Ψ m z A₁ A₂ hA₁ hA₂ slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t
  dsimp only
  have hA (A : Finset ι) (ha : A ⊆ x.cube.support∪x.firstCommon) :
      A∪x.second.sourceCommon ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon :=
    Finset.union_subset_union_left ha
  unfold secondSeparatedPair
  dsimp only [actualMarkedSecondProfileData,expansionProfileData]
  rw [hsplit F (secondRayMinus Ψ z) m x.second.frequency _ (hA A₁ hA₁),
    hsplit F (secondRayPlus Ψ z) m (-x.second.frequency) _ (hA A₂ hA₂)]
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0576

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondAssignedSource
Source SHA256: 09cec3e1140f28a20eea36d71470c8278ca4c45852e0f674b7df2263d55682fe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0577



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def pairedSlotAssignment (J₁ J₂ : Finset σ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : Fin (J₁.card+J₂.card) → ι :=
  Fin.addCases (indexedSlotAssignment J₁ q.1) (indexedSlotAssignment J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem pairedSlotAssignment_injective (J₁ J₂ : Finset σ) :
    Function.Injective (pairedSlotAssignment (ι:=ι) J₁ J₂) := by
  intro q r h
  apply Prod.ext
  · apply indexedSlotAssignment_injective J₁
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_left] using congrFun h (Fin.castAdd J₂.card j)
  · apply indexedSlotAssignment_injective J₂
    funext j
    simpa only [pairedSlotAssignment,Fin.addCases_right] using congrFun h (Fin.natAdd J₁.card j)

def pairedSlotWeight (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁ q.1)*slotAssignmentWeight J₂ a₂ q.2

theorem paired_primeMark_assignments (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι) :
    star (primeMark J₁ L₁ a₁ A)*primeMark J₂ L₂ a₂ A =
      ∑ q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)),
        pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  rw [primeMark_supported_assignments,primeMark_supported_assignments]
  simp only [star_sum,Finset.sum_product,pairedSlotWeight,Finset.sum_mul,Finset.mul_sum]
  exact Finset.sum_comm

theorem pairedSlotWeight_norm_le_one (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ) (A : Finset ι)
    (q : (∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))
    (hq : q ∈ (J₁.pi (fun i => L₁ i∩A)) ×ˢ (J₂.pi (fun i => L₂ i∩A)))
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1) :
    ‖pairedSlotWeight J₁ J₂ a₁ a₂ q‖ ≤ 1 := by
  rw [pairedSlotWeight,norm_mul,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (slotAssignmentWeight_norm_le_one J₁ L₁ a₁ A q.1 (Finset.mem_product.mp hq).1 ha₁)).trans
    (slotAssignmentWeight_norm_le_one J₂ L₂ a₂ A q.2 (Finset.mem_product.mp hq).2 ha₂)

def attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0)
    (newAssigned : Fin Jn → ι) : MarkedSecondSource ι Jo Jn where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := newAssigned

omit [DecidableEq ι] in
theorem attachSecondSlots_injective {Jo Jn : ℕ} :
    Function.Injective (fun q : MarkedSecondSource ι Jo 0 × (Fin Jn → ι) => attachSecondSlots q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · apply MarkedSecondSource.ext
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.cube) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstCommon) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstDivisor) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.second) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.quotient) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.oldAssigned) h
    · funext i; exact Fin.elim0 i
  · exact congrArg MarkedSecondSource.newAssigned h

def attachPairedSlots {Jo : ℕ} (J₁ J₂ : Finset σ)
    (q : MarkedSecondSource ι Jo 0 × ((∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))) :
    MarkedSecondSource ι Jo (J₁.card+J₂.card) :=
  attachSecondSlots q.1 (pairedSlotAssignment J₁ J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPairedSlots_injective {Jo : ℕ} (J₁ J₂ : Finset σ) :
    Function.Injective (attachPairedSlots (ι:=ι) (Jo:=Jo) J₁ J₂) := by
  intro q r h
  have he := @attachSecondSlots_injective ι Jo (J₁.card+J₂.card)
    (q.1,pairedSlotAssignment J₁ J₂ q.2) (r.1,pairedSlotAssignment J₁ J₂ r.2) h
  exact Prod.ext (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.2) he))

def assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    Finset (MarkedSecondSource ι Jo (J₁.card+J₂.card)) :=
  ((source ×ˢ ((J₁.pi (fun i => L₁ i)) ×ˢ (J₂.pi (fun i => L₂ i)))).filter
    (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q.2 j ∈ q.1.second.sourceCommon∪q.1.second.overlap)).image
      (attachPairedSlots J₁ J₂)

theorem mem_assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) :
    x ∈ assignedSecondSource source J₁ J₂ L₁ L₂ ↔
      ∃ y ∈ source, ∃ q₁ ∈ J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap)),
      ∃ q₂ ∈ J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap)),
        attachPairedSlots J₁ J₂ (y,(q₁,q₂)) = x := by
  constructor
  · intro hx
    obtain ⟨⟨y,q₁,q₂⟩,hmem,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hy,hq⟩ := Finset.mem_product.mp hmem
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine ⟨y,hy,q₁,Finset.mem_pi.mpr ?_,q₂,Finset.mem_pi.mpr ?_,rfl⟩
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · rintro ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(y,(q₁,q₂)),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy,Finset.mem_product.mpr ⟨?_,?_⟩⟩,?_⟩,rfl⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q₁ hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q₂ hq₂ k)).2

theorem assignedSecondSource_conditions (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    ActualSecondSourceConditions p (assignedSecondSource source J₁ J₂ L₁ L₂) := by
  have hmem : ∀ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      ∃ y ∈ source, ∃ q, attachPairedSlots J₁ J₂ (y,q)=x ∧
        ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ y.second.sourceCommon∪y.second.overlap := by
    intro x hx
    obtain ⟨⟨y,q⟩,hmem,he⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hmem
    exact ⟨y,(Finset.mem_product.mp hmem).1,q,he,hq⟩
  constructor
  all_goals
    intro x hx
    obtain ⟨y,hy,q,rfl,hq⟩ := hmem x hx
  · exact hs.admissible y hy
  · exact hs.common_disjoint y hy
  · exact hs.first_divisor y hy
  · exact hs.second_divisor y hy
  · exact hs.old_support y hy
  · exact hq
  · exact hs.quotient_nonzero y hy

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0577

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondAssignedSum
Source SHA256: e428fcfa524e1c9926456a5af410f96caebd2671f030a62741313a725a81ccce
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0578


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] [DecidableEq σ] in
lemma indexedSlotAssignment_apply (I : Finset σ) (q : ∀ i ∈ I,ι) (i : σ) (hi : i ∈ I) :
    indexedSlotAssignment I q (I.equivFin ⟨i,hi⟩) = q i hi := by
  exact congrArg (fun j : I => q j.val j.property) ((I.equivFin).symm_apply_apply ⟨i,hi⟩)

def eraseSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : MarkedSecondSource ι Jo 0 where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0) (a : Fin Jn → ι) :
    eraseSecondSlots (attachSecondSlots x a) = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def assignedSecondCoefficient {Jo : ℕ} (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi => x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
