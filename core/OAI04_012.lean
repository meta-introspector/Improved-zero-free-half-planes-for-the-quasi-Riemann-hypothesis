  have hi : (∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
        (w x*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
              ω₁ ω₂ G E V B X t) =
      ∫ t : Frequency × (Fin 6 → ℝ),density t*secondFullModeSum p hp hcop hg source sector pool Ψ m z
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X w t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [secondFullModeSum_physical]
  rw [hi] at he
  have hexp : Real.exp (6*L)*Real.exp (-6*L) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hn := congrArg norm he
  conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  conv_rhs at hn => rw [norm_mul]
  have hn' := congrArg (fun a : ℝ => Real.exp (6*L)*a) hn
  rw [←mul_assoc,hexp,one_mul] at hn'
  rw [←mul_assoc] at hn'
  rw [hn']
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0679

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondPhysicalRecursive
Source SHA256: 0b73dc82ed38c0facb324076610350de80b103f8f7c1cb18ee2ef48956117556
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0680




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondPhysicalRecursiveUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_balanced_physical_recursive
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*(Z^N)^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B Y R L Z N Vlabel εchild
    U density w labels K J A hZ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he (H : ℝ) : Z^(max 0 N+Vlabel)*(A*Z^(max 0 N+Vlabel+εchild)*H) =
      (A*Z^(2*(max 0 N+Vlabel)+εchild))*H := by
    calc
      _ = A*(Z^(max 0 N+Vlabel)*Z^(max 0 N+Vlabel+εchild))*H := by ring
      _ = _ := by rw [←Real.rpow_add hZ]; congr 2; ring_nf
  apply actual_second_balanced_physical_energy p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B (Z^N) Y R L
    U density w labels K J (A*Z^(2*(max 0 N+Vlabel)+εchild))
    hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels
    ho hslots₁ hslots₂ (mul_nonneg hA (Real.rpow_pos_of_pos hZ _).le) hWeighted
  · intro t J₁ hJ₁ γ hγ
    rw [second_left_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      (nonzeroChildFrequencyBall 1 R) γ pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayMinus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hleft t J₁ hJ₁ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)
  · intro t J₂ hJ₂ γ hγ
    rw [second_right_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      R γ pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayPlus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hright t J₂ hJ₂ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0680

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSourceAttachment
Source SHA256: c0332d40eeb79577ed064fbd64a22e25c758b23bf6b8bbf86c6e2a5113d357ea
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0681


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

@[ext] structure SecondParentSource (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotient : Ideal Eis
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

def attachSecondExpansion {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : MarkedSecondSource ι Jo 0 where
  cube := parent.cube
  firstCommon := parent.firstCommon
  firstDivisor := parent.firstDivisor
  second := x
  quotient := parent.quotient
  oldAssigned := parent.oldAssigned
  newAssigned := Fin.elim0

def secondParentOf {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := x.oldAssigned

omit [DecidableEq ι] in
theorem attachSecondExpansion_injective {Jo : ℕ} (parent : SecondParentSource ι Jo) :
    Function.Injective (attachSecondExpansion parent) := by
  intro x y h
  exact congrArg MarkedSecondSource.second h

omit [DecidableEq ι] in
theorem attachSecondExpansion_recover {Jo : ℕ} (x : MarkedSecondSource ι Jo 0) :
    attachSecondExpansion (secondParentOf x) x.second = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def secondSourceParentEquiv {Jo : ℕ} :
    SecondParentSource ι Jo × SecondExpansionData ι ≃ MarkedSecondSource ι Jo 0 where
  toFun x := attachSecondExpansion x.1 x.2
  invFun x := (secondParentOf x,x.second)
  left_inv x := by cases x; rfl
  right_inv := attachSecondExpansion_recover

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondParentLabel {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  (∏ i∈parent.firstCommon,p i)*jLabel p parent.cube.support
    (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit

def secondParentDivisor {Jo : ℕ} (parent : SecondParentSource ι Jo) : Eis :=
  primeSubsetGenerator (fun i => Ideal.span {p i}) parent.firstDivisor

def secondParentPuncture {Jo : ℕ} (m : Eis) (parent : SecondParentSource ι Jo) : Eis :=
  (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*
    b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit*secondParentDivisor p parent

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_source_conditions {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι))
    (ha : parent.cube.Admissible) (hC : Disjoint parent.firstCommon parent.cube.support)
    (hD : parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (source.image (attachSecondExpansion parent)) := by
  constructor
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact ha
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hC
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hD
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hE y hy
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hold
  · intro x hx i
    exact Fin.elim0 i
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    exact hq

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_inherited_profile {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    secondInheritedProfile p (attachSecondExpansion parent x) Ψ m z =
      expansionProfileData p Ψ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) z ∅ ∅ x := rfl

theorem attached_signed_weight {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) :
    actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator (attachSecondExpansion parent x).quotient) z
      (attachSecondExpansion parent x) =
    secondSignedSourceWeight p hp hcop hg Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z x := rfl

theorem secondExpansionSource_attached
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x∈source,x.divisor ⊆ x.sourceCommon)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hp hcop hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) z source
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈source.image (attachSecondExpansion parent),
        actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  have he := secondExpansionSource_signed_profile p hp hcop hg hinj hpr pool Ψ
    (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    z source hE ∅ ∅ slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ X Y
  simp only [Finset.empty_union] at he
  rw [he]
  congr 1
  rw [Finset.sum_image (fun x hx y hy h => attachSecondExpansion_injective parent h)]
  apply Finset.sum_congr rfl
  intro x hx
  rw [attached_inherited_profile,attached_signed_weight]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0681

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondParentAssembly
Source SHA256: 633567a182e5a799883741214eaccf456b4942b20a70f8764ebd64513f8e794b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0682


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

omit [DecidableEq ι] in
@[simp] theorem secondParentOf_attach {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (x : SecondExpansionData ι) : secondParentOf (attachSecondExpansion parent x) = parent := rfl

def attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι)) :
    Finset (MarkedSecondSource ι Jo 0) :=
  parents.biUnion (fun parent => (source parent).image (attachSecondExpansion parent))

omit [DecidableEq ι] in
theorem mem_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (x : MarkedSecondSource ι Jo 0) :
    x∈attachedSecondFamily parents source ↔
      secondParentOf x∈parents ∧ x.second∈source (secondParentOf x) := by
  simp only [attachedSecondFamily,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨parent,hp,y,hy,rfl⟩
    exact ⟨hp,hy⟩
  · rintro ⟨hp,hx⟩
    exact ⟨secondParentOf x,hp,x.second,hx,attachSecondExpansion_recover x⟩

omit [DecidableEq ι] in
theorem sum_attachedSecondFamily {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    {A : Type*} [AddCommMonoid A] (H : MarkedSecondSource ι Jo 0 → A) :
    ∑ x∈attachedSecondFamily parents source,H x =
      ∑ parent∈parents,∑ x∈source parent,H (attachSecondExpansion parent x) := by
  unfold attachedSecondFamily
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro parent hp
    exact Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)
  · intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨z,hz,he⟩ := Finset.mem_image.mp hy
    exact hab (congrArg secondParentOf he).symm

variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem attached_family_conditions {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (ha : ∀ parent∈parents,parent.cube.Admissible)
    (hC : ∀ parent∈parents,Disjoint parent.firstCommon parent.cube.support)
    (hD : ∀ parent∈parents,parent.firstDivisor ⊆ parent.firstCommon∪parent.cube.support)
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (hold : ∀ parent∈parents,∀ i,(parent.oldAssigned i).val ∣
      sourceIdeal p parent.cube.support*sourceIdeal p parent.firstCommon*parent.quotient)
    (hq : ∀ parent∈parents,parent.quotient ≠ 0) :
    ActualSecondSourceConditions p (attachedSecondFamily parents source) := by
  have h (x : MarkedSecondSource ι Jo 0) (hx : x∈attachedSecondFamily parents source) :=
    (mem_attachedSecondFamily parents source x).mp hx
  constructor
  · intro x hx; exact ha (secondParentOf x) (h x hx).1
  · intro x hx; exact hC (secondParentOf x) (h x hx).1
  · intro x hx; exact hD (secondParentOf x) (h x hx).1
  · intro x hx; exact hE (secondParentOf x) (h x hx).1 x.second (h x hx).2
  · intro x hx i; exact hold (secondParentOf x) (h x hx).1 i
  · intro x hx i; exact Fin.elim0 i
  · intro x hx; exact hq (secondParentOf x) (h x hx).1

theorem secondExpansionSource_whole_parent_family
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo → Finset (SecondExpansionData ι))
    (hE : ∀ parent∈parents,∀ x∈source parent,x.divisor ⊆ x.sourceCommon)
    (w : SecondParentSource ι Jo → ℂ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ parent∈parents,w parent*secondExpansionSource p hp hcop hg pool Ψ
      (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
      z (source parent)
      (fun U => primeMark slots₁ lists₁ a₁ U*W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x∈attachedSecondFamily parents source,
        (w (secondParentOf x)*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro parent hparent
  rw [secondExpansionSource_attached p hp hcop hg hinj hpr parent (source parent) (hE parent hparent)]
  rw [Finset.sum_image (fun x hx y hy he => attachSecondExpansion_injective parent he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0682

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondParentInput
Source SHA256: 9baae7763ca3f8e5b865cfbbe1dd43bc4df720e206d501e18c2ca11a3bbae47e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0683



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem secondInputCoefficient_old_divisor_mask (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) :
    secondInputCoefficient p hg Ψ (m*d) c d H S = secondInputCoefficient p hg Ψ m c d H S := by
  rw [secondInputCoefficient_fixed_mask p hg Ψ m d c d H S]
  have hd := row_power_mul_mask_power (fun i => Ideal.span {p i}) hg S d 1 1 (by decide)
  simp only [pow_one] at hd
  unfold secondInputCoefficient
  calc
    _ = Ψ (∏ i∈S,p i)*rowCoprimeMask (fun i => Ideal.span {p i}) S m*
      finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S c^4*
      (finiteSquarefreeRow (fun i => Ideal.span {p i}) hg S d*
        rowCoprimeMask (fun i => Ideal.span {p i}) S d)*H S := by ring
    _ = _ := by rw [hd]

theorem inputConjugateRow_old_divisor_mask (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ (m*d) c d H k = inputConjugateRow p hg F Ψ m c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient_old_divisor_mask]

theorem inputConjugateRow_puncture_span (F : Finset ι) (Ψ : Eis →* ℂ) (m₁ m₂ c d : Eis)
    (hspan : Ideal.span {m₁} = (Ideal.span {m₂} : Ideal Eis)) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ m₁ c d H k = inputConjugateRow p hg F Ψ m₂ c d H k := by
  simp only [inputConjugateRow,FirstCauchyArithmetic.supportConjugateSum,secondInputCoefficient,
    rowCoprimeMask_eq_of_span_eq (fun i => Ideal.span {p i}) _ hspan]

theorem fresh_input_parent_mask {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (F D : Finset ι) (hq : parent.quotient = sourceIdeal p D)
    (Ψ : Eis →* ℂ) (m : Eis) (H : Finset ι → ℂ) (k : Eis) :
    inputConjugateRow p hg F Ψ
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H k := by
  rw [←inputConjugateRow_old_divisor_mask]
  apply inputConjugateRow_puncture_span
  let b := b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit
  let d := secondParentDivisor p parent
  change Ideal.span {((m*b)*(∏ i∈D,p i))*d} =
    (Ideal.span {(m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d} : Ideal Eis)
  rw [show ((m*b)*(∏ i∈D,p i))*d = (m*b*d)*(∏ i∈D,p i) by ring,
    show (m*ConcretePrimeRowBridge.idealGenerator parent.quotient)*b*d =
      (m*b*d)*ConcretePrimeRowBridge.idealGenerator parent.quotient by ring]
  simp only [←Ideal.span_singleton_mul_span_singleton,
    ConcretePrimeRowBridge.span_idealGenerator,hq,sourceIdeal]

theorem first_fresh_parent_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (ω : ℝ → ℂ) (X t Y : ℝ) (hY : 0 < Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := firstCoreTest H (fun u => ω (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m H ω X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding k‖^2/Y)*
    (‖inputConjugateRow p hg F Ψ₀
      ((m*b0Label p parent.cube.support (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
        parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k‖^2 : ℝ)) = _
  simp_rw [fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0683

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondFreshTruncation
Source SHA256: 0feecf6b90f60f837501cefa029a00cc79e04adbea066c59c97ca02a7251e76c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0684



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_fresh_radial_truncated
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
    (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (c d : Eis) (r : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    let Ψ₀ := firstCoreTwist negative χ Ψ r
    let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
    let c₀ := c*jLabel p B v ε₁ ε₂
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m
      (primeMark slots lists coeff) om X c d r t Y =
      truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K +
        secondSourceTail p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K := by
  intro H₀ Ψ₀ m₀ c₀
  rw [firstFreshSecondPoisson_markedRadial p hp hg hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    slots lists coeff hD om a b ha hs X t Y hX hY c d r]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ m₀ c₀ d H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0684

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondCanonicalTail
Source SHA256: 6532c1bd09158372402e88823ae0e15279679b2d58c7f7d955ebbf97b06b9dd1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0685




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

theorem first_fresh_canonical_error (ε : ℝ) (hε : 0<ε) (order : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (Ct Cm : ℝ), 0<Ct ∧ 0<Cm ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι → Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i})≠2)
      (F D Bset : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m : Eis)
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
      (X height Wbound Z M n ell V delta A B j t eta tau : ℝ),
      0<X → 0<Z → 1≤X*Real.exp Wbound → b≤Real.exp Wbound →
      X*Real.exp Wbound≤Z^(n-A-B-t+4*eta) →
      ∀ (c d : Eis), d≠0 → ‖ConcreteTraceCRT.eisEmbedding d‖^2≤Z^(delta+eta) →
      ∀ (r : FirstCoreIndex) (g theta : Finset ι→ℝ),
      (∀ G∈F.powerset,Z^(g G-eta)≤primeProductNorm p G) →
      (∀ G∈F.powerset,∀ E : G.powerset,primeProductNorm p E.val≤Z^(theta E.val+eta)) →
      let Y := Z^(firstPhysicalHeight M n ell V delta B j+12*eta+tau)
      let H := Z^tau
      let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative height) X
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p Bset v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p Bset v ε₁ ε₂
      let K := fun (G E : Finset ι) => childFrequencyBall
        (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        (Z^(childM M ell A t (g G) (theta E) V j eta))
      ‖firstFreshSecondPoisson p hp hg hinj F D Bset v ε₁ ε₂ negative χ Ψ m
          (primeMark slots lists coeff) om X c d r height Y -
        truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K‖ ≤
        (128*(X*Real.exp Wbound))^4 *
          ((Cm*(X*Real.exp Wbound)^ε*SchwartzMap.seminorm ℝ 0 0 om)^2 *
            (Y*(Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)*
              (1+(X*Real.exp Wbound)^3/Y)^2/(1+H)^order)) := by
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  obtain ⟨Cm,hCm,hmark⟩ := marked_radial_uniform_bound ε hε
  refine ⟨s,Ct,Cm,hCt,hCm,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc F D Bset v ε₁ ε₂ negative χ Ψ hΨ m
    slots lists coeff hslots hcoeff hD om a b ha hs X height Wbound Z M n ell V delta A B j t eta tau
    hX hZ hL hb hLscale c d hd hdN r g theta hgN heN Y H H₀ Ψ₀ m₀ c₀ K
  have hY : 0<Y := Real.rpow_pos_of_pos hZ _
  have hH : 0≤H := (Real.rpow_pos_of_pos hZ _).le
  have hid := first_fresh_radial_truncated p hp hg hinj hc F D Bset v ε₁ ε₂ negative χ Ψ m
    slots lists coeff hD om a b ha hs X height Y hX hY c d r K
  change _ = truncatedSecondSource p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ m₀ c₀ d H₀ rowMajorant Y K at hid
  rw [hid,add_sub_cancel_left]
  have hVsupp := principalWindow_upper om a b ha hs Wbound hb negative height
  have hcoef := hmark p hp hcop slots lists coeff hslots hcoeff ∅
    (principalWindow om a b ha hs negative height) X Wbound hX hVsupp
  simp only [Finset.card_empty,pow_zero,one_mul,principalWindow_seminorm_zero] at hcoef
  apply htail p hp hg hinj hc F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z))
    m₀ c₀ d hd H₀ rowMajorant _ Y H (X*Real.exp Wbound)
    (fun G E=>Z^(childM M ell A t (g G) (theta E) V j eta))
    (by positivity) hY hH hL hcoef
  · exact markedRadial_support p slots lists coeff ∅ _ X Wbound hX hVsupp
  · intro G hG E
    exact second_correlated_radius_childM p hp d G E.val Z M n ell V delta A B j t (g G)
      (theta E.val) eta tau (X*Real.exp Wbound) hZ (zero_le_one.trans hL)
      hdN (heN G hG E) (hgN G hG) hLscale

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0685

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondParentRadial
Source SHA256: abc60e4385e96c6d7c4e4e251ac2e67893cb342ec3d8f6e9c8c9382af8911a72
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0686


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_fresh_parent_radial_truncated
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (K : Finset ι → Finset ι → Finset Eis) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let H₀ := markedRadial p slots lists coeff ∅ (principalWindow om a b ha hs negative t) X
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core t Y =
    truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ H₀
  let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) negative (-t) D
  let m₀ := (m*b0Label p parent.cube.support
    (fun i=>parent.cube.leftExponent i+parent.cube.rightExponent i)
    parent.cube.leftBit parent.cube.rightBit)*∏ i∈D,p i
  have he (k : Eis) : inputConjugateRow p hg F Ψ₀ m₀
      (secondParentLabel p parent) (secondParentDivisor p parent) H k =
    inputConjugateRow p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ k := by
    calc
      _ = inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
          (secondParentDivisor p parent) H₀ k := by
        unfold inputConjugateRow FirstCauchyArithmetic.supportConjugateSum
        apply Finset.sum_congr rfl
        intro U hU
        rw [firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX]
      _ = _ := fresh_input_parent_mask p hg parent F D hq Ψ₀ m H₀ k
  rw [firstFreshSecondPoisson_fixed_pool p hp hg hinj hc (hY:=hY)]
  rw [←inputConjugateRow_smoothed_second_poisson p hg hp hinj hc _ _ _ _ _ _ _ _ hY]
  change (∑' k : Eis,rowMajorant (‖ConcreteTraceCRT.eisEmbedding k‖^2/Y)*
    (‖inputConjugateRow p hg F Ψ₀ m₀ (secondParentLabel p parent)
      (secondParentDivisor p parent) H k‖^2 : ℝ)) = _
  simp_rw [he]
  exact inputConjugateRow_eq_truncated_add_tail p hp hg hinj hc F Ψ₀ (secondParentPuncture p m parent)
    (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y hY K

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0686

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondSourceSize
Source SHA256: 1a741a452fc04c58cb4140233c51086dd7470aebc4613e0e336e3c731f9c61c1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0687



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
noncomputable section
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)

include hp in
theorem first_source_height_bounds (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V delta B j eta tau : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hell : 0≤ell) (hV : 0≤V)
    (hdelta : 0≤delta) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) (htau : 0≤tau)
    (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hc : Z^(B-eta)≤primeProductNorm p C)
    (hd : Z^(delta-eta)≤primeProductNorm p D)
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) :
    -Mmax≤firstPhysicalHeight M r ell V delta B j+12*eta+tau ∧
    firstPhysicalHeight M r ell V delta B j+12*eta+tau≤3*Fmax+16*eta+tau := by
  have hz : 0<Z := zero_lt_one.trans hZ
  have hd' := first_source_divisor_center p hp b C D hCB hD Z r ell delta eta hZ h1 h2 hC hd
  have hb' := (Real.rpow_le_rpow_left_iff hZ).mp (hc.trans hC)
  have hj' := hJ.trans ((cube_label_norm_bounds p hp b.support b.leftExponent b.rightExponent
    b.leftBit b.rightBit b.support_pos (Z^(ell+eta)) (Real.rpow_pos_of_pos hz _).le h1 h2).1)
  rw [←Real.rpow_mul_natCast hz.le] at hj'
  have hj'' := (Real.rpow_le_rpow_left_iff hZ).mp hj'
  norm_num at hj''
  unfold firstPhysicalHeight
  constructor <;> linarith

include hp in

theorem second_source_scalar_caps (b : CubeCoordinates ι) (C D : Finset ι)
    (hCB : Disjoint C b.support)
    (hD : D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M Mmax Fmax r ell V delta B j eta tau A t L : ℝ) (hZ : 1<Z)
    (hM : 0≤M) (hMm : M≤Mmax) (hFm : 0≤Fmax) (hell : 0≤ell) (hV : 0≤V)
    (hdelta : 0≤delta) (hB : 0≤B) (hj : 0≤j) (heta : 0≤eta) (htau : 0≤tau)
    (hA : 0≤A) (ht : 0≤t) (hwhole : r+3*ell+V≤Fmax)
    (h1 : ‖eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤Z^(ell+eta))
    (h2 : ‖eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤Z^(ell+eta))
    (hC : primeProductNorm p C≤Z^(r+eta))
    (hc : Z^(B-eta)≤primeProductNorm p C)
    (hd : Z^(delta-eta)≤primeProductNorm p D)
    (hJ : Z^(j-eta)≤‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2)
    (hL : L≤Z^(r-A-B-t+4*eta)) :
    let Y := Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)
    let cap := Mmax+3*Fmax+16*eta+tau
    Y≤Z^cap ∧ Y⁻¹≤Z^cap ∧ L≤Z^cap := by
  dsimp only
  have hz : 0<Z := zero_lt_one.trans hZ
  obtain ⟨hlo,hhi⟩ := first_source_height_bounds p hp b C D hCB hD
    Z M Mmax Fmax r ell V delta B j eta tau hZ hM hMm hell hV hdelta hB hj heta htau
    hwhole h1 h2 hC hc hd hJ
  refine ⟨Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith),?_,?_⟩
  · rw [←Real.rpow_neg hz.le]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · exact hL.trans (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith))

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0687

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondTailAbsorption
Source SHA256: cc38b688f2bf6578c989b620406856e4e77d8a97a757e376c2cf9b68379a3075
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0688


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section

lemma second_tail_fixed_cap (Y L cap B P H : ℝ) (order : ℕ)
    (hY : 0<Y) (hL : 0≤L) (hc : 1≤cap) (_hB : 0≤B) (hP : 0≤P) (hH : 0≤H)
    (hy : Y≤cap) (hyi : Y⁻¹≤cap) (hl : L≤cap) :
    (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+H)^order))≤
      (4*128^4)*B^2*P*cap^13/(1+H)^order := by
  have hc0 : 0≤cap := zero_le_one.trans hc
  have hscale : 1+L^3/Y≤2*cap^4 := by
    calc
      _ ≤ 1+cap^3*cap := by rw [div_eq_mul_inv]; gcongr
      _ ≤ _ := by have hh : 1≤cap^4 := one_le_pow₀ hc; nlinarith
  calc
    _ = (128*L)^4*B^2*Y*P*(1+L^3/Y)^2/(1+H)^order := by ring
    _ ≤ (128*cap)^4*B^2*cap*P*(2*cap^4)^2/(1+H)^order := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
    _ = _ := by ring

theorem choose_second_tail_order (Lcap tau saving : ℝ) (hL : 0≤Lcap) (htau : 0<tau) :
    ∃ order : ℕ,∀ Z Y L B P : ℝ,1≤Z → 0<Y → 0≤L → 0≤B → 0≤P →
      Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (128*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+Z^tau)^order))≤
        (4*128^4)*B^2*P*Z^(-saving) := by
  obtain ⟨order,ho⟩ := exists_nat_gt ((13*Lcap+saving)/tau)
  refine ⟨order,?_⟩
  intro Z Y L B P hZ hY hL0 hB hP hy hyi hl
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := second_tail_fixed_cap Y L (Z^Lcap) B P (Z^tau) order hY hL0
    (Real.one_le_rpow hZ hL) hB hP (Real.rpow_pos_of_pos hz _).le hy hyi hl
  have hdecay : (Z^Lcap)^13/(1+Z^tau)^order≤Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^13/(Z^tau)^order := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) order)
      _ = Z^(13*Lcap-tau*(order:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp ho
        nlinarith
  apply hb.trans
  calc
    _ = ((4*128^4)*B^2*P)*((Z^Lcap)^13/(1+Z^tau)^order) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0688

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondRapidTail
Source SHA256: 8766a87f6708cc74a8f59cac45b31d6957db79f352a3925be18e931759be4f18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0689


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "O" => ActualEisensteinCubic.O

theorem full_second_rapid_correlated_tail (Lcap tau saving : ℝ)
    (hLcap : 0≤Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀ a,‖Ψ a‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (Hcol : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (Z B Y L : ℝ) (R : Finset ι→Finset ι→ℝ),
      1≤Z → 0≤B → 0<Y → 1≤L → Y≤Z^Lcap → Y⁻¹≤Z^Lcap → L≤Z^Lcap →
      (∀ U,‖Hcol U‖≤B) → (∀ U,Hcol U≠0 → primeProductNorm p U≤L) →
      (∀ G∈F.powerset,∀ E : G.powerset,correlatedSecondRadius p d G E.val L Y (Z^tau)≤R G E.val) →
      ‖secondSourceTail p hp hg hinj F Ψ m c d Hcol W Y
        (fun G E=>childFrequencyBall (d*primeSubsetGenerator (fun i=>Ideal.span {p i}) E) (R G E))‖≤
      C*B^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  obtain ⟨order,horder⟩ := choose_second_tail_order Lcap tau saving hLcap htau
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  refine ⟨s,(4*128^4)*Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W Z B Y L R hZ hB hY hL hy hyi hl hcol hsupp hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have he := htail p hp hg hinj hc F Ψ hΨ m c d hd Hcol W B Y (Z^tau) L R
    hB hY (Real.rpow_pos_of_pos hz _).le hL hcol hsupp hR
  apply he.trans
  have hh := horder Z Y L B (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hY (zero_le_one.trans hL) hB (mul_nonneg hCt.le (apply_nonneg _ _)) hy hyi hl
  convert hh using 1 ; ring

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0689

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondVariableCutoff
Source SHA256: 560ec488ba5a5099764e2ea493fddec51154d0d1f9ba54c5e19dad0379259fb1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0690


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal)
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

def secondVariableCutoff {Jo : ℕ} (parent : SecondParentSource ι Jo) (R : Finset ι → Finset ι → ℝ)
    (G E : Finset ι) : Finset Eis :=
  childFrequencyBall (secondParentDivisor p parent*primeSubsetGenerator (fun i => Ideal.span {p i}) E) (R G E)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_variable_original_support {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool residual : Finset ι) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ)
    (x : SecondExpansionData ι)
    (hx : x∈secondDyadicSector pool (secondVariableCutoff p parent R) residual label j) :
    x.sourceCommon ⊆ pool ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ pool ∧
    x.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p (attachSecondExpansion parent x)) (R x.sourceCommon x.divisor) := by
  obtain ⟨hx,hlabel⟩ := Finset.mem_filter.mp hx
  obtain ⟨hx,hresidual⟩ := Finset.mem_filter.mp hx
  exact (mem_secondExpansionPool _ _ _).mp hx

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem second_variable_attached_rows {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool residual : Finset ι) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) (j : κ)
    (x : MarkedSecondSource ι Jo 0)
    (hx : x∈(secondDyadicSector pool (secondVariableCutoff p parent R) residual label j).image
      (attachSecondExpansion parent)) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R x.second.sourceCommon x.second.divisor) := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  exact (second_variable_original_support p parent pool residual R label j y hy).2.2.2

theorem truncated_second_attached_variable [Fintype κ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι → Finset ι → ℝ)
    (label : Finset ι → SecondExpansionData ι → κ) :
    truncatedSecondSource p hp hg hinj pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) =
    truncatedSecondZero p hg pool Ψ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent)
      (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y
      (secondVariableCutoff p parent R) +
    ∑ z : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient z *
        ∑ x∈(secondDyadicSector pool (secondVariableCutoff p parent R) residual label j).image
          (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x *
            actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
              slots slots lists lists a a W W Φ Y X := by
  rw [truncatedSecondSource_eq_zero_add_dyadic p hp hcop hg hinj hc hpr
    pool Ψ (secondParentPuncture p m parent) (secondParentLabel p parent) (secondParentDivisor p parent)
    (fun U => primeMark slots lists a U*W (primeProductNorm p U/X)) Φ Y (secondVariableCutoff p parent R) label]
  congr 1
  apply Finset.sum_congr rfl
  intro z hz
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  exact secondExpansionSource_attached p hp hcop hg hinj hpr parent _
    (fun x hx => (second_variable_original_support p parent pool residual R label j x hx).2.1)
    pool Ψ m z slots slots lists lists a a W W Φ X Y

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0690

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondCenterSector
Source SHA256: f329e6b15c1d9b0f60d0239168b6867ec4bc0b3a70ed5d4aa451315225b28810
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0691


namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι γ δ κ : Type*} [DecidableEq ι] [DecidableEq γ] [DecidableEq δ] [DecidableEq κ]

def secondCenterLabel (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (residual : Finset ι)
    (x : SecondExpansionData ι) : γ × δ × κ :=
  (gIndex x.sourceCommon,thetaIndex x.divisor,other residual x)

theorem second_center_sector_rows (p : ι→Eis)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (R : γ→δ→ℝ)
    (j : γ × δ × κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈(secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>R (gIndex G) (thetaIndex E))) residual
      (secondCenterLabel gIndex thetaIndex other) j).image (attachSecondExpansion parent)) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R j.1 j.2.1) := by
  obtain ⟨y,hy,rfl⟩ := Finset.mem_image.mp hx
  have hlabel := (Finset.mem_filter.mp hy).2
  have hg : gIndex y.sourceCommon=j.1 := congrArg Prod.fst hlabel
  have ht : thetaIndex y.divisor=j.2.1 := congrArg (fun a : γ×δ×κ=>a.2.1) hlabel
  obtain ⟨hy,_⟩ := Finset.mem_filter.mp hy
  obtain ⟨hy,_⟩ := Finset.mem_filter.mp hy
  have hs := ((mem_secondExpansionPool _ _ _).mp hy).2.2.2
  change y.frequency ∈ nonzeroChildFrequencyBall
    (actualSecondMultiplier p (attachSecondExpansion parent y)) (R (gIndex y.sourceCommon) (thetaIndex y.divisor)) at hs
  change y.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p (attachSecondExpansion parent y)) (R j.1 j.2.1)
  simpa only [hg,ht] using hs

theorem second_center_sector_empty (p : ι→Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (R : γ→δ→ℝ)
    (j : γ × δ × κ) (hR : R j.1 j.2.1<1) :
    secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>R (gIndex G) (thetaIndex E))) residual
      (secondCenterLabel gIndex thetaIndex other) j = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro y hy
  have hs := second_center_sector_rows p parent pool residual gIndex thetaIndex other R j
    (attachSecondExpansion parent y) (Finset.mem_image.mpr ⟨y,hy,rfl⟩)
  have ha : actualSecondMultiplier p (attachSecondExpansion parent y) ≠ 0 :=
    mul_ne_zero (primeSubsetGenerator_ne_zero _ _) (primeSubsetGenerator_ne_zero _ _)
  rw [nonzeroChildFrequencyBall_empty _ ha _ hR] at hs
  exact Finset.notMem_empty _ hs

theorem second_center_sector_nonnegative (p : ι→Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (pool residual : Finset ι)
    (gIndex : Finset ι→γ) (thetaIndex : Finset ι→δ)
    (other : Finset ι→SecondExpansionData ι→κ) (M : γ→δ→ℝ) (Z : ℝ) (hZ : 1<Z)
    (j : γ × δ × κ)
    (hne : (secondDyadicSector pool
      (secondVariableCutoff p parent (fun G E=>Z^(M (gIndex G) (thetaIndex E)))) residual
      (secondCenterLabel gIndex thetaIndex other) j).Nonempty) : 0≤M j.1 j.2.1 := by
  by_contra hn
  have hlt : Z^(M j.1 j.2.1)<1 := Real.rpow_lt_one_of_one_lt_of_neg hZ (lt_of_not_ge hn)
  rw [second_center_sector_empty p parent pool residual gIndex thetaIndex other
    (fun a b=>Z^(M a b)) j hlt] at hne
  exact Finset.not_nonempty_empty hne

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0691

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondFullSource
Source SHA256: 8ffa1cc1ec1a5c7cf31f6f3ffe080a113d700c29290b6c0e9c1dd9f720019821
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0692



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondFibers RayFourExpansion
open InverseInitialArithmetic (sourceIdeal)
open InversePrincipalEnergy InverseSecondPrincipalCaller
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ] [Fintype κ]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem first_parent_full_second_source
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (parent : SecondParentSource ι Jo) (F D : Finset ι)
    (hq : parent.quotient = sourceIdeal p D)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ)
    (hD : ∀ i∈slots,Disjoint (lists i) D)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hs : Function.support om⊆Set.Icc a b)
    (X height Y : ℝ) (hX : 0<X) (hY : 0<Y) (core : FirstCoreIndex)
    (R : Finset ι → Finset ι → ℝ) (label : Finset ι → SecondExpansionData ι → κ) :
    let Ψ₀ := firstCoreTwist negative χ Ψ core
    let V := principalWindow om a b ha hs negative height
    let H₀ := markedRadial p slots lists coeff ∅ V X
    let K := secondVariableCutoff p parent R
    firstFreshSecondPoisson p hp hg hinj F D parent.cube.support
      (fun i => parent.cube.leftExponent i+parent.cube.rightExponent i)
      parent.cube.leftBit parent.cube.rightBit negative χ Ψ m (primeMark slots lists coeff) om X
      (∏ i∈parent.firstCommon,p i) (secondParentDivisor p parent) core height Y =
    truncatedSecondZero p hg F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
    (∑ ray : SecondRayIndex,∑ residual∈F.powerset,∑ j : κ,
      (Y : ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector F K residual label j).image (attachSecondExpansion parent),
          actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
            actualSecondProfileRow p hp hcop hg F (secondInheritedProfile p x Ψ₀ m ray)
              slots slots lists lists coeff coeff V V rowMajorant Y X) +
    secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
      (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K := by
  intro Ψ₀ V H₀ K
  have htest : H₀=(fun U=>primeMark slots lists coeff U*V (primeProductNorm p U/X)) := by
    funext U
    simp only [H₀,markedRadial,Finset.empty_union]
  have hret := truncated_second_attached_variable p hp hcop hg hinj hc hpr parent F Ψ₀ m
    slots lists coeff V rowMajorant X Y R label
  rw [←htest] at hret
  calc
    _ = truncatedSecondSource p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K +
        secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
          (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K :=
      first_fresh_parent_radial_truncated p hp hg hinj hc parent F D hq negative χ Ψ m
        slots lists coeff hD om a b ha hs X height Y hX hY core K
    _ = _ := congrArg (fun v=>v + secondSourceTail p hp hg hinj F Ψ₀ (secondParentPuncture p m parent)
        (secondParentLabel p parent) (secondParentDivisor p parent) H₀ rowMajorant Y K) hret

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0692

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondVariablePrincipal
Source SHA256: e92944d9511da28ae4e461bbf274de523f9fa8683123278a1489fb4c9e90ea5c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0693



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FourierBridge
open SecondPassIntegration CompletedHeight InversePrincipalEnergy RayFourExpansion
open InverseSecondPrincipalCaller
local notation "Eis" => ActualEisensteinCubic.O

theorem first_retained_radius_one {ι : Type*} [DecidableEq ι]
    (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (labels : Finset (Ideal Eis)) (b : CubeCoordinates ι) (Y : ℝ)
    (hlabels : ∀ f∈labels,f≠0) (hne : (firstRetainedSource p labels b Y).Nonempty) : 1≤Y := by
  obtain ⟨x,hx⟩ := hne
  obtain ⟨hf,hk⟩ := (mem_firstRetainedSource p labels b Y x).mp hx
  have hm : firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1≠0 := by
    unfold firstPhysicalMultiplier
    exact mul_ne_zero (pow_ne_zero _ (ConcretePrimeRowBridge.idealGenerator_ne_zero _ (hlabels _ hf)))
      (primeProduct_ne_zero p hp _ _)
  by_contra hy
  rw [nonzeroChildFrequencyBall_empty _ hm Y (lt_of_not_ge hy)] at hk
  exact Finset.notMem_empty _ hk

theorem firstCore_variable_principal_energy (ε : ℝ) (hε : 0<ε) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
      (p : ι→Eis) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (slots : Finset σ) (lists : σ→Finset ι) (coeff : σ→ι→ℂ),
      (slots : Set σ).PairwiseDisjoint lists →
      (∀ i∈slots,∀ k∈lists i,‖coeff i k‖≤1) →
      ∀ (F D B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      (∀ i∈slots,Disjoint (lists i) D) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis→*ℂ),
      (∀ z,‖Ψ z‖≤1) → ∀ (m c d : Eis),d≠0 → ∀ (r : FirstCoreIndex)
      (om W : 𝓢(ℝ,ℂ)) (a b : ℝ) (_ha : 0<a) (_hs : Function.support om⊆Set.Icc a b)
      (M t X Y : ℝ) (R : Finset ι→Finset ι→ℝ),b≤Real.exp M → 0<X → 1≤Y → (∀ G E,0≤R G E) →
      let H := firstCoreTest (primeMark slots lists coeff) (fun u=>om (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D
      let Ψ₀ := firstCoreTwist negative χ Ψ r
      let m₀ := (m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i
      let c₀ := c*jLabel p B v ε₁ ε₂
      ‖truncatedSecondZero p hg F Ψ₀ m₀ c₀ d H W Y (fun G E=>secondPhysicalCutoff p d (R G E) G E)‖ +
      ‖principalRestoration p hg hinj hp F Ψ₀ m₀ c₀ d H W Y (fun G E=>secondPhysicalMask p d (R G E) G E)‖ ≤
      C*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W * (SchwartzMap.seminorm ℝ 0 0 om)^2)*
        Y*(X*Real.exp M)^(1+ε) := by
  obtain ⟨s,C,hC,hbound⟩ := marked_principal_energy ε hε
  refine ⟨s,C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop slots lists coeff hslots hcoeff F D B v ε₁ ε₂ hD
    negative χ Ψ hΨ m c d hd r om W a b ha hs M t X Y R hb hX hY hR H Ψ₀ m₀ c₀
  let V := principalWindow om a b ha hs negative t
  let H₀ := markedRadial p slots lists coeff ∅ V X
  have he (U : Finset ι) : secondInputCoefficient p hg Ψ₀ m₀ c₀ d H U=
      secondInputCoefficient p hg Ψ₀ m₀ c₀ d H₀ U :=
    firstCoreTest_coefficient p hp hg hinj slots lists coeff D U hD om a b ha hs negative X t hX Ψ₀
      (m*b0Label p B v ε₁ ε₂) c₀ d
  rw [zero_congr_input p hg F Ψ₀ m₀ c₀ d H H₀ he,
    restoration_congr_input p hp hg hinj F Ψ₀ m₀ c₀ d H H₀ he]
  have hz : ∀ G∈F.powerset,∀ E∈G.powerset,(0:Eis)∈secondPhysicalCutoff p d (R G E) G E := by
    intro G hG E hE
    exact zero_mem_childFrequencyBall _ (mul_ne_zero hd (primeSubsetGenerator_ne_zero _ _)) _ (hR G E)
  have hbnd := hbound p hp hg hinj hcop slots lists coeff hslots hcoeff ∅ F Ψ₀
    (fun z=>(firstCoreTwist_norm_le negative χ Ψ r z).trans (hΨ z)) m₀ c₀ d V W X M Y
    hX hY (principalWindow_upper om a b ha hs M hb negative t)
    (fun G E=>secondPhysicalCutoff p d (R G E) G E) hz
    (fun G E=>secondPhysicalMask p d (R G E) G E)
    (fun G _ E k=>secondPhysicalMask_norm_le_one p d (R G E.val) G E.val k.val)
  simpa only [H₀,V,Finset.card_empty,pow_zero,mul_one,principalWindow_seminorm_zero] using hbnd

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0693

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondVaryingBalanced
Source SHA256: 2c794279b9de6494baba2089f8af880e7d0fdf75a0a35501f17cb3ec9522830f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0694



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O

variable {κ ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_varying_balanced_source (source : Finset κ) (F : Finset ι)
    (x : κ → SecondProfileData ι) (w : κ → ℂ)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : κ → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (V : Fin 6 → ℝ → ℂ)
    (G₀ E₀ V₀ K₀ X₀ Y L : ℝ)
    (hG : 0 < G₀) (hE : 0 < E₀) (hV : 0 < V₀) (hK : 0 < K₀) (hX : 0 < X₀)
    (density : Frequency × (Fin 6 → ℝ) → ℂ) (hDensity : Integrable density)
    (hsep : ∀ y : Fin 6 → ℝ,
      (Real.exp (-6*L):ℂ) * secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ V
        (Y*K₀/(E₀*V₀^2*X₀^2)) y =
      ∫ t : Frequency × (Fin 6 → ℝ), density t *
        pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2)
    (hn : ∀ j ∈ source,(x j).divisor ≠ 0 ∧ (x j).frequency ≠ 0)
    (hω₁ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₁ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₁ (primeProductNorm p N/X₀) = 1)
    (hω₂ : ∀ j ∈ source, ∀ N ∈ (F\(x j).overlap).powerset,
      W₂ (primeProductNorm p (x j).common*primeProductNorm p (x j).overlap*primeProductNorm p N/(G₀*V₀*X₀)) ≠ 0 →
        ω₂ (primeProductNorm p N/X₀) = 1)
    (hcut : ∀ j ∈ secondProfileIndices source F x,
      ω₁ (primeProductNorm p j.2.1/X₀) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1) :
    (Real.exp (-6*L):ℂ) * (∑ j ∈ source,w j * actualSecondProfileRow p hp hcop hg F (x j)
      slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ W₁ W₂ Φ Y (G₀*V₀*X₀)) =
    ((E₀*V₀*X₀:ℝ):ℂ)⁻¹ * ∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ j ∈ source,w j * secondSeparatedPair p hp hcop hg F (x j)
        slots₁ slots₂ (lists₁ j) (lists₂ j) a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t := by
  apply actualSecondVaryingFreshRows_normalized_density p hp hcop hg source F x w
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ Y G₀ E₀ V₀ K₀ X₀ density hDensity
  intro j hj
  obtain ⟨hjS,hN,hM⟩ := (mem_secondProfileIndices source F x j).mp hj
  have h1 : star (W₁ (primeProductNorm p (x j.1).common*primeProductNorm p (x j.1).overlap*
      primeProductNorm p j.2.1/(G₀*V₀*X₀))) ≠ 0 → star (ω₁ (primeProductNorm p j.2.1/X₀)) = 1 := by
    intro hh
    rw [hω₁ j.1 hjS j.2.1 hN (star_ne_zero.mp hh),star_one]
  have h2 := hω₂ j.1 hjS j.2.2 hM
  have h3 : star (ω₁ (primeProductNorm p j.2.1/X₀)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X₀) ≠ 0 → ∀ i,
      V i (secondRelativeLog (secondActualNorms p (x j.1) j.2.1 j.2.2) G₀ E₀ V₀ K₀ X₀ i) = 1 :=
    fun ha hb => hcut j hj (star_ne_zero.mp ha) hb
  have he := InverseSecondProfileUniform.fresh_physical_profile
    (fun x => star (W₁ x)) W₂ Φ V G₀ E₀ V₀ K₀ X₀ Y L hG hE hV hK hX
    (fun x => star (ω₁ x)) ω₂ (secondActualNorms p (x j.1) j.2.1 j.2.2)
    (secondActualNorms_pos p hp (x j.1) (hn j.1 hjS).1 (hn j.1 hjS).2 j.2.1 j.2.2)
    (by simpa [secondActualNorms] using h1)
    (by simpa [secondActualNorms] using h2)
    (by simpa [secondActualNorms] using h3)
  rw [hsep] at he
  simpa [secondActualNorms] using he

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0694

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondVaryingPhysical
Source SHA256: 1a672158a901b79e4f0251ef411336c2730c220daa147c0a0d65d4c3cd975771
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0695



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondVaryingPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
universe u₁ u₂
variable {ι : Type u₁} {σ : Type u₂} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_varying_modes_common_sectors
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : MarkedSecondSource ι Jo 0 → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ))
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      (∑ x ∈ source,w x * secondSeparatedPair p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ ω₁ ω₂ G E V B X t) =
      ∑ uv : Eisˣ × Eisˣ, ∑ x ∈ secondSourceSector source sector uv, w x *
        ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (lists₁ x) (lists₂ x) a₁ a₂
            ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := exists_second_uniform_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t w
  rw [secondSourceSector_partition source sector]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx,hxs⟩ := Finset.mem_filter.mp hx
  congr 1
  have hh := hsector x hx
  rw [hxs] at hh
  exact second_inherited_mode_canonical p hp hcop hg x uv.1 uv.2 hh
    pool Ψ m z slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ ω₁ ω₂ G E V B X t

theorem actual_second_varying_balanced_profile_children
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : MarkedSecondSource ι Jo 0 → σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (Real.exp (-6*L):ℂ) * ((Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X))) =
      ((Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹) *
        ∫ t : Frequency × (Fin 6 → ℝ),density t *
          ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,
            (w x*actualSecondSignedWeight p hp hcop hg Ψ
              (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
            ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
              secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (lists₁ x) (lists₂ x) a₁ a₂
                ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := actual_second_varying_modes_common_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hn : ∀ x ∈ source,(secondInheritedProfile p x Ψ m z).divisor ≠ 0 ∧
      (secondInheritedProfile p x Ψ m z).frequency ≠ 0 := by
    intro x hx
    refine ⟨primeSubsetGenerator_ne_zero _ _,?_⟩
    have hh := (mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p x) R _).mp (hrows x hx)
    intro he
    change x.second.frequency = 0 at he
    simp only [he,mul_zero,map_zero,norm_zero,zero_pow (by omega : 2 ≠ 0),lt_self_iff_false] at hh
    exact hh.1
  have he := actual_second_varying_balanced_source p hp hcop hg source pool
    (fun x : MarkedSecondSource ι Jo 0 => secondInheritedProfile p x Ψ m z)
    (fun x : MarkedSecondSource ι Jo 0 => w x*actualSecondSignedWeight p hp hcop hg Ψ
      (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ ω₁ ω₂ Φ U G E V B X Y L
    hG hE hV hB hX density hDensity hsep hn hω₁ hω₂ hcut
  calc
    _ = ((Y:ℂ)*secondRayCoefficient z) * ((Real.exp (-6*L):ℂ)*
        ∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (lists₁ x) (lists₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X)) := by ring
    _ = _ := by
      rw [he]
      rw [←mul_assoc]
      apply congrArg (fun a : ℂ => ((Y:ℂ)*secondRayCoefficient z*((E*V*X:ℝ):ℂ)⁻¹)*a)
      apply integral_congr_ae
      filter_upwards with t
      apply congrArg (fun a : ℂ => density t*a)
      exact hsector pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t _

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0695

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedPhysicalEnergy
Source SHA256: 73f5d26107b7f6505a6f059abdbf2a0648d76954a4a4d0652b982da2caf7a370
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0696




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedPhysicalEnergyUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_physical_energy
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B X Y R L : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      0 < G → 0 < E → 0 < V → 0 < B → 0 < X → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*X^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₁ (primeProductNorm p N/X) = 1) →
      (∀ x ∈ source,∀ N ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p N/(G*V*X)) ≠ 0 → ω₂ (primeProductNorm p N/X) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/X) ≠ 0 → ω₂ (primeProductNorm p j.2.2/X) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B X i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ ≤
          A*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*X))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*X : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*A*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  obtain ⟨sector,hsector⟩ := actual_second_varying_balanced_profile_children p hp hcop hg hpr (σ:=σ) source hs
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w labels K J A hd₁ hd₂ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he := hsector pool Ψ m z slots₁ slots₂ (fun x i=>lists₁ i\deleted₁ x) (fun x i=>lists₂ i\deleted₂ x) a₁ a₂ W₁ W₂ ω₁ ω₂ Φ G E V B X Y R L
    U density w hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
  have hb := actual_second_deleted_all_modes_integral p hp hcop hg hpr hinj hc source hs sector pool Ψ hΨ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ hd₁ hd₂ ha₁ ha₂ ω₁ ω₂ G E V B X R labels hlabels hrows
    K ho hslots₁ hslots₂ w hw A hA J density hWeighted hleft hright
  have hi : (∫ t : Frequency × (Fin 6 → ℝ),density t *
      ∑ uv : Eisˣ × Eisˣ,∑ x∈secondSourceSector source sector uv,
        (w x*actualSecondSignedWeight p hp hcop hg Ψ
          (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
          ∑ J₁∈slots₁.powerset,∑ J₂∈slots₂.powerset,
            secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂
              ω₁ ω₂ G E V B X t) =
      ∫ t : Frequency × (Fin 6 → ℝ),density t*secondDeletedFullModeSum p hp hcop hg source sector pool Ψ m z
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B X w t := by
    apply integral_congr_ae
    filter_upwards with t
    rw [secondDeletedFullModeSum_physical]
  rw [hi] at he
  have hexp : Real.exp (6*L)*Real.exp (-6*L) = 1 := by
    rw [←Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hn := congrArg norm he
  conv_lhs at hn => rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  conv_rhs at hn => rw [norm_mul]
  have hn' := congrArg (fun a : ℝ => Real.exp (6*L)*a) hn
  rw [←mul_assoc,hexp,one_mul] at hn'
  rw [←mul_assoc] at hn'
  rw [hn']
  exact mul_le_mul_of_nonneg_left hb (by positivity)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0696

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedPhysicalRecursive
Source SHA256: cd032a1f5ef03333090e02c4eac6bafd65856cf5b4fe423ae7647ec2962e3711
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0697




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedPhysicalRecursiveUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})

theorem actual_second_deleted_physical_recursive
    (hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (W₁ W₂ ω₁ ω₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (U : Fin 6 → ℝ → ℂ) (density : Frequency × (Fin 6 → ℝ) → ℂ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K J : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → Integrable density →
      (∀ y : Fin 6 → ℝ,(Real.exp (-6*L):ℂ)*secondPoissonProfile (fun x => star (W₁ x)) W₂ Φ U
        (Y*B/(E*V^2*(Z^N)^2)) y = ∫ t : Frequency × (Fin 6 → ℝ),density t*
          pureProfileMode secondLeftSlope secondRightSlope secondKernelSlope y t.1 t.2) →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₁ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        W₂ (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U i (secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      Integrable (fun t : Frequency × (Fin 6 → ℝ) =>
        tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ W₁ W₂ Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          ∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖density t‖) := by
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ W₁ W₂ ω₁ ω₂ Φ G E V B Y R L Z N Vlabel εchild
    U density w labels K J A hd₁ hd₂ hZ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have he (H : ℝ) : Z^(max 0 N+Vlabel)*(A*Z^(max 0 N+Vlabel+εchild)*H) =
      (A*Z^(2*(max 0 N+Vlabel)+εchild))*H := by
    calc
      _ = A*(Z^(max 0 N+Vlabel)*Z^(max 0 N+Vlabel+εchild))*H := by ring
      _ = _ := by rw [←Real.rpow_add hZ]; congr 2; ring_nf
  apply actual_second_deleted_physical_energy p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ W₁ W₂ ω₁ ω₂ Φ G E V B (Z^N) Y R L
    U density w labels K J (A*Z^(2*(max 0 N+Vlabel)+εchild))
    hd₁ hd₂ hG hE hV hB hX hDensity hsep hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels
    ho hslots₁ hslots₂ (mul_nonneg hA (Real.rpow_pos_of_pos hZ _).le) hWeighted
  · intro t J₁ hJ₁ γ hγ
    rw [second_left_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      (nonzeroChildFrequencyBall 1 R) γ pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayMinus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hleft t J₁ hJ₁ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)
  · intro t J₂ hJ₂ γ hγ
    rw [second_right_normalized_energy p hp hcop hg K (labels.filter Squarefree)
      R γ pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ Z N Vlabel hZ t]
    rw [normalized_child_energy_radical_puncture p hp hcop hg pool (secondRayPlus Ψ z)
      (actualSecondInheritedPuncture m γ)]
    exact (mul_le_mul_of_nonneg_left (hright t J₂ hJ₂ γ hγ) (Real.rpow_pos_of_pos hZ _).le).trans_eq (he _)

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0697

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingEnergy
Source SHA256: bfbb54cec6144766604f98a81f2bc8d7d4e47a9db16dd920974bc0f04669b512
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0698



namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingPhysicalUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
theorem actual_second_deleted_moving_physical_recursive
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨C,hC,hmeasure⟩ := InverseSecondProfileUniform.second_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨C,hC,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ρ c₁ c₂ θ₁ θ₂ w labels K A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hRad : 0 < Y*B/(E*V^2*(Z^N)^2) := by positivity
  obtain ⟨b₃,hb₃⟩ := hmeasure (Y*B/(E*V^2*(Z^N)^2)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_second_deleted_physical_recursive p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ
    G E V B Y R L Z N Vlabel εchild (fun i y => U₀ i (y+ρ i)) den w labels K J A
    hd₁ hd₂ hZ hG hE hV hB hX hden (by simpa only [star_star] using hsep)
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have hd : (∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖den t‖) ≤
      C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hd (by
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ))) (by positivity))

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0698

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingEnergyUniform
Source SHA256: 85a0d47e0c697ec2cdfad7d13543b8261ab855e08ce0325b373408f501d91693
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0699





namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingPhysicalUnitsUniform : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
theorem actual_second_deleted_moving_physical_recursive_uniform_types
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J : ℕ) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (K : ℕ) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          ∑ γ∈actualSecondTriples p 1 1 source,tripleDivisorWeight K γ)*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨C,hC,hmeasure⟩ := InverseSecondProfileUniform.second_profile_common_measure
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ρ c₁ c₂ θ₁ θ₂ w labels K A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hRad : 0 < Y*B/(E*V^2*(Z^N)^2) := by positivity
  obtain ⟨b₃,hb₃⟩ := hmeasure (Y*B/(E*V^2*(Z^N)^2)) hRad
  obtain ⟨hsep,hWeighted,hMoment⟩ := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  let g := fun i => rooted (U₀ i) (M₀ i) (InverseClippingProfiles.secondBalancedSlope i) (hU i)
  let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) hg₁
  let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) hg₂
  let den := density g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have hden : Integrable den := balanced_density_integrable g f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L
  have he := actual_second_deleted_physical_recursive p hp hcop hg hpr hinj hc source hs
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) ω₁ ω₂ Φ
    G E V B Y R L Z N Vlabel εchild (fun i y => U₀ i (y+ρ i)) den w labels K J A
    hd₁ hd₂ hZ hG hE hV hB hX hden (by simpa only [star_star] using hsep)
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hWeighted hleft hright
  have hd : (∫ t : Frequency × (Fin 6 → ℝ),tripleHeight J t.1*coordinateHeight J t.2*‖den t‖) ≤
      C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
        (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
          (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by
    apply (le_div_iff₀ (by positivity)).mpr
    exact (mul_comm _ _).le.trans hMoment
  exact he.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hd (by
      apply mul_nonneg
      · positivity
      · exact Finset.sum_nonneg (fun γ _ => tripleDivisorWeight_nonneg K γ))) (by positivity))

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0699

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingMass
Source SHA256: 508ad97d3a86a9738bf5064950ad52992aaca9da3458691758d73c049293328b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0700




namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingMassUnits : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]
theorem actual_second_deleted_moving_mass_recursive
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨Cp,hCp,hmoving⟩ := actual_second_deleted_moving_physical_recursive (ι:=ι) (σ:=σ)
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Cm,hCm,hmass⟩ := actual_second_original_mass K εmass hεmass
  refine ⟨Cp*Cm,mul_nonneg hCp hCm.le,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have he := hmoving p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ρ c₁ c₂ θ₁ θ₂ w labels K A hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hm := hmass p hp source 1 1 Z ell Ractive j tcount gcount theta eta hZ
    hs.quotient_nonzero hs.second_divisor hcube₁ hcube₂ hactive hj hquot hcommon hdiv
  have hfac : 0 ≤ 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild)) := by positivity
  have hh : 0 ≤ Cp*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by positivity
  have hpref : 0 ≤ Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N):ℝ):ℂ)⁻¹‖ := by positivity
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hfac) hh) hpref
  exact he.trans (hb.trans_eq (by ring))

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0700

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PhysicalBlockBudget
Source SHA256: 20ecdfadef291316fe02384873a24f8749b0b1b2a3c45f57c07c367e783cb3e5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0701



namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

theorem second_source_scalar_norm (Y E V X : ℝ)
    (hY : 0<Y) (hE : 0<E) (hV : 0<V) (hX : 0<X) (a : ℂ) :
    ‖(Y:ℂ)*a*((E*V*X:ℝ):ℂ)⁻¹‖ = ‖a‖*(Y/(E*V*X)) := by
  rw [norm_mul,norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,
    Complex.norm_real,Real.norm_eq_abs,abs_of_pos hY,abs_of_pos (by positivity : 0<E*V*X)]
  ring

theorem physical_block_rpow_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ) /
        (Z^θ*Z^v*Z^(secondFormalColumn r A B t g v)) * Real.exp (6*(η*Real.log Z))) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hZpos : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_physical_scalar Z hZpos]
  have hexp : Real.exp ((9/2:ℝ)*(η*Real.log Z))=Z^((9/2:ℝ)*η) := by
    rw [Real.rpow_def_of_pos hZpos]
    congr 1
    ring
  rw [hexp,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos,←Real.rpow_add hZpos]
  apply Real.rpow_le_rpow_of_exponent_le hZ
  have hb := physical_step_energy_exponent M r ell V δ A B R j t g θ v η τ π ε
    (max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v) hclip
  nlinarith

theorem physical_block_scalar_budget
    (Z : ℝ) (hZ : 1≤Z) (M r ell V δ A B R j t g θ v η τ π ε εmass : ℝ)
    (ray : ℂ) (C : ℝ) (hC : 0≤C)
    (hclip : max 0 (secondFormalColumn r A B t g v)-secondFormalColumn r A B t g v≤6*η)
    (hεmass : εmass*(secondCount ell R j t g θ+11*η/2)≤π) :
    C * Z^(firstKappa M r ell V δ A B R) * Real.exp ((9/2:ℝ)*(η*Real.log Z)) *
      (Real.exp (6*(η*Real.log Z)) *
        ‖((Z^(firstPhysicalHeight M r ell V δ B j+12*η+τ):ℝ):ℂ)*ray*
          ((Z^θ*Z^v*Z^(secondFormalColumn r A B t g v):ℝ):ℂ)⁻¹‖) *
      Z^((secondCount ell R j t g θ+11*η/2)*(1+εmass)) *
      Z^(2*(max 0 (secondFormalColumn r A B t g v)+secondFormalLabel B θ v j)+ε) ≤
    C*‖ray‖*Z^(r+3*ell+V+40*η+τ+π+ε) := by
  have hz : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  rw [second_source_scalar_norm _ _ _ _ (by positivity) (by positivity) (by positivity) (by positivity)]
  have hh := mul_le_mul_of_nonneg_left
    (physical_block_rpow_budget Z hZ M r ell V δ A B R j t g θ v η τ π ε εmass hclip hεmass)
    (mul_nonneg hC (norm_nonneg ray))
  convert hh using 1 ; ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0701

/-! Original module: OAI.NumberTheory.DirichletL.Descent.SecondDeletedMovingMassUniform
Source SHA256: 044c70861fe16c3be040d9ce28c72be883d557422b86bdd7b488a853b8220e40
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0702






namespace OAI

namespace SevenEighths.InverseMoment
open scoped BigOperators Classical ContDiff
open InverseSecondFibers ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation MeasureTheory SchwartzMap InverseInitialClippedColumns
noncomputable section
local notation "Eis" => ActualEisensteinCubic.O
local instance inverseSecondDeletedMovingMassUnitsUniform : Fintype Eisˣ := @Fintype.ofFinite _ PrimaryIdealUnitReindex.finite_units
open InverseSecondProfileUniform InverseAmbientProfileTower
theorem actual_second_deleted_moving_mass_recursive_uniform_types
    (U₀ : Fin 6 → 𝓢(ℝ,ℂ)) (g₁ g₂ Φ : 𝓢(ℝ,ℂ))
    (M₀ B₀ : Fin 6 → ℝ) (m₁ m₂ bcap : ℝ)
    (hM : ∀ i,0 ≤ M₀ i) (hB₀ : ∀ i,0 ≤ B₀ i)
    (hU : ∀ i,Function.support (U₀ i) ⊆ Set.Icc (-M₀ i) (M₀ i))
    (hg₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (Aker J K : ℕ) (εmass : ℝ) (hεmass : 0 < εmass) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ {ι σ : Type} [DecidableEq ι] [DecidableEq σ] (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (_hs : ActualSecondSourceConditions p source),
    ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (deleted₁ deleted₂ : MarkedSecondSource ι Jo 0→Finset ι)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B Y R L Z N Vlabel εchild : ℝ)
        (ell Ractive j tcount gcount theta eta : ℝ) (ρ : Fin 6 → ℝ) (c₁ c₂ θ₁ θ₂ : ℝ)
        (w : MarkedSecondSource ι Jo 0 → ℂ)
        (labels : Finset (Ideal Eis)) (A : ℝ),
      (∀ x∈source,∀ i∈deleted₁ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ x∈source,∀ i∈deleted₂ x,i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient) →
      (∀ i,|ρ i| ≤ B₀ i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ bcap → c₂ ≤ bcap → 0 ≤ L →
      0 < Z → 0 < G → 0 < E → 0 < V → 0 < B → 0 < (Z^N) → 0 < Y →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (fun x => star (positiveSource g₁ c₁ θ₁ x)) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₁ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ x ∈ source,∀ Q ∈ (pool\x.second.overlap).powerset,
        (positiveSource g₂ c₂ θ₂) (primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap*
          primeProductNorm p Q/(G*V*(Z^N))) ≠ 0 → ω₂ (primeProductNorm p Q/(Z^N)) = 1) →
      (∀ j ∈ secondProfileIndices source pool (fun x => secondInheritedProfile p x Ψ m z),
        ω₁ (primeProductNorm p j.2.1/(Z^N)) ≠ 0 → ω₂ (primeProductNorm p j.2.2/(Z^N)) ≠ 0 → ∀ i,
        U₀ i ((secondRelativeLog (secondActualNorms p (secondInheritedProfile p j.1 Ψ m z) j.2.1 j.2.2)
          G E V B (Z^N) i)+ρ i) = 1) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ x∈source,primeProductNorm p x.second.sourceCommon ≤ Z^(gcount+eta)) →
      (∀ x∈source,Z^(theta-eta) ≤ primeProductNorm p x.second.divisor) →
      (∀ a,‖Ψ a‖ ≤ 1) → (∀ x∈source,‖w x‖ ≤ 1) →
      (∀ i∈slots₁,∀ q∈lists₁ i,‖a₁ i q‖ ≤ 1) →
      (∀ i∈slots₂,∀ q∈lists₂ i,‖a₂ i q‖ ≤ 1) →
      (∀ x∈source,(actualSecondChild p 1 1 x).2.1 ∈ labels) →
      Jo ≤ 2*K → slots₁.card ≤ K → slots₂.card ≤ K → 0 ≤ A →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈slots₁.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₁\J₁) lists₁ a₁
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈slots₂.powerset,∀ γ∈actualSecondTriples p 1 1 source,
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ z)
          (actualSecondInheritedRadicalPuncture m γ) (slots₂\J₂) lists₂ a₂
          (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 N)) Z (max 0 N+Vlabel) ≤
          A*Z^(max 0 N+Vlabel+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      ‖(Y : ℂ)*secondRayCoefficient z *
        (∑ x ∈ source,(w x*actualSecondSignedWeight p hp hcop hg Ψ
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x) *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
            slots₁ slots₂ (fun i=>lists₁ i\deleted₁ x) (fun i=>lists₂ i\deleted₂ x) a₁ a₂ (fun x => star (positiveSource g₁ c₁ θ₁ x)) (positiveSource g₂ c₂ θ₂) Φ Y (G*V*(Z^N)))‖ ≤
      (Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N) : ℝ):ℂ)⁻¹‖)*
        ((36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild))*
          Z^((ell+Ractive/2-j+tcount+gcount-theta+11*eta/2)*(1+εmass)))*
          (C*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
            (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
              (1+Y*B/(E*V^2*(Z^N)^2))^Aker)) := by
  obtain ⟨Cp,hCp,hmoving⟩ := actual_second_deleted_moving_physical_recursive_uniform_types
    U₀ g₁ g₂ Φ M₀ B₀ m₁ m₂ bcap hM hB₀ hU hg₁ hg₂ Aker J
  obtain ⟨Cm,hCm,hmass⟩ := actual_second_original_mass K εmass hεmass
  refine ⟨Cp*Cm,mul_nonneg hCp hCm.le,?_⟩
  intro ι σ _ _ p hp _ hcop hg hpr hinj hc Jo source hs pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂
    ω₁ ω₂ G E V B Y R L Z N Vlabel εchild ell Ractive j tcount gcount theta eta ρ c₁ c₂ θ₁ θ₂ w labels A
    hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hcube₁ hcube₂ hactive hj hquot hcommon hdiv
    hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have he := hmoving p hp hcop hg hpr hinj hc source hs pool Ψ m z
    slots₁ slots₂ lists₁ lists₂ a₁ a₂ deleted₁ deleted₂ ω₁ ω₂ G E V B Y R L Z N Vlabel εchild
    ρ c₁ c₂ θ₁ θ₂ w labels K A hd₁ hd₂ hρ hc₁ hc₂ hc₁b hc₂b hL hZ hG hE hV hB hX hY
    hrows hω₁ hω₂ hcut hΨ hw ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hleft hright
  have hm := hmass p hp source 1 1 Z ell Ractive j tcount gcount theta eta hZ
    hs.quotient_nonzero hs.second_divisor hcube₁ hcube₂ hactive hj hquot hcommon hdiv
  have hfac : 0 ≤ 36*(2:ℝ)^slots₁.card*(2:ℝ)^slots₂.card*(A*Z^(2*(max 0 N+Vlabel)+εchild)) := by positivity
  have hh : 0 ≤ Cp*((1+‖θ₁‖)^InverseClippingProfiles.momentOrder J *
      (1+‖θ₂‖)^InverseClippingProfiles.momentOrder J) /
        (1+Y*B/(E*V^2*(Z^N)^2))^Aker := by positivity
  have hpref : 0 ≤ Real.exp (6*L)*‖(Y : ℂ)*secondRayCoefficient z*((E*V*(Z^N):ℝ):ℂ)⁻¹‖ := by positivity
  have hb := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hfac) hh) hpref
  exact he.trans (hb.trans_eq (by ring))

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0702

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityPrincipal
Source SHA256: 985c1cd4d0d9cfb85e7f449f7ff2c712349927dde47ee416ef8f9df8ed3b8aae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0703




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
  (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def wholePriorityPrincipalEnergy
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
    (Ψ:O→*ℂ) (m d:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (selector:Finset ι→ℂ) (om W:𝓢(ℝ,ℂ)) (X t Y:ℝ)
    (R:Finset ι→Finset ι→Finset ι→ℝ) : ℝ :=
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  (32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
    (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
      ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
        b.leftBit b.rightBit negative Ψ m D core‖*
      ∑J∈slots.powerset,‖primeMark J lists a (A∪D)‖^2*
        (let H:=firstCoreTest (primeMark (slots\J) (fun i=>lists i\(A∪D)) a)
          (fun u=>om (Real.exp u)) (columnLog p (primeProductNorm p D*X)) negative (-t) D
         let Ψ₀:=firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
         let m₀:=(m*b0Label p b.support (fun i=>b.leftExponent i+b.rightExponent i)
           b.leftBit b.rightBit)*∏i∈D,p i
         let c₀:=(∏i∈C,p i)*jLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i)
           b.leftBit b.rightBit
         ‖truncatedSecondZero p hg pool Ψ₀ m₀ c₀ d H W Y
           (fun G E=>secondPhysicalCutoff p d (R D G E) G E)‖+
         ‖principalRestoration p hg hinj hp pool Ψ₀ m₀ c₀ d H W Y
           (fun G E=>secondPhysicalMask p d (R D G E) G E)‖)

theorem whole_priority_principal_bound (ε:ℝ) (hε:0<ε) :
    ∃ (s:Finset (ℕ×ℕ)) (Cp:ℝ),0<Cp ∧
    ∀ {ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m d:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (selector:Finset ι→ℂ) (om W:𝓢(ℝ,ℂ)) (lo hi:ℝ)
      (_hlo:0<lo) (_hs:Function.support om⊆Set.Icc lo hi)
      (M t X Y:ℝ) (R:Finset ι→Finset ι→Finset ι→ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → d≠0 → hi≤Real.exp M → 0<X → 1≤Y → (∀D G E,0≤R D G E) →
      wholePriorityPrincipalEnergy p hp hg hinj pool b C extra negative Ψ m d slots lists a selector om W X t Y R ≤
        Cp*(4:ℝ)^slots.card*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*
          Y*(X*Real.exp M)^(1+ε)*
          (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p
            ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D))^(2*ε)) := by
  obtain ⟨s,Cp,hCp,hprinc⟩ := firstCore_variable_principal_energy ε hε
  obtain ⟨Cm,hCm,hmark⟩ := finite_primeMark_small_power ε hε
  refine ⟨s,((32*512:ℝ)^2*512)*Cp*Cm^2,by positivity,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop pool b C extra negative Ψ m d slots lists a selector om W lo hi hlo hs
    M t X Y R hslots ha hΨ hd hhi hX hY hR
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  let P:=Cp*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W*(SchwartzMap.seminorm ℝ 0 0 om)^2)*Y*(X*Real.exp M)^(1+ε)
  have hP:0≤P:=by dsimp [P];positivity
  have hm (J:Finset σ) (hJ:J∈slots.powerset) (D:Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤Cm^2*(primeProductNorm p (A∪D))^(2*ε) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij) (fun i hi=>ha i (hj hi)) (A∪D)
    have he:((primeProductNorm p (A∪D))^ε)^2=(primeProductNorm p (A∪D))^(2*ε):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^ε)^2:=pow_le_pow_left₀ (norm_nonneg _) hh 2
      _= _:=by rw [mul_pow,he]
  have hn (D:Finset ι) : 0≤primeProductNorm p (A∪D):=(primeProductNorm_pos p hp _).le
  unfold wholePriorityPrincipalEnergy
  dsimp only
  have hinner (r:RayCharacter×RayCharacter) (D:Finset ι) (core:FirstCoreIndex) (J:Finset σ)
      (hJ:J∈slots.powerset) := hprinc p hp hg hinj hcop (slots\J) (fun i=>lists i\(A∪D)) a
    (residual_lists_pairwise slots J lists A D hslots) (residual_coeff_bound slots J lists a A D ha)
    pool D b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
    (fun i _=>residual_lists_avoid lists A D i) negative (if negative then r.1 else r.2) Ψ hΨ
    m (∏i∈C,p i) d hd core om W lo hi hlo hs M t X Y (R D) hhi hX hY (hR D)
  change _≤_
  calc
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P)) := by
      gcongr with r hr D hD core hc
      calc
        _≤∑J∈slots.powerset,Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P := by
          apply Finset.sum_le_sum
          intro J hJ
          exact mul_le_mul (hm J hJ D) (hinner r D core J hJ) (by positivity) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _))
        _= _:=by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤(32*512)*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        ((32*512)*((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*P))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _)) (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _)) hP))
    _= ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤ ((32*512:ℝ)^2)*((2:ℝ)^slots.card)^2*Cm^2*P*512*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · simpa only [Fintype.sum_prod_type] using crossCoeff_sum_norm_le
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn D) _))
    _= _ := by
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [P,A]
      ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0703

/-! Original module: OAI.NumberTheory.DirichletL.Descent.PrincipalSelectorMass
Source SHA256: 66e76744d7e742bb759caf80733b88cac30556aecaa99655f39487b27bee771b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0704


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.InverseMoment
open FirstPassCubeLabels SecondPassArithmetic
local notation "O" => ActualEisensteinCubic.O

theorem first_selector_weighted_mass {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool A:Finset ι) (selector:Finset ι→ℂ) (E T S ε:ℝ)
    (hE:0≤E) (hT:0<T) (hS:0≤S) (hε:0≤ε)
    (hA:primeProductNorm p A≤E)
    (hselector:∀D∈pool.powerset,‖selector D‖≤S)
    (hsupport:∀D∈pool.powerset,selector D≠0→primeProductNorm p D≤T) :
    (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)≤
      128*T*S*(E*T)^ε := by
  have hfilter:(∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)=
      ∑D∈boundedPrimeSupports p pool T,‖selector D‖*(primeProductNorm p (A∪D))^ε:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro D hD hnot
    have hz:selector D=0:=by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hD,hsupport D hD h⟩)
    simp [hz]
  rw [hfilter]
  calc
    _≤∑D∈boundedPrimeSupports p pool T,S*(E*T)^ε:=by
      apply Finset.sum_le_sum
      intro D hD
      have hnorm:primeProductNorm p (A∪D)≤E*T:=
        (primeProductNorm_union_le_mul p hp A D).trans
          (mul_le_mul hA (Finset.mem_filter.mp hD).2 (primeProductNorm_pos p hp D).le hE)
      exact mul_le_mul (hselector D (Finset.mem_filter.mp hD).1)
        (Real.rpow_le_rpow (primeProductNorm_pos p hp _).le hnorm hε)
        (Real.rpow_nonneg (primeProductNorm_pos p hp _).le _) hS
    _= ((boundedPrimeSupports p pool T).card:ℝ)*S*(E*T)^ε:=by simp;ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj pool T hT) hS)
      (Real.rpow_nonneg (mul_nonneg hE hT.le) _)

theorem first_whole_extracted_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι) (hb:b.Admissible) (C extra:Finset ι) (he:extra⊆b.support)
    (negative:Bool) (B:ℝ) (hB:0≤B)
    (h₁:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.leftExponent)‖^2≤B)
    (h₂:‖ConcreteTraceCRT.eisEmbedding (primeProduct p b.support b.rightExponent)‖^2≤B) :
    primeProductNorm p (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))≤
      B^2*primeProductNorm p C := by
  have hbits:(if negative then b.rightDivisor else b.leftDivisor)⊆b.support:=by
    cases negative
    · exact hb.1
    · exact hb.2
  have hs:extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)⊆b.support∪C:=by
    exact Finset.union_subset (he.trans Finset.subset_union_left)
      (Finset.union_subset_union hbits (Finset.Subset.refl C))
  apply (primeProductNorm_mono p hp hs).trans
  apply (primeProductNorm_union_le_mul p hp b.support C).trans
  exact mul_le_mul_of_nonneg_right (cubeCoordinates_radical_bound p hp b B hB h₁ h₂)
    (primeProductNorm_pos p hp C).le

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0704

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.FirstPriorityParents
Source SHA256: 6cdd50384fd65ac1631f786ba933d3590c4106ac0aa556e8a22f765e563ee706
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0705




namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseFirstPriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic
local notation "O" => ActualEisensteinCubic.O

@[ext] structure Source (ι : Type*) (Jo : ℕ) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  firstDivisor : Finset ι
  quotientSupport : Finset ι
  oldAssigned : Fin Jo → SmoothMobiusCorrection.PrimeIdeal

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def extractedSupport (negative : Bool) (x : Source ι Jo) : Finset ι :=
  ((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon)∪x.quotientSupport

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def parent (x : Source ι Jo) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := sourceIdeal p x.quotientSupport
  oldAssigned := x.oldAssigned

theorem parent_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) :
    Function.Injective (parent p (Jo:=Jo)) := by
  intro x y h
  apply Source.ext
  · exact congrArg SecondParentSource.cube h
  · exact congrArg SecondParentSource.firstCommon h
  · exact congrArg SecondParentSource.firstDivisor h
  · exact sourceIdeal_injective p hinj (congrArg SecondParentSource.quotient h)
  · exact congrArg SecondParentSource.oldAssigned h

def appendParent {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : SecondParentSource ι (Jo+Jn) where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := Fin.addCases x.oldAssigned q

def forgetAppended {Jn : ℕ} (x : SecondParentSource ι (Jo+Jn)) : SecondParentSource ι Jo where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  quotient := x.quotient
  oldAssigned := fun i=>x.oldAssigned (Fin.castAdd Jn i)

omit [DecidableEq ι] in
@[simp] theorem forget_append {Jn : ℕ} (x : SecondParentSource ι Jo)
    (q : Fin Jn→SmoothMobiusCorrection.PrimeIdeal) : forgetAppended (appendParent x q)=x := by
  apply SecondParentSource.ext <;> try rfl
  funext i
  simp only [forgetAppended,appendParent,Fin.addCases_left]

omit [DecidableEq ι] in
theorem appendParent_injective {Jn : ℕ} :
    Function.Injective (fun q : SecondParentSource ι Jo × (Fin Jn→SmoothMobiusCorrection.PrimeIdeal)=>
      appendParent q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · simpa only [forget_append] using congrArg forgetAppended h
  · funext i
    simpa only [appendParent,Fin.addCases_right] using
      congrArg (fun x : SecondParentSource ι (Jo+Jn)=>x.oldAssigned (Fin.natAdd Jo i)) h

def attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) : SecondParentSource ι (Jo+(J.card+J.card)) :=
  appendParent (parent p q.1) (fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))

omit [DecidableEq σ] in
theorem attach_injective (hinj : Function.Injective (fun i=>Ideal.span {p i})) (J : Finset σ) :
    Function.Injective (attach p (Jo:=Jo) J) := by
  intro q r h
  have he := @appendParent_injective ι Jo (J.card+J.card)
    (parent p q.1,fun i=>sourcePrime p (pairedSlotAssignment J J q.2 i))
    (parent p r.1,fun i=>sourcePrime p (pairedSlotAssignment J J r.2 i)) h
  apply Prod.ext
  · exact parent_injective p hinj (congrArg Prod.fst he)
  · apply pairedSlotAssignment_injective J J
    funext i
    exact hinj (congrArg (fun q : SecondParentSource ι Jo ×
      (Fin (J.card+J.card)→SmoothMobiusCorrection.PrimeIdeal)=>(q.2 i).val) he)

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem forget_attach (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    forgetAppended (attach p J q)=parent p q.1 := forget_append _ _

def assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈extractedSupport negative q.1)

def assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (assignmentSource source negative J lists).image (attach p J)

theorem sum_assignmentSource {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈assignmentSource source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (x,q) := by
  rw [assignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_assignedParents (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈assignedParents p source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),H (attach p J (x,q)) := by
  rw [assignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_assignmentSource source negative J lists _

def coefficient (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) :
    SecondParentSource ι (Jo+(J.card+J.card))→ℂ :=
  Function.extend (attach p J) (fun q=>w q.1*pairedSlotWeight J J a a q.2) (fun _=>0)

omit [DecidableEq σ] in
theorem coefficient_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    coefficient p J a w (attach p J q)=w q.1*pairedSlotWeight J J a a q.2 :=
  (attach_injective p hinj J).extend_apply _ _ _

theorem paired_parent_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (extractedSupport negative x))*
      primeMark J lists a (extractedSupport negative x))*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_assignedParents p hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem paired_parent_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    paired_parent_sum p hinj source negative J lists a w H

lemma mem_assignmentSource (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈assignmentSource source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)) := by
  rw [←paired_assignment_filter]
  simp only [assignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_assignedParents (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈assignedParents p source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative x)),attach p J (x,q)=y := by
  simp only [assignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_assignmentSource source negative J lists x q).mp hq |>.1,
      q,(mem_assignmentSource source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_assignmentSource source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

structure SourceValid (x : Source ι Jo) : Prop where
  admissible : x.cube.Admissible
  common_disjoint : Disjoint x.firstCommon x.cube.support
  first_divisor : x.firstDivisor⊆x.firstCommon∪x.cube.support
  old_support : ∀ i,(x.oldAssigned i).val∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport

theorem extracted_prime_dvd (x : Source ι Jo) (hx : x.cube.Admissible)
    (negative : Bool) (i : ι) (hi : i∈extractedSupport negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · obtain hi|hi := Finset.mem_union.mp hi
    · have hb : i∈x.cube.support := by
        cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hi
        · exact hx.1 hi
        · exact hx.2 hi
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i hb) _) _
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _) _
  · exact dvd_mul_of_dvd_right (source_prime_dvd p _ i hi) _

theorem attach_old_support (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩extractedSupport negative x))×ˢ
      (J.pi (fun i=>lists i∩extractedSupport negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈extractedSupport negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      extracted_prime_dvd p x hx.admissible negative _ (hh k)

omit [DecidableEq σ] in

theorem attach_physical_data (J : Finset σ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (m : O) :
    secondParentLabel p (attach p J q)=secondParentLabel p (parent p q.1) ∧
    secondParentDivisor p (attach p J q)=secondParentDivisor p (parent p q.1) ∧
    secondParentPuncture p m (attach p J q)=secondParentPuncture p m (parent p q.1) :=
  ⟨rfl,rfl,rfl⟩

theorem coefficient_norm (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (B : ℝ)
    (ha : ∀ i∈J,∀ k∈lists i,‖a i k‖≤1) (hw : ∀ x∈source,‖w x‖≤B)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) : ‖coefficient p J a w y‖≤B := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [coefficient_attach p hinj,norm_mul]
  exact (mul_le_of_le_one_right (norm_nonneg _) (pairedSlotWeight_norm_le_one J J lists lists a a
    _ q hq ha ha)).trans (hw x hx)

theorem assigned_family_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈assignedParents p source negative J lists,∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p (attachedSecondFamily (assignedParents p source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact attach_old_support p negative J lists x (hs x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

def fixedPoint (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (D : Finset ι) : Source ι Jo :=
  ⟨b,C,E,D,old⟩

def fixedSource (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Finset (Source ι Jo) :=
  F.powerset.image (fixedPoint b C E old)

omit [DecidableEq ι] in
theorem fixedPoint_injective (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) : Function.Injective (fixedPoint b C E old) := by
  intro D D' h
  exact congrArg Source.quotientSupport h

def parentFunction (H : Source ι Jo→ℂ) : SecondParentSource ι Jo→ℂ :=
  Function.extend (parent p) H (fun _=>0)

theorem parentFunction_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (H : Source ι Jo→ℂ) (x : Source ι Jo) : parentFunction p H (parent p x)=H x :=
  (parent_injective p hinj).extend_apply _ _ _

theorem paired_source_sq_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w H : Source ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (extractedSupport negative x)‖^2 : ℝ)*H x) =
    ∑ y∈assignedParents p source negative J lists,
      coefficient p J a w y*parentFunction p H (forgetAppended y) := by
  simpa only [parentFunction_parent p hinj] using
    paired_parent_sq_sum p hinj source negative J lists a w (parentFunction p H)

theorem fixed_priority_complex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w H : Finset ι→ℂ) :
    (∑ D∈F.powerset,w D*(‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 : ℝ)*H D) =
    ∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>w x.quotientSupport) y *
        parentFunction p (fun x=>H x.quotientSupport) (forgetAppended y) := by
  have he := paired_source_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>w x.quotientSupport) (fun x=>H x.quotientSupport)
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  simpa only [fixedPoint,extractedSupport,fixedSource] using he

theorem fixed_priority_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Finset ι→ℝ) :
    (∑ D∈F.powerset,w D*‖primeMark J lists a
      (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(w x.quotientSupport:ℂ)) y).re := by
  have he := paired_parent_sq_sum p hinj (fixedSource F b C E old) negative J lists a
    (fun x=>(w x.quotientSupport:ℂ)) (fun _=>1)
  simp only [mul_one] at he
  rw [fixedSource,Finset.sum_image (fun _ _ _ _ h=>fixedPoint_injective b C E old h)] at he
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,sub_zero,
    fixedPoint,extractedSupport,fixedSource] using hr

variable (hp : ∀ i,p i≠0) (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def priorityOuter (b : CubeCoordinates ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (selector : Finset ι→ℂ) (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℝ :=
  (‖RayFourExpansion.crossCoeff r.1 r.2‖*‖selector D‖) *
    ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit negative Ψ m D core‖

def priorityPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m d : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter)
    (core : FirstCoreIndex) (D : Finset ι) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj F D b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (fun U=>primeMark (slots\J)
      (fun i=>lists i\(((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)) a U)
    ω X (∏i∈C,p i) d core t Y

theorem first_priority_physical_slice (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ)
    (r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter) (core : FirstCoreIndex) :
    (∑ D∈F.powerset,
      priorityOuter p hg b negative Ψ m selector r core D *
      ‖primeMark J lists a (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪D)‖^2 *
      (priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core D).re) =
    (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
      coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
      parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
        slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  have he := fixed_priority_complex p hinj F b C E old negative J lists a
    (fun D=>(priorityOuter p hg b negative Ψ m selector r core D:ℂ))
    (priorityPoisson p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots J lists a ω X t Y r core)
  have hr := congrArg Complex.re he
  simpa only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero] using hr

theorem first_priority_energy_reindex (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (b : CubeCoordinates ι) (C E : Finset ι)
    (old : Fin Jo→SmoothMobiusCorrection.PrimeIdeal) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (selector : Finset ι→ℂ) (ω : ℝ→ℂ) (X t Y : ℝ) :
    firstPrioritySecondEnergy p hp hg hinj F b C negative Ψ m
      (primeSubsetGenerator (fun i=>Ideal.span {p i}) E) slots lists a selector ω X t Y =
    (32*512)*(2:ℝ)^slots.card *
      ∑ r : RayFourExpansion.RayCharacter×RayFourExpansion.RayCharacter,
      ∑ core : FirstCoreIndex,∑ J∈slots.powerset,
      (∑ y∈assignedParents p (fixedSource F b C E old) negative J lists,
        coefficient p J a (fun x=>(priorityOuter p hg b negative Ψ m selector r core x.quotientSupport:ℂ)) y *
        parentFunction p (fun x=>priorityPoisson p hp hg hinj F b C negative Ψ m
          (primeSubsetGenerator (fun i=>Ideal.span {p i}) E)
          slots J lists a ω X t Y r core x.quotientSupport) (forgetAppended y)).re := by
  simp_rw [←first_priority_physical_slice p hp hg hinj]
  unfold firstPrioritySecondEnergy
  dsimp only
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro core hcore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro D hD
  unfold priorityOuter priorityPoisson
  ring

end SevenEighths.InverseFirstPriorityParents

end

end OAI
end OAIOriginalModule0705

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMass
Source SHA256: 09233b2c0ff0376cb1100afe9eb88928a1b8945cb1a799e824961c50de489430
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0706



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open IdealMobiusDivisorSum (idealDivisors mem_idealDivisors)
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

abbrev Core (ι : Type*) := CubeCoordinates ι×Finset ι×Finset ι

def core {ι : Type*} {Jo : ℕ} (x : Source ι Jo) : Core ι :=
  (x.cube,x.firstCommon,x.quotientSupport)

def divisorTarget {ι : Type*} [DecidableEq ι] (p : ι→O) (q : Core ι) : Ideal O :=
  sourceIdeal p q.1.support*sourceIdeal p q.2.1*sourceIdeal p q.2.2

lemma divisorTarget_ne_zero {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) : divisorTarget p q≠0 :=
  mul_ne_zero (mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)

lemma firstDivisor_dvd_target {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ} (x : Source ι Jo) (hx : SourceValid p x) :
    sourceIdeal p x.firstDivisor∣divisorTarget p (core x) := by
  have hd := sourceIdeal_dvd p _ _ hx.first_divisor
  rw [sourceIdeal_union p _ _ hx.common_disjoint] at hd
  apply hd.trans
  change sourceIdeal p x.firstCommon*sourceIdeal p x.cube.support∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport
  rw [mul_comm (sourceIdeal p x.firstCommon)]
  exact dvd_mul_right _ _

theorem core_fiber_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) {Jo : ℕ}
    (S : Finset (Source ι Jo)) (q : Core ι)
    (hS : ∀x∈S,SourceValid p x) (hq : ∀x∈S,core x=q) :
    S.card≤(idealDivisors (divisorTarget p q)).card^(Jo+1) := by
  let D := idealDivisors (divisorTarget p q)
  have hD := divisorTarget_ne_zero p hp q
  let encode (x : S) : D×(Fin Jo→D) :=
    (⟨sourceIdeal p x.val.firstDivisor,(mem_idealDivisors hD).mpr (by
      simpa only [hq x.val x.property] using firstDivisor_dvd_target p x.val (hS x.val x.property))⟩,
      fun i=>⟨(x.val.oldAssigned i).val,(mem_idealDivisors hD).mpr (by
        have hh := (hS x.val x.property).old_support i
        change (x.val.oldAssigned i).val∣divisorTarget p (core x.val) at hh
        simpa only [hq x.val x.property] using hh)⟩)
  have hi : Function.Injective encode := by
    intro x y he
    have hk := (hq x.val x.property).trans (hq y.val y.property).symm
    have hd : x.val.firstDivisor=y.val.firstDivisor :=
      sourceIdeal_injective p hinj (congrArg (fun z=>z.1.val) he)
    have ho : x.val.oldAssigned=y.val.oldAssigned := by
      funext i
      apply Subtype.ext
      exact congrArg (fun z=>(z.2 i).val) he
    apply Subtype.ext
    exact Source.ext (congrArg Prod.fst hk) (congrArg (fun q=>q.2.1) hk) hd
      (congrArg (fun q=>q.2.2) hk) ho
  have hh := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,D,pow_succ,mul_comm] using hh

theorem core_fiber_small_power (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(q : Core ι),
    (∀x∈S,SourceValid p x) → (∀x∈S,core x=q) →
    (S.card:ℝ)≤C*(Ideal.absNorm (divisorTarget p q):ℝ)^eps := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power
    (eps/(Jmax+1)) (by positivity)
  refine ⟨D^(Jmax+1),by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S q hS hq
  have h0 := divisorTarget_ne_zero p hp q
  have hcard : S.card≤(idealDivisors (divisorTarget p q)).card^(Jmax+1) :=
    (core_fiber_card p hp hinj S q hS hq).trans
      (Nat.pow_le_pow_right (InverseInitialFibers.divisor_card_pos _ h0) (Nat.add_le_add_right hJo 1))
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ h0) (Jmax+1)
  apply (show (S.card:ℝ)≤((idealDivisors (divisorTarget p q)).card:ℝ)^(Jmax+1) by exact_mod_cast hcard).trans
  apply hb.trans_eq
  rw [mul_pow]
  congr 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  field_simp

lemma divisorTarget_norm_bound {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) (B V T : ℝ)
    (hB : 0≤B) (hV : 0≤V) (_hT : 0≤T)
    (hb₁ : ‖eisEmbedding (primeProduct p q.1.support q.1.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p q.1.support q.1.rightExponent)‖^2≤B)
    (hC : primeProductNorm p q.2.1≤V) (ht : primeProductNorm p q.2.2≤T) :
    (Ideal.absNorm (divisorTarget p q):ℝ)≤B^2*V*T := by
  unfold divisorTarget
  simp only [map_mul,Nat.cast_mul,sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span]
  change primeProductNorm p q.1.support*primeProductNorm p q.2.1*primeProductNorm p q.2.2≤_
  exact mul_le_mul (mul_le_mul (cubeCoordinates_radical_bound p hp q.1 B hB hb₁ hb₂)
    hC (primeProductNorm_pos p hp _).le (sq_nonneg _)) ht (primeProductNorm_pos p hp _).le
    (mul_nonneg (sq_nonneg _) hV)

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end OAIOriginalModule0706

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassCount
Source SHA256: 09eb156ea6787d657a71681fbfa102c95d2ce843fec108b9d4b1a0703d6e262f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0707


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma support_family_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (S : Finset (Finset ι)) (U : ℝ) (hU : 0<U) (hS : ∀A∈S,primeProductNorm p A≤U) :
    (S.card:ℝ)≤128*U := by
  by_cases h1 : 1≤U
  · have hh := DescentFiberCost.finite_ideal_count_real (S.image (sourceIdeal p)) U h1
      (by intro I hI;obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI;exact sourceIdeal_ne_zero p hp A)
      (by
        intro I hI
        obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI
        simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hS A hA)
    simpa only [Finset.card_image_of_injective S (sourceIdeal_injective p hinj)] using hh

  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact h1 ((primeProductNorm_ge_one p hp A).trans (hS A hA))
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem original_source_card (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T : ℝ),
    1≤B → 0≤H → 0<V → 0<T → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    (S.card:ℝ)≤C*B^(1+eps)*H*V*T*(B^2*V*T)^eps := by
  obtain ⟨Cf,hCf,hfiber⟩ := core_fiber_small_power Jmax eps heps
  obtain ⟨Cb,hCb,hcube⟩ := cube_coordinates_parity_count eps heps
  refine ⟨Cf*Cb*128^2,by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T hB hH hV hT hS hleft hright hactive hcommon hquot
  let Q := S.image core
  let bs := S.image Source.cube
  let cs := S.image Source.firstCommon
  let ts := S.image Source.quotientSupport
  have hbcount : (bs.card:ℝ)≤Cb*B^(1+eps)*H := hcube p hp hinj bs B H hB hH
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact (hS x hx).admissible)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hleft x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hright x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hactive x hx)
  have hccount : (cs.card:ℝ)≤128*V := support_family_card p hp hinj cs V hV
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hcommon x hx)
  have htcount : (ts.card:ℝ)≤128*T := support_family_card p hp hinj ts T hT
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hquot x hx)
  have hsub : Q⊆bs×ˢ(cs×ˢts) := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩⟩
  have hQcard : (Q.card:ℝ)≤(Cb*B^(1+eps)*H)*(128*V)*(128*T) := by
    have hh : (Q.card:ℝ)≤(bs.card:ℝ)*((cs.card:ℝ)*(ts.card:ℝ)) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp only [Finset.card_product])
    apply hh.trans
    calc
      _ ≤ (Cb*B^(1+eps)*H)*((128*V)*(128*T)) := by gcongr
      _ = _ := by ring
  have hF (q : Core ι) (hq : q∈Q) :
      ((S.filter (fun x=>core x=q)).card:ℝ)≤Cf*(B^2*V*T)^eps := by
    have hf := hfiber p hp hinj Jo hJo (S.filter (fun x=>core x=q)) q
      (fun x hx=>hS x (Finset.mem_filter.mp hx).1) (fun x hx=>(Finset.mem_filter.mp hx).2)
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hCf.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (divisorTarget_norm_bound p hp (core x) B V T (zero_le_one.trans hB) hV.le hT.le
        (hleft x hx) (hright x hx) (hcommon x hx) (hquot x hx)) heps.le
  have he : (S.card:ℝ)=∑q∈Q,((S.filter (fun x=>core x=q)).card:ℝ) := by
    calc
      _ = ∑_x∈S,(1:ℝ) := by simp
      _ = ∑q∈Q,∑_x∈S.filter (fun x=>core x=q),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem core hx) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑_q∈Q,Cf*(B^2*V*T)^eps := Finset.sum_le_sum hF
    _ = (Q.card:ℝ)*(Cf*(B^2*V*T)^eps) := by simp
    _ ≤ ((Cb*B^(1+eps)*H)*(128*V)*(128*T))*(Cf*(B^2*V*T)^eps) :=
      mul_le_mul_of_nonneg_right hQcard (by positivity)
    _ = _ := by ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end OAIOriginalModule0707

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassWeighted
Source SHA256: b87d0591e3a08450c73b3750a83714940675355c48883e2ad0273eace3df174b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0708


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def principalSupport {ι : Type*} [DecidableEq ι] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo) : Finset ι :=
  (extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪x.quotientSupport

lemma principalSupport_norm {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo)
    (hx : SourceValid p x) (hextra : extra x.cube⊆x.cube.support)
    (B V T : ℝ) (hB : 0≤B) (hV : 0≤V)
    (hb₁ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B)
    (hC : primeProductNorm p x.firstCommon≤V) (ht : primeProductNorm p x.quotientSupport≤T) :
    primeProductNorm p (principalSupport extra negative x)≤B^2*V*T := by
  have hh := first_whole_extracted_norm p hp x.cube hx.admissible x.firstCommon (extra x.cube)
    hextra negative B hB hb₁ hb₂
  unfold principalSupport
  apply (primeProductNorm_union_le_mul p hp _ _).trans
  exact mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left hC (sq_nonneg _))) ht
    (primeProductNorm_pos p hp _).le (mul_nonneg (sq_nonneg _) hV)

theorem original_weighted_mass (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(B H V T a : ℝ),
    1≤B → 0≤H → 0<V → 0<T → 0≤a → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤T) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*B^(1+eps)*H*V*T*(B^2*V*T)^(eps+a) := by
  obtain ⟨C,hC,hcount⟩ := original_source_card Jmax eps heps
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T a hB hH hV hT ha hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hcard := hcount p hp hinj Jo hJo S B H V T hB hH hV hT hS hb₁ hb₂ hactive hcommon hquot
  have hBp : 0<B := zero_lt_one.trans_le hB
  calc
    _ ≤ ∑_x∈S,(B^2*V*T)^a := Finset.sum_le_sum (fun x hx=>
      Real.rpow_le_rpow (primeProductNorm_pos p hp _).le
        (principalSupport_norm p hp extra negative x (hS x hx) (hextra x hx) B V T hBp.le hV.le
          (hb₁ x hx) (hb₂ x hx) (hcommon x hx) (hquot x hx)) ha)
    _ = (S.card:ℝ)*(B^2*V*T)^a := by simp
    _ ≤ (C*B^(1+eps)*H*V*T*(B^2*V*T)^eps)*(B^2*V*T)^a :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (by positivity : 0<B^2*V*T)]

lemma weighted_mass_power (Z ell R Bfirst t eta eps a : ℝ) (hZ : 0<Z) :
    (Z^(ell+eta))^(1+eps)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(eps+a)=
    Z^(ell+R/2+Bfirst+t+7*eta/2+eps*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul_natCast hZ.le]
  repeat rw [←Real.rpow_add hZ]
  rw [←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
  congr 1
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end OAIOriginalModule0708

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassSource
Source SHA256: 66ec557f38e5109df6fe53f45b88df5accc85f32ba4c3bf9d11b8c2b513d360a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0709


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma active_norm_of_square {ι : Type*} [DecidableEq ι] (p : ι→O)
    (A : Finset ι) (Z R eta : ℝ) (hZ : 0<Z)
    (hA : primeProductNorm p A≤Z^(R+eta)) :
    ‖eisEmbedding (∏i∈A,p i)‖≤Z^((R+eta)/2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hZ.le _)).mp
  have hh : (Z^((R+eta)/2))^2=Z^(R+eta) := by
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    norm_num
  rw [hh]
  exact hA

theorem original_weighted_source (Jmax : ℕ) (delta : ℝ) (hdelta : 0<delta) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z ell R Bfirst t eta a loss : ℝ),
    1≤Z → 0≤ell+eta → 0≤a →
    7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)≤loss →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(Bfirst+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*Z^(ell+R/2+Bfirst+t+loss) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax delta hdelta
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z ell R Bfirst t eta a loss hZ hell ha hloss hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^(ell+eta)) (Z^((R+eta)/2))
    (Z^(Bfirst+eta)) (Z^(t+eta)) a (Real.one_le_rpow hZ hell)
    (Real.rpow_nonneg hZp.le _) (Real.rpow_pos_of_pos hZp _)
    (Real.rpow_pos_of_pos hZp _) ha hS hb₁ hb₂
    (fun x hx=>active_norm_of_square p _ Z R eta hZp (hactive x hx))
    hcommon hquot extra negative hextra
  apply hh.trans
  calc
    _ = C*( (Z^(ell+eta))^(1+delta)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(delta+a)) := by ring
    _ = C*Z^(ell+R/2+Bfirst+t+7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
      rw [weighted_mass_power Z ell R Bfirst t eta delta a hZp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end OAIOriginalModule0709

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPrincipalMassPrefactor
Source SHA256: 88afd12c6b53c761eb52a05b5c2ec3be84caeebb7a01431df40956b29431d53a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0710



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

def physicalPrincipalFactor (Z M r ell V delta A B R j t eta tau eps window : ℝ) : ℝ :=
  (Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
    Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)*
    (Z^(r-A-B-t)*Real.exp window)^(1+eps)

lemma principal_nominal_identity (M r ell V delta A B R j t : ℝ) :
    firstKappa M r ell V delta A B R+firstPhysicalHeight M r ell V delta B j+
      (r-A-B-t)+(ell+R/2+B+t)=r+3*ell+V-B-j := by
  unfold firstKappa firstPhysicalHeight
  ring

lemma physical_principal_exact (Z M r ell V delta A B R j t eta tau eps window loss : ℝ)
    (hZ : 0<Z) :
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)=
    Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss) := by
  have he : Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  have hw : (Real.exp window)^(1+eps)=Real.exp (window*(1+eps)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  unfold physicalPrincipalFactor
  rw [he,Real.mul_rpow (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le,
    ←Real.rpow_mul hZ.le,hw]
  have hx : r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss=
    firstKappa M r ell V delta A B R+(9/2:ℝ)*eta+
    (firstPhysicalHeight M r ell V delta B j+12*eta+tau)+
    (r-A-B-t)*(1+eps)+(ell+R/2+B+t+loss) := by
    unfold firstKappa firstPhysicalHeight
    ring
  rw [hx]
  simp only [Real.rpow_add hZ]
  ring

theorem original_physical_weighted_source (Jmax : ℕ) (dsmall : ℝ) (hdsmall : 0<dsmall) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))
    (Z M r ell V delta A B R j t eta tau eps window pi : ℝ),
    1≤Z → 0≤ell+eta → 0≤eps → 0≤B → 0≤j →
    eps*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)≤pi+eta/2 →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^(B+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^(2*eps))≤
      C*Real.exp (window*(1+eps))*Z^(r+3*ell+V+17*eta+tau+pi) := by
  obtain ⟨C,hC,hsource⟩ := original_weighted_source Jmax dsmall hdsmall
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z M r ell V delta A B R j t eta tau eps window pi hZ hell heps hB hj hcost hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  let loss := 7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hsource p hp hinj Jo hJo S Z ell R B t eta (2*eps) loss hZ hell
    (by positivity) (le_refl _) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hP : 0≤physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window := by
    unfold physicalPrincipalFactor
    positivity
  calc
    _ ≤ physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (C*Z^(ell+R/2+B+t+loss)) := mul_le_mul_of_nonneg_left hh hP
    _ = C*(physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)) := by ring
    _ = C*(Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss)) := by
      rw [physical_principal_exact Z M r ell V delta A B R j t eta tau eps window loss hZp]
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
      dsimp [loss]
      linarith

end SevenEighths.InverseMomentGlobalPrincipalMass
end

end OAI
end OAIOriginalModule0710

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityTailMass
Source SHA256: 11018780bacb3284224d0b0e0b7a31174883541abc15f70d543663477bcce6c5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0711


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseMomentGlobalPrincipalMass
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

theorem original_tail_mass (Jmax : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤Jmax → ∀(S : Finset (Source ι Jo))(Z L : ℝ),
    1≤Z → 0≤L → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^L) →
    (∀x∈S,‖eisEmbedding (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤Z^L) →
    (∀x∈S,primeProductNorm p x.firstCommon≤Z^L) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤Z^L) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,primeProductNorm p (principalSupport extra negative x))≤C*Z^(13*L) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z L hZ hL hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^L) (Z^L) (Z^L) (Z^L) 1
    (Real.one_le_rpow hZ hL) (by positivity) (by positivity) (by positivity)
    (by norm_num) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  simp only [Real.rpow_one] at hh
  apply hh.trans_eq
  have he : Z^(13*L)=(Z^L)^13 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    norm_num
    ring
  rw [he]
  norm_num
  ring

end SevenEighths.InverseMomentGlobalPriorityTail
end

end OAI
end OAIOriginalModule0711

/-! Original module: OAI.NumberTheory.DirichletL.Descent.WholePriorityParents
Source SHA256: bc4659a1512821ca2f99d2b7030ff7b9160d62f43f0be7dd3d95e323a6a2b436
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0712



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMomentWholePriorityParents
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}

def wholeExtractedSupport (extra : Source ι Jo→Finset ι)
    (negative : Bool) (x : Source ι Jo) : Finset ι := extra x∪extractedSupport negative x

variable (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) :
    Finset (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :=
  (source ×ˢ ((J.pi lists)×ˢ(J.pi lists))).filter
    (fun q=>∀ i,pairedSlotAssignment J J q.2 i∈wholeExtractedSupport extra negative q.1)

def wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) : Finset (SecondParentSource ι (Jo+(J.card+J.card))) :=
  (wholeAssignmentSource extra source negative J lists).image (attach p J)

theorem sum_wholeAssignmentSource (extra : Source ι Jo→Finset ι) {A : Type*} [AddCommMonoid A]
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (H : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))→A) :
    ∑ q∈wholeAssignmentSource extra source negative J lists,H q =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (x,q) := by
  rw [wholeAssignmentSource,Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro x hx
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem sum_wholeAssignedParents (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    {A : Type*} [AddCommMonoid A] (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (H : SecondParentSource ι (Jo+(J.card+J.card))→A) :
    ∑ y∈wholeAssignedParents p extra source negative J lists,H y =
      ∑ x∈source,∑ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),H (attach p J (x,q)) := by
  rw [wholeAssignedParents,Finset.sum_image (fun _ _ _ _ h=>attach_injective p hinj J h)]
  exact sum_wholeAssignmentSource extra source negative J lists _

theorem wholePaired_parent_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(star (primeMark J lists a (wholeExtractedSupport extra negative x))*
      primeMark J lists a (wholeExtractedSupport extra negative x))*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  rw [sum_wholeAssignedParents p extra hinj]
  apply Finset.sum_congr rfl
  intro x hx
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul,coefficient_attach p hinj,forget_attach]

theorem wholePaired_parent_sq_sum (extra : Source ι Jo→Finset ι) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (a : σ→ι→ℂ) (w : Source ι Jo→ℂ) (H : SecondParentSource ι Jo→ℂ) :
    (∑ x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport extra negative x)‖^2 : ℝ)*H (parent p x)) =
    ∑ y∈wholeAssignedParents p extra source negative J lists,
      coefficient p J a w y*H (forgetAppended y) := by
  simpa only [Complex.sq_norm,Complex.normSq_eq_conj_mul_self,starRingEnd_apply] using
    wholePaired_parent_sum p extra hinj source negative J lists a w H

lemma mem_wholeAssignmentSource (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (q : (∀ i∈J,ι)×(∀ i∈J,ι)) :
    (x,q)∈wholeAssignmentSource extra source negative J lists ↔ x∈source ∧
      q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)) := by
  rw [←paired_assignment_filter]
  simp only [wholeAssignmentSource,Finset.mem_filter,Finset.mem_product]
  tauto

theorem mem_wholeAssignedParents (extra : Source ι Jo→Finset ι) (source : Finset (Source ι Jo)) (negative : Bool)
    (J : Finset σ) (lists : σ→Finset ι) (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    y∈wholeAssignedParents p extra source negative J lists ↔
      ∃ x∈source,∃ q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
        (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x)),attach p J (x,q)=y := by
  simp only [wholeAssignedParents,Finset.mem_image]
  constructor
  · rintro ⟨⟨x,q⟩,hq,he⟩
    exact ⟨x,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.1,
      q,(mem_wholeAssignmentSource extra source negative J lists x q).mp hq |>.2,he⟩
  · rintro ⟨x,hx,q,hq,he⟩
    exact ⟨(x,q),(mem_wholeAssignmentSource extra source negative J lists x q).mpr ⟨hx,hq⟩,he⟩

theorem whole_extracted_prime_dvd (extra : Source ι Jo→Finset ι)
    (x : Source ι Jo) (hx : x.cube.Admissible) (he : extra x⊆x.cube.support)
    (negative : Bool) (i : ι) (hi : i∈wholeExtractedSupport extra negative x) :
    (sourcePrime p i).val∣sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*
      sourceIdeal p x.quotientSupport := by
  obtain hi|hi := Finset.mem_union.mp hi
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (source_prime_dvd p _ i (he hi)) _) _
  · exact extracted_prime_dvd p x hx negative i hi

theorem whole_attach_old_support (extra : Source ι Jo→Finset ι)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (x : Source ι Jo) (hx : SourceValid p x) (he : extra x⊆x.cube.support)
    (q : (∀ i∈J,ι)×(∀ i∈J,ι))
    (hq : q∈(J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))×ˢ
      (J.pi (fun i=>lists i∩wholeExtractedSupport extra negative x))) :
    ∀ i,((attach p J (x,q)).oldAssigned i).val∣
      sourceIdeal p (attach p J (x,q)).cube.support*
        sourceIdeal p (attach p J (x,q)).firstCommon*(attach p J (x,q)).quotient := by
  have hh : ∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x := by
    have hf : q∈((J.pi lists)×ˢ(J.pi lists)).filter
        (fun q=>∀ i,pairedSlotAssignment J J q i∈wholeExtractedSupport extra negative x) := by
      rwa [paired_assignment_filter]
    exact (Finset.mem_filter.mp hf).2
  intro i
  refine Fin.addCases (fun k=>?_) (fun k=>?_) i
  · simpa only [attach,appendParent,parent,Fin.addCases_left] using hx.old_support k
  · simpa only [attach,appendParent,parent,Fin.addCases_right] using
      whole_extracted_prime_dvd p extra x hx.admissible he negative _ (hh k)

theorem whole_assigned_family_conditions (hp : ∀ i,p i≠0)
    (extra : Source ι Jo→Finset ι)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (he : ∀ x∈source,extra x⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (expansion : SecondParentSource ι (Jo+(J.card+J.card))→Finset (SecondExpansionData ι))
    (hE : ∀ y∈wholeAssignedParents p extra source negative J lists,
      ∀ x∈expansion y,x.divisor⊆x.sourceCommon) :
    ActualSecondSourceConditions p
      (attachedSecondFamily (wholeAssignedParents p extra source negative J lists) expansion) := by
  apply attached_family_conditions p _ _
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).admissible
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).common_disjoint
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact (hs x hx).first_divisor
  · exact hE
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact whole_attach_old_support p extra negative J lists x (hs x hx) (he x hx) q hq
  · intro y hy
    obtain ⟨x,hx,q,hq,rfl⟩ := (mem_wholeAssignedParents p extra source negative J lists y).mp hy
    exact sourceIdeal_ne_zero p hp x.quotientSupport

end SevenEighths.InverseMomentWholePriorityParents

end

end OAI
end OAIOriginalModule0712

/-! Original module: OAI.NumberTheory.DirichletL.Inversion.PrioritySecondSource
Source SHA256: 24fc0cb403c53b2d7567f31fb60b7658d2de89e0e6281a5c82311e84dc1a17dd
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0713



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InversePrioritySecondSource
open ActualEisensteinCubic SecondPassArithmetic FirstPassCubeLabels FirstCauchyArithmetic
open InverseMoment InverseInitialArithmetic InverseFirstPriorityParents
open InversePrincipalEnergy InverseSecondPrincipalCaller RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
variable {ι σ κ : Type*} [DecidableEq ι] [DecidableEq σ] [DecidableEq κ]
variable {Jo : ℕ} (p : ι→O) [∀ i,(Ideal.span {p i}).IsMaximal]

def quotientSupport (y : SecondParentSource ι Jo) : Finset ι :=
  Function.extend (sourceIdeal p) id (fun _=>∅) y.quotient

theorem quotientSupport_parent (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (x : Source ι Jo) : quotientSupport p (parent p x)=x.quotientSupport :=
  (sourceIdeal_injective p hinj).extend_apply _ _ _

omit [DecidableEq σ] in
theorem quotientSupport_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    quotientSupport p (attach p J q)=q.1.quotientSupport :=
  quotientSupport_parent p hinj q.1

def residualLists (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) : Finset ι :=
  lists i \ (((if negative then y.cube.rightDivisor else y.cube.leftDivisor)∪y.firstCommon)∪
    quotientSupport p y)

omit [DecidableEq σ] in
theorem residualLists_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    residualLists p negative lists (attach p J q)=
      fun i=>lists i\extractedSupport negative q.1 := by
  funext i
  unfold residualLists
  rw [quotientSupport_attach p hinj]
  rfl

omit [DecidableEq σ] [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem residualLists_disjoint (negative : Bool) (lists : σ→Finset ι)
    (y : SecondParentSource ι Jo) (i : σ) :
    Disjoint (residualLists p negative lists y i) (quotientSupport p y) := by
  apply Finset.disjoint_left.mpr
  intro q hq hd
  exact (Finset.mem_sdiff.mp hq).2 (Finset.mem_union_right _ hd)

theorem assigned_quotient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (y : SecondParentSource ι (Jo+(J.card+J.card)))
    (hy : y∈assignedParents p source negative J lists) :
    y.quotient=sourceIdeal p (quotientSupport p y) := by
  obtain ⟨x,hx,q,hq,rfl⟩ := (mem_assignedParents p source negative J lists y).mp hy
  rw [quotientSupport_attach p hinj]
  rfl

def retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) : Finset (MarkedSecondSource ι Jo 0) :=
  attachedSecondFamily parents (fun y=>secondDyadicSector pool (secondVariableCutoff p y (R y))
    residual (label y) j)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem mem_retainedPool (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0) :
    x∈retainedPool p pool parents R label residual j ↔
      secondParentOf x∈parents ∧ x.second∈secondDyadicSector pool
        (secondVariableCutoff p (secondParentOf x) (R (secondParentOf x))) residual
        (label (secondParentOf x)) j := mem_attachedSecondFamily _ _ _

theorem retainedPool_conditions (hp : ∀ i,p i≠0)
    (source : Finset (Source ι Jo)) (hs : ∀ x∈source,SourceValid p x)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) :
    ActualSecondSourceConditions p
      (retainedPool p pool (assignedParents p source negative J lists) R label residual j) := by
  apply assigned_family_conditions p hp source hs negative J lists
  intro y hy x hx
  exact (second_variable_original_support p y pool residual (R y) (label y) j x hx).2.1

omit [∀ i,(Ideal.span {p i}).IsMaximal] in
theorem retainedPool_original_support
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι Jo 0)
    (hx : x∈retainedPool p pool parents R label residual j) :
    x.second.sourceCommon⊆pool ∧ x.second.divisor⊆x.second.sourceCommon ∧
    x.second.overlap⊆pool ∧ x.second.frequency∈nonzeroChildFrequencyBall
      (actualSecondMultiplier p x) (R (secondParentOf x) x.second.sourceCommon x.second.divisor) := by
  have hh := (mem_retainedPool p pool parents R label residual j x).mp hx
  simpa only [attachSecondExpansion_recover] using
    second_variable_original_support p (secondParentOf x) pool residual (R (secondParentOf x))
      (label (secondParentOf x)) j x.second hh.2

def attachOriginal (J : Finset σ)
    (q : (Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) × SecondExpansionData ι) :
    MarkedSecondSource ι (Jo+(J.card+J.card)) 0 :=
  attachSecondExpansion (attach p J q.1) q.2

omit [DecidableEq σ] in
theorem attachOriginal_injective (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) : Function.Injective (attachOriginal p (Jo:=Jo) J) := by
  intro q r he
  apply Prod.ext
  · apply attach_injective p hinj J
    exact congrArg secondParentOf he
  · exact congrArg MarkedSecondSource.second he

theorem retainedPool_iff_original
    (source : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ) (lists : σ→Finset ι)
    (pool : Finset ι)
    (R : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι (Jo+(J.card+J.card))→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :
    x∈retainedPool p pool (assignedParents p source negative J lists) R label residual j ↔
      ∃ s∈source,∃ q∈(J.pi (fun i=>lists i∩extractedSupport negative s))×ˢ
        (J.pi (fun i=>lists i∩extractedSupport negative s)),
        ∃ e∈secondDyadicSector pool (secondVariableCutoff p (attach p J (s,q)) (R (attach p J (s,q))))
          residual (label (attach p J (s,q))) j,attachOriginal p J ((s,q),e)=x := by
  constructor
  · intro hx
    obtain ⟨hy,he⟩ := (mem_retainedPool p _ _ _ _ _ _ x).mp hx
    obtain ⟨s,hs,q,hq,ha⟩ := (mem_assignedParents p source negative J lists (secondParentOf x)).mp hy
    refine ⟨s,hs,q,hq,x.second,?_,?_⟩
    · simpa only [ha] using he
    · unfold attachOriginal
      rw [ha,attachSecondExpansion_recover]
  · rintro ⟨s,hs,q,hq,e,he,rfl⟩
    apply (mem_retainedPool p _ _ _ _ _ _ _).mpr
    refine ⟨?_,he⟩
    exact (mem_assignedParents p source negative J lists _).mpr ⟨s,hs,q,hq,rfl⟩

omit [DecidableEq σ] in
theorem attached_coefficient (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (J : Finset σ) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) (e : SecondExpansionData ι) :
    coefficient p J a w (secondParentOf (attachOriginal p J (q,e)))=
      w q.1*pairedSlotWeight J J a a q.2 := coefficient_attach p hinj J a w q

variable (hp : ∀ i,p i≠0)
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem varying_lists_parent_family
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo))
    (source : SecondParentSource ι Jo→Finset (SecondExpansionData ι))
    (hE : ∀ y∈parents,∀ x∈source y,x.divisor⊆x.sourceCommon)
    (w : SecondParentSource ι Jo→ℂ) (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : SecondParentSource ι Jo→σ→Finset ι)
    (a₁ a₂ : σ→ι→ℂ) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    (∑ y∈parents,w y*secondExpansionSource p hp hcop hg pool Ψ
      (secondParentPuncture p m y) (secondParentLabel p y) (secondParentDivisor p y) z (source y)
      (fun U=>primeMark slots₁ (lists₁ y) a₁ U*W₁ (primeProductNorm p U/X))
      (fun U=>primeMark slots₂ (lists₂ y) a₂ U*W₂ (primeProductNorm p U/X)) Φ Y) =
    (Y:ℂ)*secondRayCoefficient z * ∑ x∈attachedSecondFamily parents source,
      (w (secondParentOf x)*actualSecondSignedWeight p hp hcop hg Ψ
        (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x)*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ (lists₁ (secondParentOf x)) (lists₂ (secondParentOf x)) a₁ a₂ W₁ W₂ Φ Y X := by
  rw [sum_attachedSecondFamily]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [secondExpansionSource_attached p hp hcop hg hinj hpr y (source y) (hE y hy)]
  rw [Finset.sum_image (fun x hx z hz he=>attachSecondExpansion_injective y he)]
  simp only [Finset.mul_sum,secondParentOf_attach]
  apply Finset.sum_congr rfl
  intro x hx
  ring

def parentPoisson (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (y : SecondParentSource ι Jo) : ℂ :=
  firstFreshSecondPoisson p hp hg hinj pool (quotientSupport p y) y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit negative
    (if negative then r.1 else r.2) Ψ m
    (primeMark (slots\J) (residualLists p negative lists y) a) ω X
    (∏ i∈y.firstCommon,p i) (secondParentDivisor p y) core t Y

theorem parentPoisson_attach (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (ω : ℝ→ℂ) (X t Y : ℝ) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (q : Source ι Jo × ((∀ i∈J,ι)×(∀ i∈J,ι))) :
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a ω X t Y r core (attach p J q)=
      priorityPoisson p hp hg hinj pool q.1.cube q.1.firstCommon negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) q.1.firstDivisor)
        slots J lists a ω X t Y r core q.1.quotientSupport := by
  unfold parentPoisson
  rw [quotientSupport_attach p hinj,residualLists_attach p hinj]
  rfl

def retainedRow (pool : Finset ι) (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : ℝ→ℂ) (X Y : ℝ) (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0) : ℂ :=
  actualSecondSignedWeight p hp hcop hg Ψ
    (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
    actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
      (slots\J) (slots\J) (residualLists p negative lists (secondParentOf x))
      (residualLists p negative lists (secondParentOf x)) a a V V rowMajorant Y X

theorem parentPoisson_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (y : SecondParentSource ι Jo) (pool : Finset ι)
    (hq : y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : Finset ι→Finset ι→ℝ) (label : Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := secondVariableCutoff p y R
    parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y =
      truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K := by
  intro Ψ₀ V H K
  have hsum : (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          actualSecondSignedWeight p hp hcop hg Ψ₀
            (m*ConcretePrimeRowBridge.idealGenerator x.quotient) ray x *
          actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m ray)
            (slots\J) (slots\J) (residualLists p negative lists y) (residualLists p negative lists y)
            a a V V rowMajorant Y X) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈(secondDyadicSector pool K residual label j).image (attachSecondExpansion y),
          retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x := by
    apply Finset.sum_congr rfl
    intro ray hray
    apply Finset.sum_congr rfl
    intro residual hresidual
    apply Finset.sum_congr rfl
    intro j hj
    apply congrArg ((Y:ℂ)*secondRayCoefficient ray * ·)
    apply Finset.sum_congr rfl
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    rfl
  have he := first_parent_full_second_source p hp hcop hg hinj hc hpr y pool (quotientSupport p y) hq
    negative (if negative then r.1 else r.2) Ψ m (slots\J) (residualLists p negative lists y) a
    (fun i _=>residualLists_disjoint p negative lists y i) om lo hi hlo hs X t Y hX hY core R label
  exact he.trans (congrArg (fun z : ℂ=>truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K + z +
    secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) H rowMajorant Y K) hsum)

omit [∀ i,(Ideal.span {p i}).IsMaximal] in

theorem retained_sum
    (pool : Finset ι) (parents : Finset (SecondParentSource ι Jo))
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ)
    (residual : Finset ι) (j : κ) (w : SecondParentSource ι Jo→ℂ)
    (H : MarkedSecondSource ι Jo 0→ℂ) :
    (∑ y∈parents,w y*∑ x∈(secondDyadicSector pool (secondVariableCutoff p y (R y))
      residual (label y) j).image (attachSecondExpansion y),H x) =
    ∑ x∈retainedPool p pool parents R label residual j,w (secondParentOf x)*H x := by
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h),Finset.mul_sum]
  rfl

omit [DecidableEq ι] [DecidableEq κ] in
private theorem commute_parent_sectors [Fintype κ]
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (H : SecondParentSource ι Jo→SecondRayIndex→Finset ι→κ→ℂ) :
    (∑ y∈parents,∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,H y ray residual j) =
    ∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,∑ y∈parents,H y ray residual j := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray hray
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro residual hresidual
  rw [Finset.sum_comm]

theorem parent_family_full [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (hpr : ∀ i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (hq : ∀ y∈parents,y.quotient=sourceIdeal p (quotientSupport p y))
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (om : 𝓢(ℝ,ℂ)) (lo hi : ℝ) (hlo : 0<lo) (hs : Function.support om⊆Set.Icc lo hi)
    (X t Y : ℝ) (hX : 0<X) (hY : 0<Y) (r : RayCharacter×RayCharacter) (core : FirstCoreIndex)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) :
    let Ψ₀ := firstCoreTwist negative (if negative then r.1 else r.2) Ψ core
    let V := principalWindow om lo hi hlo hs negative t
    let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
    let K := fun y=>secondVariableCutoff p y (R y)
    (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
    (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
      (Y:ℂ)*secondRayCoefficient ray *
        ∑ x∈retainedPool p pool parents R label residual j,
          w (secondParentOf x)*retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
    (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
  intro Ψ₀ V H K
  have he : (∑ y∈parents,w y*parentPoisson p hp hg hinj pool negative Ψ m slots J lists a om X t Y r core y) =
    ∑ y∈parents,w y*(truncatedSecondZero p hg pool Ψ₀ (secondParentPuncture p m y)
      (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y) +
      (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
        (Y:ℂ)*secondRayCoefficient ray *
          ∑ x∈(secondDyadicSector pool (K y) residual (label y) j).image (attachSecondExpansion y),
            retainedRow p hp hcop hg pool negative Ψ₀ m slots J lists a V X Y ray x) +
      secondSourceTail p hp hg hinj pool Ψ₀ (secondParentPuncture p m y)
        (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [parentPoisson_full p hp hcop hg hinj hc hpr y pool (hq y hy) negative Ψ m slots J lists a
      om lo hi hlo hs X t Y hX hY r core (R y) (label y)]
  rw [he]
  simp only [mul_add,Finset.sum_add_distrib]
  congr 1
  congr 1
  simp only [Finset.mul_sum]
  rw [commute_parent_sectors]
  apply Finset.sum_congr rfl
  intro ray hray
  apply Finset.sum_congr rfl
  intro residual hresidual
  apply Finset.sum_congr rfl
  intro j hj
  rw [retainedPool,sum_attachedSecondFamily]
  apply Finset.sum_congr rfl
  intro y hy
  rw [Finset.sum_image (fun _ _ _ _ h=>attachSecondExpansion_injective y h)]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [secondParentOf_attach]
  ring

def fullSource [Fintype κ]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (parents : Finset (SecondParentSource ι Jo)) (pool : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m : O)
    (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : SecondParentSource ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ)
    (R : SecondParentSource ι Jo→Finset ι→Finset ι→ℝ)
    (label : SecondParentSource ι Jo→Finset ι→SecondExpansionData ι→κ) : ℂ :=
  let H := fun y=>markedRadial p (slots\J) (residualLists p negative lists y) a ∅ V X
  let K := fun y=>secondVariableCutoff p y (R y)
  (∑ y∈parents,w y*truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y)) +
  (∑ ray : SecondRayIndex,∑ residual∈pool.powerset,∑ j : κ,
    (Y:ℂ)*secondRayCoefficient ray *
      ∑ x∈retainedPool p pool parents R label residual j,
        w (secondParentOf x)*retainedRow p hp hcop hg pool negative Ψ m slots J lists a V X Y ray x) +
  (∑ y∈parents,w y*secondSourceTail p hp hg hinj pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y) (H y) rowMajorant Y (K y))
