open InversePrioritySecondSource
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]{Jo:ℕ}
variable (p:ι→O)[∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem global_original_priority_slice
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)
    (H:Source ι Jo→ℂ):
    (∑x∈globalParentSource outer pool selector,
      globalPriorityOuter p hg negative Ψ m ray core
        (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*H x)=
    ∑x∈outer,∑D∈pool.powerset,
      (priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*H (fillFirstQuotient x D):=by
  rw [sum_globalParentSource outer pool selector houter]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector x D≠0
  · rw [ite_eq_left hs]
    simp only [globalPriorityOuter,erase_fillFirstQuotient,eraseFirstQuotient_eq _ (houter x hx)]
    dsimp only [fillFirstQuotient,priorityOuter]
    simp only [norm_one,mul_one,Complex.ofReal_mul]
    ring
  · rw [ite_eq_right hs,priorityOuter_zero p hg x.cube negative Ψ m (selector x) ray core D (not_ne_iff.mp hs)]
    simp

theorem global_second_energy_source
    (hp:∀i,p i≠0)(hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (outer:Finset (Source ι Jo))(pool:Finset ι)(selector:Source ι Jo→Finset ι→ℂ)
    (houter:∀x∈outer,x.quotientSupport=∅)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ):
    (∑x∈outer,firstWholePrioritySecondEnergy p hp hg hinj pool x.cube x.firstCommon
      (extra x.cube) negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.firstDivisor)
      slots lists a (selector x) om X t Y)=
    (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
      (∑x∈globalParentSource outer pool selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x)).re:=by
  have hs (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(J:Finset σ):
      (∑x∈globalParentSource outer pool selector,
        globalPriorityOuter p hg negative Ψ m ray core
          (fun x=>(‖selector (eraseFirstQuotient x) x.quotientSupport‖:ℂ)) x*
        (‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p x))=
      ∑x∈outer,∑D∈pool.powerset,(priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*
        (‖primeMark J lists a ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D)‖^2:ℝ)*
        wholePriorityPoisson p hp hg hinj pool x.cube x.firstCommon x.firstDivisor (extra x.cube)
          negative Ψ m slots J lists a om X t Y ray core D:=by
    simp_rw [mul_assoc]
    rw [global_original_priority_slice p hg outer pool selector houter negative Ψ m ray core]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro D hD
    have hm : wholeExtractedSupport (fun x=>extra x.cube) negative (fillFirstQuotient x D)=
        ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D) := by
      simp only [wholeExtractedSupport,extractedSupport,fillFirstQuotient,Finset.union_assoc]
    rw [hm]
    have hf : fillFirstQuotient x D = fixedPoint x.cube x.firstCommon x.firstDivisor x.oldAssigned D := by
      cases x;rfl
    rw [hf]
    change (priorityOuter p hg x.cube negative Ψ m (selector x) ray core D:ℂ)*
      ((‖primeMark J lists a ((extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪D)‖^2:ℝ)*
        parentPoisson p hp hg hinj pool negative Ψ m slots J (fun i=>lists i\extra x.cube)
          a om X t Y ray core (parent p (fixedPoint x.cube x.firstCommon x.firstDivisor x.oldAssigned D))) = _
    rw [parentPoisson_fixed_whole p hp hg hinj]
  simp_rw [hs]
  simp only [Complex.re_sum,Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  unfold firstWholePrioritySecondEnergy
  simp only [Finset.mul_sum,wholePriorityPoisson,priorityOuter]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro ray hray
  simp_rw [Finset.sum_comm (s:=pool.powerset) (t:=(Finset.univ : Finset FirstCoreIndex))]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro core hcore
  simp_rw [Finset.sum_comm (s:=pool.powerset) (t:=slots.powerset)]
  rw [Finset.sum_comm (s:=outer)]
  apply Finset.sum_congr rfl
  intro J hJ
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro D hD
  ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0775

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityRays
Source SHA256: b1ce98166a2232d803242503d19b460c90f2f5ab55cc32d00c78bd667d71839f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0776


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_retained_all_rays
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    global_priority_retained_moving_radius (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C*(512*32^2),Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff source Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤P:=by dsimp [P];positivity
  have hH:0≤H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤C*A*H*(512*32^2):=mul_le_mul_of_nonneg_left secondRayCoefficient_mass (by positivity)
    _= _:=by dsimp [H];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0776

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityAggregate
Source SHA256: 3736c72d9064ac21eee309f8a787c60cc675f5de4d6b438042e2b110db3ed965
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0777



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
def globalPriorityRetainedAggregate
    (p:ι→Eis)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))(w:InverseFirstPriorityParents.Source ι Jo→ℂ)
    (negative:Bool)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  (32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>R),
        globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a V X Y z x‖

theorem global_priority_retained_aggregate
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      slots.card≤K → 0≤A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff);
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤eta ∧
      2≤Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤Z ∧
      1≤b ∧
      b≤Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w
          negative Ψ m slots lists a (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    global_priority_retained_all_rays (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  let Ctot:=(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hslots hA hdata
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:=C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
    P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤H:=by
    obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
      ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
    exact he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a (fun _=>cutoff)
      Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
      haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hZ:1<Z:=(hdata 1 1 ∅ (Finset.empty_subset _)).2.2.2.1
  have hH:0≤H:=by dsimp [H];positivity
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
  change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤H at hb
  change P*((32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤_
  calc
    _=(32*512)*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hr
      apply Finset.sum_congr rfl
      intro core hc
      apply Finset.sum_congr rfl
      intro assigned ha
      ring
    _≤(32*512)*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ray _=>Finset.sum_le_sum fun core _=>Finset.sum_le_sum fun assigned ha=>hb ray core assigned (Finset.mem_powerset.mp ha)
    _=(32*512)*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
      ring
    _≤(32*512)*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
    _= _:=by dsimp [Ctot,H];ring
end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0777

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGates
Source SHA256: 19cae7af2acaf1917ab965da5183d4541c6b6c07a01390144b5bf2a61080f090
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0778




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def retainedSource (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) : Finset (MarkedSecondSource ι (Jo+(J.card+J.card)) 0) :=
  unifiedSource p pool (wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>cutoff)

lemma original_parent_witness
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,forgetAppended (Jo:=Jo) (secondParentOf x)=parent p y := by
  have hp := ((mem_unifiedSource p pool _ (fun _=>cutoff) x).mp hx).1
  obtain ⟨y,hy,q,hq,he⟩ := (mem_wholeAssignedParents p (fun x=>extra x.cube) original negative J lists _).mp hp
  exact ⟨y,hy,by simpa only [forget_attach] using congrArg (forgetAppended (Jo:=Jo)) he.symm⟩

lemma original_coordinates
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ)
    (x : MarkedSecondSource ι (Jo+(J.card+J.card)) 0)
    (hx : x∈retainedSource p extra original negative J lists pool cutoff) :
    ∃y∈original,x.cube=y.cube ∧ x.firstCommon=y.firstCommon ∧
      x.firstDivisor=y.firstDivisor ∧ x.quotient=sourceIdeal p y.quotientSupport ∧
      (∀i:Fin Jo,x.oldAssigned (Fin.castAdd (J.card+J.card) i)=y.oldAssigned i) := by
  obtain ⟨y,hy,he⟩ := original_parent_witness p extra original negative J lists pool cutoff x hx
  exact ⟨y,hy,congrArg SecondParentSource.cube he,congrArg SecondParentSource.firstCommon he,
    congrArg SecondParentSource.firstDivisor he,congrArg SecondParentSource.quotient he,
    fun i=>congrArg (fun z=>z.oldAssigned i) he⟩

lemma retained_conditions (hp : ∀i,p i≠0)
    (extra : CubeCoordinates ι→Finset ι) (original : Finset (Source ι Jo))
    (hvalid : ∀x∈original,SourceValid p x) (hextra : ∀x∈original,extra x.cube⊆x.cube.support)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (pool : Finset ι)
    (cutoff : Finset ι→Finset ι→ℝ) :
    ActualSecondSourceConditions p (retainedSource p extra original negative J lists pool cutoff) :=
  unified_conditions p hp extra original hvalid hextra negative J lists pool (fun _=>cutoff)

lemma original_numeric_gates (extra : CubeCoordinates ι→Finset ι)
    (original : Finset (Source ι Jo)) (negative : Bool) (J : Finset σ)
    (lists : σ→Finset ι) (pool : Finset ι) (cutoff : Finset ι→Finset ι→ℝ)
    (B A C Q JL JU D : ℝ)
    (hB₁ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤B)
    (hB₂ : ∀y∈original,‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤B)
    (hA : ∀y∈original,primeProductNorm p (cubeActiveSupport y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)≤A)
    (hC : ∀y∈original,primeProductNorm p y.firstCommon≤C)
    (hQ : ∀y∈original,primeProductNorm p y.quotientSupport≤Q)
    (hJ : ∀y∈original,JL≤‖eisEmbedding (jLabel p y.cube.support
      (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p y.cube.support (fun i=>y.cube.leftExponent i+y.cube.rightExponent i)
        y.cube.leftBit y.cube.rightBit)‖^2≤JU)
    (hD : ∀y∈original,primeProductNorm p y.firstDivisor≤D) :
    ∀x∈retainedSource p extra original negative J lists pool cutoff,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤B ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤B ∧
      primeProductNorm p (cubeActiveSupport x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)≤A ∧ primeProductNorm p x.firstCommon≤C ∧
      (Ideal.absNorm x.quotient:ℝ)≤Q ∧
      JL≤‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤JU ∧
      primeProductNorm p x.firstDivisor≤D := by
  intro x hx
  obtain ⟨y,hy,hb,hc,hd,hq,ho⟩ := original_coordinates p extra original negative J lists pool cutoff x hx
  rw [hb,hc,hd,hq]
  refine ⟨hB₁ y hy,hB₂ y hy,hA y hy,hC y hy,?_,(hJ y hy).1,(hJ y hy).2,hD y hy⟩
  simpa only [sourceIdeal,←eisEmbedding_norm_sq_eq_absNorm_span,primeProductNorm] using hQ y hy

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end OAIOriginalModule0778

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalRetainedGatesGeometry
Source SHA256: 7c0bf0e853b2efbda2d9e5797feaea69d2264518d91e5c7b104aff8896bd15b2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0779


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentGlobalRetainedGates
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityRetainedSource InversePrioritySecondSource InverseInitialArithmetic
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

lemma actual_profile_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (F : Finset ι) (x : SecondProfileData ι) (slots₁ slots₂ : Finset σ)
    (lists₁ lists₂ : σ→Finset ι) (a₁ a₂ : σ→ι→ℂ)
    (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (Y X b : ℝ) (hX : 0<X)
    (hW : ∀y,W₁ y≠0 → y≤b)
    (hgeom : b*X<primeProductNorm p x.common*primeProductNorm p x.overlap) :
    actualSecondProfileRow p hp hcop hg F x slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X=0 := by
  rw [actualSecondProfileRow_eq_whole]
  apply Finset.sum_eq_zero
  intro N hN
  apply Finset.sum_eq_zero
  intro M hM
  have hzero : W₁ (primeProductNorm p x.common*primeProductNorm p x.overlap*primeProductNorm p N/X)=0 := by
    by_contra hn
    have hh := (div_le_iff₀ hX).mp (hW _ hn)
    have hlo := le_mul_of_one_le_right
      (mul_nonneg (primeProductNorm_pos p hp x.common).le (primeProductNorm_pos p hp x.overlap).le)
      (primeProductNorm_ge_one p hp N)
    linarith
  simp [secondNormProfile,secondActualNorms,hzero]

lemma wholeRow_zero_of_geometry
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (W : ℝ→ℂ) (X Y b : ℝ) (hX : 0<X) (hW : ∀y,W y≠0 → y≤b)
    (ray : SecondRayIndex) (x : MarkedSecondSource ι Jo 0)
    (hgeom : b*X<primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap) :
    wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x=0 := by
  rw [wholeRow_eq]
  have hh := actual_profile_zero_of_geometry p hp hcop hg pool (secondInheritedProfile p x Ψ m ray)
    (slots\J) (slots\J) (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
    (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a W W rowMajorant Y X b hX hW hgeom
  rw [hh,mul_zero]

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
def geometrySource {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    Finset (MarkedSecondSource ι Jo Jn) :=
  source.filter (fun x=>primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X)

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_subset {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    geometrySource p source b X⊆source := Finset.filter_subset _ _

omit hp [∀i,(Ideal.span {p i}).IsMaximal] in
omit [DecidableEq ι] in
lemma geometrySource_gate {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (b X : ℝ) :
    ∀x∈geometrySource p source b X,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X :=
  fun _x hx=>(Finset.mem_filter.mp hx).2

lemma original_retained_geometry_sum
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    {Jo : ℕ} (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι)
    (source : Finset (MarkedSecondSource ι Jo 0)) (w : MarkedSecondSource ι Jo 0→ℂ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (W : ℝ→ℂ) (X Y b : ℝ)
    (hX : 0<X) (hW : ∀y,W y≠0 → y≤b) (ray : SecondRayIndex) :
    (∑x∈source,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x)=
    ∑x∈geometrySource p source b X,w x*wholeRow p hp hcop hg extra pool negative Ψ m slots J lists a W X Y ray x := by
  rw [geometrySource,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  split_ifs with hg₀
  · rfl
  · rw [wholeRow_zero_of_geometry p hp hcop hg extra pool negative Ψ m slots J lists a W X Y b hX hW
      ray x (lt_of_not_ge hg₀),mul_zero]

end SevenEighths.InverseMomentGlobalRetainedGates
end

end OAI
end OAIOriginalModule0779

/-! Original module: OAI.NumberTheory.DirichletL.Descent.GlobalPriorityFilteredEnergy
Source SHA256: 258765823be9f29960d6fb4d4d197e2af9fb9fd22f85148e0495b42ad390480f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0780





namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open FourierBridge CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion FirstCauchyArithmetic
local notation "Eis"=>ActualEisensteinCubic.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_filtered_moving_radius
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤B₀ i) (K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (ω₁ ω₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤hiFresh ∧ HasCompactSupport (ω₁:ℝ→ℂ) ∧ HasCompactSupport (ω₂:ℝ→ℂ) ∧
      tsupport (ω₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (ω₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∀ J:ℕ, ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, ConcretePrimeRowBridge.goodLambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let originalSource:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀(z:SecondRayIndex)
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
    let source:=InverseMomentGlobalRetainedGates.geometrySource p originalSource b X;
      hi≤b →
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤eta → 2≤Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ConcreteTraceCRT.eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ConcreteTraceCRT.eisEmbedding (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤Z → 1≤b → b≤Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤pi) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hp hcop hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest ω₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖(Y:ℂ)*secondRayCoefficient z *
        ∑x∈originalSource,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*‖secondRayCoefficient z‖*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,hordered⟩:=
    actual_priority_retained_moving_radius_window_order (ι:=ι) (σ:=σ) om rowMajorant lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ K εmass hεmass
  refine ⟨ω₁,ω₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,?_⟩
  intro J
  obtain ⟨C,Cbin,hC,hCbin,he⟩:=hordered J
  refine ⟨coefficientBound*C,Cbin,mul_nonneg coefficientBound_pos.le hC,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff originalSource Ψ₀ z
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A source hhib
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hsub:source⊆originalSource:=InverseMomentGlobalRetainedGates.geometrySource_subset p originalSource b X
  have hsource:ActualSecondSourceConditions p source:=
    ActualSecondSourceConditions.mono p (unified_conditions p hp extra original hvalid hextra negative assigned lists pool cutoff) hsub
  have hd:∀x∈source,∀i∈InverseMomentWholeRetainedSource.deleted p extra negative x,
      i∈x.cube.support∪x.firstCommon ∨ (Ideal.span {p i}:Ideal Eis)∣x.quotient:=
    fun x hx=>unified_deleted_support p hinj extra original hvalid hextra negative assigned lists pool cutoff x (hsub hx)
  have hw:∀x∈source,‖normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x‖≤1:=
    fun x hx=>normalizedGlobalPriorityWeight_norm p hg hinj extra original pool negative Ψ m ray core w hwOriginal hΨ
      assigned lists a haassigned cutoff x (hsub hx)
  have hΨ₀:∀n,‖Ψ₀ n‖≤1:=fun n=>(firstCoreTwist_norm_le negative (if negative then ray.1 else ray.2)
    Ψ core n).trans (hΨ n)
  have he₀:=he p hp hcop hg hpr hinj hc source hsource pool Ψ₀ m z (slots\assigned) (slots\assigned)
    lists lists a a (InverseMomentWholeRetainedSource.deleted p extra negative)
    (InverseMomentWholeRetainedSource.deleted p extra negative)
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t
    (normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a) labels A
    hd hd hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ₀ hw
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hrow:∀x:MarkedSecondSource ι (Jo+(assigned.card+assigned.card)) 0,wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
      (principalWindow om lo hi hlo hsupport negative t) X Y z x=
      actualSecondSignedWeight p hp hcop hg Ψ₀ (m*ConcretePrimeRowBridge.idealGenerator x.quotient) z x*
      actualSecondProfileRow p hp hcop hg pool (secondInheritedProfile p x Ψ₀ m z)
        (slots\assigned) (slots\assigned)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x)
        (fun i=>lists i\InverseMomentWholeRetainedSource.deleted p extra negative x) a a
        (principalWindow om lo hi hlo hsupport negative t) (principalWindow om lo hi hlo hsupport negative t)
        rowMajorant Y X:=fun x=>wholeRow_eq p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a _ X Y z x
  have hupper:∀y,principalWindow om lo hi hlo hsupport negative t y≠0 → y≤b:=by
    intro y hy
    have hy':y∈Function.support om:=by
      rw [←principalWindow_support om lo hi hlo hsupport negative t]
      exact hy
    exact (hsupport hy').2.trans hhib
  rw [InverseMomentGlobalRetainedGates.original_retained_geometry_sum p hp hcop hg extra pool originalSource
    (globalPriorityWeight p hg negative Ψ m ray core w assigned a) negative Ψ₀ m slots assigned lists a
    (principalWindow om lo hi hlo hsupport negative t) X Y b hX hupper z]
  rw [globalPriority_sum_normalized p hg negative Ψ m ray core w assigned a source]
  rw [show (Y:ℂ)*secondRayCoefficient z*((coefficientBound:ℂ)*
      ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x)=
      (coefficientBound:ℂ)*((Y:ℂ)*secondRayCoefficient z*
        ∑x∈source,normalizedGlobalPriorityWeight p hg negative Ψ m ray core w assigned a x*
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x) by ring]
  rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg coefficientBound_pos.le]
  simp_rw [hrow,←mul_assoc]
  convert mul_le_mul_of_nonneg_left he₀ coefficientBound_pos.le using 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0780
