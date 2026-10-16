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
      1<Z → 2≤Z^eta → 0≤M → M≤Mmax → 0≤ell → 0≤V → -eta≤r → r+3*ell+V≤Fmax →
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
          (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)‖≤
      Ctail*Γ*G₁*G₂*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  let saving':=saving+4*Fmax+14*eta
  obtain ⟨s,Ct,Cm,hCt,hCm,hloc⟩:=first_whole_cube_rapid_physical_tail 1 (by norm_num)
    Mmax Fmax eta tau saving' hMm hFm heta htau
  obtain ⟨Ca,hCa,hagg⟩:=full_first_tail_from_local 1 (by norm_num)
  refine ⟨s,Ca*65536*Cm^2*Ct,by positivity,?_⟩
  intro ι σ _ _ p hp _ hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂ slots lists weights extra₁ extra₂
    test₁ test₂ W Z M r ell V Γ G₁ G₂ hZ hbin hM hMmax hell hV hr hwhole hΓ hG₁ hG₂ hΨ₁ hΨ₂
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
        (firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau) D‖≤E:=by
    have hCB:Disjoint C b.support:=Finset.disjoint_left.mpr (fun i hi hib=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp (Finset.mem_filter.mp hC).1) hi)).2 hib)
    have hupper (x:ℝ) (hx:1≤x):x≤Z^(firstDyadicExponent Z x+eta):=
      (first_dyadic_bounds Z eta x hZ hbin hx).2.2
    have hlower (x:ℝ) (hx:1≤x):Z^(firstDyadicExponent Z x-eta)≤x:=by
      exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith : firstDyadicExponent Z x-eta≤firstDyadicExponent Z x)).trans
        (first_dyadic_bounds Z eta x hZ hbin hx).2.1
    have hjpos:0<‖eisEmbedding (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2:=
      SecondPassIntegration.elementNorm_pos _ (primeProduct_ne_zero p hp _ _)
    have he:=hloc p hp hinj hcop hg hc pool b C D (extra₁ b) (extra₂ b) I Ψ₁ Ψ₂ m₁ m₂
      slots lists weights (test₁ b) (test₂ b) W (B^2) G₁ G₂ Z M r ell V
      (firstDyadicExponent Z (primeProductNorm p C))
      (firstDyadicExponent Z (‖eisEmbedding (jLabel p b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))
      (fun D=>firstDyadicExponent Z (primeProductNorm p D))
      (hadm b hb) hCB (Finset.mem_powerset.mp hD) (hI0 I hI) (sq_nonneg _) hG₁ hG₂ hZ.le hM hMmax
      hell hV hr hwhole (Finset.mem_filter.mp hC).2 (hextra extra₁ he₁ b hb) (hextra extra₂ he₂ b hb)
      hΨ₁ hΨ₂ hslots hw (ht₁ b hb) (ht₂ b hb) (hs₁ b hb) (hs₂ b hb) (hb₁ b hb) (hb₂ b hb) (hIF I hI)
      (hupper _ (primeProductNorm_ge_one p hp D)) (hlower _ (primeProductNorm_ge_one p hp C))
      (hlower _ (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)))
    simpa only [firstLocalPhysicalTail,firstDyadicPhysicalCutoff,firstDyadicRadius,Real.rpow_one,E,L] using he
  have he:=hagg p hp hinj hcop hg hc pool bs labels a Ψ₁ Ψ₂ m₁ m₂
    (fun b U=>primeMark slots lists weights (extra₁ b∪U)*test₁ b U)
    (fun b U=>primeMark slots lists weights (extra₂ b∪U)*test₂ b U) W (Z^M) B L (Z^(V+eta)) Γ E
    (fun b C I=>firstDyadicPhysicalCutoff p b C I Z M r ell V eta tau)
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
end OAIOriginalModule0814

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicOriginalBranches
Source SHA256: 99daa5d838b03b7eb8da4b8cdf6a414ca3a3500e3e5477b0bc47aa0ad6f6815c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0815



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic EisensteinSchwartzPoisson
open ConcreteTraceCRT (eisEmbedding)
open CompletedHeight SecondPassIntegration FourierBridge
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_zero_tail
    (om:𝓢(ℝ,ℂ))(b Mmax Fmax eta tau saving eps:ℝ)
    (hs:∀y,om y≠0→y≤b)(hMm:0≤Mmax)(hFm:0≤Fmax)(heta:0≤eta)(htau:0<tau)(heps:0<eps):
    ∃Czero Ctail:ℝ,0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta:ℝ),
      1<Z→2≤Z^eta→0≤M→M≤Mmax→0≤ell→0≤V→ (-eta≤r) → (r+3*ell+V≤Fmax)→0≤Γ→b≤Z^eta→
      (∀u,‖Ψ u‖≤1)→(∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))→
      (∀I∈labels,I≠0)→(∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))→
      (∀I∈labels,∀v∈Q,‖β I v‖≤Γ)→
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀q∈lists i,‖weights i q‖≤1)→
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let mark:=fun (v:ι→₀ℕ) U=>primeMark slots lists weights (v.support∪U);
      Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualZero p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M))‖≤
          Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta)) ∧
      ‖reopenedPhysicalSourceSum pool Q labels β (fun q C I=>
        canonicalCubeDualTail p hp hcop hg pool q C Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (firstDyadicPhysicalCutoff p q C I Z M r ell V eta tau))‖≤Ctail*Γ^2*Z^(-saving):=by
  obtain ⟨Cz,hCz,hzero⟩:=original_first_zero_physical eps heps
  obtain ⟨s,Ct,hCt,htail⟩:=full_first_dyadic_marked_rapid_tail Mmax Fmax eta tau saving hMm hFm heta htau
  let G:=SchwartzMap.seminorm ℝ 0 0 om
  let Cz':=Cz*G^2*‖paperRadialFourier rowMajorant 0‖
  let Ct':=Ct*G^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) rowMajorant)
  refine ⟨Cz',Ct',by dsimp [Cz'];positivity,by dsimp [Ct'];positivity,?_⟩
  intro ι σ _ _ p hp _ hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ hbin hM hMmax hell hV hr hF hΓ hb hΨ hQ hn hlabels hβ hslots hw W mark
  have hz:0<Z:=zero_lt_one.trans hZ
  have hG:0≤G:=apply_nonneg _ _
  have hW:∀U,‖W (primeProductNorm p U)‖≤G:=by
    intro U
    simp only [W,normTwistedSource,norm_mul,logPhase_norm,one_mul]
    exact om.norm_le_seminorm ℝ _
  have hsupport:∀U,W (primeProductNorm p U)≠0→primeProductNorm p U≤Z^(r+eta):=by
    intro U hU
    have hnon:om (primeProductNorm p U/Z^r)≠0:=by
      intro hh
      exact hU (by simp [W,normTwistedSource,hh])
    have hle:primeProductNorm p U≤b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hnon)
    apply hle.trans
    calc
      b*Z^r≤Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  have hzero':=hzero p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights W rowMajorant
    Z M r ell V eta Γ G hZ (by linarith) (by linarith) hΓ hG hΨ hQ hn hlabels hβ hslots hw hW hsupport
  have hcb:=reopenedCubeFamily_cube_norms p Q _ hQ
  have htail':=htail p hp hinj hcop hg hc pool (reopenedCubeFamily Q) labels (reopenedPairCoefficient β)
    Ψ Ψ m m slots lists weights (fun q=>q.rightExponent.support) (fun q=>q.leftExponent.support)
    (fun _ U=>W (primeProductNorm p U)) (fun _ U=>W (primeProductNorm p U)) rowMajorant Z M r ell V
    (Γ^2) G G hZ hbin hM hMmax hell hV hr hF (sq_nonneg _) hG hG hΨ hΨ
    (reopenedCubeFamily_admissible Q) (fun q hq=>(hcb q hq).1) (fun q hq=>(hcb q hq).2)
    hn hlabels (fun q hq C _ I hI=>reopenedPairCoefficient_bound Q labels β Γ hΓ hβ q hq C I hI)
    hslots hw (fun _ _=>Finset.subset_union_right) (fun _ _=>Finset.subset_union_left)
    (fun _ _=>hW) (fun _ _=>hW) (fun _ _=>hsupport) (fun _ _=>hsupport)
  constructor
  · simpa only [mark,Finset.union_comm,Cz',G,mul_assoc,mul_left_comm,mul_comm] using hzero'
  · simpa only [mark,reopenedPhysicalSourceSum,Ct',pow_two,mul_assoc,mul_left_comm,mul_comm] using htail'

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0815

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileParents
Source SHA256: 93b7649722527cbd1febb65b8ed34469e87b3618a8da4a505be79fd0915b73c9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0816



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows ActualEisensteinCubic
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_eq_caps : originalNorms p=InverseFirstGlobalCaps.originalNorms p := by
  funext x i
  fin_cases i <;> rfl

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalOuterCell_eq_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k=InverseFirstGlobalCaps.outerCell p pool Q k := by
  unfold originalOuterCell InverseFirstGlobalCaps.outerCell InverseFirstGlobalCaps.outerGate
  ext x
  simp only [Finset.mem_filter,originalNorms_eq_caps,InverseFirstGlobalCaps.originalNorms_outer]

lemma originalChildEnergy_eq_caps (hp : ∀i,p i≠0)
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) :
    originalChildEnergy p hp hg hinj pool Q k l negative Ψ m mark omega T t Y=
      ∑x∈InverseFirstGlobalCaps.outerCell p pool Q k,
        firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
          (mark (if negative then x.1.rightExponent else x.1.leftExponent))
          (commonSelector p (fun _=>1) l) omega T t Y := by
  rw [originalChildEnergy,originalOuterCell_eq_caps]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0816

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveSource
Source SHA256: e975d02319fa24fd2ca5a6d668de210e56cddeadbd9209f498ca4ddc6e38b9a2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0817


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def refinedOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (gate : FirstOriginalOuter ι→Prop) : Finset (FirstOriginalOuter ι) :=
  (originalOuterCell p pool Q k).filter gate

def refinedSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) : Finset (OriginalIndex ι) :=
  (sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k).filter
      (fun x=>gate x.1 ∧ firstOriginalWeight p β cutoff x.1 x.2≠0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedSource_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) :
    refinedSource p pool Q labels β cutoff Y k gate⊆sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k :=
  Finset.filter_subset _ _

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_weight_frequency (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (x : OriginalIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2≠0) :
    x.2.2∈reopenedPhysicalCutoff p x.1.1 x.2.1 (cutoff x.1.1 x.1.2.1 x.2.1) x.1.2.2 := by
  by_contra hh
  exact hx (by simp [firstOriginalWeight,hh])

theorem refined_source_radius (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ysource Ychild : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop)
    (hn : ∀I∈labels,I≠0)
    (hcut : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤Ychild) :
    refinedSource p pool Q labels β cutoff Ysource k gate⊆
      firstGlobalRetainedSource p (refinedOuter p pool Q k gate) (fun _=>labels) (fun x=>x.1) Ychild := by
  intro x hx
  obtain ⟨hxcell,hgate,hweight⟩ := Finset.mem_filter.mp hx
  have hxold := original_cell_subset p pool Q labels Ysource k hxcell
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxold
  have hm := (mem_firstRetainedSource p labels x.1.1 Ysource x.2).mp hf
  have houter : x.1∈refinedOuter p pool Q k gate := Finset.mem_filter.mpr ⟨ho,hgate⟩
  have hE := firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hn x.2.1 hm.1)
  apply Finset.mem_sigma.mpr
  refine ⟨houter,(mem_firstRetainedSource p labels x.1.1 Ychild x.2).mpr ⟨hm.1,?_⟩⟩
  apply Finset.mem_erase.mpr
  refine ⟨(Finset.mem_erase.mp hm.2).1,?_⟩
  apply (mem_childFrequencyBall _ hE Ychild x.2.2).mpr
  exact ((mem_childFrequencyBall _ hE _ x.2.2).mp
    (original_weight_frequency p β cutoff x hweight)).trans (hcut x.1 houter x.2.1 hm.1)

def labelGate (j : ℕ) (x : FirstOriginalOuter ι) : Prop :=
  InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedOuter_label (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (j : ℕ) :
    refinedOuter p pool Q k (labelGate p j)=
      (InverseFirstGlobalCaps.outerCell p pool Q k).filter
        (fun x=>InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j) := by
  rw [refinedOuter,originalOuterCell_eq_caps]
  ext x
  simp [labelGate]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0817

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveEnergy
Source SHA256: 92e1c04ac63cfbdac5a625c912f528184fe9fcc7b8e36aff4c00a371206b03f2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0818





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]

def refinedChildEnergy (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (gate : FirstOriginalOuter ι→Prop) (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) : ℝ :=
  ∑x∈refinedOuter p pool Q k gate,
    firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
      (mark (if negative then x.1.rightExponent else x.1.leftExponent))
      (commonSelector p (fun _=>1) l) omega T t Y

def refinedCellRows (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
    (refinedSource p pool Q labels β cutoff Y k gate)
    pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) W₁ W₂ Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s

theorem original_refined_cell_physical_budget (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ : ℝ)
    (hm₁ : 0≤m₁) (hm₂ : 0≤m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) :
    ∃(omega₁ omega₂ : 𝓢(ℝ,ℂ))(lo hi : ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁ : ℝ→ℂ) ∧ HasCompactSupport (omega₂ : ℝ→ℂ) ∧
      tsupport (omega₁ : ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂ : ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀(ε : ℝ),0<ε→∀(Aker J : ℕ),∃ Cprofile Kpush : ℝ,0≤Cprofile ∧ 0<Kpush ∧
    ∀{ι : Type*}[DecidableEq ι](p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
      (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
      (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Γ Ysource Y : ℝ)
      (_hΨ : ∀u,‖Ψ u‖≤1) (_hΓ : 0≤Γ) (_hY : 0<Y)
      (_hsf : ∀I∈labels,Squarefree I) (_hn : ∀I∈labels,I≠0)
      (_hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop)
      (_hcutoff : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤Y)
      (T₁ T₂ K theta L : ℝ)
      (_hT₁ : 0<T₁) (_hT₂ : 0<T₂) (_hK : 0<K) (_hL : 0≤L)
      (Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta : ℝ)
      (_hB : 0≤Benergy) (_hZ : 0<Z)
      (_hscale : rawScales k l T₁ T₂=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
      (_hLe : L=eta*Real.log Z)
      (_hleft : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate true Ψ m mark omega₁ T₁
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
      (_hright : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate false Ψ m mark omega₂ T₂
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Ysource (rawScales k l T₁ T₂)‖≤
        ((Γ^2*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖-theta‖)^InverseClippingProfiles.momentOrder J*
          (1+‖theta‖)^InverseClippingProfiles.momentOrder J)/
          (1+K*(rawScales k l T₁ T₂) 6/((rawScales k l T₁ T₂) 3*(rawScales k l T₁ T₂) 4*
            ((rawScales k l T₁ T₂) 5)^2*T₁*T₂))^Aker)) := by
  obtain ⟨w₁,w₂,U,M₀,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,hM,hUc,hUs,hwin⟩ :=
    original_cell_windows g₁ g₂ m₁ m₂ 1 (fun _=>0) hm₁ hm₂ hg₁ hg₂ (fun _=>le_rfl)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro ε hε Aker J
  obtain ⟨Cprofile,Kpush,hC,hKp,he⟩ := actual_first_original_subset_physical_budget
    ε hε U g₁ g₂ Φ M₀ (fun _=>0) m₁ m₂ 1
    hM (fun _=>le_rfl) hUs hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hC,hKp,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Ysource Y hΨ hΓ hY hsf hn hβ
    k l gate hcutoff T₁ T₂ K theta L hT₁ hT₂ hK hL Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hB hZ hscale hLe hleft hright
  let source := refinedSource p pool Q labels β cutoff Ysource k gate
  have hgates := hwin p hp hg pool Q labels Ysource (coefficient p hp hcop hg Ψ m mark true)
    (coefficient p hp hcop hg Ψ m mark false) k l T₁ T₂ (fun _=>0) 1 1 (-theta) theta
    hT₁ hT₂ (by intro i;simp) le_rfl le_rfl le_rfl le_rfl
  have hb := he p hp hg hinj hcop hc hpr pool (refinedOuter p pool Q k gate) (fun x=>x.1) (fun x=>x.2.1)
    Ψ Ψ m m (divisorElement p) (fun x=>mark x.1.rightExponent) (fun x=>mark x.1.leftExponent)
    (fun _=>commonSelector p (fun _=>1) l) (fun _=>labels) (firstOriginalWeight p β cutoff) (Γ^2) Y
    hΨ hΨ (sq_nonneg _) hY (fun _ _=>hsf) (fun _ _=>hn)
    (fun x hx=>original_weight_bound p pool Q labels β cutoff Γ Y hΓ hβ x (original_outer_cell_subset p pool Q k (Finset.mem_filter.mp hx).1))
    w₁ w₂ (fun _=>0) 1 1 (-theta) theta (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    K L hK (rawScales k l T₁ T₂) (rawScales_pos k l T₁ T₂ hT₁ hT₂)
    source (refined_source_radius p hp pool Q labels β cutoff Ysource Y k gate hn hcutoff)
    (fun x hx=>original_source_positive p hp pool Q labels Ysource x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (by intro i;simp) le_rfl le_rfl le_rfl le_rfl hL
    (fun x hx=>hgates.1 x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hgates.2.1 x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hgates.2.2 x (Finset.mem_filter.mp hx).1)
    Benergy hB Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe
    (by simpa [refinedChildEnergy,rawScales] using hleft)
    (by simpa [refinedChildEnergy,rawScales] using hright)
  unfold refinedCellRows
  unfold SevenEighths.InverseMomentFirstOriginalProfile.coefficient SevenEighths.InverseMomentFirstOriginalProfile.weight
  simpa [source,rawScales] using hb

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0818

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveIdentity
Source SHA256: 297ce90bdbf7146e90c2326698ded1d4a93b092b13d8ec3926be769b09ef0f87
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0819


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_refined_cell_profile_identity (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (s : Fin 9→ℝ) (hs : ∀i,0<s i)
    (hleft : s 0*s 2*s 5*s 7=X) (hright : s 1*s 2*s 5*s 8=X) :
    let source := refinedSource p pool Q labels β cutoff Y k gate
    (∑x∈source,∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) l j.2.1*
      sourceSummand p hp hcop hg β cutoff Ψ m mark
        (fun y=>normTwistedSource om theta (y/X)) Φ K x j)=
    refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
      (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
      (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y s := by
  intro source
  let W₁ := fun y=>star (normTwistedSource om theta ((s 0*s 2*s 5*s 7)*y/X))
  let W₂ := fun y=>normTwistedSource om theta ((s 1*s 2*s 5*s 8)*y/X)
  have he := original_family_profiles p hp hg source pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hp hcop hg Ψ m mark true) (coefficient p hp hcop hg Ψ m mark false)
    (weight p hp hcop hg β cutoff Ψ m) om a b ha hsom Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K X theta
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s hs
    (by intro x hx;have hh:=original_source_positive p hp pool Q labels Y x (Finset.mem_filter.mp (refinedSource_subset p pool Q labels β cutoff Y k gate hx)).1
        exact ⟨hh.1,hh.2.1,hh.2.2.1⟩) hX hleft hright
  change _=firstFamilyPhysicalRows p hg source pool _ _ _ _ _ _ Φ _ _ _ _ K _ _ s
  rw [←he]
  have hl : s 0*s 2*s 5*s 7≠0 := hleft.trans_ne (ne_of_gt hX)
  have hr : s 1*s 2*s 5*s 8≠0 := hright.trans_ne (ne_of_gt hX)
  simp only [firstFamilyPhysicalRows,firstBlockedPhysicalRows,sourceSummand,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro j hj
  simp only [firstNormProfile,mul_div_cancel₀ _ hl,mul_div_cancel₀ _ hr]
  ring

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0819

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLivePartition
Source SHA256: 7d18bebe006de1ccff06a06c13d00baf0445b5db45f42da70e76e1857d5e3b96
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0820



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

abbrev JointKey := SourceIndex × ℕ × ℕ

def jointKey (x : OriginalIndex ι) (j : FirstCommonIndex ι) : JointKey :=
  (sourceIndex (originalNorms p) x,dyadIndex (primeProductNorm p j.2.1),
    dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))

def liveJointKeys (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) : Finset JointKey :=
  ((S×ˢfirstCommonIndices pool).filter (fun x=>term x.1 x.2≠0)).image
    (fun x=>jointKey p x.1 x.2)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma sum_live_joint_cells (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) :
    (∑x∈S,∑j∈firstCommonIndices pool,term x j)=
      ∑k∈liveJointKeys p S pool term,∑x∈S,∑j∈firstCommonIndices pool,
        if jointKey p x j=k then term x j else 0 := by
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : term x j=0
  · simp [hz]
  · have hk : jointKey p x j∈liveJointKeys p S pool term :=
      Finset.mem_image.mpr ⟨(x,j),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hx,hj⟩,hz⟩,rfl⟩
    simp [hk]

lemma sourceSummand_zero_of_weight (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ)
    (x : OriginalIndex ι) (j : FirstCommonIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2=0) :
    sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K x j=0 := by
  simp [sourceSummand,weight,retainedCubeWeight,hx]

lemma joint_cell_eq_refined (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (k : JointKey) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    (∑x∈S,∑j∈firstCommonIndices pool,if jointKey p x j=k then term x j else 0)=
      ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
        ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  simp only [refinedSource,sourceCell,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hw : firstOriginalWeight p β cutoff x.1 x.2=0
  · have ht : ∀j,term x j=0 := fun j=>sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hw
    simp [ht,hw]
  · by_cases hs : sourceIndex (originalNorms p) x=k.1
    · by_cases hj : dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)=k.2.2
      · simp [jointKey,hs,hj,labelGate,hw,Prod.ext_iff,commonSelector,ite_mul]
      · simp [jointKey,hs,hj,labelGate,Prod.ext_iff]
    · simp [jointKey,hs,Prod.ext_iff]

theorem original_retained_joint_partition (hp : ∀i,p i≠0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ)
    (s : Fin 9→ℝ) (hs : ∀i,0<s i) :
    let S := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s=
      ∑k∈liveJointKeys p S pool term,
        ∑x∈refinedSource p pool Q labels β cutoff Y k.1 (labelGate p k.2.2),
          ∑j∈firstCommonIndices pool,commonSelector p (fun _=>1) k.2.1 j.2.1*term x j := by
  intro S term
  rw [original_retained_sum p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff s hs,
    sum_live_joint_cells p S pool term]
  apply Finset.sum_congr rfl
  intro k hk
  exact joint_cell_eq_refined p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y k

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0820

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveCount
Source SHA256: b26085349e953084f255d78e1b664844b6c7a8edf201d3647a6e66870f1aded5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0821


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels InverseMomentFirstChildWindows InverseSecondSourceBlocks
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (B : ℕ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,sourceIndex (originalNorms p) x i≤B) ∧
      dyadIndex (primeProductNorm p j.2.1)≤B ∧
      dyadIndex (InverseFirstGlobalCaps.jNorm p x.1)≤B) :
    (liveJointKeys p S pool term).card≤(B+1)^8 := by
  let box := (Fintype.piFinset (fun _ : Fin 6=>Finset.range (B+1))) ×ˢ
    (Finset.range (B+1) ×ˢ Finset.range (B+1))
  have hsub : liveJointKeys p S pool term⊆box := by
    intro k hk
    obtain ⟨⟨x,j⟩,hm,rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hm,hn⟩ := Finset.mem_filter.mp hm
    obtain ⟨hx,hj⟩ := Finset.mem_product.mp hm
    obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
    exact Finset.mem_product.mpr ⟨Fintype.mem_piFinset.mpr
      (fun i=>Finset.mem_range.mpr (Nat.lt_succ_of_le (h₁ i))),
      Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le h₂),
        Finset.mem_range.mpr (Nat.lt_succ_of_le h₃)⟩⟩
  have hc : box.card=(B+1)^8 := by
    simp only [box,Finset.card_product,Fintype.card_piFinset,Finset.card_range,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
    ring
  exact hc ▸ Finset.card_le_card hsub

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem liveJointKeys_card_of_norm_cap (S : Finset (OriginalIndex ι)) (pool : Finset ι)
    (term : OriginalIndex ι→FirstCommonIndex ι→ℂ) (R : ℝ)
    (hcap : ∀x∈S,∀j∈firstCommonIndices pool,term x j≠0→
      (∀i,0<originalNorms p x i ∧ originalNorms p x i≤R) ∧
      (0<primeProductNorm p j.2.1 ∧ primeProductNorm p j.2.1≤R) ∧
      (0<InverseFirstGlobalCaps.jNorm p x.1 ∧ InverseFirstGlobalCaps.jNorm p x.1≤R)) :
    (liveJointKeys p S pool term).card≤(dyadIndex R+1)^8 := by
  apply liveJointKeys_card
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := hcap x hx j hj hn
  have hm : ∀a : ℝ,0<a→a≤R→dyadIndex a≤dyadIndex R := fun a ha haR=>
    Nat.floor_mono (Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2) ha haR)
  exact ⟨fun i=>hm _ (h₁ i).1 (h₁ i).2,hm _ h₂.1 h₂.2,hm _ h₃.1 h₃.2⟩

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0821

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveAggregate
Source SHA256: faed28f9969dada68082fe126ed44bb25e047088049c7a15988191f30eecfc1e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0822




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform CompletedHeight
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem original_retained_joint_profile_bound (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (om : 𝓢(ℝ,ℂ)) (a b : ℝ) (ha : 0<a) (hsom : Function.support om⊆Set.Icc a b)
    (Φ : 𝓢(ℝ,ℂ)) (K Y X theta : ℝ) (hX : 0<X)
    (reference : Fin 9→ℝ) (href : ∀i,0<reference i) :
    let source := firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y
    let W := fun y=>normTwistedSource om theta (y/X)
    let term := sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K
    ‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff reference‖≤
      ∑k∈liveJointKeys p source pool term,
        ‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
          (positiveSource (priorityLogWindow om a b ha hsom true) 1 (-theta))
          (positiveSource (priorityLogWindow om a b ha hsom false) 1 theta) Φ K Y (physicalScales X k.1 k.2.1)‖ := by
  intro source W term
  rw [original_retained_joint_partition p hp hcop hg pool Q labels β cutoff Ψ m mark W Φ K Y reference href]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro k hk
  have hp₁ := (physicalScales_products X k.1 k.2.1).1
  have hp₂ := (physicalScales_products X k.1 k.2.1).2
  rw [original_refined_cell_profile_identity p hp hcop hg pool Q labels β cutoff Ψ m mark om a b ha hsom
    Φ K Y X theta hX k.1 k.2.1 (labelGate p k.2.2) (physicalScales X k.1 k.2.1) (physicalScales_pos X hX k.1 k.2.1) hp₁ hp₂]

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0822

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveSupport
Source SHA256: f4669ce94c5c695cee83a31b7a83e816cd1e1a5eb71e3406a2ecd640e44b7065
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0823




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
variable (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
variable (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

def liveNormCap (L B Y : ℝ) : ℝ := max Y (max L (max (L*B^2) (B^2)))

theorem original_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K L B : ℝ)
    (hB : 0≤B) (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤L) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K)).card≤
        (dyadIndex (liveNormCap L B Y)+1)^8 := by
  apply liveJointKeys_card_of_norm_cap
  intro x hx j hj hn
  obtain ⟨h₁,h₂,h₃⟩ := InverseMomentFirstLiveCaps.original_live_norm_caps p hp hcop hg
    pool Q labels Y β cutoff Ψ m mark W Φ K L B hB hQ hlabels hW x hx j hn
  have hc : ∀i : Fin 6,(![L,L,L,L*B^2,B^2,Y] : Fin 6→ℝ) i≤liveNormCap L B Y := by
    intro i
    fin_cases i <;> simp [liveNormCap,le_max_iff]
  refine ⟨fun i=>⟨lt_of_lt_of_le zero_lt_one (original_source_norms_ge_one p hp pool Q labels Y x hx i),(h₁ i).trans (hc i)⟩,?_,?_⟩
  · exact ⟨primeProductNorm_pos p hp _,h₂.trans (le_max_of_le_right (le_max_left _ _))⟩
  · refine ⟨lt_of_lt_of_le zero_lt_one (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _)),?_⟩
    exact h₃.trans (le_max_of_le_right (le_max_of_le_right (le_max_right _ _)))

theorem original_twisted_live_joint_card (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (labels : Finset (Ideal O)) (Y : ℝ) (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (W : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K b B X theta : ℝ)
    (hX : 0<X) (hB : 0≤B) (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤B)
    (hlabels : ∀I∈labels,I≠0) (hW : ∀y,W y≠0→y≤b) :
    (liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark
        (fun y=>CompletedHeight.normTwistedSource W theta (y/X)) Φ K)).card≤
        (dyadIndex (liveNormCap (b*X) B Y)+1)^8 := by
  apply original_live_joint_card p hp hcop hg pool Q labels Y β cutoff Ψ m mark _ Φ K (b*X) B hB hQ hlabels
  intro y hy
  have hwy : W (y/X)≠0 := by
    intro hz
    exact hy (by simp [CompletedHeight.normTwistedSource,hz])
  exact (div_le_iff₀ hX).mp (hW _ hwy)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0823

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveCountBudget
Source SHA256: 54ed9036e79aad4b1c10219a26931b7262c79cf3402f6ac333637492b13119b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0824


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O

lemma liveNormCap_power_bound (b Lcap Z r ell F eta tau : ℝ)
    (_hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hZ : 2 ≤ Z)
    (hr : r ≤ Lcap) (hell : ell ≤ Lcap) (hF : 0 ≤ F) (hFcap : F ≤ Lcap)
    (heta : 0 ≤ eta) (heta1 : eta ≤ 1) (htau : 0 ≤ tau) (htau1 : tau ≤ 1) :
    1 ≤ liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ∧
    liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)) ≤
      max 1 b * Z^(3*Lcap+16) := by
  have hz : 0<Z := by linarith
  have hz1 : 1 ≤ Z := by linarith
  have hb1 : 1 ≤ max 1 b := le_max_left _ _
  have hbmax : b ≤ max 1 b := le_max_right _ _
  have hpow (a : ℝ) (ha : a ≤ 3*Lcap+16) : Z^a ≤ max 1 b*Z^(3*Lcap+16) :=
    (Real.rpow_le_rpow_of_exponent_le hz1 ha).trans (le_mul_of_one_le_left (Real.rpow_nonneg hz.le _) hb1)
  have hsq : (Z^(ell+eta))^2=Z^(2*(ell+eta)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
    congr 1
    ring
  refine ⟨(Real.one_le_rpow hz1 (by linarith : 0 ≤ 2*F+15*eta+tau)).trans (le_max_left _ _),?_⟩
  unfold liveNormCap
  apply max_le (hpow _ (by linarith))
  apply max_le
  · exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  apply max_le
  · rw [hsq,mul_assoc,←Real.rpow_add hz]
    exact mul_le_mul hbmax (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith))
      (Real.rpow_nonneg hz.le _) (by linarith)
  · rw [hsq]
    exact hpow _ (by linarith)

lemma dyadIndex_power_log_bound (b A : ℝ) (hb : 1 ≤ b) (hA : 0 ≤ A) :
    ∃ C : ℝ,0<C ∧ ∀ Z R : ℝ,2 ≤ Z → 1 ≤ R → R ≤ b*Z^A →
      ((dyadIndex R+1:ℕ):ℝ)^8 ≤ C*(1+Real.log Z)^8 := by
  let c := 1+Real.log b/Real.log 2+A/Real.log 2
  have hl2 : 0<Real.log 2 := Real.log_pos (by norm_num)
  have hcb : 0 ≤ Real.log b/Real.log 2 := div_nonneg (Real.log_nonneg hb) hl2.le
  have hcA : 0 ≤ A/Real.log 2 := div_nonneg hA hl2.le
  have hc : 0<c := by dsimp [c];linarith
  refine ⟨c^8,pow_pos hc _,?_⟩
  intro Z R hZ hR hbound
  have hz : 0<Z := by linarith
  have hr : 0<R := by linarith
  have hb0 : 0<b := by linarith
  have hlz : 0 ≤ Real.log Z := Real.log_nonneg (by linarith)
  have hf := Nat.floor_le (Real.logb_nonneg (by norm_num : (1:ℝ)<2) hR)
  have hl := Real.log_le_log hr hbound
  rw [Real.log_mul (ne_of_gt hb0) (ne_of_gt (Real.rpow_pos_of_pos hz _)),Real.log_rpow hz] at hl
  have hstep : ((dyadIndex R+1:ℕ):ℝ) ≤ c*(1+Real.log Z) := by
    simp only [Nat.cast_add,Nat.cast_one,dyadIndex,Real.logb] at *
    have hd := div_le_div_of_nonneg_right hl hl2.le
    have hmul : 0 ≤ (Real.log b/Real.log 2)*Real.log Z := mul_nonneg hcb hlz
    dsimp [c]
    have he : (Real.log b+A*Real.log Z)/Real.log 2=Real.log b/Real.log 2+(A/Real.log 2)*Real.log Z := by ring
    rw [he] at hd
    nlinarith
  calc
    _ ≤ (c*(1+Real.log Z))^8 := pow_le_pow_left₀ (by positivity) hstep 8
    _= _ := by rw [mul_pow]

theorem live_joint_scalar_log_budget (b Lcap : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤
        C*(1+Real.log Z)^8 := by
  obtain ⟨C,hC,hcount⟩ := dyadIndex_power_log_bound (max 1 b) (3*Lcap+16) (le_max_left _ _) (by linarith)
  refine ⟨C,hC,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  have hc := liveNormCap_power_bound b Lcap Z r ell F eta tau hb hcap hZ hr hell hF hFcap heta heta1 htau htau1
  exact hcount Z _ hZ hc.1 hc.2

lemma log_eighth_small_power (ε : ℝ) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z : ℝ,1 ≤ Z → (1+Real.log Z)^8 ≤ C*Z^ε := by
  let δ := ε/8
  have hd : 0<δ := by dsimp [δ];positivity
  refine ⟨(1+1/δ)^8,by positivity,?_⟩
  intro Z hZ
  have hz : 0<Z := by linarith
  have h1 := Real.one_le_rpow hZ hd.le
  have hl := Real.log_le_rpow_div hz.le hd
  have hb : 1+Real.log Z ≤ (1+1/δ)*Z^δ := by
    calc
      _ ≤ Z^δ+Z^δ/δ := add_le_add h1 hl
      _=_ := by ring
  calc
    _ ≤ ((1+1/δ)*Z^δ)^8 := pow_le_pow_left₀ (by linarith [Real.log_nonneg hZ]) hb 8
    _=(1+1/δ)^8*Z^ε := by
      have he : (Z^δ)^8=Z^ε := by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le]
        congr 1
        dsimp [δ]
        ring
      rw [mul_pow,he]

theorem live_joint_scalar_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀ Z r ell F eta tau : ℝ,2 ≤ Z → r ≤ Lcap → ell ≤ Lcap →
      0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      ((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau)))+1:ℕ):ℝ)^8 ≤ C*Z^ε := by
  obtain ⟨C₁,hC₁,h₁⟩ := live_joint_scalar_log_budget b Lcap hb hcap
  obtain ⟨C₂,hC₂,h₂⟩ := log_eighth_small_power ε hε
  refine ⟨C₁*C₂,mul_pos hC₁ hC₂,?_⟩
  intro Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1
  exact (h₁ Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1).trans
    ((mul_le_mul_of_nonneg_left (h₂ Z (by linarith)) hC₁.le).trans_eq (mul_assoc _ _ _).symm)

theorem original_live_joint_small_power (b Lcap ε : ℝ) (hb : 0 ≤ b) (hcap : 0 ≤ Lcap) (hε : 0<ε) :
    ∃ C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι → O)(hp : ∀i,p i≠0)
      [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (pool : Finset ι)(Q : Finset (ι→₀ℕ))(labels : Finset (Ideal O))
      (β : Ideal O → (ι→₀ℕ) → ℂ)(cutoff : CubeCoordinates ι → Finset ι → Ideal O → Finset ι → ℝ)
      (Ψ : O→*ℂ)(m : O)(mark : (ι→₀ℕ) → Finset ι → ℂ)(W : ℝ → ℂ)(Φ : 𝓢(ℝ,ℂ))
      (K Z r ell F eta tau theta : ℝ),
      2 ≤ Z → r ≤ Lcap → ell ≤ Lcap → 0 ≤ F → F ≤ Lcap → 0 ≤ eta → eta ≤ 1 → 0 ≤ tau → tau ≤ 1 →
      (∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2 ≤ Z^(ell+eta)) →
      (∀I∈labels,I≠0) → (∀y,W y≠0 → y ≤ b) →
      ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hcop hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤ C*Z^ε := by
  obtain ⟨C,hC,hcount⟩ := live_joint_scalar_small_power b Lcap ε hb hcap hε
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hcop hg pool Q labels β cutoff Ψ m mark W Φ K Z r ell F eta tau theta
    hZ hr hell hF hFcap heta heta1 htau htau1 hQ hlabels hW
  have hz : 0<Z := by linarith
  have he := original_twisted_live_joint_card p hp hcop hg pool Q labels (Z^(2*F+15*eta+tau))
    β cutoff Ψ m mark W Φ K b (Z^(ell+eta)) (Z^r) theta
    (Real.rpow_pos_of_pos hz _) (Real.rpow_nonneg hz.le _) hQ hlabels hW
  have he' : ((liveJointKeys p
        (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1)
          (Z^(2*F+15*eta+tau))) pool
        (sourceSummand p hp hcop hg β cutoff Ψ m mark
          (fun y=>CompletedHeight.normTwistedSource W theta (y/Z^r)) Φ K)).card:ℝ) ≤
      (((dyadIndex (liveNormCap (b*Z^r) (Z^(ell+eta)) (Z^(2*F+15*eta+tau))))+1:ℕ):ℝ)^8 := by exact_mod_cast he
  exact he'.trans (hcount Z r ell F eta tau hZ hr hell hF hFcap heta heta1 htau htau1)

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0824

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstStepScalarCaps
Source SHA256: 33240702eacea3b5d2aca090ac641c842825c86f8d26d2d3cf212ea39ecc092c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0825


namespace OAI

noncomputable section

namespace SevenEighths.InverseMoment

 theorem first_step_scalar_caps (Z A M r ell V delta aa bb rr t j eta tau window b:ℝ)
    (hZ:1<Z)(hA:0≤A)(hM:0≤M)(hMcap:M≤A)(hr: -1≤r)(hrcap:r≤A)
    (hell:0≤ell)(hellcap:ell≤A)(hV:0≤V)(hVcap:V≤A)
    (hd:0≤delta)(hdcap:delta≤A)(haa:0≤aa)(haacap:aa≤A)
    (hbb:0≤bb)(hbbcap:bb≤A)(hrr:0≤rr)(_hrrcap:rr≤A)
    (ht:0≤t)(_htcap:t≤A)(hj:0≤j)(hjcap:j≤A)
    (heta:0≤eta)(heta1:eta≤1)(htau:0≤tau)(htau1:tau≤1)
    (hwindow:Real.exp window≤Z^eta)(hb:b≤Z^eta):
    let X:=Z^(r-aa-bb-t);
    let Y:=Z^(firstPhysicalHeight M r ell V delta bb j+12*eta+tau);
    X*Real.exp window≤Z^(A+1) ∧ Y≤Z^(16*A+20) ∧ Y⁻¹≤Z^(4*A+2) ∧
    b*X≤Z^(16*A+20) ∧ delta+eta+2*(A+1)+tau+(4*A+2)≤16*A+20 ∧
    firstKappa M r ell V delta aa bb rr+(9/2:ℝ)*eta≤16*A+20 ∧
    (∀e:ℝ,e≤A→Z^(e+eta)≤Z^(16*A+20)):=by
  intro X Y
  have hz:0<Z:=zero_lt_one.trans hZ
  have hX:X≤Z^A:=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hX0:0≤X:=Real.rpow_nonneg hz.le _
  have hxy:X*Real.exp window≤Z^(A+1):=by
    calc
      _≤Z^A*Z^eta:=mul_le_mul hX hwindow (Real.exp_pos _).le (Real.rpow_nonneg hz.le _)
      _=Z^(A+eta):=(Real.rpow_add hz A eta).symm
      _≤Z^(A+1):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨hxy,?_,?_,?_,by linarith,?_,?_⟩
  · apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · rw [show Y⁻¹=Z^(-(firstPhysicalHeight M r ell V delta bb j+12*eta+tau)) by
      dsimp [Y];rw [Real.rpow_neg hz.le]]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    unfold firstPhysicalHeight
    linarith
  · calc
      b*X≤Z^eta*Z^A:=mul_le_mul hb hX hX0 (Real.rpow_nonneg hz.le _)
      _=Z^(eta+A):=(Real.rpow_add hz eta A).symm
      _≤Z^(16*A+20):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  · unfold firstKappa
    linarith
  · intro e he
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith

theorem first_step_scalar_losses (A r ell aa bb rr t eta pi em ed:ℝ)
    (hA:0≤A)(hr:r≤A)(hell:ell≤A)(haa:0≤aa)(_hbb:0≤bb)(hbbA:bb≤A)
    (hrr:rr≤A)(_ht:0≤t)(htA:t≤A)(_heta:0≤eta)(heta1:eta≤1)
    (he:0≤em)(hd:0≤ed)(hpi:0≤pi)(hetaPi:6*eta≤pi)
    (hem:em*(20*A+30)≤pi/4)(hed:ed*(20*A+30)≤pi/4):
    em*(ell+rr/2+t+(16*A+20)+11*eta/2)≤pi ∧
    em*(r-aa-bb-t)+7*eta/2+ed*(3*ell+bb+t+5*eta)+
      2*em*(2*ell+bb+t+4*eta)≤pi+eta/2:=by
  have hm:=mul_le_mul_of_nonneg_left (show ell+rr/2+t+(16*A+20)+11*eta/2≤20*A+30 by linarith) he
  have h1:=mul_le_mul_of_nonneg_left (show r-aa-bb-t+2*(2*ell+bb+t+4*eta)≤20*A+30 by linarith) he
  have h2:=mul_le_mul_of_nonneg_left (show 3*ell+bb+t+5*eta≤20*A+30 by linarith) hd
  constructor <;> nlinarith

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0825

/-! Original module: OAI.NumberTheory.DirichletL.Descent.OriginalCellPriority
Source SHA256: f6fc8a39fe0473e144f5de16797e48cf83b2040fd76eebce1470139f5f6eab63
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0826



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic FirstCauchyArithmetic
open InverseFirstPriorityParents InverseFirstGlobalParents
local notation "O"=>ActualEisensteinCubic.O
variable {ι σ:Type}[DecidableEq ι][DecidableEq σ]

def originalSubsetSource (outer:Finset (FirstOriginalOuter ι)):Finset (Source ι 0):=
  outer.image ofOriginal

theorem original_subset_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (outer:Finset (FirstOriginalOuter ι))(pool:Finset ι)
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)(extra:CubeCoordinates ι→Finset ι)
    (negative:Bool)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑k∈outer,firstCanonicalSecondEnergy p hp hg hinj pool k.1 k.2.1
      negative Ψ m (primeSubsetGenerator (fun i=>Ideal.span {p i}) k.2.2)
      (fun U=>primeMark slots lists a (extra k.1∪U)) (selector k) om X t Y) ≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (globalParentSource (originalSubsetSource outer) pool (originalSelector selector))
      (fun x=>(‖selector (toOriginal x) x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have hempty:∀x∈originalSubsetSource outer,x.quotientSupport=∅:=by
    intro x hx
    obtain ⟨k,hk,rfl⟩:=Finset.mem_image.mp hx
    rfl
  have he:=global_canonical_to_original_priority p hp hg hinj hc
    (originalSubsetSource outer) pool (originalSelector selector) hempty extra
    negative Ψ m slots lists a om X t Y hY
  rw [show originalSubsetSource outer=outer.image ofOriginal from rfl,
    Finset.sum_image (fun _ _ _ _ h=>ofOriginal_injective h)] at he
  have hs (k:FirstOriginalOuter ι): originalSelector selector (ofOriginal k)=selector k :=
    originalSelector_ofOriginal_fun selector k
  simp_rw [hs] at he
  simpa only [originalSubsetSource,ofOriginal,originalSelector,toOriginal,eraseFirstQuotient] using he

theorem original_cell_parent_source
    (p:ι→O)(pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ):
    globalParentSource (originalSubsetSource (InverseFirstGlobalCaps.outerCell p pool Q k))
      pool (originalSelector (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.parentCell p pool Q selector k l:=by
  ext x
  rw [InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,
    Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,he⟩
    exact ⟨o,ho,D,hD,by simpa using hs,he⟩
  · rintro ⟨o,ho,D,hD,hs,he⟩
    exact ⟨ofOriginal o,⟨o,ho,rfl⟩,D,⟨hD,by simpa using hs⟩,he⟩

theorem original_cell_canonical_priority
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(selector:FirstOriginalOuter ι→Finset ι→ℂ)
    (k:InverseMomentFirstChildWindows.SourceIndex)(l:ℕ)
    (extra:CubeCoordinates ι→Finset ι)(negative:Bool)(Ψ:O→*ℂ)(m:O)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(om:ℝ→ℂ)(X t Y:ℝ)(hY:0<Y):
    (∑o∈InverseFirstGlobalCaps.outerCell p pool Q k,
      firstCanonicalSecondEnergy p hp hg hinj pool o.1 o.2.1 negative Ψ m
        (primeSubsetGenerator (fun i=>Ideal.span {p i}) o.2.2)
        (fun U=>primeMark slots lists a (extra o.1∪U))
        (InverseMomentFirstChildWindows.commonSelector p (selector o) l) om X t Y)≤
    globalPriorityOriginalEnergy p hg hp hinj extra pool
      (InverseFirstGlobalCaps.parentCell p pool Q selector k l)
      (fun x=>(‖InverseMomentFirstChildWindows.commonSelector p (selector (toOriginal x)) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y:=by
  have he:=original_subset_canonical_priority p hp hg hinj hc
    (InverseFirstGlobalCaps.outerCell p pool Q k) pool
    (fun x=>InverseMomentFirstChildWindows.commonSelector p (selector x) l) extra negative Ψ m slots lists a om X t Y hY
  rwa [original_cell_parent_source] at he

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0826

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstOriginalProfileLiveParents
Source SHA256: dd768f07c174c92f41624d8d137971c882f38ed8adf9b7899c1183f70bfea163
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0827



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstOriginalProfile
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type} [DecidableEq ι] [DecidableEq σ]

lemma refined_parent_source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (selector : FirstOriginalOuter ι→Finset ι→ℂ) (k : SourceIndex) (l j : ℕ) :
    globalParentSource (originalSubsetSource (refinedOuter p pool Q k (labelGate p j)))
      pool (originalSelector (fun x=>commonSelector p (selector x) l))=
      InverseFirstGlobalCaps.labelParentCell p pool Q selector k l j := by
  ext x
  rw [InverseFirstGlobalCaps.labelParentCell,Finset.mem_filter,InverseFirstGlobalCaps.mem_parentCell]
  simp only [globalParentSource,Finset.mem_biUnion,originalSubsetSource,Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨y,⟨o,ho,rfl⟩,D,⟨hD,hs⟩,rfl⟩
    have ho' := Finset.mem_filter.mp ho
    refine ⟨⟨o,?_,D,hD,by simpa using hs,rfl⟩,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho'.1
    · simpa [labelGate,fillFirstQuotient,toOriginal,ofOriginal] using ho'.2
  · rintro ⟨⟨o,ho,D,hD,hs,rfl⟩,hj⟩
    refine ⟨ofOriginal o,⟨o,?_,rfl⟩,D,⟨hD,by simpa using hs⟩,rfl⟩
    apply Finset.mem_filter.mpr
    refine ⟨?_,?_⟩
    · simpa only [originalOuterCell_eq_caps] using ho
    · simpa [labelGate,fillFirstQuotient,toOriginal,ofOriginal] using hj

theorem refined_child_priority (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (om : ℝ→ℂ) (X t Y : ℝ) (hY : 0<Y) :
    refinedChildEnergy p hp hg hinj pool Q k l (labelGate p j) negative Ψ m
      (fun v U=>primeMark slots lists a (v.support∪U)) om X t Y ≤
    globalPriorityOriginalEnergy p hg hp hinj
      (fun b=>if negative then b.rightExponent.support else b.leftExponent.support) pool
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
      (fun x=>(‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ))
      negative Ψ m slots lists a om X t Y := by
  have he := original_subset_canonical_priority p hp hg hinj hc
    (refinedOuter p pool Q k (labelGate p j)) pool (fun _=>commonSelector p (fun _=>1) l)
    (fun b=>if negative then b.rightExponent.support else b.leftExponent.support)
    negative Ψ m slots lists a om X t Y hY
  rw [refined_parent_source] at he
  cases negative <;> simpa [refinedChildEnergy,divisorElement] using he

end SevenEighths.InverseMomentFirstOriginalProfile
end

end OAI
end OAIOriginalModule0827

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicCell
Source SHA256: b6a0b61b5a97f5f0b019c71b034629066ad99bc81dcbbb8487696833321c62ef
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0828



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)

def firstCellRadius (Z M r ell V eta tau:ℝ)(k:SourceIndex)(j:ℕ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (dyadicExponent Z (k 3))
    (dyadicExponent Z (k 2)) (dyadicExponent Z j)+12*eta+tau)

theorem first_dyadic_radius_cell (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(x:FirstOriginalOuter ι)
    (hx:x∈refinedOuter p pool Q k (labelGate p j))
    (Z M r ell V eta tau:ℝ):
    firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau=
      firstCellRadius Z M r ell V eta tau k j:=by
  rw [refinedOuter_label] at hx
  obtain ⟨hx,hj⟩:=Finset.mem_filter.mp hx
  have hg:outerGate p k x:=(Finset.mem_filter.mp hx).2
  have hC:=hg 2
  have hD:=hg 3
  change dyadIndex (primeProductNorm p x.2.1)=k 2 at hC
  change dyadIndex (‖eisEmbedding (primeSubsetGenerator (fun i=>Ideal.span {p i}) x.2.2)‖^2)=k 3 at hD
  rw [primeSubsetGenerator_norm_eq_productNorm] at hD
  unfold firstDyadicRadius firstCellRadius firstDyadicExponent
  rw [hD,hC]
  change dyadIndex (‖eisEmbedding (jLabel p x.1.support
    (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)‖^2)=j at hj
  rw [hj]

theorem first_dyadic_refined_cutoff (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(Z M r ell V eta tau:ℝ):
    ∀x∈refinedOuter p pool Q k (labelGate p j),∀_I:Ideal O,
      firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤
        firstCellRadius Z M r ell V eta tau k j:=by
  intro x hx I
  exact (first_dyadic_radius_cell p pool Q k j x hx Z M r ell V eta tau).le

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0828

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicLiveRadius
Source SHA256: b0d3f630446a971a168e19038d24a1ab51da319d659d4250fec44621a48a041d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0829



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem first_dyadic_original_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    ∀x∈firstOriginalOuter pool Q,firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤Z^(2*Fmax+15*eta+tau):=by
  intro x hx
  have hm:=(mem_firstOriginalOuter pool Q x).mp hx
  have hb:=reopenedCubeFamily_cube_norms p Q _ hQ x.1 hm.1
  exact first_dyadic_radius_global_cap p hp x.1 x.2.1 x.2.2 (Finset.mem_powerset.mp hm.2.2)
    Z M r ell V eta tau Fmax hZ hbin hM hF hb.1 hb.2

include hp in
theorem first_live_cell_radius_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (labels:Finset (Ideal O))(Y:ℝ)(term:OriginalIndex ι→FirstCommonIndex ι→ℂ)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hM:0≤M)
    (hF:r+3*ell+V≤Fmax)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool term):
    firstCellRadius Z M r ell V eta tau k.1 k.2.2≤Z^(2*Fmax+15*eta+tau):=by
  obtain ⟨⟨x,j⟩,hx,rfl⟩:=Finset.mem_image.mp hk
  have hm:=Finset.mem_product.mp (Finset.mem_filter.mp hx).1
  have ho: x.1∈firstOriginalOuter pool Q:=(Finset.mem_sigma.mp hm.1).1
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    apply Finset.mem_filter.mpr
    refine ⟨?_,rfl⟩
    apply InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y
    exact Finset.mem_filter.mpr ⟨hm.1,rfl⟩
  change firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))≤_
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Fmax hZ hbin hM hF hQ x.1 ho

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0829

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicRetainedEnergy
Source SHA256: 10a65c29ca01479d44afe204c1b485628ab7341a589c54d361aaea06952cbe73
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0830




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_retained_energy
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:1<Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps)*(keys.card:ℝ):=by
  let g₁:=priorityLogWindow om a b ha hs true
  let g₂:=priorityLogWindow om a b ha hs false
  let M₀:=|Real.log a|+|Real.log b|
  have hm:0≤M₀:=by dsimp [M₀];positivity
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_refined_cell_physical_budget
    g₁ g₂ Φ M₀ M₀ hm hm (priorityLogWindow_support om a b ha hs true) (priorityLogWindow_support om a b ha hs false)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨Cp,Kp,hCp,hKp,hcell⟩:=he eps heps 0 J
  refine ⟨Cp*Kp,mul_nonneg hCp hKp.le,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hΨ hΓ hK hB hsf hn hβ Y cutoff W source keys hleft hright
  have hz:0<Z:=zero_lt_one.trans hZ
  have hsum:=original_retained_joint_profile_bound p hp hcop hg pool Q labels β cutoff Ψ m mark
    om a b ha hs Φ K Y (Z^r) theta (Real.rpow_pos_of_pos hz _) (fun _=>1) (by intro i;norm_num)
  have hnrm:0≤Z^(-r-2*ell-V)*Z^M:=mul_nonneg (Real.rpow_nonneg hz.le _) (Real.rpow_nonneg hz.le _)
  apply (mul_le_mul_of_nonneg_left hsum hnrm).trans
  rw [Finset.mul_sum]
  have hpoint:∀k∈keys,
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k.1 k.2.1 (labelGate p k.2.2)
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Y (physicalScales (Z^r) k.1 k.2.1)‖≤
      (Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=by
    intro k hk
    let T₁:=(physicalScales (Z^r) k.1 k.2.1) 7
    let T₂:=(physicalScales (Z^r) k.1 k.2.1) 8
    have hT₁:0<T₁:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 7
    have hT₂:0<T₂:=physicalScales_pos _ (Real.rpow_pos_of_pos hz _) _ _ 8
    have hY:0<firstCellRadius Z M r ell V eta tau k.1 k.2.2:=Real.rpow_pos_of_pos hz _
    have hl:=hleft k hk
    have hr:=hright k hk
    have heta:0≤eta:=by
      apply (Real.rpow_le_rpow_left_iff hZ).mp
      rw [Real.rpow_zero]
      linarith
    have hL:0≤eta*Real.log Z:=mul_nonneg heta (Real.log_nonneg hZ.le)
    have he' := hcell p hp hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Y
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) hΨ hΓ hY hsf hn hβ k.1 k.2.1 (labelGate p k.2.2)
      (fun x hx I _=>first_dyadic_refined_cutoff p pool Q k.1 k.2.2 Z M r ell V eta tau x hx I)
      T₁ T₂ K theta (eta*Real.log Z) hT₁ hT₂ hK hL Benergy Z M r ell V (dyadicExponent Z (k.1 3))
      (dyadicExponent Z (k.1 0)) (dyadicExponent Z (k.1 1)) (dyadicExponent Z (k.1 2))
      (dyadicExponent Z (k.1 4)) (dyadicExponent Z k.2.1) (dyadicExponent Z (k.1 5)) eta
      hB hz (physicalScales_rpow Z r hZ k.1 k.2.1) rfl hl hr
    have hrad:=first_live_cell_radius_cap p hp pool Q labels Y _ Z M r ell V eta tau Fmax hZ hbin hM hF hQ k hk
    have hpow:=Real.rpow_le_rpow hY.le hrad heps.le
    rw [←Real.rpow_mul hz.le] at hpow
    simp only [pow_zero,div_one,norm_neg] at he'
    calc
      _≤(Γ^2*Kp*(firstCellRadius Z M r ell V eta tau k.1 k.2.2)^eps*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=he'
      _≤(Γ^2*Kp*Z^((2*Fmax+15*eta+tau)*eps)*Benergy)*
          (Cp*((1+‖theta‖)^InverseClippingProfiles.momentOrder J*(1+‖theta‖)^InverseClippingProfiles.momentOrder J)):=by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow (by positivity)) hB
      _=_:=by rw [show 2*InverseClippingProfiles.momentOrder J=InverseClippingProfiles.momentOrder J+InverseClippingProfiles.momentOrder J by omega,pow_add];ring
  calc
    _≤∑_k∈keys,(Cp*Kp)*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Fmax+15*eta+tau)*eps):=
      Finset.sum_le_sum hpoint
    _=_:=by simp [mul_comm]

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0830

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicRetainedBudget
Source SHA256: e27def2a796b87cb0d8f1f0c1e01842d7b66e1b5a83278a22705ede4d259e57a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0831





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_retained_budget
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap:ℝ)(hcap:0≤Lcap)(hb:0≤b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι:Type}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)(_hF0:0≤Fmax)(_hFcap:Fmax≤Lcap)
      (_heta:0≤eta)(_heta1:eta≤1)(_htau:0≤tau)(_htau1:tau≤1)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) true Ψ m mark omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        refinedChildEnergy p hp hg hinj pool Q k.1 k.2.1 (labelGate p k.2.2) false Ψ m mark omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps+eps) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_retained_energy om Φ a b ha hs
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,henergy⟩:=he eps heps J
  obtain ⟨Cc,hCc,hcount⟩:=original_live_joint_small_power b Lcap eps hb hcap heps
  refine ⟨C*Cc,mul_nonneg hC hCc.le,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
    Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1<Z:=by linarith
  have he':=henergy p hp hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ1 hbin hM hF hQ hΨ hΓ hK hB hsf hn hβ hleft hright
  have hnkey:=hcount p hp hcop hg pool Q labels β cutoff Ψ m mark om Φ K Z r ell Fmax eta tau theta
    hZ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hQ hn (fun y hy=>(hs hy).2)
  apply he'.trans
  calc
    _≤C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
        Z^((2*Fmax+15*eta+tau)*eps)*(Cc*Z^eps):=
      mul_le_mul_of_nonneg_left hnkey (by positivity)
    _=_:=by rw [Real.rpow_add hz];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0831

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicPriorityBudget
Source SHA256: 0d2d24dff0699095b6cf087919caadf1219187adb240187c35ed0d28814cb349
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0832






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_priority_budget
    (om Φ:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap:ℝ)(hcap:0≤Lcap)(hb:0≤b):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C:ℝ,0≤C ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V eta tau Fmax Γ K theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Fmax)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)(_hF0:0≤Fmax)(_hFcap:Fmax≤Lcap)
      (_heta:0≤eta)(_heta1:eta≤1)(_htau:0≤tau)(_htau1:tau≤1)
      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hK:0<K)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Fmax+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K);
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (Z^(-r-2*ell-V)*Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W Φ K Y cutoff (fun _=>1)‖≤
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Fmax+15*eta+tau)*eps+eps) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_retained_budget om Φ a b ha hs Lcap hcap hb
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,henergy⟩:=he eps heps J
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
    mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  apply henergy p hp hg hinj hcop hc hpr pool Q labels β Ψ m mark Z M r ell V eta tau Fmax Γ K theta Benergy
    hZ hbin hM hF hQ hrcap hellcap hF0 hFcap heta heta1 htau htau1 hΨ hΓ hK hB hsf hn hβ
  · intro k hk z
    have he':=refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 true Ψ m slots lists weights w₁
      ((physicalScales (Z^r) k.1 k.2.1) 7)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _)
    exact (mul_le_mul_of_nonneg_left he' (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hleft k hk z)
  · intro k hk z
    have he':=refined_child_priority p hp hg hinj hc pool Q k.1 k.2.1 k.2.2 false Ψ m slots lists weights w₂
      ((physicalScales (Z^r) k.1 k.2.1) 8)
      (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
      (firstCellRadius Z M r ell V eta tau k.1 k.2.2) (Real.rpow_pos_of_pos hz _)
    exact (mul_le_mul_of_nonneg_left he' (mul_nonneg (Real.rpow_nonneg hz.le _) (Real.exp_pos _).le)).trans (hright k hk z)

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0832

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstDyadicFullEnergy
Source SHA256: e5165973b95ff4763c9dcf8308297cb02e19e282d5098fc5b844fa664ff010a3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0833







namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem original_dyadic_full_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap Mmax eta tau saving:ℝ)(hcap:0≤Lcap)(hMmax:0≤Mmax)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃C Czero Ctail:ℝ,0≤C ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V Γ theta Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Mmax)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hΨ:∀u,‖Ψ u‖≤1)(_hΓ:0≤Γ)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)(_hβ:∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om theta (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q (β I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*Γ^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta))+
        C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Lcap+15*eta+tau)*eps+eps)+Ctail*Γ^2*Z^(-saving) :=by
  obtain ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=original_dyadic_priority_budget om rowMajorant a b ha hs Lcap hcap hb
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨C,hC,hret⟩:=he eps heps J
  obtain ⟨Cz,Ct,hCz,hCt,hbranches⟩:=original_dyadic_zero_tail om b Mmax Lcap eta tau (saving+eta) eps
    (fun y hy=>(hs hy).2) hMmax hcap heta htau heps
  refine ⟨C,Cz,Ct,hC,hCz,hCt,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta Benergy
    hZ hbin hM hF hMcap hell hV hr hbZ hQpool hQ hrcap hellcap hΨ hΓ hB hsf hn hβ hlabels hslots hweights
    mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hZ1:1<Z:=by linarith
  have hK:0<Z^M:=Real.rpow_pos_of_pos hz _
  have he':=original_global_physical_energy p hp hcop hg hinj hc hpr pool Q hQpool labels hn β Ψ m mark W
    (Z^M) Y hK cutoff (fun _ _ _ _ _ _ _=>Real.rpow_nonneg hz.le _)
    (fun x hx _ _=>first_dyadic_original_cap p hp pool Q Z M r ell V eta tau Lcap hZ1 hbin hM hF hQ x hx)
    (fun _=>1) (by intro i;norm_num)
  have hret':=hret p hp hg hinj hcop hc hpr pool Q labels β Ψ m slots lists weights Z M r ell V eta tau Lcap Γ
    (Z^M) theta Benergy hZ hbin hM hF hQ hrcap hellcap hcap le_rfl heta heta1 htau.le htau1 hΨ hΓ hK hB hsf hn hβ hleft hright
  obtain ⟨hz',ht'⟩:=hbranches p hp hcop hg hinj hc pool Q labels β Ψ m slots lists weights Z M r ell V Γ theta
    hZ1 hbin hM hMcap hell hV hr hF hΓ hbZ hΨ hQ hn hlabels hβ hslots hweights
  have hfactor:Z^(-r-2*ell-V)≤Z^eta:=Real.rpow_le_rpow_of_exponent_le hZ1.le (by linarith)
  have htail:Z^(-r-2*ell-V)*‖reopenedPhysicalSourceSum pool Q labels β (fun q D I=>
        canonicalCubeDualTail p hp hcop hg pool q D Ψ Ψ m m (ConcretePrimeRowBridge.idealGenerator I)
          (fun U=>mark q.rightExponent U*W (primeProductNorm p U))
          (fun U=>mark q.leftExponent U*W (primeProductNorm p U)) rowMajorant (Z^M)
          (reopenedPhysicalCutoff p q I (cutoff q D I)))‖≤Ct*Γ^2*Z^(-saving):=by
    have ht'':_≤Ct*Γ^2*Z^(-(saving+eta)):=ht'
    apply (mul_le_mul hfactor ht'' (norm_nonneg _) (Real.rpow_nonneg hz.le _)).trans
    apply le_of_eq
    rw [show Z^eta*(Ct*Γ^2*Z^(-(saving+eta)))=(Ct*Γ^2)*(Z^eta*Z^(-(saving+eta))) by ring,
      ←Real.rpow_add hz]
    congr 2
    ring
  have hall:=mul_le_mul_of_nonneg_left he' (Real.rpow_nonneg hz.le (-r-2*ell-V))
  simp only [mul_add] at hall
  apply hall.trans
  have hr':Z^(-r-2*ell-V)*((Z^M)*‖originalRetainedFamily p hp hcop hg pool Q labels β Ψ m mark W rowMajorant (Z^M) Y cutoff (fun _=>1)‖)≤
      C*Γ^2*Benergy*(1+‖theta‖)^(2*InverseClippingProfiles.momentOrder J)*Z^((2*Lcap+15*eta+tau)*eps+eps):=by
    simpa only [mul_assoc] using hret'
  exact add_le_add (add_le_add hz' hr') htail

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0833

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongSource
Source SHA256: 15470a71e9a98d153ccf86a46cdae2e32acd60d748910f215af76db5f44b28c4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0834



namespace OAI

noncomputable section

open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalCubeSeparation CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation FourierBridge CompletedHeight
local notation "O"=>ActualEisensteinCubic.O

theorem long_frequency_profile
    {ι:Type*}(p:ι→O)(hp:∀i,p i≠0)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)
    (Z r ξ:ℝ)(hZ:0<Z)(T:Finset ι) :
    frequencyTwist V ξ (columnLog p (Z^r) T)=
      normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
        (primeProductNorm p T/Z^r) := by
  rw [normTwistedSource,radialFromLog_column p hp V (V.smooth ⊤) A hV _ (Real.rpow_pos_of_pos hZ r)]
  simp only [frequencyTwist_apply,columnLog]

theorem long_marked_source_eq
    {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(β:(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m f z:O)
    (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(A:ℝ)(hV:∀s,V s≠0→|s|≤A)(Z r ξ:ℝ)(hZ:0<Z) :
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (T∪v.support)*
        frequencyTwist V ξ (columnLog p (Z^r) T)) z =
    varyingReopenedRow p hp hcop hg pool Q β Ψ m f
      (fun v T=>primeMark slots lists weights (v.support∪T)*
        normTwistedSource (radialFromLog V (V.smooth ⊤) A hV) ξ
          (primeProductNorm p T/Z^r)) z := by
  congr 1
  funext v T
  rw [long_frequency_profile p hp V A hV Z r ξ hZ T,Finset.union_comm T v.support]

theorem marked_long_filter
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists weights=
      markedReopenedCubeBin S D (progressingCubes S D H₀ Q) Ψ m f z W X H₀ slots lists weights := by
  unfold markedReopenedCubeBin progressingCubes
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hz:largeCubeCoefficient H₀ (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v)=0 := by
    by_contra hh
    exact hn (Finset.mem_filter.mpr ⟨hv,(largeCubeCoefficient_support H₀ _ hh).2⟩)
  simp only [hz,zero_mul]

theorem long_cube_progress
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell:ℝ)(hZ:1<Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-1/Real.log Z≤ell+V := by
  obtain ⟨v,hv⟩:=hne
  obtain ⟨hv,hlower⟩:=Finset.mem_filter.mp hv
  have hz:0<Z:=zero_lt_one.trans hZ
  have he:=Real.log_le_log (Real.rpow_pos_of_pos hz _) (hlower.trans (hupper v hv))
  rw [Real.log_rpow hz,Real.log_mul (Real.exp_pos _).ne' (Real.rpow_pos_of_pos hz _).ne',
    Real.log_exp,Real.log_rpow hz] at he
  have hlog:=Real.log_pos hZ
  have hd: (cutoff-ell-V)*Real.log Z≤1:=by nlinarith
  have hh:cutoff-ell-V≤1/Real.log Z:=(le_div_iff₀ hlog).mpr hd
  linarith

theorem long_cube_progress_with_slack
    (S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Z cutoff V ell eta:ℝ)(hZ:1<Z)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) Q).Nonempty)
    (hupper:∀v∈Q,(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤
      Real.exp 1*Z^ell) :
    cutoff-eta≤ell+V := by
  have h:=long_cube_progress S D Q Z cutoff V ell hZ hne hupper
  have hh:1/Real.log Z≤eta:=(div_le_iff₀ (Real.log_pos hZ)).mpr (by simpa only [mul_comm] using hlog)
  linarith

theorem short_sum_zero_of_label_large
    (Ψ:O→*ℂ)(W:ℝ→ℂ)(mark:Ideal O→ℂ)(X Z cutoff V:ℝ)
    (hZ:1≤Z)(hV:cutoff≤V) :
    markedShortCompletedSum Ψ W X (Z^(cutoff-V)) mark=0 := by
  have ht:Z^(cutoff-V)≤1:=by
    have he:=Real.rpow_le_rpow_of_exponent_le hZ (show cutoff-V≤0 by linarith)
    simpa only [Real.rpow_zero] using he
  unfold markedShortCompletedSum
  trans ∑' _ : Ideal O,(0:ℂ)
  · apply tsum_congr
    intro I
    by_cases hi:I=0
    · subst I
      simp
    rw [ite_eq_right (not_lt.mpr (ht.trans (norm_at_least_one I hi)))]
  · exact tsum_zero

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0834

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongCoefficient
Source SHA256: 809dc6fec469dab5af2e623e76f29766440af8500491ad8dc62c8113ef2ea06f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0835


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualLongCoefficient {ι:Type*}(p:ι→O)(Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)
    (I:Ideal O)(v:ι→₀ℕ) : ℂ :=
  separatedCubeCoefficient
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ v

theorem actualLongCoefficient_uniform (eps:ℝ)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*}(p:ι→O)(_hp:∀i,p i≠0)(Ψ:O→*ℂ)(_hΨ:∀x,‖Ψ x‖≤1)
      (m:O)(H₀ B ξ:ℝ)(I:Ideal O)(v:ι→₀ℕ),0<B→
      B≤‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2→
      ‖ConcreteTraceCRT.eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*B→
      ‖actualLongCoefficient p Ψ m H₀ B ξ I v‖≤C*(Real.exp 1*B)^eps := by
  obtain ⟨C,hC,hbound⟩:=reopenedCubeCoefficient_small_power eps heps
  refine ⟨C*Real.exp (1/2),mul_pos hC (Real.exp_pos _),?_⟩
  intro ι p hp Ψ hΨ m H₀ B ξ I v hB hlo hhi
  have hne:Ideal.span {primeProduct p v.support v}≠0 := by
    apply Ideal.span_singleton_eq_bot.not.mpr
    exact Finset.prod_ne_zero_iff.mpr (fun i hi=>pow_ne_zero _ (hp i))
  rw [eisEmbedding_norm_sq_eq_absNorm_span] at hlo hhi
  have hh:=hbound H₀ (rowTwist Ψ m (idealGenerator I) 1)
    (rowTwist_norm Ψ hΨ m (idealGenerator I) 1) _ hne
  have hb:‖reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p v.support v})‖≤C*(Real.exp 1*B)^eps :=
    hh.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hhi heps.le) hC.le)
  have hs:=separatedCubeCoefficient_bound
    (fun u:ι→₀ℕ=>reopenedCubeCoefficient H₀ (rowTwist Ψ m (idealGenerator I) 1)
      (Ideal.span {primeProduct p u.support u}))
    (fun u:ι→₀ℕ=>(Ideal.absNorm (Ideal.span {primeProduct p u.support u}):ℝ)) B ξ
    (C*(Real.exp 1*B)^eps) hB (by positivity) v hlo hhi hb
  unfold actualLongCoefficient
  convert hs using 1 ; ring

theorem actualLongCoefficient_complete
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(H₀ B ξ:ℝ)(I:Ideal O)
    (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ) :
    actualLongCoefficient (poolPrimary (InitialMeanSquare.outsideSquarefreeIdeals S D))
      Ψ (m*excludedGenerator S) H₀ B ξ I v=
    separatedCubeCoefficient
      (fun u=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1)
        (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u))
      (fun u=>(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) u):ℝ)) B ξ v := by
  simp only [actualLongCoefficient,cubeIdeal_eq_primeProduct_span _
    (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0835

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongFull
Source SHA256: 3c1a8f4feb59d86172933d65efb4c4ffd9735ee9ac6e1ca9f345aa676df31174
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0836









namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation FourierBridge CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem actual_long_dyadic_full_energy
    (om:𝓢(ℝ,ℂ))(a b:ℝ)(ha:0<a)(hs:Function.support om⊆Set.Icc a b) (Lcap Mmax eta tau saving:ℝ)(hcap:0≤Lcap)(hMmax:0≤Mmax)(hb:0≤b)
    (heta:0≤eta)(heta1:eta≤1)(htau:0<tau)(htau1:tau≤1):
    ∃(omega₁ omega₂:𝓢(ℝ,ℂ))(lo hi:ℝ),0<lo ∧ lo≤hi ∧
      HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀eps:ℝ,0<eps→∀J:ℕ,∃Ccoef C Czero Ctail:ℝ,0<Ccoef ∧ 0≤C ∧ 0≤Czero ∧ 0≤Ctail ∧
    ∀{ι σ:Type}[DecidableEq ι][DecidableEq σ](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
      (hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr:∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
      (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
      (Ψ:O→*ℂ)(m mCoef:O)
      (slots:Finset σ)(lists:σ→Finset ι)(weights:σ→ι→ℂ)
      (Z M r ell V H₀ ξ Benergy:ℝ)
      (_hZ:2≤Z)(_hbin:2≤Z^eta)(_hbinExp:Real.exp 1≤Z^eta)(_hM:0≤M)(_hF:r+3*ell+V≤Lcap)(_hMcap:M≤Mmax)(_hell:0≤ell)(_hV:0≤V)(_hr: -eta≤r)
      (_hbZ:b≤Z^eta)(_hQpool:∀v∈Q,v.support⊆pool)
      (_hQlo:∀v∈Q,Z^ell≤‖eisEmbedding (primeProduct p v.support v)‖^2)
      (_hQhi:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Real.exp 1*Z^ell)
      (_hrcap:r≤Lcap)(_hellcap:ell≤Lcap)

      (_hΨ:∀u,‖Ψ u‖≤1)(_hB:0≤Benergy)
      (_hsf:∀I∈labels,Squarefree I)(_hn:∀I∈labels,I≠0)
      (_hlabels:∀I∈labels,(Ideal.absNorm I:ℝ)≤Z^(V+eta))
      (_hslots:(slots:Set σ).PairwiseDisjoint lists)(_hweights:∀i∈slots,∀q∈lists i,‖weights i q‖≤1),
      let mark:=fun v U=>primeMark slots lists weights (v.support∪U);
      let Y:=Z^(2*Lcap+15*eta+tau);
      let cutoff:=fun (q:CubeCoordinates ι) (C:Finset ι) (_I:Ideal O) (D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
      let W:=fun y=>normTwistedSource om ξ (y/Z^r);
      let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
      let keys:=liveJointKeys p source pool (sourceSummand p hp hcop hg (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) cutoff Ψ m mark W rowMajorant (Z^M));
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 0))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.rightExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          true Ψ m slots lists weights omega₁
          ((physicalScales (Z^r) k.1 k.2.1) 7)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      (∀k∈keys,∀z:Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V (dyadicExponent Z (k.1 3)) (dyadicExponent Z (k.1 1))
          (dyadicExponent Z (k.1 2)) (dyadicExponent Z (k.1 4)))*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityOriginalEnergy p hg hp hinj (fun q=>q.leftExponent.support) pool
          (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k.1 k.2.1 k.2.2)
          (fun x=>(‖commonSelector p (fun _=>1) k.2.1 x.quotientSupport‖:ℂ))
          false Ψ m slots lists weights omega₂
          ((physicalScales (Z^r) k.1 k.2.1) 8)
          (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
          (firstCellRadius Z M r ell V eta tau k.1 k.2.2)≤Benergy*(tripleHeight J z.1*coordinateHeight J z.2))→
      Z^(-r-2*ell-V)*CanonicalRowCompletion.rowFamilyEnergy labels (fun I z=>
        varyingReopenedRow p hp hcop hg pool Q ((actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) I) Ψ m (ConcretePrimeRowBridge.idealGenerator I)
          (fun v U=>mark v U*W (primeProductNorm p U)) z) (Z^M)≤
        Czero*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Z^(M-ell+3*eta+eps*(5*ell+2*r+7*eta))+
        C*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Benergy*(1+‖ξ‖)^(2*InverseClippingProfiles.momentOrder J)*
          Z^((2*Lcap+15*eta+tau)*eps+eps)+Ctail*(Ccoef*(Real.exp 1*Z^ell)^eps)^2*Z^(-saving) := by
  obtain ⟨omega₁,omega₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,he⟩:=
    original_dyadic_full_energy om a b ha hs Lcap Mmax eta tau saving hcap hMmax hb heta heta1 htau htau1
  refine ⟨omega₁,omega₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro eps heps J
  obtain ⟨Ccoef,hCcoef,hcoef⟩:=actualLongCoefficient_uniform eps heps
  obtain ⟨C,Czero,Ctail,hC,hCzero,hCtail,hfull⟩:=he eps heps J
  refine ⟨Ccoef,C,Czero,Ctail,hCcoef,hC,hCzero,hCtail,?_⟩
  intro ι σ _ _ p hp _ hg hinj hcop hc hpr pool Q labels Ψ m mCoef slots lists weights
    Z M r ell V H₀ ξ Benergy hZ hbin hbinExp hM hF hMcap hell hV hr hbZ hQpool hQlo hQhi
    hrcap hellcap hΨ hB hsf hn hlabels hslots hweights mark Y cutoff W source keys hleft hright
  have hz:0<Z:=by linarith
  have hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta) := by
    intro v hv
    apply (hQhi v hv).trans
    calc
      Real.exp 1*Z^ell≤Z^eta*Z^ell:=mul_le_mul_of_nonneg_right hbinExp (Real.rpow_nonneg hz.le _)
      _=Z^(ell+eta):=by rw [Real.rpow_add hz];ring
  have hβ:∀I∈labels,∀v∈Q,
      ‖actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ I v‖≤Ccoef*(Real.exp 1*Z^ell)^eps := by
    intro I hI v hv
    exact hcoef p hp Ψ hΨ mCoef H₀ (Z^ell) ξ I v (Real.rpow_pos_of_pos hz _) (hQlo v hv) (hQhi v hv)
  exact hfull p hp hg hinj hcop hc hpr pool Q labels
    (actualLongCoefficient p Ψ mCoef H₀ (Z^ell) ξ) Ψ m slots lists weights
    Z M r ell V (Ccoef*(Real.exp 1*Z^ell)^eps) ξ Benergy hZ hbin hM hF hMcap hell hV hr hbZ
    hQpool hQ hrcap hellcap hΨ (by positivity) hB hsf hn hβ hlabels hslots hweights hleft hright

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0836

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongGeometry
Source SHA256: 3c228ce6ac1113840375dd35e9327b5331f3e569e108e1f66794c91051c2c0f7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0837


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve CanonicalCubeSeparation FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

def actualCubeLength (Z:ℝ)(j:ℕ):ℝ:=Real.logb Z (normLogScale j)

theorem actualCubeLength_power (Z:ℝ)(hZ:1<Z)(j:ℕ) :
    Z^(actualCubeLength Z j)=normLogScale j :=
  Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (normLogScale_pos j)

theorem actual_long_bin_geometry
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (b Z N V cutoff eta L:ℝ)(j:ℕ)(hZ:1<Z)(hL:1≤L)(heta:eta≤1)
    (hV:0≤V)(hparent:N+V≤L)(hb:b≤Z^eta)(hlog:1≤eta*Real.log Z)
    (hne:(progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j)).Nonempty) :
    let ell:=actualCubeLength Z j;
    let r:=N-3*ell;
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
    let Q:=progressingCubes S D (Z^(cutoff-V)) (activeCubeLogBin S D b (Z^N) j);
    0≤ell ∧ -eta≤r ∧ r≤L ∧ ell≤L ∧ r+3*ell+V≤L ∧ cutoff-eta≤ell+V ∧
      ∀v∈Q,Z^ell≤‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2 ∧
        ‖ConcreteTraceCRT.eisEmbedding (primeProduct (poolPrimary F) v.support v)‖^2≤Real.exp 1*Z^ell := by
  dsimp only
  have hz:0<Z:=zero_lt_one.trans hZ
  have hp:Z^(actualCubeLength Z j)=normLogScale j:=actualCubeLength_power Z hZ j
  have hel:0≤actualCubeLength Z j:=Real.logb_nonneg hZ (normLogScale_ge_one j)
  have hnorm (v:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ)
      (hv:v∈activeCubeLogBin S D b (Z^N) j) :
      Z^(actualCubeLength Z j)≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ) ∧
      (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)≤Real.exp 1*Z^(actualCubeLength Z j) := by
    rw [hp]
    exact activeCubeLogBin_norms S D b (Z^N) j v hv
  obtain ⟨v,hv⟩:=hne
  have hvbin: v∈activeCubeLogBin S D b (Z^N) j := (Finset.mem_filter.mp hv).1
  have hactive:= (Finset.mem_filter.mp hvbin).1
  have hcube:(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3≤b*Z^N :=
    (Finset.mem_filter.mp hactive).2
  have hsc:(Z^(actualCubeLength Z j))^3≤Z^(N+eta) := by
    calc
      _≤(Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v):ℝ)^3 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hz.le _) (hnorm v hvbin).1 3
      _≤b*Z^N:=hcube
      _≤Z^eta*Z^N:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(N+eta):=by rw [Real.rpow_add hz];ring
  rw [←Real.rpow_mul_natCast hz.le] at hsc
  have hscale:actualCubeLength Z j*3≤N+eta := (Real.rpow_le_rpow_left_iff hZ).mp hsc
  have hprogress:=long_cube_progress_with_slack S D (activeCubeLogBin S D b (Z^N) j)
    Z cutoff V (actualCubeLength Z j) eta hZ hlog ⟨v,hv⟩ (fun v hv=>(hnorm v hv).2)
  refine ⟨hel,by linarith,by linarith,by linarith,by linarith,hprogress,?_⟩
  intro u hu
  rw [cubeIdeal_primeProduct_norm _ (InitialMeanSquare.outsideSquarefree_admissible S D hbad)]
  exact hnorm u (Finset.mem_filter.mp hu).1

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0837

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongIntegral
Source SHA256: 1ace9c318e741ec03009f02dd78dec47408c99e4334f5148070a6a3b8dd4a772
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0838


namespace OAI

namespace SevenEighths.InverseMoment
noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory ActualEisensteinCubic CompletedGauss CanonicalRowCompletion
open ConcretePrimeRowBridge CanonicalQuadraticSieve SecondPassArithmetic FirstPassCubeLabels
open CanonicalCubeSeparation JointLogSeparation
local notation "O" => ActualEisensteinCubic.O

theorem actual_long_bin_normalized_energy
    {σ : Type*} [DecidableEq σ]
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Q : Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D) →₀ ℕ))
    (labels : Finset (Ideal O)) (Ψ : O →* ℂ) (m : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hb : 0≤b) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u| ≤ columnWindowRadius a b → V u = 1)
    (Z r cubeLength Vheight H₀ K E : ℝ) (d : ℕ)
    (hZ : 0 < Z) (hD : b*(Z^(r+3*cubeLength))≤D) (hK : 0 < K) (hE : 0 ≤ E)
    (hn : ∀ v ∈ Q, (Z^cubeLength) ≤ (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (InitialMeanSquare.outsideSquarefreeIdeals S D) v) : ℝ) ≤ Real.exp 1*(Z^cubeLength))
    (slots : Finset σ)
    (lists : σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (weights : σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    let F := InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF := InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun I v => reopenedCubeCoefficient H₀
      (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    (∀ ξ : ℝ, Z^(-r-2*cubeLength-Vheight)*rowFamilyEnergy labels (fun I z =>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Q
        (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ) Ψ m (idealGenerator I)
        (fun v T => primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K ≤
      E*(1+|ξ|)^(2*d)) →
    Z^(-Vheight)*rowFamilyEnergy labels (fun I z =>
      markedReopenedCubeBin S D Q Ψ m (idealGenerator I) z W (Z^(r+3*cubeLength)) H₀ slots lists weights) K ≤
      E *
        (∫ ξ : ℝ, ‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by
  dsimp only
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  let β:=fun I v=>reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) 1) (cubeIdeal F v)
  let n:=fun v=>(Ideal.absNorm (cubeIdeal F v):ℝ)
  intro hsource
  have hcancel:Z^(r+2*cubeLength+Vheight)*Z^(-r-2*cubeLength-Vheight)=1 := by
    rw [←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hpoint:∀ξ:ℝ,rowFamilyEnergy labels (fun I z=>
      varyingReopenedRow (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
        (poolPrimary_good F hF) Finset.univ Q (separatedCubeCoefficient (β I) n (Z^cubeLength) ξ)
        Ψ m (idealGenerator I)
        (fun v T=>primeMark slots lists weights (T∪v.support)*frequencyTwist V ξ (columnLog (poolPrimary F) (Z^r) T)) z) K≤
      (Z^(r+2*cubeLength+Vheight)*E)*(1+|ξ|)^(2*d) := by
    intro ξ
    have hh:=mul_le_mul_of_nonneg_left (hsource ξ) (Real.rpow_nonneg hZ.le (r+2*cubeLength+Vheight))
    rw [←mul_assoc,hcancel,one_mul] at hh
    simpa only [mul_assoc] using hh
  have hX:Z^(r+3*cubeLength)=(Z^cubeLength)^3*Z^r := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ]
    congr 1
    ring
  have hbnd:=markedReopenedCubeBin_energy S D hbad hSp Q labels Ψ m W a b ha hb hs hW V hV
    (Z^cubeLength) (Z^r) (Z^(r+3*cubeLength)) H₀ K (Z^(r+2*cubeLength+Vheight)*E) d
    (Real.rpow_pos_of_pos hZ _) (Real.rpow_pos_of_pos hZ _) hX hD hK (by positivity)
    hn hn' slots lists weights hpoint
  have hc:Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight)=1 := by
    rw [←Real.rpow_mul_natCast hZ.le,←Real.rpow_add hZ,←Real.rpow_neg hZ.le,
      ←Real.rpow_add hZ,←Real.rpow_add hZ]
    convert Real.rpow_zero Z using 2 ; ring
  have hh:=mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hZ.le (-Vheight))
  apply hh.trans_eq
  calc
    _=(Z^(-Vheight)*((Z^cubeLength)^2*Z^r)⁻¹*Z^(r+2*cubeLength+Vheight))*
      E*(∫ξ:ℝ,‖reopeningCoefficient W a b ha hs hW ξ‖*(1+|ξ|)^d)^2 := by ring
    _=_:=by rw [hc,one_mul]

end
end SevenEighths.InverseMoment

end OAI
end OAIOriginalModule0838

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongNormalization
Source SHA256: e134b8b53e5effd2f0e150118501fd31bd1b22a73c078a62bad1f0509c83a6ae
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0839




namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem child_ball_unit_mem (u:Oˣ)(R:ℝ)(k:O) :
    (u:O)*k∈nonzeroChildFrequencyBall 1 R ↔ k∈nonzeroChildFrequencyBall 1 R := by
  simp only [mem_nonzeroChildFrequencyBall 1 one_ne_zero,one_mul,
    GaussGeneratorTransport.norm_eisEmbedding_unit_mul]

theorem child_ball_unit_sum {A:Type*}[AddCommMonoid A](u:Oˣ)(R:ℝ)(f:O→A) :
    ∑k∈nonzeroChildFrequencyBall 1 R,f ((u:O)*k)=
      ∑k∈nonzeroChildFrequencyBall 1 R,f k := by
  apply Finset.sum_bij (fun k _=>(u:O)*k)
  · intro k hk
    exact (child_ball_unit_mem u R k).mpr hk
  · intro x hx y hy he
    exact mul_left_cancel₀ u.ne_zero he
  · intro y hy
    refine ⟨((u⁻¹:Oˣ):O)*y,(child_ball_unit_mem u⁻¹ R y).mpr hy,?_⟩
    rw [←mul_assoc,←Units.val_mul,mul_inv_cancel,Units.val_one,one_mul]
  · intros
    rfl

variable {ι σ:Type*}[DecidableEq ι]
  (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
  (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg:∀i,goodLambda∉Ideal.span {p i})

theorem canonical_ball_generator_energy
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(I:Ideal O)(hI:primaryGenerator I≠0)
    (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(W:ℝ→ℂ)(X K:ℝ) :
    (∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2)=
    ∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2 := by
  obtain ⟨u,hu⟩:=generator_eq_unit_primary I (idealGenerator I) (span_idealGenerator I) hI
  let P:O→ℝ:=fun k=>
    ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2
  have hrot:=child_ball_unit_sum (u^4) K P
  have he (k:O):
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2=
      P (((u^4:Oˣ):O)*k) := by
    rw [hu,finiteCanonicalMarkedRow_label_transfer]
    rfl
  simp only [he]
  exact hrot.symm

theorem normalized_energy_le_actual_family
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryGenerator I≠0)
    (weight:Ideal O→ℝ)(C:ℝ)(hC:0≤C)(hw:∀I∈labels,0≤weight I ∧ weight I≤C)
    (W:ℝ→ℂ)(X Z F K:ℝ)(hZ:0<Z)(hK:0<K) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 K) weight W X Z F ≤
      Z^(-F)*C*rowFamilyEnergy labels (fun I k=>
        finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X) K := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  have he : (∑ I∈labels,weight I*(Z^(-F)*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2))=
      Z^(-F)*(∑ I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 K,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (primaryGenerator I) k slots lists a W X‖^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros
    ring
  rw [he]
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hZ.le _)
  rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro I hI
  rw [canonical_ball_generator_energy p hp hcop hg pool Ψ m I (hlabels I hI)]
  have hball:=finite_nonzero_row_energy_le_majorant
    (fun k=>finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X)
    (nonzeroChildFrequencyBall 1 K) K hK
    (by intro k hk
        rw [←eisEmbedding_norm_sq_eq_absNorm_span]
        simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).2)
    (by intro k hk hn
        have hh:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero K k).mp hk).1
        simp only [hn,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hh)
  exact (mul_le_mul_of_nonneg_right (hw I hI).2 (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans
    (mul_le_mul_of_nonneg_left hball hC)

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0839

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalCompleteNormalized
Source SHA256: 938a23be99533e549dfbb01dfb5a00e01b31541e2fee3ac0c03746cbc53e6ae1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0840




namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem normalizedColumnEnergy_eq_generator_sum {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,primaryGenerator I≠0)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z F R:ℝ)(hZ:0<Z) :
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z F=
    Z^(-F)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X‖^2) := by
  have hn:‖((Z^(-F/2):ℝ):ℂ)‖^2=Z^(-F) := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hZ _),
      ←Real.rpow_mul_natCast hZ.le]
    congr 1
    ring
  unfold normalizedColumnEnergy
  simp only [norm_mul,mul_pow,hn,←Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  rw [canonical_ball_generator_energy p hp hcop hg pool Ψ m I (hlabels I hI)]
  ring

theorem outside_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)
    (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0<Z) :
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) k slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  exact (normalizedColumnEnergy_eq_generator_sum (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (hlabels I hI)) weight W X Z Fexp R hZ).symm

theorem reflection_complete_normalized_energy {σ:Type*}[DecidableEq σ]
    (q D:ℕ)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals (reflectionExcludedPrimes q) D)→ℂ)
    (labels:Finset (Ideal O))(hlabels:∀I∈labels,Supported I)
    (weight:Ideal O→ℝ)(W:ℝ→ℂ)(X Z Fexp R:ℝ)(hZ:0<Z) :
    let S:=reflectionExcludedPrimes q
    let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
    let hF:=InitialMeanSquare.outsideSquarefree_admissible S D (reflectionExcludedPrimes_bad q)
    letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
      fun i=>by rw [poolPrimary_span F hF i];infer_instance
    Z^(-Fexp)*(∑I∈labels,weight I*∑k∈nonzeroChildFrequencyBall 1 R,
      ‖outsideCanonicalMarkedRow S D (reflectionExcludedPrimes_bad q) Ψ m (idealGenerator I) k
        slots lists a W X‖^2)=
    normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
      (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ
      (ActualFiber.maskElement q m) slots lists a labels
      (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp := by
  have h:=outside_complete_normalized_energy (reflectionExcludedPrimes q) D
    (reflectionExcludedPrimes_bad q) Ψ m slots lists a labels hlabels weight W X Z Fexp R hZ
  exact h.trans (reflection_pool_mask_energy q D Finset.univ Ψ m slots lists a labels
    (nonzeroChildFrequencyBall 1 R) weight W X Z Fexp).symm

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0840

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongBins
Source SHA256: 361e42d600b50a7c65e96a3b3c8ee0b16c99ff78344944a39a2b6355752fbec9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0841


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns
local notation "O"=>ActualEisensteinCubic.O

theorem actual_marked_family_binned
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (hbad:fixedBadPrimes⊆S)(hSp:∀P∈S,Prime P)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(hWc:HasCompactSupport W)
    (b X H₀ K:ℝ)(hX:0<X)(hK:0<K)(hW:∀t,W t≠0→t≤b)(hD:b*X≤D)
    (slots:Finset σ)(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ) :
    rowFamilyEnergy labels (fun I z=>outsideCanonicalMarkedRow S D hbad Ψ m
      (idealGenerator I) z slots lists a W X) K ≤
    2*X*(rowFamilyEnergy labels (fun I z=>
      markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)) K+
      (cubeLogRange b X).card*∑j∈cubeLogRange b X,
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (idealGenerator I) z W X H₀ slots lists a) K) := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK]
  have he:∀I z,
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W X‖^2 ≤
      2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2) := by
    intro I z
    have hh:=original_marked_binned_energy S D Ψ m (idealGenerator I) z W b X H₀ slots lists a
      hbad hSp hWc hX hW hD
    have hs:(∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2)=
        ∑j∈cubeLogRange b X,
        ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
          Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2 := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [marked_long_filter S D (activeCubeLogBin S D b X j) Ψ m (idealGenerator I) z W X H₀ slots lists a]
    rw [hs] at hh
    exact hh
  calc
    _≤∑I∈labels,∑z∈(firstFrequencyDisk (2*K)).erase 0,
      (rowMajorant (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re *
      (2*X*(‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W X H₀
        (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)‖^2+
        (cubeLogRange b X).card*∑j∈cubeLogRange b X,
          ‖markedReopenedCubeBin S D (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
            Ψ m (idealGenerator I) z W X H₀ slots lists a‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      exact mul_le_mul_of_nonneg_left (he I z) (rowMajorant_nonneg _)
    _=_ := by
      simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        exact mul_left_comm _ _ _
      · simp_rw [Finset.sum_comm (s:=(firstFrequencyDisk (2*K)).erase 0) (t:=cubeLogRange b X)]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro I hI
        apply Finset.sum_congr rfl
        intro z hz
        ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0841

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongCount
Source SHA256: f1bbfb2acdb2b8d3ebf1869c234543c1395dbbb2af04aa3b33c4fdad2f13b846
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0842


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open CanonicalRowCompletion SecondPassArithmetic

theorem actual_cube_bin_count (b L eps:ℝ)(hb:0≤b)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀X Z:ℝ,0≤X→1≤Z→X≤Z^L→
      ((cubeLogRange b X).card:ℝ)^2≤C*Z^eps := by
  have hLp:0<L+1:=by linarith
  have hd:0<3*eps/(L+1):=by positivity
  obtain ⟨C,hC,hh⟩:=cubeLogRange_sq_small_power b (3*eps/(L+1)) hb hd
  refine ⟨C,hC,?_⟩
  intro X Z hX hZ hXL
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hscale:(Z^((L+1)/3))^3=Z^(L+1) := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    ring
  have hpow:(Z^((L+1)/3))^(3*eps/(L+1))=Z^eps := by
    rw [←Real.rpow_mul hz.le]
    congr 1
    field_simp
  have hbnd:=hh X (Z^((L+1)/3)) hX (Real.one_le_rpow hZ (by positivity))
    (by rw [hscale];exact hXL.trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)))
  simpa only [hpow] using hbnd

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0842

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongWeight
Source SHA256: 5fee752620b88ccac142922dbea1e6ba629c2bc90953d8e4d90b0100f2a3f95f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0843



namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem second_label_weight_uniform (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀(Z V:ℝ),1≤Z→V≤L→∀I:Ideal O,I≠0→
      (I.absNorm:ℝ)≤Z^V→secondLabelWeight K I≤C*Z^eps := by
  let delta:=eps/(L+1)
  have hd:0<delta:=div_pos heps (by linarith)
  obtain ⟨C,hC,hh⟩:=ideal_divisor_power_small (9+4*K) delta hd
  refine ⟨C,hC,?_⟩
  intro Z V hZ hV I hI hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hbudget:L*delta≤eps := by
    have he:(L+1)*delta=eps:=by dsimp [delta];field_simp
    nlinarith
  calc
    secondLabelWeight K I≤C*(I.absNorm:ℝ)^delta:=hh I hI
    _≤C*(Z^L)^delta:=by
      gcongr
      exact hnorm.trans (Real.rpow_le_rpow_of_exponent_le hZ hV)
    _=C*Z^(L*delta):=by rw [←Real.rpow_mul hz.le]
    _≤C*Z^eps:=by gcongr

theorem normalized_second_energy_le_actual_family (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,goodLambda∉Ideal.span {p i})
      (pool:Finset ι)(Ψ:O→*ℂ)(m:O)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (W:ℝ→ℂ)(X Z F V R:ℝ),1≤Z→0<R→V≤L→
      (∀I∈labels,(I.absNorm:ℝ)≤Z^V)→
      normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W X Z F≤
        C*Z^(-F+eps)*rowFamilyEnergy labels (fun I k=>
          finiteCanonicalMarkedRow p hp hcop hg pool Ψ m (idealGenerator I) k slots lists a W X) R := by
  obtain ⟨C,hC,hh⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro ι σ _ _ p hp _ hcop hg pool Ψ m slots lists a labels hlabels W X Z F V R hZ hR hV hnorm
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=normalized_energy_le_actual_family p hp hcop hg pool Ψ m slots lists a labels
    (fun I hI=>supported_primaryGenerator_ne_zero I (admissible_supported (hlabels I hI)))
    (secondLabelWeight K) (C*Z^eps) (by positivity)
    (fun I hI=>⟨by unfold secondLabelWeight;positivity,
      hh Z V hZ hV I (hlabels I hI).1 (hnorm I hI)⟩) W X Z F R hz hR
  convert hb using 1
  rw [Real.rpow_add hz]
  ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0843

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongCaller
Source SHA256: 4528b2ecce32768cce0c91695dd5119a02fff5179895383540cfe79b1eb9aff6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0844




namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers InverseInitialClippedColumns IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem normalized_complete_marked_split (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,Admissible I)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤Z→0<R→V≤L→(∀I∈labels,(I.absNorm:ℝ)≤Z^V)→
      (∀t,W t≠0→t≤b)→b*Z^N≤D→
      let F:=InitialMeanSquare.outsideSquarefreeIdeals S D;
      let hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad;
      letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
        fun i=>by rw [poolPrimary_span F hF i];infer_instance;
      normalizedColumnEnergy (poolPrimary F) (poolPrimary_ne_zero F hF)
        (poolPrimary_coprime F hF) (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels
        (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K) W (Z^N) Z (N+V)≤
      2*C*Z^(-V+eps)*(
        rowFamilyEnergy labels (fun I z=>markedShortCompletedSum
          (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z) W (Z^N) H₀
          (indexedIdealMark (fun i:primePool F=>i.val) slots lists a)) R+
        (cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
          rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
            (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
            Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R) := by
  obtain ⟨C,hC,hh⟩:=normalized_second_energy_le_actual_family K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀
    hZ hR hV hnorm hW hD
  let F:=InitialMeanSquare.outsideSquarefreeIdeals S D
  have hF:=InitialMeanSquare.outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal:=
    fun i=>by rw [poolPrimary_span F hF i];infer_instance
  dsimp only
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hb:=hh (poolPrimary F) (poolPrimary_ne_zero F hF) (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) Finset.univ Ψ m slots lists a labels hlabels W
    (Z^N) Z (N+V) V R hZ hR hV hnorm
  have hsplit:=actual_marked_family_binned S D hbad hSp labels Ψ m W hWc
    b (Z^N) H₀ R (Real.rpow_pos_of_pos hz _) hR hW hD slots lists a
  have hcost: C*Z^(-(N+V)+eps)*(2*Z^N)=2*C*Z^(-V+eps) := by
    calc
      _=2*C*(Z^(-(N+V)+eps)*Z^N):=by ring
      _=2*C*Z^(-V+eps):=by rw [←Real.rpow_add hz];congr 2;ring
  apply hb.trans
  have he:=mul_le_mul_of_nonneg_left hsplit (show 0≤C*Z^(-(N+V)+eps) by positivity)
  rw [←mul_assoc,hcost] at he
  exact he

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0844

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongAggregate
Source SHA256: cb0d2ffb8c4b7c02e87632e081eb343629110eb13c221e2b07daae0400d236ca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0845


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
local notation "O"=>ActualEisensteinCubic.O

 theorem actual_marked_bin_empty
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (Q:Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→₀ℕ))
    (Ψ:O→*ℂ)(m f z:O)(W:ℝ→ℂ)(X H₀:ℝ)(slots:Finset σ)
    (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (he:¬(progressingCubes S D H₀ Q).Nonempty) :
    markedReopenedCubeBin S D Q Ψ m f z W X H₀ slots lists a=0 := by
  rw [marked_long_filter,Finset.not_nonempty_iff_eq_empty.mp he]
  simp only [markedReopenedCubeBin,Finset.sum_empty]

theorem actual_large_bins_aggregate
    {σ:Type*}[DecidableEq σ](S:Finset (Ideal O))(D:ℕ)
    (labels:Finset (Ideal O))(Ψ:O→*ℂ)(m:O)(W:ℝ→ℂ)(b X H₀ R Z V E:ℝ)
    (slots:Finset σ)(lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
    (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
    (hbin:∀j∈cubeLogRange b X,
      (progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty→
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R≤E)
    (hE:0≤E) :
    Z^(-V)*((cubeLogRange b X).card*∑j∈cubeLogRange b X,
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R)≤
      ((cubeLogRange b X).card:ℝ)^2*E := by
  have hj (j:ℕ)(hj:j∈cubeLogRange b X) :
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R≤E := by
    by_cases hn:(progressingCubes S D H₀ (activeCubeLogBin S D b X j)).Nonempty
    · exact hbin j hj hn
    · rw [Finset.not_nonempty_iff_eq_empty.mp hn]
      simpa only [markedReopenedCubeBin,Finset.sum_empty,rowFamilyEnergy,
        nonzeroRowMajorantSum,norm_zero,zero_pow (by decide:2≠0),Complex.ofReal_zero,
        mul_zero,ite_self,tsum_zero,Finset.sum_const_zero,Complex.zero_re] using hE
  calc
    _=(cubeLogRange b X).card*∑j∈cubeLogRange b X,
      Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b X j))
        Ψ m (idealGenerator I) z W X H₀ slots lists a) R := by rw [←Finset.mul_sum];ring
    _≤(cubeLogRange b X).card*∑_j∈cubeLogRange b X,E := by
      gcongr
      exact hj _ ‹_›
    _=_ := by rw [Finset.sum_const,nsmul_eq_mul];ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0845

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongFinite
Source SHA256: d6107c0c8f844020d6e0cfbeb82461cc80fe880a94a782cb6a15e096dcbf4d4e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0846


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_finite_split (K:ℕ)(L eps:ℝ)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(b Z N V R H₀:ℝ),
      1≤Z → 0<R → V≤L → (∀I∈labels,(I.absNorm:ℝ)≤Z^V) →
      (∀t,W t≠0 → t≤b) → b*Z^N≤D →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2) ≤
      2*(Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2))+
      2*C*Z^(-V+eps)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
        rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R := by
  obtain ⟨C,hC,hweight⟩:=second_label_weight_uniform K L eps hL heps
  refine ⟨C,hC,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have hz:0<Z:=zero_lt_one.trans_le hZ
  let bins:=cubeLogRange b (Z^N)
  let short:=fun I z=>markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
    W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val) slots lists a)
  let long:=fun j I z=>markedReopenedCubeBin S D
    (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
    Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a
  let ball:=nonzeroChildFrequencyBall 1 R
  have hpoint (I:Ideal O)(z:O):
      ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2≤
      2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2) := by
    have hh:=original_marked_binned_energy S D Ψ m (idealGenerator I) z W b (Z^N) H₀ slots lists a
      hbad hSp hWc (Real.rpow_pos_of_pos hz _) hW hD
    convert hh using 1
    congr 2
    apply congrArg (fun x:ℝ=>(bins.card:ℝ)*x)
    apply Finset.sum_congr rfl
    intro j hj
    rw [marked_long_filter S D (activeCubeLogBin S D b (Z^N) j) Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a]
  have hlong (j:ℕ):
      (∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2)≤
      C*Z^eps*rowFamilyEnergy labels (long j) R := by
    rw [rowFamilyEnergy,Complex.re_sum,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro I hI
    have hb:=finite_nonzero_row_energy_le_majorant (long j I) ball R hR
      (by intro z hz;rw [←eisEmbedding_norm_sq_eq_absNorm_span]
          simpa only [one_mul] using ((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).2)
      (by intro z hz he
          have hn:=((mem_nonzeroChildFrequencyBall 1 one_ne_zero R z).mp hz).1
          simp only [he,mul_zero,map_zero,norm_zero,pow_succ,lt_self_iff_false] at hn)
    exact (mul_le_mul_of_nonneg_right (hweight Z V hZ hV I (hlabels I hI) (hnorm I hI))
      (Finset.sum_nonneg (fun _ _=>sq_nonneg _))).trans (mul_le_mul_of_nonneg_left hb (by positivity))
  have hsum:=Finset.sum_le_sum (s:=labels) (fun I hI=>
    mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=ball) (fun z hz=>hpoint I z))
      (show 0≤secondLabelWeight K I by unfold secondLabelWeight;positivity))
  have he:=mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg hz.le (-(N+V)))
  have hc:Z^(-(N+V))*Z^N=Z^(-V):=by rw [←Real.rpow_add hz];congr 1;ring
  have rearrange:
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈ball,
        2*Z^N*(‖short I z‖^2+bins.card*∑j∈bins,‖long j I z‖^2))=
      2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)+
      2*Z^(-V)*bins.card*∑j∈bins,∑I∈labels,secondLabelWeight K I*∑z∈ball,‖long j I z‖^2 := by
    simp only [mul_add,Finset.sum_add_distrib,Finset.mul_sum]
    simp_rw [Finset.sum_comm (s:=ball) (t:=bins)]
    rw [Finset.sum_comm (s:=labels) (t:=bins)]
    simp only [←Finset.mul_sum,mul_assoc,mul_left_comm]
    rw [←hc]
    ring
  rw [rearrange] at he
  apply he.trans
  have hj:=mul_le_mul_of_nonneg_left (Finset.sum_le_sum (s:=bins) (fun j hj=>hlong j))
    (show 0≤2*Z^(-V)*(bins.card:ℝ) by positivity)
  rw [←Finset.mul_sum] at hj
  have hpow:Z^(-V)*Z^eps=Z^(-V+eps):=(Real.rpow_add hz _ _).symm
  convert add_le_add_left hj (2*Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈ball,‖short I z‖^2)) using 1 <;>
    dsimp [bins,short,long,ball] <;> (try rw [←hpow]) <;> ring

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0846

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalLongTotal
Source SHA256: 2d255b9b3c463c35cf950d0c2b376efbb632ef8e1078f494c633eff3be3b061a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0847


namespace OAI

noncomputable section

open scoped BigOperators Classical
namespace SevenEighths.InverseMoment
open ActualEisensteinCubic CompletedGauss CanonicalRowCompletion ConcretePrimeRowBridge
open CanonicalQuadraticSieve FirstPassCubeLabels SecondPassArithmetic
open InverseSecondFibers IdealMobiusDivisorSum
local notation "O"=>ActualEisensteinCubic.O

theorem actual_complete_energy_from_live_bins (K:ℕ)(b L eps:ℝ)
    (hb:0≤b)(hL:0≤L)(heps:0<eps) :
    ∃C:ℝ,0<C ∧ ∀{σ:Type*}[DecidableEq σ]
      (S:Finset (Ideal O))(D:ℕ)(hbad:fixedBadPrimes⊆S)(_hSp:∀P∈S,Prime P)
      (labels:Finset (Ideal O))(_hlabels:∀I∈labels,I≠0)
      (Ψ:O→*ℂ)(m:O)(slots:Finset σ)
      (lists:σ→Finset (primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)))
      (a:σ→primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)→ℂ)
      (W:ℝ→ℂ)(_hWc:HasCompactSupport W)(Z N V R H₀ Eshort Elong:ℝ),
      1≤Z → 0<R → N≤L → V≤L → (∀I∈labels,(I.absNorm:ℝ)≤Z^V) →
      (∀t,W t≠0 → t≤b) → b*Z^N≤D → 0≤Elong →
      Z^(-V)*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖markedShortCompletedSum (rowTwist Ψ (m*excludedGenerator S) (idealGenerator I) z)
          W (Z^N) H₀ (indexedIdealMark (fun i:primePool (InitialMeanSquare.outsideSquarefreeIdeals S D)=>i.val)
            slots lists a)‖^2)≤Eshort →
      (∀j∈cubeLogRange b (Z^N),
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j)).Nonempty →
        Z^(-V)*rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
          (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
          Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R≤Elong) →
      Z^(-(N+V))*(∑I∈labels,secondLabelWeight K I*∑z∈nonzeroChildFrequencyBall 1 R,
        ‖outsideCanonicalMarkedRow S D hbad Ψ m (idealGenerator I) z slots lists a W (Z^N)‖^2)≤
      2*Eshort+C*Z^eps*Elong := by
  obtain ⟨Cw,hCw,hw⟩:=actual_complete_finite_split K L (eps/2) hL (by positivity)
  obtain ⟨Cb,hCb,hbnd⟩:=actual_cube_bin_count b L (eps/2) hb hL (by positivity)
  refine ⟨2*Cw*Cb,by positivity,?_⟩
  intro σ _ S D hbad hSp labels hlabels Ψ m slots lists a W hWc Z N V R H₀ Eshort Elong
    hZ hR hN hV hnorm hW hD hE hshort hlong
  have hz:0<Z:=zero_lt_one.trans_le hZ
  have hs:=hw S D hbad hSp labels hlabels Ψ m slots lists a W hWc b Z N V R H₀ hZ hR hV hnorm hW hD
  have ha:=actual_large_bins_aggregate S D labels Ψ m W b (Z^N) H₀ R Z V Elong slots lists a hlong hE
  have hc:=hbnd (Z^N) Z (Real.rpow_nonneg hz.le _) hZ (Real.rpow_le_rpow_of_exponent_le hZ hN)
  have hh:Z^(eps/2)*Z^(eps/2)=Z^eps := by rw [←Real.rpow_add hz];congr 1;ring
  have hp:Z^(-V+eps/2)=Z^(-V)*Z^(eps/2):=Real.rpow_add hz _ _
  have ha':2*Cw*Z^(-V+eps/2)*(cubeLogRange b (Z^N)).card*∑j∈cubeLogRange b (Z^N),
      rowFamilyEnergy labels (fun I z=>markedReopenedCubeBin S D
        (progressingCubes S D H₀ (activeCubeLogBin S D b (Z^N) j))
        Ψ m (idealGenerator I) z W (Z^N) H₀ slots lists a) R≤
      (2*Cw*Cb)*Z^eps*Elong := by
    have h1:=mul_le_mul_of_nonneg_left ha (show 0≤2*Cw*Z^(eps/2) by positivity)
    have h2:=mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hE)
      (show 0≤2*Cw*Z^(eps/2) by positivity)
    have ht:=h1.trans h2
    rw [hp]
    convert ht using 1
    · ring
    · rw [←hh];ring
  exact hs.trans (add_le_add (mul_le_mul_of_nonneg_left hshort (by norm_num:0≤(2:ℝ))) ha')

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0847

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalReopeningHeight
Source SHA256: 1de7cd1f92e4b6f35b7fe6cefe0d25d94dc4caf0b9e4fa4958296584ef9a2d23
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0848



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff

namespace SevenEighths.InverseMoment
open MeasureTheory CanonicalCubeSeparation FourierBridge JointLogSeparation CompletedHeight

theorem reopening_coefficient_twist (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(theta:ℝ)
    (hT:ContDiff ℝ ∞ (normTwistedSource W theta)):
    reopeningCoefficient (normTwistedSource W theta) a b ha
      ((normTwistedSource_support W theta).trans hs) hT=
      𝓕 (frequencyTwist (sourceLogProfile W a b ha hs hW) theta) :=by
  unfold reopeningCoefficient
  congr 1
  ext x
  simp only [sourceLogProfile_apply,frequencyTwist_apply,normTwistedSource,Real.log_exp]

theorem reopening_twisted_moment (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)≤
      C*(1+‖theta‖)^(J+(volume:Measure ℝ).integrablePower) :=by
  obtain ⟨C,hC,he⟩:=frequencyTwist_fourier_moment J (sourceLogProfile W a b ha hs hW)
  refine ⟨C,hC,?_⟩
  intro theta hT
  rw [reopening_coefficient_twist W a b ha hs hW theta hT]
  simpa only [Real.norm_eq_abs,mul_comm] using he theta

theorem reopening_twisted_moment_squared (W:ℝ→ℂ)(a b:ℝ)(ha:0<a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(J:ℕ):
    ∃C:ℝ,0≤C ∧ ∀theta:ℝ,∀hT:ContDiff ℝ ∞ (normTwistedSource W theta),
      (∫ξ:ℝ,‖reopeningCoefficient (normTwistedSource W theta) a b ha
        ((normTwistedSource_support W theta).trans hs) hT ξ‖*(1+|ξ|)^J)^2≤
      C*(1+‖theta‖)^(2*(J+(volume:Measure ℝ).integrablePower)) :=by
  obtain ⟨C,hC,he⟩:=reopening_twisted_moment W a b ha hs hW J
  refine ⟨C^2,sq_nonneg _,?_⟩
  intro theta hT
  have hh:=pow_le_pow_left₀ (integral_nonneg (fun ξ=>by positivity)) (he theta hT) 2
  simpa only [mul_pow,←pow_mul,Nat.mul_comm] using hh

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0848

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepGates
Source SHA256: 783da7d8457af02743f11e56f27e0dd93477ca4d1b4881f9a6461be183f17f99
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0849




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

def extra (negative : Bool) (c : CubeCoordinates ι) : Finset ι :=
  if negative then c.rightExponent.support else c.leftExponent.support

lemma extra_subset (negative : Bool) (c : CubeCoordinates ι) : extra negative c⊆c.support := by
  cases negative
  · exact Finset.subset_union_left
  · exact Finset.subset_union_right

lemma dyadic_exponent_nonneg (Z : ℝ) (hZ : 1<Z) (n : ℕ) :
    0≤InverseFirstGlobalCaps.dyadicExponent Z n :=
  Real.logb_nonneg hZ (by unfold dyadScale;exact one_le_pow₀ (by norm_num : (1:ℝ)≤2))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma label_parent_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,SourceValid p y := by
  intro y hy
  obtain ⟨o,ho,D,hD,hs,rfl⟩ := (InverseFirstGlobalCaps.mem_parentCell p pool Q (fun _ _=>1) k l y).mp
    (Finset.mem_filter.mp hy).1
  exact original_fill_valid p pool Q o (Finset.mem_filter.mp ho).1 D

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem label_parent_bounds (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit)
        ≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p y.firstCommon≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      primeProductNorm p y.quotientSupport≤Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤InverseFirstGlobalCaps.jNorm p (toOriginal y) ∧
      InverseFirstGlobalCaps.jNorm p (toOriginal y)≤Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p y.firstDivisor≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro y hy
  have hparent := (Finset.mem_filter.mp hy).1
  have hc := InverseFirstGlobalCaps.parentCell_cube_bounds p pool Q (fun _ _=>1) k l Z ell eta hQ y hparent
  have hn := InverseFirstGlobalCaps.parentCell_norm_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hi := InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l Z eta hZ hbin y hparent
  have hj := InverseFirstGlobalCaps.labelParentCell_bounds p hp pool Q (fun _ _=>1) k l j Z eta hZ hbin y hy
  refine ⟨hc.1,hc.2,?_,hi.1.2,?_,?_,hj.2.2,?_⟩
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.2.2
  · simpa only [hn.2.1] using hn.2.2.2
  · exact (Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)).trans hj.2.1
  · simpa only [InverseFirstGlobalCaps.sourceIdeal_norm] using hi.2.1.2

include hp in

theorem retained_label_numeric (pool : Finset ι) (Q : Finset (ι→₀ℕ))
    (k : SourceIndex) (l j : ℕ) (Z ell eta : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (cutoff : Finset ι→Finset ι→ℝ) (b X : ℝ) :
    let source := supportedRetainedSource p (extra negative)
      (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j) negative J lists pool cutoff b X
    ∀x∈source,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(InverseFirstGlobalCaps.dyadicExponent Z l+eta) ∧
      Z^(InverseFirstGlobalCaps.dyadicExponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(InverseFirstGlobalCaps.dyadicExponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(InverseFirstGlobalCaps.dyadicExponent Z (k 3)+eta) := by
  intro source x hx
  have h := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact original_numeric_gates p (extra negative) _ negative J lists pool cutoff _ _ _ _ _ _ _
    (fun y hy=>(h y hy).1) (fun y hy=>(h y hy).2.1) (fun y hy=>(h y hy).2.2.1)
    (fun y hy=>(h y hy).2.2.2.1) (fun y hy=>(h y hy).2.2.2.2.1)
    (fun y hy=>⟨(h y hy).2.2.2.2.2.1,(h y hy).2.2.2.2.2.2.1⟩)
    (fun y hy=>(h y hy).2.2.2.2.2.2.2) x (supported_subset p _ _ negative J lists pool cutoff b X hx)

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end OAIOriginalModule0849

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepSource
Source SHA256: c4baf5bd0c7877ff07cb157028ddb47c104e489dabe3965bce21f70e0fead083
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0850


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

abbrev exponent := InverseFirstGlobalCaps.dyadicExponent

def columnA (Z : ℝ) (k : SourceIndex) (negative : Bool) : ℝ :=
  exponent Z (k (if negative then 0 else 1))

def columnScale (Z r : ℝ) (k : SourceIndex) (l : ℕ) (negative : Bool) : ℝ :=
  Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l)

def secondCutoff (p : ι→O) (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (G E : Finset ι) : ℝ :=
  uniformSecondRadius p Z (exponent Z (k 3)) eta G E
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)

def source (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :=
  supportedRetainedSource p (extra negative)
    (InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j)
    negative J lists pool (secondCutoff p Z M r ell V eta tau window k l j negative)
    b (columnScale Z r k l negative)

variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_valid (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ActualSecondSourceConditions p (source p pool Q k l j negative J lists Z M r ell V eta tau window b) :=
  supported_conditions p hp _ _ (label_parent_valid p pool Q k l j) (fun y _hy=>extra_subset negative y.cube)
    negative J lists pool _ b _

lemma source_frequency_ne_zero (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,x.second.frequency≠0 :=
  supported_frequency_ne_zero p _ _ negative J lists pool _ b _

lemma source_geometry (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative :=
  geometrySource_gate p _ b _

include hp in
theorem source_row_gates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hwindow : Real.exp window≤Z^(4*eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) := by
  intro S
  have hz : 0<Z := zero_lt_one.trans hZ
  have hc : columnScale Z r k l negative*Real.exp window≤
      Z^(r-columnA Z k negative-exponent Z (k 2)-exponent Z l+4*eta) := by
    unfold columnScale
    rw [Real.rpow_add hz]
    exact mul_le_mul_of_nonneg_left hwindow (Real.rpow_nonneg hz.le _)
  exact supported_cell_row_gates p hp _ _ negative J lists pool Z M r ell V (exponent Z (k 3))
    (columnA Z k negative) (exponent Z (k 2)) (exponent Z j) (exponent Z l) eta tau
    (columnScale Z r k l negative*Real.exp window) b (columnScale Z r k l negative)
    hZ heta hbin (by unfold columnScale;positivity) hc

include hp in
theorem source_outer_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap : ℝ)
    (hZ : 1<Z)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap) :
    ∀x∈source p pool Q k l j negative J lists Z M r ell V eta tau window b,
      ∀i,outerNorms p x i≤Z^Lcap := by
  exact supported_outer_caps p hp _ _ negative J lists pool Z (exponent Z (k 3)) eta
    (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j)
    tau b (columnScale Z r k l negative) Lcol LY Lcap hZ.le
    (by unfold columnScale;positivity) (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    hcol hYi hgeom hphysical

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end OAIOriginalModule0850

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepChildren
Source SHA256: 9272abd398c306d5dc69dc0774254d0917b4073ee62d0579c51e9b8cfc5ed7be
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0851


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_labels (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤
        Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_label_gates p hp _ _ negative J lists pool _ b (columnScale Z r k l negative)
    Z (exponent Z (k 2)) (exponent Z j) eta hZ hbin
    (fun y hy=>(hb y hy).2.2.2.1) (fun y hy=>(hb y hy).2.2.2.2.2.2.1)

include hp in
theorem source_child_margins
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b : ℝ)
    (m : O) (hm : m≠0) (Qwidth z c : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hV : 0≤V)
    (hparent : CanonicalMargins (r+3*ell+V) M Qwidth z c)
    (hpuncture : (Ideal.absNorm (Ideal.span {m}:Ideal O).radical:ℝ)≤Z^Qwidth)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d,∀γ∈actualSecondTriples p 1 1 (cell p S d),
      actualSecondInheritedRadicalPuncture m γ≠0 ∧ 0≤actualSecondPunctureWidth Z m γ ∧
      ‖eisEmbedding (actualSecondInheritedRadicalPuncture m γ)‖^2=Z^(actualSecondPunctureWidth Z m γ) ∧
      CanonicalMargins (actualCellTotalExponent Z (columnScale Z r k l negative)
        (exponent Z (k 2)) (exponent Z j) eta d)
        (childM M ell (columnA Z k negative) (exponent Z l) (secondCellExponent Z d 0)
          (secondCellExponent Z d 1) V (exponent Z j) eta)
        (actualSecondPunctureWidth Z m γ) z (c-7*eta) := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_child_margins p hp hpr _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=>extra_subset negative y.cube) negative J lists pool _ b m hm
    Z r ell V M Qwidth z c (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta
    hZ hparent (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hV
    (dyadic_exponent_nonneg Z hZ _) heta hbin hpuncture
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.1)

include hp in
theorem source_row_decrease (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b short : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta)
    (hterminal : short≤ell+V) (hsmall : eta≤short/16)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,actualCellRowExponent Z M ell (columnA Z k negative)
      (exponent Z l) V (exponent Z j) eta d+3*short/2≤M := by
  intro S
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ
  exact supported_row_rank_decrease p hp _ _ (label_parent_valid p pool Q k l j)
    (fun y hy=>extra_subset negative y.cube) negative J lists pool _ b (columnScale Z r k l negative)
    Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta short hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta hbin hterminal hsmall
    (fun y hy=>(hb y hy).1) (fun y hy=>(hb y hy).2.1) (fun y hy=>(hb y hy).2.2.2.2.2.1)

include hp in
theorem source_mass_gate (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heps : 0≤eps)
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi := by
  intro S
  exact source_cell_mass_gate p hp S (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    Z Lcap ell (exponent Z (k 4)) (exponent Z j) (exponent Z l) eta eps pi hZ
    (dyadic_exponent_nonneg Z hZ _) heps
    (source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical) hbudget

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end OAIOriginalModule0851

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstCanonicalChildren
Source SHA256: 14ab506c4d7114d8918f67c057d594c5b390957f84281876ffcc97417302ba51
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0852



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstGlobalCaps InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ:Type*}[DecidableEq ι][DecidableEq σ]
variable (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_total_cap (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,actualCellTotalExponent Z (columnScale Z r k l negative)
      (exponent Z (k 2)) (exponent Z j) eta d≤r+3*ell+V+15*eta :=by
  intro S d hd
  obtain ⟨x,hx⟩:=(mem_keys_iff p S d).mp hd
  have hn:=retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists
    (secondCutoff p Z M r ell V eta tau window k l j negative) b (columnScale Z r k l negative)
    x (cell_subset p S d hx)
  have he:=actual_cell_child_total_upper p hp S
    (source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b)
    (source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b)
    d x hx Z r ell V (columnA Z k negative) (exponent Z (k 2)) (exponent Z l) (exponent Z j) eta b hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) hell hV heta hbin hb hbt
    (source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b)
    hn.1 hn.2.1 hn.2.2.2.2.2.1
  exact he

include hp in
theorem source_state_bounds (pool:Finset ι)(Q:Finset (ι→₀ℕ))(k:SourceIndex)(l j:ℕ)
    (negative:Bool)(J:Finset σ)(lists:σ→Finset ι)(Z M r ell V eta tau window b cutoff:ℝ)
    (hZ:1<Z)(heta:0≤eta)(hbin:2≤Z^eta)(hell:0≤ell)(hV:0≤V)
    (hb:1≤b)(hbt:b≤Z^(6*eta))(hwindow:Real.exp window≤Z^(4*eta))
    (hterminal:cutoff≤ell+V)(hsmall:eta≤cutoff/16)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta)):
    let S:=source p pool Q k l j negative J lists Z M r ell V eta tau window b;
    ∀d∈keys p S,
      0≤max 0 (secondCellColumnExponent Z (columnScale Z r k l negative) d) ∧
      0≤actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d ∧
      actualCellTotalExponent Z (columnScale Z r k l negative) (exponent Z (k 2)) (exponent Z j) eta d≤r+3*ell+V+15*eta ∧
      0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d ∧
      actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d+3*cutoff/2≤M :=by
  intro S d hd
  refine ⟨le_max_left _ _,actual_cell_label_nonneg Z _ _ eta d hZ
    (dyadic_exponent_nonneg Z hZ _) (dyadic_exponent_nonneg Z hZ _) heta,?_,?_,?_⟩
  · exact source_total_cap p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hell hV hb hbt hQ d hd
  · exact (source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow).2 d hd
  · exact source_row_decrease p hp pool Q k l j negative J lists Z M r ell V eta tau window b cutoff hZ heta hbin hterminal hsmall hQ d hd

end SevenEighths.InverseMomentFirstLabelCell

end

end OAI
end OAIOriginalModule0852

/-! Original module: OAI.NumberTheory.DirichletL.Descent.CanonicalChildSupport
Source SHA256: 144dc4c2b149a3635dbd857081a98116c28dd3474277598a2629e649be25fb4b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0853


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic CanonicalQuadraticSieve
open InverseInitialArithmetic InverseSecondSourceBlocks InverseSecondFibers
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[DecidableEq ι](p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
variable (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
variable (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_prime_supported (i:ι):Supported (Ideal.span {p i}) :=by
  have hn:(Ideal.span {p i}:Ideal O)≠0:=Ideal.span_singleton_eq_bot.not.mpr (hp i)
  refine ⟨hn,?_⟩
  intro P hP
  obtain ⟨hprime,hle⟩:=(Ideal.mem_normalizedFactors_iff hn).mp hP
  have he:Ideal.span {p i}=P:=(inferInstance:(Ideal.span {p i}:Ideal O).IsMaximal).eq_of_le hprime.ne_top hle
  subst P
  exact ⟨hg i,hc i⟩

lemma canonical_supported_prod {α:Type*}(S:Finset α)(f:α→Ideal O)
    (hf:∀i∈S,Supported (f i)):Supported (∏i∈S,f i) :=by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Supported (1:Ideal O)
    refine ⟨one_ne_zero,?_⟩
    intro P hP
    rw [UniqueFactorizationMonoid.normalizedFactors_one] at hP
    exact (Multiset.notMem_zero P hP).elim
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi,supported_mul_iff]
    exact ⟨hf i (Finset.mem_insert_self _ _),ih (fun j hj=>hf j (Finset.mem_insert_of_mem hj))⟩

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_source_ideal_supported (S:Finset ι):Supported (sourceIdeal p S) :=by
  rw [sourceIdeal,FiniteGaussPhase.span_finset_prod]
  exact canonical_supported_prod S (fun i=>Ideal.span {p i}) (fun i _=>canonical_source_prime_supported p hp hg hc i)

include hp hg hc in
omit [DecidableEq ι] in
lemma canonical_prime_product_supported (S:Finset ι)(v:ι→ℕ):Supported (Ideal.span {primeProduct p S v}) :=by
  rw [primeProduct,FiniteGaussPhase.span_finset_prod]
  apply canonical_supported_prod
  intro i hi
  rw [←Ideal.span_singleton_pow]
  exact supported_pow (canonical_source_prime_supported p hp hg hc i) _

include hp hg hc in
lemma actual_second_label_supported {Jo Jn:ℕ}(x:MarkedSecondSource ι Jo Jn):
    Supported (actualSecondChild p 1 1 x).2.1 :=by
  change Supported ((Ideal.span {jLabel p x.cube.support
    (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit})*
    sourceIdeal p x.firstCommon*sourceIdeal p x.second.divisor*sourceIdeal p x.second.overlap)
  simp only [supported_mul_iff]
  exact ⟨⟨⟨canonical_prime_product_supported p hp hg hc _ _,canonical_source_ideal_supported p hp hg hc _⟩,
    canonical_source_ideal_supported p hp hg hc _⟩,canonical_source_ideal_supported p hp hg hc _⟩

include hp hg hc in
theorem actual_cell_labels_supported {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈actualCellLabels p S d,Supported I :=by
  intro I hI
  obtain ⟨x,hx,rfl⟩:=Finset.mem_image.mp hI
  exact actual_second_label_supported p hp hg hc x

include hp hg hc in
theorem actual_cell_labels_admissible {Jo Jn:ℕ}(S:Finset (MarkedSecondSource ι Jo Jn))(d:BlockIndex):
    ∀I∈(actualCellLabels p S d).filter Squarefree,CanonicalQuadraticSieve.Admissible I :=by
  intro I hI
  obtain ⟨hm,hs⟩:=Finset.mem_filter.mp hI
  have hh:=actual_cell_labels_supported p hp hg hc S d I hm
  exact ⟨hh.1,hs,hh.2⟩

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0853

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepData
Source SHA256: 94421dc998d39866f847c72800afd8d07359baa9a01563837666a390ce40b2a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0854


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
variable (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem source_step_arithmetic (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (J : Finset σ) (lists : σ→Finset ι) (Z M r ell V eta tau window b Lcol LY Lcap eps pi : ℝ)
    (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (heps : 0≤eps)
    (hwindow : Real.exp window≤Z^(4*eta))
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hcol : columnScale Z r k l negative*Real.exp window≤Z^Lcol)
    (hYi : (firstCellRadius Z M r ell V eta tau k j)⁻¹≤Z^LY)
    (hgeom : b*columnScale Z r k l negative≤Z^Lcap)
    (hphysical : exponent Z (k 3)+eta+2*Lcol+tau+LY≤Lcap)
    (hbudget : eps*(ell+exponent Z (k 4)/2+exponent Z l+Lcap+11*eta/2)≤pi) :
    let S := source p pool Q k l j negative J lists Z M r ell V eta tau window b
    ActualSecondSourceConditions p S ∧
    (∀x∈S,x.second.frequency≠0) ∧
    (∀x∈S,x.second.frequency∈nonzeroChildFrequencyBall (actualSecondMultiplier p x)
      (actualCellRowRadius Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta (index p x))) ∧
    (∀d∈keys p S,0≤actualCellRowExponent Z M ell (columnA Z k negative) (exponent Z l) V (exponent Z j) eta d) ∧
    (∀x∈S,
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤Z^(ell+eta) ∧
      ‖eisEmbedding (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤Z^(ell+eta) ∧
      primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)
        ≤Z^(exponent Z (k 4)+eta) ∧
      primeProductNorm p x.firstCommon≤Z^(exponent Z (k 2)+eta) ∧
      (Ideal.absNorm x.quotient:ℝ)≤Z^(exponent Z l+eta) ∧
      Z^(exponent Z j-eta)≤
        ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit)‖^2 ∧
      ‖eisEmbedding (jLabel p x.cube.support (fun i=>x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)‖^2≤Z^(exponent Z j+eta) ∧
      primeProductNorm p x.firstDivisor≤Z^(exponent Z (k 3)+eta)) ∧
    (∀d,∀x∈cell p S d,(actualSecondChild p 1 1 x).2.1∈actualCellLabels p S d) ∧
    (∀d,∀I∈(actualCellLabels p S d).filter Squarefree,
      Squarefree I ∧ I≠0 ∧ (Ideal.absNorm I:ℝ)≤Z^(actualCellLabelExponent Z (exponent Z (k 2)) (exponent Z j) eta d)) ∧
    (∀x∈S,∀i,outerNorms p x i≤Z^Lcap) ∧
    (∀x∈S,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤b*columnScale Z r k l negative) ∧
    (∀d∈keys p S,eps*(secondCount ell (exponent Z (k 4)) (exponent Z j) (exponent Z l)
      (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)≤pi) := by
  intro S
  have hr := source_row_gates p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hwindow
  have hl := source_labels p hp pool Q k l j negative J lists Z M r ell V eta tau window b hZ heta hbin hQ
  exact ⟨source_valid p hp pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_frequency_ne_zero p pool Q k l j negative J lists Z M r ell V eta tau window b,
    hr.1,hr.2,
    retained_label_numeric p hp pool Q k l j Z ell eta hZ heta hbin hQ negative J lists _ b _,
    hl.1,hl.2,
    source_outer_caps p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap
      hZ hcol hYi hgeom hphysical,
    source_geometry p pool Q k l j negative J lists Z M r ell V eta tau window b,
    source_mass_gate p hp pool Q k l j negative J lists Z M r ell V eta tau window b Lcol LY Lcap eps pi
      hZ heps hcol hYi hgeom hphysical hbudget⟩

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end OAIOriginalModule0854

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLabelCellStepPhysicalGates
Source SHA256: 087f8b0ba97eedcc132af88c20e873f0cc1f492681a87af39fe3d5c844e928f1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0855


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.InverseMomentFirstLabelCell
open InverseMoment ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseFirstPriorityParents InverseFirstGlobalParents
open InverseMomentGlobalRetainedGates InverseInitialArithmetic InverseSecondSourceBlocks
open InverseSecondUniformCutoff InversePrioritySecondSource
open ConcreteTraceCRT (eisEmbedding)
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) (hp : ∀i,p i≠0)

def parentWeight (l : ℕ) (x : Source ι 0) : ℂ :=
  (‖commonSelector p (fun _=>1) l x.quotientSupport‖:ℂ)

lemma parentWeight_norm (l : ℕ) (x : Source ι 0) : ‖parentWeight p l x‖≤1 := by
  simp only [parentWeight,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
  simpa using InverseFirstGlobalCaps.commonSelector_norm p (fun _=>1) l x.quotientSupport

lemma secondCutoff_nonneg (Z M r ell V eta tau window : ℝ) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (hZ : 0<Z) (G E : Finset ι) :
    0≤secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  apply uniformSecondRadius_nonneg _ _ _ _ _ _ _ _ _ hZ.le
  · unfold firstCellRadius
    positivity
  · exact Real.rpow_nonneg hZ.le _

include hp in
theorem secondCutoff_dominates (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (negative : Bool) (Z M r ell V eta tau window : ℝ) (hZ : 1<Z) (hbin : 2≤Z^eta) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,∀G E : Finset ι,
      correlatedSecondRadius p (secondParentDivisor p (parent p y)) G E
        (columnScale Z r k l negative*Real.exp window) (firstCellRadius Z M r ell V eta tau k j) (Z^tau)≤
      secondCutoff p Z M r ell V eta tau window k l j negative G E := by
  intro y hy G E
  have hd := (InverseFirstGlobalCaps.parentCell_ideal_bounds p hp pool Q (fun _ _=>1) k l
    Z eta hZ hbin y (Finset.mem_filter.mp hy).1).2.1.2
  apply correlated_le_uniform p Z (exponent Z (k 3)) eta _ G E _ _ _
    (by unfold firstCellRadius;exact Real.rpow_pos_of_pos (zero_lt_one.trans hZ) _)
    (Real.rpow_nonneg (zero_lt_one.trans hZ).le _)
  simpa [secondParentDivisor,parent,InverseFirstGlobalCaps.sourceIdeal_norm,
    primeSubsetGenerator_norm_eq_productNorm] using hd

include hp in
theorem parent_tail_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l j : ℕ)
    (Z ell eta Lcap : ℝ) (hZ : 1<Z) (heta : 0≤eta) (hbin : 2≤Z^eta) (hcap : 0≤Lcap)
    (hQ : ∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hell : ell+eta≤Lcap) (hactive : exponent Z (k 4)+eta≤Lcap)
    (hcommon : exponent Z (k 2)+eta≤Lcap) (hquot : exponent Z l+eta≤Lcap) :
    ∀y∈InverseFirstGlobalCaps.labelParentCell p pool Q (fun _ _=>1) k l j,
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.leftExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (primeProduct p y.cube.support y.cube.rightExponent)‖^2≤Z^Lcap ∧
      ‖eisEmbedding (∏i∈cubeActiveSupport y.cube.support
        (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i)‖≤Z^Lcap ∧
      primeProductNorm p y.firstCommon≤Z^Lcap ∧ primeProductNorm p y.quotientSupport≤Z^Lcap := by
  intro y hy
  have hb := label_parent_bounds p hp pool Q k l j Z ell eta hZ heta hbin hQ y hy
  have hpw {a : ℝ} (ha : a≤Lcap) : Z^a≤Z^Lcap := Real.rpow_le_rpow_of_exponent_le hZ.le ha
  refine ⟨hb.1.trans (hpw hell),hb.2.1.trans (hpw hell),?_,
    hb.2.2.2.1.trans (hpw hcommon),hb.2.2.2.2.1.trans (hpw hquot)⟩
  have he := hb.2.2.1.trans (hpw hactive)
  have hone := Real.one_le_rpow hZ.le hcap
  change ‖eisEmbedding (∏i∈_,p i)‖^2≤Z^Lcap at he
  have hn := norm_nonneg (eisEmbedding (∏i∈cubeActiveSupport y.cube.support
    (fun i=>y.cube.leftExponent i+y.cube.rightExponent i) y.cube.leftBit y.cube.rightBit,p i))
  nlinarith

end SevenEighths.InverseMomentFirstLabelCell
end

end OAI
end OAIOriginalModule0855

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveColumnScale
Source SHA256: 37a09bd5c516be209ef94f74a1dbee7f34682ca3ccbd26cb01edfa8b3cb20ef1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0856




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem first_profile_live_products (W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L:ℝ)(q:Fin 9→ℝ)
    (hq:∀i,1≤q i)(hW:∀x,W x≠0→x≤L)
    (hn:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K q≠0):
    q 0*q 2*q 5≤L ∧ q 1*q 2*q 5≤L:=by
  have h₁:W (q 0*q 2*q 5*q 7)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  have h₂:W (q 1*q 2*q 5*q 8)≠0:=by intro h;apply hn;simp [firstNormProfile,h]
  constructor
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (zero_le_one.trans (hq 0)) (zero_le_one.trans (hq 2))) (zero_le_one.trans (hq 5))) (hq 7)).trans (hW _ h₁)
  · exact (le_mul_of_one_le_right (mul_nonneg (mul_nonneg (zero_le_one.trans (hq 1)) (zero_le_one.trans (hq 2))) (zero_le_one.trans (hq 5))) (hq 8)).trans (hW _ h₂)

private theorem dyadic_column_scale {a c z X b : ℝ}
    (ha : 1 ≤ a) (hc : 1 ≤ c) (hz : 1 ≤ z) (hprod : a * c * z ≤ b * X) :
    1 ≤ X / (dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z)) * b := by
  have hscale : dyadScale (dyadIndex a) * dyadScale (dyadIndex c) *
      dyadScale (dyadIndex z) ≤ a * c * z :=
    mul_le_mul
      (mul_le_mul (dyadIndex_bounds a ha).1 (dyadIndex_bounds c hc).1
        (dyadScale_pos _).le (zero_le_one.trans ha))
      (dyadIndex_bounds z hz).1 (dyadScale_pos _).le
      (mul_nonneg (zero_le_one.trans ha) (zero_le_one.trans hc))
  rw [div_mul_eq_mul_div,
    le_div_iff₀ (mul_pos (mul_pos (dyadScale_pos _) (dyadScale_pos _)) (dyadScale_pos _)),
    one_mul, mul_comm X b]
  exact hscale.trans hprod

theorem original_live_column_scale {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K X b:ℝ)
    (_hX:0<X)(hW:∀y,W y≠0→y≤b*X)
    (k:JointKey)(hk:k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K)):
    1≤physicalScales X k.1 k.2.1 7*b ∧ 1≤physicalScales X k.1 k.2.1 8*b:=by
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  have hs:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hq:∀i,1≤firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
      (divisorElement p x.1) x.2.2 j i:=by
    intro i
    fin_cases i
    · exact hs 0
    · exact hs 1
    · exact hs 2
    · exact hs 3
    · exact hs 4
    · exact primeProductNorm_ge_one p hp _
    · exact hs 5
    · exact primeProductNorm_ge_one p hp _
    · exact primeProductNorm_ge_one p hp _
  have hprof:firstNormProfile (fun y=>star (W y)) W Φ (fun _ _=>1) K
      (firstCommonNorms p (leftNorm p x) (rightNorm p x) (commonNorm p x) (activeNorm p x)
        (divisorElement p x.1) x.2.2 j)≠0:=by
    intro hzero
    exact hnon (by unfold sourceSummand;rw [hzero,mul_zero])
  have hb:=first_profile_live_products W Φ K (b*X) _ hq hW hprof
  constructor
  · change 1 ≤ X / (dyadScale (dyadIndex (leftNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 0) (hs 2) (primeProductNorm_ge_one p hp _) hb.1
  · change 1 ≤ X / (dyadScale (dyadIndex (rightNorm p x)) *
        dyadScale (dyadIndex (commonNorm p x)) *
        dyadScale (dyadIndex (primeProductNorm p j.2.1))) * b
    exact dyadic_column_scale (hs 1) (hs 2) (primeProductNorm_ge_one p hp _) hb.2

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0856

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveExponentCaps
Source SHA256: 28bbe20264334b90897f71eddd09822c7c1fa9556a7a72adbd98cd4f20107937
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0857



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile CompletedHeight
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

lemma actual_dyadic_exponent_cap (Z eta x A:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)(hx:1≤x)(hcap:x≤Z^A):
    0≤dyadicExponent Z (dyadIndex x) ∧ dyadicExponent Z (dyadIndex x)≤A:=by
  have h:=first_dyadic_bounds Z eta x hZ hbin hx
  exact ⟨h.1,(Real.rpow_le_rpow_left_iff hZ).mp (h.2.1.trans hcap)⟩

theorem original_live_exponent_caps {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(om:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))
    (K Z r ell F eta tau theta b:ℝ)(hZ:1<Z)(hbin:2≤Z^eta)
    (hF:0≤F)(hr:r≤F)(hell:ell≤F)(heta:0≤eta)(htau:0≤tau)(hb:b≤Z^eta)
    (hQ:∀v∈Q,‖eisEmbedding (primeProduct p v.support v)‖^2≤Z^(ell+eta))
    (hlabels:∀I∈labels,I≠0)(hs:∀y,om y≠0→y≤b):
    let Y:=Z^(2*F+15*eta+tau);
    let W:=fun y=>normTwistedSource om theta (y/Z^r);
    let source:=firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y;
    ∀k∈liveJointKeys p source pool (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),
      (∀i,0≤dyadicExponent Z (k.1 i) ∧ dyadicExponent Z (k.1 i)≤3*F+15*eta+tau) ∧
      (0≤dyadicExponent Z k.2.1 ∧ dyadicExponent Z k.2.1≤3*F+15*eta+tau) ∧
      (0≤dyadicExponent Z k.2.2 ∧ dyadicExponent Z k.2.2≤3*F+15*eta+tau):=by
  intro Y W source k hk
  have hz:0<Z:=zero_lt_one.trans hZ
  have hW:∀y,W y≠0→y≤Z^(r+eta):=by
    intro y hy
    have hh:om (y/Z^r)≠0:=by intro hh;exact hy (by simp [W,normTwistedSource,hh])
    calc
      y≤b*Z^r:=(div_le_iff₀ (Real.rpow_pos_of_pos hz _)).mp (hs _ hh)
      _≤Z^eta*Z^r:=mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hz.le _)
      _=Z^(r+eta):=by rw [←Real.rpow_add hz];congr 1;ring
  obtain ⟨⟨x,j⟩,hmem,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hmem
  obtain ⟨hx,hj⟩:=Finset.mem_product.mp hm
  obtain ⟨h₁,h₂,h₃⟩:=InverseMomentFirstLiveCaps.original_live_norm_caps p hp hcop hg pool Q labels Y β cutoff Ψ m mark W Φ K
    (Z^(r+eta)) (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) hQ hlabels hW x hx j hnon
  have hlow:=original_source_norms_ge_one p hp pool Q labels Y x hx
  have hsq:(Z^(ell+eta))^2=Z^(2*ell+2*eta):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le];congr 1;norm_num;ring
  have hA:Z^(r+eta)≤Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  have hB:(Z^(ell+eta))^2≤Z^(3*F+15*eta+tau):=by
    rw [hsq]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hAB:Z^(r+eta)*(Z^(ell+eta))^2≤Z^(3*F+15*eta+tau):=by
    rw [hsq,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hY:Y≤Z^(3*F+15*eta+tau):=Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  refine ⟨?_,?_,?_⟩
  · intro i
    apply actual_dyadic_exponent_cap Z eta _ _ hZ hbin (hlow i)
    apply (h₁ i).trans
    fin_cases i <;> first | exact hA | exact hAB | exact hB | exact hY
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin (primeProductNorm_ge_one p hp _) (h₂.trans hA)
  · exact actual_dyadic_exponent_cap Z eta _ _ hZ hbin
      (EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (primeProduct_ne_zero p hp _ _)) (h₃.trans hB)

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0857

/-! Original module: OAI.NumberTheory.DirichletL.Descent.FirstLiveRadiusPositive
Source SHA256: 0ec3edf5362679f3d0c374bf552e9aca3b3a663d1edf13ce2de6f7418933b7af
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0858


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.InverseMoment
open ActualEisensteinCubic FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open ConcreteTraceCRT (eisEmbedding)
local notation "O"=>ActualEisensteinCubic.O

theorem first_live_cell_radius_one {ι:Type}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y Z M r ell V eta tau:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K:ℝ)
    (hlabels:∀I∈labels,I≠0):
    let cutoff:=fun (q:CubeCoordinates ι)(C:Finset ι)(_I:Ideal O)(D:Finset ι)=>firstDyadicRadius p q C D Z M r ell V eta tau;
    ∀k∈liveJointKeys p
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) pool
      (sourceSummand p hp hcop hg β cutoff Ψ m mark W Φ K),1≤firstCellRadius Z M r ell V eta tau k.1 k.2.2:=by
  intro cutoff k hk
  obtain ⟨⟨x,j⟩,hm,rfl⟩:=Finset.mem_image.mp hk
  obtain ⟨hm,hnon⟩:=Finset.mem_filter.mp hm
  have hx:=(Finset.mem_product.mp hm).1
  have hweight:firstOriginalWeight p β cutoff x.1 x.2≠0:=by
    intro hh
    exact hnon (sourceSummand_zero_of_weight p hp hcop hg β cutoff Ψ m mark W Φ K x j hh)
  have hrow:=original_weight_frequency p β cutoff x hweight
  obtain ⟨ho,hf⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hI,hfreq⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hf
  have hfreq0:x.2.2≠0:=(Finset.mem_erase.mp hfreq).1
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hI)
  have hn:= (mem_childFrequencyBall _ hE _ _).mp hrow
  have hone:=EisensteinSchwartzPoisson.one_le_eisenstein_norm_sq _ (mul_ne_zero hE hfreq0)
  have href:x.1∈refinedOuter p pool Q (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
      (labelGate p (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))):=by
    rw [refinedOuter_label]
    refine Finset.mem_filter.mpr ⟨?_,rfl⟩
    exact InverseFirstGlobalCaps.sourceCell_outer p pool Q labels Y _ _ (Finset.mem_filter.mpr ⟨hx,rfl⟩)
  change 1≤firstCellRadius Z M r ell V eta tau (sourceIndex (InverseMomentFirstOriginalProfile.originalNorms p) x)
    (dyadIndex (InverseFirstGlobalCaps.jNorm p x.1))
  rw [←first_dyadic_radius_cell p pool Q _ _ x.1 href]
  exact hone.trans hn

end SevenEighths.InverseMoment

end

end OAI
end OAIOriginalModule0858

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Canonical
Source SHA256: 3f13deefe9d03002173a565be205edab82dfa53f50ff2a66b860b8b4ed22b358
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule0859




namespace OAI

noncomputable section
open scoped BigOperators Classical
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentCanonical
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT ConcretePrimeRowBridge
open CenteredMomentCorrelation

theorem actualSextic_order_six (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2) :
    orderOf (actualSextic P hg) = 6 := by
  let Φ : MulChar (O ⧸ P) O →* MulChar (O ⧸ P) ℂ :=
    MulChar.ringHomCompHom eisEmbedding
  have hΦ : Function.Injective Φ := by
    intro x y h
    apply MulChar.ext
    intro t
    apply eisEmbedding_injective
    exact congrArg (fun f : MulChar (O ⧸ P) ℂ => f t) h
  exact (orderOf_injective Φ hΦ _).trans (sexticChar_order P hg hchar)

def primePowerRow (P : Ideal O) [P.IsMaximal] (hg : goodLambda ∉ P)
    {c : ℕ} (hc : 1 ≤ c) (x : O ⧸ P ^ c) : ℂ :=
  (actualSextic P hg ^ c) (primePowerReduction P hc x)

theorem canonical_primePower_units (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v ≠ 0) :
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    fullCorrelation (fun x => v * x) (fun y => (u : O ⧸ P ^ c) * y)
      (primePowerRow P hg hc) (primePowerRow P hg hc) k =
    (Ideal.absNorm P : ℂ) ^ (c - 1) *
      actualSextic P hg (primePowerReduction P hc u / primePowerReduction P hc v) ^ c *
      (if primePowerReduction P hc k = 0 then (Ideal.absNorm P : ℂ) - 1
       else if 6 ∣ c then (Ideal.absNorm P : ℂ) - 2 else -1) :=
  primePower_localCorrelation_units P hc (actualSextic P hg)
    (actualSextic_order_six P hg hchar) u v k hv

theorem canonical_primePower_second_zero (P : Ideal O) [P.IsMaximal]
    (hg : goodLambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    {c : ℕ} (hc : 1 ≤ c) [Fintype (O ⧸ P ^ c)] [Fintype (O ⧸ P)]
    (u : (O ⧸ P ^ c)ˣ) (v k : O ⧸ P ^ c)
    (hv : primePowerReduction P hc v = 0) :
