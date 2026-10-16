  have hfc':∀x∈Sc,x.frequency≠0:=fun x hx=>hfw x (Finset.mem_filter.mp hx).1
  have hswhole:=hwindow p hp Finset.univ S hdiv hf ψ hψ Z D B v θ H c₁ c₂ θ₁ θ₂
    (zero_lt_one.trans hZp) hc₁ hbc₁ hc₂ hbc₂
  have hpoint:pointSource Finset.univ Sc⊆pointSource Finset.univ Sw:=by
    intro x hx
    obtain ⟨y,hy,hm⟩:=Finset.mem_biUnion.mp hx
    exact Finset.mem_biUnion.mpr ⟨y,(Finset.mem_filter.mp hy).1,hm⟩
  have hsupport:BlockSupport p (pointSource Finset.univ Sc) W₁ W₂ fresh fresh
      (fun i=>Vlog i) Z D B v θ H c₁ c₂ θ₁ θ₂:=
    ⟨fun x hx=>hswhole.1 x (hpoint hx),fun x hx=>hswhole.2.1 x (hpoint hx),
      fun x hx=>hswhole.2.2 x (hpoint hx)⟩
  rw [physicalBlock_coprimeSource p hp hcop hg hprimary Finset.univ _ hdivw hfw]
  by_cases hempty:physicalBlock p hp hcop hg (pointSource Finset.univ Sc) (w∘erasePoint) Ψ
      (assignedElement assigned qelem) (primeMark (all\assigned) lists coeff)
      (clippedSource W₁ c₁ θ₁) (clippedSource W₂ c₂ θ₂) Φ Z D m=0
  · rw [hempty,norm_zero];positivity
  have hclip:= (InverseInitialEnergyCallerEmpty.physical_nonzero_clipping p hp hcop hg
    hprimary Finset.univ Sc hdivc hfc' (w∘erasePoint) Ψ (assignedElement assigned qelem)
    (primeMark (all\assigned) lists coeff) W₁ W₂ fresh fresh (fun i=>Vlog i) Φ
    Z D B v θ H m c₁ c₂ θ₁ θ₂ af (max 1 bf) η hZp (le_max_left _ _) hfs' hsupport hlog hempty).2
  have hqt:quotientSet p Sc⊆quotientSet p Sw:=
    Finset.image_subset_image (Finset.filter_subset _ _)
  have hn:∀t∈quotientSet p Sc,(t.absNorm:ℝ)≤Z^(B-θ+2*η):=by
    intro t ht
    exact retained_quotient_bound p hp S (fun _=>1) (ψ 0) (ψ 1)
      (lo 0) (hi 0) (lo 1) (hi 1) Z B θ η (zero_lt_one.trans hZp)
      (hψ 0) (hψ 1) (hhiZ 0) hloZ hdiv t
      (window_quotient_subset_retained p S ψ Z D B v θ H (hqt ht))
  have hstates:∀t∈quotientSet p Sc,
      assignedElement assigned qelem*primaryGenerator t≠0 ∧ 0≤θ+v+2*η ∧ 0≤θ+H+2*η ∧
      0≤fullPunctureWidth Z t (assignedElement assigned qelem) ∧
      ‖eisEmbedding (assignedElement assigned qelem*primaryGenerator t)‖^2=
        Z^(fullPunctureWidth Z t (assignedElement assigned qelem)) ∧
      θ+H+2*η≤cap ∧ max 0 (columnCenter D B v)+(θ+v+2*η)≤cap ∧
      CanonicalMargins (max 0 (columnCenter D B v)+(θ+v+2*η)) (θ+H+2*η)
        (fullPunctureWidth Z t (assignedElement assigned qelem))
        (assignedCenter (all\assigned) z+η) gap:=by
    intro t ht
    have hs:=actual_window_state p hp hprimary S ψ lo hi hψ Z D B v θ H η hZp hη hhiZ hloZ
      hdiv hf all assigned hassigned qelem z al bl primeW hz hqe hprimeW hprimeLive hprodj (hqt ht)
      m r τ (2*gap) (2*gap) hDeq hmargin₁ hmargin₂ (by simp;positivity)
      (by simp only [min_self];linarith) (by simp only [min_self];linarith) hrad hclip
    simp only [min_self] at hs
    obtain ⟨hm,hN,hV,hM,hQ,he,hmargin,hF,hMr,hshift⟩:=hs
    refine ⟨hm,hV,hM,hQ,he,hMr.trans hparent,hF.trans hparent,?_⟩
    convert hmargin using 1 <;> simp [columnCenter]
  apply hbound Z hZ Dpool hD (all\assigned) ((Finset.card_le_card Finset.sdiff_subset).trans hK)
    lists Hslot coeff (fun i hi j hj hij=>hdis (Finset.mem_sdiff.mp hi).1 (Finset.mem_sdiff.mp hj).1 hij) hHs hPs hac
    (assignedCenter (all\assigned) z+η) (by apply add_nonneg _ hη;exact Finset.sum_nonneg (fun i hi=>hz i (Finset.mem_sdiff.mp hi).1))
    hprod Ψ hΨ hperiod Sc hdivc hfc' (assignedElement assigned qelem) D B v θ H (B-θ+2*η) m η
    hR hη c₁ c₂ θ₁ θ₂ (zero_lt_one.trans_le hc₁) (zero_lt_one.trans_le hc₂) hsupport hn w
    (fun x hx=>hw x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (idealRange (Z^(θ+v+2*η))) (nonzeroChildFrequencyBall 1 (Z^(θ+H+2*η)))
    (fun f hf=>mem_idealRange.mp hf) (Finset.Subset.refl _) ?_ ?_ hclip rfl hstates
  · intro k hk
    exact (child_ball_neg _ k).mpr hk
  · intro x hx
    exact InverseInitialCanonicalDomains.actual_window_domains p hp hcop hg (poolPrimary_odd F hFa)
      hprimary S hdiv hf ψ lo hi hψ Z D B v θ H η (zero_lt_one.trans hZp) hhiZ x hx _

end SevenEighths.InverseInitialRetainedWindow

end

end OAI
end OAIOriginalModule1611

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PlainWindowEnergy
Source SHA256: 215f0e673c53068554f80d6e631185b7cc28c488c845aefeb8ca6fb12417b6bb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1612



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentPlainWindowEnergy
open CanonicalQuadraticSieve CenteredMomentRowNorm CenteredMomentPlainEnergy
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem plain_column_integral {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    rowPolynomial S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) z=
      ∫ w : ℝ,columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z := by
  have hi (i : α) : Integrable (fun w : ℝ => β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i})) :=
    ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul _).mul_const _
  unfold rowPolynomial
  calc
    _ = ∑ i∈S,∫ w : ℝ,β i*
      (columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
        heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i}))*CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_mul_const,integral_const_mul,← height_column_integral V hVc hVs τ _ (ha i).1 t θ X hX]
      ring
    _ = _ := by
      rw [← integral_finsetSum _ (fun i _ => hi i)]
      apply integral_congr_ae
      filter_upwards [] with w
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem plain_column_integrable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V) (z : O) :
    Integrable (fun w : ℝ => columnDensity V hVc hVs w*logPhase (θ-w) (Real.log X)*
      rowPolynomial S a (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z) := by
  have hi (i : α) := ((height_column_integrable V hVc hVs τ _ (ha i).1 t θ X hX).const_mul (β i)).mul_const
    (CanonicalRowCompletion.idealRowHom z (Ideal.span {a i}))
  convert integrable_finsetSum S (fun i _ => hi i) using 1
  funext w
  simp only [rowPolynomial,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem rowEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖rowPolynomial S a c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rowEnergy S a c U K).re := by
  have hs := Complex.hasSum_re (rowEnergy_summable S a ha c U K hK).hasSum
  simpa only [rowEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

theorem finite_weighted_le_rowEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖rowPolynomial S a c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (rowEnergy S a c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (rowEnergy_hasSum_re S a ha c U K hK)

theorem plain_window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(rowEnergy S a
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re≤E*(1+‖w‖)^(2*J)) :
    (rowEnergy S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hU z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖rowPolynomial S a c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (plain_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      simpa only [mul_comm,Nat.mul_comm] using
        (finite_weighted_le_rowEnergy S a ha _ U K hK hU rows).trans (henergy w)
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*rowPolynomial S a c z := by
      rw [show rowPolynomial S a c z=_ from plain_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a c z‖^2)] at hh
    simpa only [mul_comm] using hh
  have hs := rowEnergy_hasSum_re S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hU z)) hfin

theorem plain_window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(rowEnergy S a
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K).re≤E*(1+‖v‖)^(2*J)) :
    (rowEnergy S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply plain_window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentPlainWindowEnergy

end

end OAI
end OAIOriginalModule1612

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalWindowPair
Source SHA256: 5c5cf58f5b0fc0ba11a73a980c66adba7e9cb0db02bf8c4defa5941946711f8e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1613



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWindowPair
open CenteredMomentPlainWindowEnergy CenteredMomentRowNorm CenteredMomentSmooth
open CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem paired_integrals {κ:Type*}(rows:Finset κ)(f g:κ→ℝ→ℂ)
    (hf:∀z∈rows,Integrable (f z))(hg:∀z∈rows,Integrable (g z))
    (a b:ℝ→ℝ)(ha:Integrable a)(hb:Integrable b)
    (_ha0:∀u,0≤a u)(_hb0:∀v,0≤b v)(E:ℝ)(_hE:0≤E)
    (hpair:∀u v,∑z∈rows,‖f z u‖*‖g z v‖≤E*a u*b v):
    (∑z∈rows,‖∫u,f z u‖*‖∫v,g z v‖)≤E*(∫u,a u)*(∫v,b v):=by
  have hinner (u:ℝ):
      (∑z∈rows,‖f z u‖*‖∫v,g z v‖)≤E*a u*(∫v,b v):=by
    calc
      _≤∑z∈rows,‖f z u‖*(∫v,‖g z v‖):=
        Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_left
          (norm_integral_le_integral_norm _) (norm_nonneg _))
      _=∫v,∑z∈rows,‖f z u‖*‖g z v‖:=by
        rw [integral_finsetSum _ (fun z hz=>(hg z hz).norm.const_mul _)]
        simp only [integral_const_mul]
      _≤∫v,E*a u*b v:=integral_mono
        (integrable_finsetSum rows (fun z hz=>(hg z hz).norm.const_mul _))
        (hb.const_mul _) (fun v=>hpair u v)
      _=E*a u*(∫v,b v):=integral_const_mul _ _
  calc
    _≤∑z∈rows,(∫u,‖f z u‖)*‖∫v,g z v‖:=
      Finset.sum_le_sum (fun z hz=>mul_le_mul_of_nonneg_right
        (norm_integral_le_integral_norm _) (norm_nonneg _))
    _=∫u,∑z∈rows,‖f z u‖*‖∫v,g z v‖:=by
      rw [integral_finsetSum _ (fun z hz=>(hf z hz).norm.mul_const _)]
      simp only [integral_mul_const]
    _≤∫u,E*a u*(∫v,b v):=integral_mono
      (integrable_finsetSum rows (fun z hz=>(hf z hz).norm.mul_const _))
      ((ha.const_mul E).mul_const _) hinner
    _=E*(∫u,a u)*(∫v,b v):=by rw [integral_mul_const,integral_const_mul]

theorem plain_window_pair {α β:Type*}
    (rows:Finset O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:α→ℂ)(d:β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑z∈rows,
      ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
      ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑z∈rows,
      ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) z‖*
      ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  let f:=fun z:O=>fun u:ℝ=>columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁-u) (Real.log X)*
    rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z
  let g:=fun z:O=>fun v:ℝ=>columnDensity V₂ hc₂ hs₂ v*logPhase (θ₂-v) (Real.log Y)*
    rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z
  have hf (z:O):Integrable (f z):=plain_column_integrable S a ha c τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ z
  have hg (z:O):Integrable (g z):=plain_column_integrable T b hb d τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ z
  have hh:=paired_integrals rows f g (fun z _=>hf z) (fun z _=>hg z)
    (fun u=>(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun v=>(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun u=>by positivity) (fun v=>by positivity) E hE ?_
  · simpa only [f,g,←plain_column_integral S a ha c τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁,
      ←plain_column_integral T b hb d τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂] using hh
  · intro u v
    simp only [f,g,norm_mul,logPhase_norm,mul_one]
    calc
      _=(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
        (∑z∈rows,
          ‖rowPolynomial S a (fun i=>c i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
          ‖rowPolynomial T b (fun j=>d j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _≤(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
          (E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):=
        mul_le_mul_of_nonneg_left (hpair u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _=_:=by ring

end SevenEighths.CenteredMomentExceptionalWindowPair

end

end OAI
end OAIOriginalModule1613

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalIndexedWindow
Source SHA256: a697da96db63aeb56139b213f2b9972e7da600667466aef3a354a4185fc08bbe
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1614


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalIndexedWindow
open CenteredMomentExceptionalWindowPair CenteredMomentPlainWindowEnergy
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem indexed_plain_window_pair {κ α β:Type*}
    (rows:Finset κ)(row:κ→O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:κ→α→ℂ)(d:κ→β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑z∈rows,
      ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)‖*
      ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑z∈rows,
      ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) (row z)‖*
      ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) (row z)‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  let f:=fun z:κ=>fun u:ℝ=>columnDensity V₁ hc₁ hs₁ u*logPhase (θ₁-u) (Real.log X)*
    rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)
  let g:=fun z:κ=>fun v:ℝ=>columnDensity V₂ hc₂ hs₂ v*logPhase (θ₂-v) (Real.log Y)*
    rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)
  have hf (z:κ):Integrable (f z):=plain_column_integrable S a ha (c z) τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ (row z)
  have hg (z:κ):Integrable (g z):=plain_column_integrable T b hb (d z) τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ (row z)
  have hh:=paired_integrals rows f g (fun z _=>hf z) (fun z _=>hg z)
    (fun u=>(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)
    (fun v=>(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖)
    (columnDensity_moments V₁ hc₁ hs₁ J₁) (columnDensity_moments V₂ hc₂ hs₂ J₂)
    (fun u=>by positivity) (fun v=>by positivity) E hE ?_
  · have hfEq (z:κ):
        (∫u:ℝ,f z u)=rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
          columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) (row z):=
        (plain_column_integral S a ha (c z) τ₁ t₁ θ₁ X hX V₁ hc₁ hs₁ (row z)).symm
    have hgEq (z:κ):
        (∫v:ℝ,g z v)=rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
          columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) (row z):=
        (plain_column_integral T b hb (d z) τ₂ t₂ θ₂ Y hY V₂ hc₂ hs₂ (row z)).symm
    simpa only [hfEq,hgEq] using hh
  · intro u v
    simp only [f,g,norm_mul,logPhase_norm,mul_one]
    calc
      _=(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
        (∑z∈rows,
          ‖rowPolynomial S a (fun i=>c z i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) (row z)‖*
          ‖rowPolynomial T b (fun j=>d z j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) (row z)‖):=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro z hz
        ring
      _≤(‖columnDensity V₁ hc₁ hs₁ u‖*‖columnDensity V₂ hc₂ hs₂ v‖)*
          (E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):=
        mul_le_mul_of_nonneg_left (hpair u v) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _=_:=by ring

end SevenEighths.CenteredMomentExceptionalIndexedWindow

end

end OAI
end OAIOriginalModule1614

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ExceptionalWholeWindow
Source SHA256: 7d7b5163b140412c0b94eac22c3a0f646c439f9af5a3fe70f113eed592985d9c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1615


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentExceptionalWholeWindow
open CenteredMomentExceptionalIndexedWindow CenteredMomentPlainWindowEnergy
open CenteredMomentRowNorm CenteredMomentSmooth CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem rowPolynomial_factor {α:Type*}(S:Finset α)(a:α→O)(c:α→ℂ)(v:ℂ)(z:O):
    rowPolynomial S a (fun i=>v*c i) z=v*rowPolynomial S a c z:=by
  simp only [rowPolynomial,Finset.mul_sum,mul_assoc]

theorem whole_plain_window_pair {γ α β:Type*}
    (Ds:Finset γ)(μ:γ→ℂ)(rows:Finset O)(S:Finset α)(T:Finset β)(a:α→O)(b:β→O)
    (ha:∀i,CanonicalQuadraticSieve.Supported (Ideal.span {a i}))
    (hb:∀j,CanonicalQuadraticSieve.Supported (Ideal.span {b j}))
    (c:γ→α→ℂ)(d:γ→β→ℂ)(τ₁ τ₂:Character)(t₁ t₂ θ₁ θ₂ X Y:ℝ)(hX:0<X)(hY:0<Y)
    (V₁ V₂:ℝ→ℂ)(hc₁:HasCompactSupport V₁)(hc₂:HasCompactSupport V₂)
    (hs₁:ContDiff ℝ ∞ V₁)(hs₂:ContDiff ℝ ∞ V₂)(J₁ J₂:ℕ)(E:ℝ)(hE:0≤E)
    (hpair:∀u v:ℝ,(∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖rowPolynomial S a (fun i=>c L i*heightCoeff τ₁ (t₁+2*Real.pi*(u-θ₁)) (Ideal.span {a i})) z‖*
      ‖rowPolynomial T b (fun j=>d L j*heightCoeff τ₂ (t₂+2*Real.pi*(v-θ₂)) (Ideal.span {b j})) z‖)≤
        E*(1+‖u‖)^J₁*(1+‖v‖)^J₂):
    (∑L∈Ds,‖μ L‖*∑z∈rows,
      ‖rowPolynomial S a (fun i=>c L i*heightCoeff τ₁ t₁ (Ideal.span {a i})*
        columnPhase V₁ (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ₁) z‖*
      ‖rowPolynomial T b (fun j=>d L j*heightCoeff τ₂ t₂ (Ideal.span {b j})*
        columnPhase V₂ (Real.log ((Ideal.absNorm (Ideal.span {b j}):ℝ)/Y)) θ₂) z‖)≤
      E*(∫u:ℝ,(1+‖u‖)^J₁*‖columnDensity V₁ hc₁ hs₁ u‖)*
        (∫v:ℝ,(1+‖v‖)^J₂*‖columnDensity V₂ hc₂ hs₂ v‖):=by
  have hh:=indexed_plain_window_pair (Ds×ˢrows) (fun x:γ×O=>x.2) S T a b ha hb
    (fun x i=>μ x.1*c x.1 i) (fun x j=>d x.1 j) τ₁ τ₂ t₁ t₂ θ₁ θ₂ X Y hX hY
    V₁ V₂ hc₁ hc₂ hs₁ hs₂ J₁ J₂ E hE ?_
  · simpa only [mul_assoc,rowPolynomial_factor,norm_mul,
      Finset.sum_product,Finset.mul_sum,mul_assoc] using hh
  · intro u v
    simpa only [mul_assoc,rowPolynomial_factor,norm_mul,
      Finset.sum_product,Finset.mul_sum,mul_assoc] using hpair u v

end SevenEighths.CenteredMomentExceptionalWholeWindow

end

end OAI
end OAIOriginalModule1615

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RestrictedWindow
Source SHA256: 9a00ac97aedebd1bdf351d3fd97825c13e8555dadeff4c588bd5da42083f36a8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1616



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentRestrictedWindow
open CanonicalQuadraticSieve CenteredMomentRowNorm CenteredMomentRestrictedEnergy
open CenteredMomentPlainWindowEnergy CenteredMomentHeckeColumnWindow CenteredMomentHeckeWindowEnergy
open HeckeFamily FourierBridge CenteredMomentSmooth
local notation "O" => ActualEisensteinCubic.O

theorem restricted_hasSum_weighted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖rowPolynomial S a c z‖^2*
      (if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0))
      (restrictedEnergy keep S a c U K) := by
  simpa only [mul_ite,mul_zero,restrictedEnergy] using
    (restricted_summable keep S a ha c U K hK).hasSum

theorem finite_weighted_le_restricted {α : Type*} (keep : O → Prop)
    (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖rowPolynomial S a c z‖^2*
      (if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0))≤
      restrictedEnergy keep S a c U K := by
  apply sum_le_hasSum rows _ (restricted_hasSum_weighted keep S a ha c U K hK)
  intro z hz
  apply mul_nonneg (sq_nonneg _)
  split_ifs
  · exact hU z
  · exact le_rfl

theorem restricted_window_energy_from_shifted {α : Type*} (keep : O → Prop)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(restrictedEnergy keep S a
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K)≤E*(1+‖w‖)^(2*J)) :
    (restrictedEnergy keep S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => if keep z then (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re else 0
  have hu (z : O) : 0≤u z := by dsimp only [u];split_ifs;exact hU z;exact le_rfl
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hu z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖rowPolynomial S a c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (plain_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      have hbound :=
        (finite_weighted_le_restricted keep S a ha _ U K hK hU rows).trans (henergy w)
      rw [Nat.mul_comm 2 J] at hbound
      calc
        _ = ∑ z ∈ rows, ‖rowPolynomial S a
            (fun i => β i * heightCoeff τ (t + 2 * Real.pi * (w - θ))
              (Ideal.span {a i})) z‖ ^ 2 * u z := by
          apply Finset.sum_congr rfl
          intro z hz
          exact mul_comm _ _
        _ ≤ _ := hbound
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*rowPolynomial S a c z := by
      rw [show rowPolynomial S a c z=_ from plain_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖rowPolynomial S a c z‖^2)] at hh
    calc
      _ = ∑ z ∈ rows, u z * ‖rowPolynomial S a c z‖ ^ 2 := by
        apply Finset.sum_congr rfl
        intro z hz
        exact mul_comm _ _
      _ ≤ _ := hh
  have hs := restricted_hasSum_weighted keep S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hu z)) hfin

theorem restricted_window_energy_from_height {α : Type*} (keep : O → Prop)
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(restrictedEnergy keep S a
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K)≤E*(1+‖v‖)^(2*J)) :
    (restrictedEnergy keep S a (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K)≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply restricted_window_energy_from_shifted keep V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentRestrictedWindow

end

end OAI
end OAIOriginalModule1616

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SmoothedWindowEnergy
Source SHA256: 71fd6d27d1041f1b3e7ebee6ff9b24df7a106605c391168bb9511be1ac486c39
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1617


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
open MeasureTheory

namespace SevenEighths.CenteredMomentSmoothedWindowEnergy
open CanonicalQuadraticSieve CenteredMomentGaussEnergy CenteredMomentHeckeColumnWindow
open CenteredMomentHeckeWindowEnergy HeckeFamily FourierBridge
local notation "O" => ActualEisensteinCubic.O

theorem gaussEnergy_hasSum_re {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K) :
    HasSum (fun z : O => ‖gaussPolynomial S a ha c z‖^2*
      (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (gaussEnergy S a ha c U K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c U K hK).hasSum
  simpa only [gaussEnergy,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] using hs

theorem finite_weighted_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i,Supported (Ideal.span {a i})) (c : α → ℂ)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re) (rows : Finset O) :
    (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)≤
      (gaussEnergy S a ha c U K).re :=
  sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hU z)) (gaussEnergy_hasSum_re S a ha c U K hK)

theorem smoothed_window_energy_from_shifted {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ w : ℝ,(gaussEnergy S a ha
      (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) U K).re≤E*(1+‖w‖)^(2*J)) :
    (gaussEnergy S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  let u := fun z : O => (U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re
  let c := fun i => β i*heightCoeff τ t (Ideal.span {a i})*
    CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ
  have hnorm (z : O) (x : ℂ) : ‖(Real.sqrt (u z):ℂ)*x‖^2=u z*‖x‖^2 := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _),mul_pow,
      Real.sq_sqrt (hU z)]
  have hfin (rows : Finset O) : (∑ z∈rows,‖gaussPolynomial S a ha c z‖^2*u z)≤
      E*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
    let φ := fun z : rows => fun w : ℝ => (Real.sqrt (u z):ℂ)*
      (logPhase (θ-w) (Real.log X)*gaussPolynomial S a ha
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z)
    have hi (z : rows) : Integrable (fun w => columnDensity V hVc hVs w*φ z w) := by
      have h := (gauss_column_integrable S a ha β τ t θ X hX V hVc hVs z).const_mul (Real.sqrt (u z):ℂ)
      convert h using 1
      funext w
      dsimp only [φ]
      ring
    have hb (w : ℝ) : (∑ z : rows,‖φ z w‖^2)≤E*((1+‖w‖)^J)^2 := by
      simp only [φ]
      simp_rw [hnorm]
      simp only [norm_mul,logPhase_norm,one_mul,← pow_mul]
      rw [Finset.sum_coe_sort rows (fun z : O => u z*‖gaussPolynomial S a ha
        (fun i => β i*heightCoeff τ (t+2*Real.pi*(w-θ)) (Ideal.span {a i})) z‖^2)]
      simpa only [mul_comm,Nat.mul_comm] using
        (finite_weighted_le_gaussEnergy S a ha _ U K hK hU rows).trans (henergy w)
    have hh := finite_weighted_integral_energy (columnDensity V hVc hVs) φ
      (fun w => (1+‖w‖)^J) (by intro w;positivity) E hE (columnDensity_moments V hVc hVs J) hi hb
    have he (z : rows) : (∫ w : ℝ,columnDensity V hVc hVs w*φ z w)=
        (Real.sqrt (u z):ℂ)*gaussPolynomial S a ha c z := by
      rw [show gaussPolynomial S a ha c z=_ from gauss_column_integral S a ha β τ t θ X hX V hVc hVs z,
        ← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with w
      dsimp only [φ]
      ring
    simp only [he,hnorm] at hh
    rw [Finset.sum_coe_sort rows (fun z : O => u z*‖gaussPolynomial S a ha c z‖^2)] at hh
    simpa only [mul_comm] using hh
  have hs := gaussEnergy_hasSum_re S a ha c U K hK
  rw [← hs.tsum_eq]
  exact Real.tsum_le_of_sum_le (fun z => mul_nonneg (sq_nonneg _) (hU z)) hfin

theorem smoothed_window_energy_from_height {α : Type*}
    (V : ℝ → ℂ) (hVc : HasCompactSupport V) (hVs : ContDiff ℝ ∞ V)
    (J : ℕ) (S : Finset α) (a : α → O) (ha : ∀ i,Supported (Ideal.span {a i}))
    (β : α → ℂ) (τ : Character) (t θ X : ℝ) (hX : 0<X)
    (U : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0<K)
    (hU : ∀ z : O,0≤(U (‖ConcreteTraceCRT.eisEmbedding z‖^2/K)).re)
    (E : ℝ) (hE : 0≤E)
    (henergy : ∀ v : ℝ,(gaussEnergy S a ha
      (fun i => β i*heightCoeff τ v (Ideal.span {a i})) U K).re≤E*(1+‖v‖)^(2*J)) :
    (gaussEnergy S a ha (fun i => β i*heightCoeff τ t (Ideal.span {a i})*
      CenteredMomentSmooth.columnPhase V (Real.log ((Ideal.absNorm (Ideal.span {a i}):ℝ)/X)) θ) U K).re≤
      (E*heightCost t θ^(2*J))*(∫ w : ℝ,(1+‖w‖)^J*‖columnDensity V hVc hVs w‖)^2 := by
  apply smoothed_window_energy_from_shifted V hVc hVs J S a ha β τ t θ X hX U K hK hU
    (E*heightCost t θ^(2*J)) (mul_nonneg hE (pow_nonneg (heightCost_pos t θ).le _))
  intro w
  calc
    _ ≤ E*(1+‖t+2*Real.pi*(w-θ)‖)^(2*J) := henergy _
    _ ≤ E*(heightCost t θ*(1+‖w‖))^(2*J) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (norm_height_shift t θ w) _) hE
    _ = _ := by rw [mul_pow,mul_assoc]

end SevenEighths.CenteredMomentSmoothedWindowEnergy

end

end OAI
end OAIOriginalModule1617

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Tail
Source SHA256: 6f2f1e08b58832d1dcd29b811cba68e20a9c2c439fa407f95b6e62daf1761976
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1618


namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => ActualEisensteinCubic.O
namespace SevenEighths.CenteredMomentTail
open ActualEisensteinCubic ConcreteTraceCRT CubicEisenstein EisensteinSchwartzPoisson
open CenteredMomentCommonSupport CenteredMomentCorrelation CenteredMomentFourier
open CenteredMomentSupportedCorrelation

theorem residueGauss_norm_le (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖residueGauss d hd χ h‖ ≤ (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  let := finite_quotient_span hd
  let : Fintype (Residue d) := Fintype.ofFinite _
  rw [residueGauss, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue d, ‖χ x * quotientTrace d hd (h * x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue d, (1 : ℝ) := Finset.sum_le_sum fun x _ => by
      rw [norm_mul, (quotientTrace d hd).norm_apply, mul_one]
      exact QuadraticInitialBound.norm_finite_character_le_one χ x
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem normalizedResidueGauss_norm_le (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖normalizedResidueGauss d hd χ h‖ ≤ Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {d}) := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hd)))
  rw [normalizedResidueGauss, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (div_le_iff₀ (Real.sqrt_pos.mpr hn)).mpr
  rw [Real.mul_self_sqrt hn.le]
  exact residueGauss_norm_le d hd χ h

theorem normalizedResidueGauss_div_root_norm_le_one (d : O) (hd : d ≠ 0)
    (χ : MulChar (Residue d) ℂ) (h : Residue d) :
    ‖normalizedResidueGauss d hd χ h /
      (Real.sqrt (Ideal.absNorm (Ideal.span {d}) : ℝ) : ℂ)‖ ≤ 1 := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {d}) := by
    exact_mod_cast (Nat.pos_of_ne_zero
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hd)))
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (div_le_one (Real.sqrt_pos.mpr hn)).mpr (normalizedResidueGauss_norm_le d hd χ h)

theorem fullModulusCorrelation_norm_le (u v : O) (_hu : u ≠ 0) (_hv : v ≠ 0)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ) (j : O) :
    ‖fullModulusCorrelation u v χu χv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  unfold fullModulusCorrelation fullCorrelation
  calc
    _ ≤ ∑ x : Residue u, ‖∑ y : Residue v,
      if scaledResidue u v (u * v) rfl x - scaledResidue v u (u * v) (mul_comm u v) y =
        Ideal.Quotient.mk _ j then χu x * star (χv y) else 0‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue u, ∑ _y : Residue v, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro y hy
      split_ifs
      · rw [norm_mul, norm_star]
        exact (mul_le_of_le_one_left (norm_nonneg _)
          (QuadraticInitialBound.norm_finite_character_le_one χu x)).trans
          (QuadraticInitialBound.norm_finite_character_le_one χv y)
      · simp
    _ = _ := by
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem actualCorrelation_norm_le (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})) (j : O) :
    ‖actualCorrelation u v hu hv j‖ ≤
      (Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ) := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  unfold actualCorrelation
  exact fullModulusCorrelation_norm_le u v (supported_element_ne_zero u hu)
    (supported_element_ne_zero v hv) _ _ j

theorem weighted_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      ∀ c : O → ℂ, (∀ h, ‖c h‖ ≤ B) →
      ‖∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T B hK hT hB c hc
  let S := {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2}
  have hs : Summable (fun h : S => ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    (paperRadialFourier_lattice_summable_norm W K hK).subtype _
  have hpoint (h : S) : ‖c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hc _) (norm_nonneg _)
  have hsum : Summable (fun h : S =>
      ‖c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hpoint (hs.mul_left B)
  calc
    _ ≤ ∑' h : S, ‖c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : S, B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hpoint (hs.mul_left B)
    _ = B * ∑' h : S, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ _ := by
      simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left (ht W K T hK hT) hB

theorem weighted_set_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K T B : ℝ), 0 < K → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K * ‖eisEmbedding h‖ ^ 2) →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K T B hK hT hB hD c δ hc hδ
  let L := {h : O | T ≤ K * ‖eisEmbedding h‖ ^ 2}
  let f : D → L := fun h => ⟨h.val, hD h.val h.property⟩
  have hfi : Function.Injective f := by
    intro x y h
    exact Subtype.ext (congrArg (fun z : L => z.val) h)
  have hs := paperRadialFourier_lattice_summable_norm W K hK
  have hp (h : D) : ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
      B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      ((mul_le_of_le_one_left (norm_nonneg _) (hδ h.val h.property)).trans (hc h.val h.property))
      (norm_nonneg _)
  have hsum : Summable (fun h : D =>
      ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hp ((hs.subtype D).mul_left B)
  calc
    _ ≤ ∑' h : D, ‖δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' h : D, B * ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      hsum.tsum_le_tsum hp ((hs.subtype D).mul_left B)
    _ = B * ∑' h : D, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ := tsum_mul_left
    _ ≤ B * ∑' h : L, ‖paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ :=
      mul_le_mul_of_nonneg_left ((hs.subtype D).tsum_le_tsum_of_inj f hfi
        (fun _ _ => norm_nonneg _) (fun _ => le_rfl) (hs.subtype L)) hB
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_left (ht W K T hK hT) hB using 1
      · rfl
      · ring

theorem uniform_sector_lattice_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (D : Set O) (K₀ T B : ℝ), 0 < K₀ → 0 ≤ T → 0 ≤ B →
      (∀ h ∈ D, T ≤ K₀ * ‖eisEmbedding h‖ ^ 2) →
      ∀ K : ℝ, K₀ ≤ K →
      ∀ c δ : O → ℂ, (∀ h ∈ D, ‖c h‖ ≤ B) → (∀ h ∈ D, ‖δ h‖ ≤ 1) →
      ‖∑' h : D, δ h.val * c h.val * paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        B * (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
          ((min 1 K₀) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_set_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W D K₀ T B hK₀ hT hB hD K hK c δ hc hδ
  have hD' (h : O) (hh : h ∈ D) : T ≤ K * ‖eisEmbedding h‖ ^ 2 :=
    (hD h hh).trans (mul_le_mul_of_nonneg_right hK (sq_nonneg _))
  apply (ht W D K T B (hK₀.trans_le hK) hT hB hD' c δ hc hδ).trans
  apply div_le_div_of_nonneg_left (by positivity)
    (by have : 0 < min 1 K₀ := lt_min zero_lt_one hK₀; positivity)
  gcongr

theorem actual_correlation_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
      ∀ (u v : O) (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
        (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v})),
      ‖∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        actualCorrelation u v hu hv (-h.val) *
          paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
        ((Ideal.absNorm (Ideal.span {u}) : ℝ) * (Ideal.absNorm (Ideal.span {v}) : ℝ)) *
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T hK hT u v hu hv
  exact ht W K T _ hK hT (by positivity) _
    (fun h => actualCorrelation_norm_le u v hu hv (-h))

theorem actual_first_gauss_tail (A : ℕ) :
    ∃ (s : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ℝ, ℂ)) (K T : ℝ), 0 < K → 0 ≤ T →
      ∀ {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
        (hinj : Function.Injective P) (hg : ∀ i, ConcretePrimeRowBridge.goodLambda ∉ P i)
        (_hchar : ∀ i, ringChar (O ⧸ P i) ≠ 2)
        (B : Finset ι) (c d : ι → ℕ)
        (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
        (χa : MulChar (Residue a) ℂ) (χb : MulChar (Residue b) ℂ),
      let r := CenteredMomentInitial.activeModulus P B c d
      let ξ := CenteredMomentInitial.commonCharacter P hinj hg B c d
      ‖∑' h : {h : O // T ≤ K * ‖eisEmbedding h‖ ^ 2},
        (normalizedResidueGauss r (CenteredMomentInitial.activeModulus_ne_zero P B c d) ξ
            (Ideal.Quotient.mk _ h.val) *
          (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h.val) /
            (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)) *
          star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h.val)) /
            (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) *
          paperRadialFourier W (K * ‖eisEmbedding h.val‖ ^ 2)‖ ≤
          (C * s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) /
            ((min 1 K) ^ 2 * (1 + T) ^ A) := by
  obtain ⟨s, C, hC, ht⟩ := weighted_lattice_tail A
  refine ⟨s, C, hC, ?_⟩
  intro W K T hK hT ι P _ hinj hg hchar B c d a b ha hb χa χb
  dsimp only
  simpa only [one_mul] using ht W K T 1 hK hT zero_le_one
    (fun h => normalizedResidueGauss _ (CenteredMomentInitial.activeModulus_ne_zero P B c d)
      (CenteredMomentInitial.commonCharacter P hinj hg B c d) (Ideal.Quotient.mk _ h) *
      (normalizedResidueGauss a ha χa (Ideal.Quotient.mk _ h) /
        (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)) *
      star (normalizedResidueGauss b hb χb (Ideal.Quotient.mk _ (-h)) /
        (Real.sqrt (Ideal.absNorm (Ideal.span {b}) : ℝ) : ℂ))) (by
      intro h
      rw [norm_mul, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        ((mul_le_of_le_one_left (norm_nonneg _)
          (CenteredMomentInitial.common_gauss_norm_le_one P hinj hg hchar B c d h)).trans
          (normalizedResidueGauss_div_root_norm_le_one a ha χa _))).trans
        (normalizedResidueGauss_div_root_norm_le_one b hb χb _))

end SevenEighths.CenteredMomentTail
end

end OAI
end OAIOriginalModule1618

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramFrequencyConvergence
Source SHA256: d508f202f7b99ab762134490e648ebffccb033289b8b21301378a01ac066f2cf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1619



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O

lemma actual_correlation_radial_summable (I J : SupportedIdeal) (C : O) (hC : C≠0)
    (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    Summable (fun k : O=>actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)*
      paperRadialFourier U (Q*‖eisEmbedding (C*k)‖^2/
        ‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2)) := by
  let t:=Q*‖eisEmbedding C‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2
  have hc : 0<‖eisEmbedding C‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hC))
  have hd : 0<‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero (mul_ne_zero
      (supported_primaryGenerator_ne_zero _ I.property) (supported_primaryGenerator_ne_zero _ J.property))))
  have ht : 0<t := div_pos (mul_pos hQ hc) hd
  have hs := paperRadialFourier_lattice_summable_norm U t ht
  let B : ℝ := (Ideal.absNorm I.val:ℝ)*Ideal.absNorm J.val
  have hb (k : O) : ‖actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)‖≤B := by
    have hh := CenteredMomentTail.actualCorrelation_norm_le (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (C*k)
    simpa only [(primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ I.property)).1,
      (primaryGenerator_spec _ (supported_primaryGenerator_ne_zero _ J.property)).1] using hh
  have harg (k : O) : Q*‖eisEmbedding (C*k)‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2=t*‖eisEmbedding k‖^2 := by
    simp only [map_mul,norm_mul,mul_pow,t]
    ring
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k=>norm_nonneg _) _ (hs.mul_left B)
  intro k
  rw [norm_mul,harg]
  exact mul_le_mul_of_nonneg_right (hb k) (norm_nonneg _)

lemma originalCommonBlock_summable (S : Finset (Ideal O)) (hS : ∀p∈S,p.IsMaximal)
    (σ : RayFourExpansion.RayRing) (C : SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Summable (fun k : GramFrequency=>originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  unfold originalCommonBlock
  apply summable_sum
  intro I hI
  apply summable_sum
  intro J hJ
  by_cases hij : IsCoprime I.val J.val
  · simp only [hij,ite_true]
    have hs := (actual_correlation_radial_summable (supportedIdealProduct C I) (supportedIdealProduct C J)
      (primaryGenerator C.val) (supported_primaryGenerator_ne_zero _ C.property) U Q hQ).subtype (fun k : O=>k≠0)
    simpa only [Function.comp_def,mul_assoc] using hs.mul_left
      ((lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C I)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C I).val:ℝ)/Y))*
       star (lowGramCoefficient (calibrationForSet S hS) σ (supportedIdealProduct C J)*
        lowGramProfile W v ((Ideal.absNorm (supportedIdealProduct C J).val:ℝ)/Y)))
  · simpa only [hij,ite_false] using (summable_zero : Summable (fun _ : GramFrequency=>(0:ℂ)))

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1619

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramEnergyNonzero
Source SHA256: bc894f29b3d0d4219f8363d3de8f077b39919d8dea453b97683092babcf85ace
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1620




namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O

lemma original_pair_zero_split (I J : SupportedIdeal) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    (∑'h : O,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
      ((supported_span_primaryGenerator_iff _).mpr I.property)
      ((supported_span_primaryGenerator_iff _).mpr J.property) (-h)*
      paperRadialFourier U (Q*‖eisEmbedding h‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) 0*paperRadialFourier U 0+
      ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
        paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  have hs := actual_correlation_radial_summable I J (-1) (by norm_num) U Q hQ
  simp only [neg_one_mul,map_neg,norm_neg] at hs
  have hh := hs.tsum_eq_add_tsum_ite 0
  simpa only [neg_zero,map_zero,norm_zero,zero_pow (by decide : 2≠0),mul_zero,zero_div,nonzero_tsum_indicator] using hh

theorem original_energy_nonzero (C : CalibrationData) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y : ℝ) (hY : 0<Y) (σ : RayRing) (v : ℝ) (U : SchwartzMap ℝ ℂ) (Q : ℝ) (hQ : 0<Q) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=>primaryGenerator I.val)
      (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
      (lowGaussColumn C W Y σ v) U Q=
      lowGramZeroMode C W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,
        ((lowGramCoefficient C σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
          star (lowGramCoefficient C σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y)))*
        ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
          ((supported_span_primaryGenerator_iff _).mpr I.property)
          ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
          paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2) := by
  rw [lowGram_source_poisson C W hW Y hY σ v U Q hQ,lowGramZeroMode_eq_source]
  simp_rw [original_pair_zero_split _ _ U Q hQ,mul_add,Finset.sum_add_distrib]
  simp only [mul_add]
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  ring

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1620

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramCommonEnergy
Source SHA256: ed94d76e75d348f80649e7aa443a74446ace763933ad1fa70949208bc937832c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1621



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss ConcreteTraceCRT RayFourExpansion
open CenteredMomentSupportedCorrelation EisensteinSchwartzPoisson CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma gcdCommon_product_coprime (C I J : SupportedIdeal) (h : IsCoprime I.val J.val) :
    gcdCommon (supportedIdealProduct C I) (supportedIdealProduct C J)=C := by
  have hh:=congrArg (fun t : CoprimeTriple=>t.val.1) (gcdTriple_multiply ⟨(C,I,J),h⟩)
  exact hh

def originalPairWeight (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (Y v : ℝ) (I J : SupportedIdeal) : ℂ :=
  (lowGramCoefficient (calibrationForSet S hS) σ I*lowGramProfile W v ((Ideal.absNorm I.val:ℝ)/Y))*
    star (lowGramCoefficient (calibrationForSet S hS) σ J*lowGramProfile W v ((Ideal.absNorm J.val:ℝ)/Y))

theorem original_nonzero_common_sum (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    (∑I∈lowGaussColumns W hW Y hY,∑J∈lowGaussColumns W hW Y hY,
      originalPairWeight S hS σ W Y v I J*
      ∑'h : GramFrequency,actualCorrelation (primaryGenerator I.val) (primaryGenerator J.val)
        ((supported_span_primaryGenerator_iff _).mpr I.property)
        ((supported_span_primaryGenerator_iff _).mpr J.property) (-h.val)*
        paperRadialFourier U (Q*‖eisEmbedding h.val‖^2/‖eisEmbedding (primaryGenerator I.val*primaryGenerator J.val)‖^2))=
      ∑C∈commonPool (lowGaussColumns W hW Y hY),∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v := by
  simp_rw [actual_gcd_nonzero_frequency_source]
  rw [original_window_gcd]
  apply Finset.sum_congr rfl
  intro C hC
  let F:=lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)
  let f := fun (I J : SupportedIdeal) (k : GramFrequency)=>
    if IsCoprime I.val J.val then
      originalPairWeight S hS σ W Y v (supportedIdealProduct C I) (supportedIdealProduct C J)*
      actualCorrelation (primaryGenerator (supportedIdealProduct C I).val) (primaryGenerator (supportedIdealProduct C J).val)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C I).property)
        ((supported_span_primaryGenerator_iff _).mpr (supportedIdealProduct C J).property) (primaryGenerator C.val*k.val)*
      paperRadialFourier U (Q*‖eisEmbedding (primaryGenerator C.val*k.val)‖^2/
        ‖eisEmbedding (primaryGenerator (supportedIdealProduct C I).val*primaryGenerator (supportedIdealProduct C J).val)‖^2) else 0
  have hf (I J : SupportedIdeal) : Summable (f I J) := by
    by_cases hij : IsCoprime I.val J.val
    · have hh := ((actual_correlation_radial_summable (supportedIdealProduct C I) (supportedIdealProduct C J)
        (primaryGenerator C.val) (supported_primaryGenerator_ne_zero _ C.property) U Q hQ).subtype (fun k : O=>k≠0)).mul_left
          (originalPairWeight S hS σ W Y v (supportedIdealProduct C I) (supportedIdealProduct C J))
      simpa only [f,hij,ite_true,Function.comp_def,mul_assoc] using hh
    · simpa only [f,hij,ite_false] using (summable_zero : Summable (fun _ : GramFrequency=>(0:ℂ)))
  have hr : (∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v)=
      ∑I∈F,∑J∈F,∑'k : GramFrequency,f I J k := by
    change (∑'k : GramFrequency,∑I∈F,∑J∈F,f I J k)=_
    rw [Summable.tsum_finsetSum (fun I hI=>summable_sum (fun J hJ=>hf I J))]
    apply Finset.sum_congr rfl
    intro I hI
    exact Summable.tsum_finsetSum (fun J hJ=>hf I J)
  rw [hr]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases hij : IsCoprime I.val J.val
  · simp only [hij,ite_true,f,gcdCommon_product_coprime C I J hij]
    rw [←tsum_mul_left]
    apply tsum_congr
    intro k
    ring
  · simp only [hij,ite_false,f,tsum_zero]

theorem original_energy_common_blocks (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    gaussEnergy (lowGaussColumns W hW Y hY) (fun I=>primaryGenerator I.val)
      (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
      (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q=
      lowGramZeroMode (calibrationForSet S hS) W hW Y hY σ v U Q+
      ((Q/Y^3:ℝ):ℂ)*(∑C∈commonPool (lowGaussColumns W hW Y hY),
        ∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v) := by
  rw [original_energy_nonzero _ _ _ _ _ _ _ _ _ hQ]
  congr 1
  congr 1
  exact original_nonzero_common_sum S hS σ W hW Y Q hY hQ U v

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1621

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramSourceDivisors
Source SHA256: fddf89c1f2343ff523d821f0e887934e26e911abfa45f3d18b5616424135faf0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1622



namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
open CenteredMomentMobiusRegroup UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sourceDivisors (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) : Finset SupportedIdeal :=
  (divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val).preimage
    Subtype.val Subtype.val_injective.injOn
lemma sourceDivisors_mem (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) :
    D∈sourceDivisors W hW Y hY C ↔
      D.val∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val := Finset.mem_preimage

def sourceDivisorUnion (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) : Finset SupportedIdeal :=
  F.biUnion (sourceDivisors W hW Y hY)

def sourceMobiusWeight (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) : ℂ :=
  if D∈sourceDivisors W hW Y hY C then (moebius D.val:ℂ) else 0
lemma sourceMobiusWeight_norm (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y) (C D : SupportedIdeal) :
    ‖sourceMobiusWeight W hW Y hY C D‖≤1 := by
  unfold sourceMobiusWeight
  split_ifs
  · exact CubicEisenstein.norm_ideal_moebius_le_one _
  · simp

lemma sourceDivisors_sum (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y : ℝ) (hY : 0<Y)
    (C : SupportedIdeal) (f : Id→ℂ) :
    (∑D∈sourceDivisors W hW Y hY C,f D.val)=
      ∑D∈divisorPool (lowGaussColumns W hW (commonResidualScale C Y) (commonResidualScale_pos C Y hY)) Subtype.val,f D := by
  apply Finset.sum_bij (fun D _=>D.val)
  · intro D hD;exact (sourceDivisors_mem W hW Y hY C D).mp hD
  · intro D hD E hE h;exact Subtype.val_injective h
  · intro D hD
    refine ⟨⟨D,divisorPool_supported _ _ hD⟩,?_,rfl⟩
    exact (sourceDivisors_mem W hW Y hY C _).mpr hD
  · intro D hD;rfl

lemma sourceMobiusWeight_rectangle (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y : ℝ) (hY : 0<Y) (C : SupportedIdeal) (hC : C∈F) (f : SupportedIdeal→ℂ) :
    (∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*f D)=
      ∑D∈sourceDivisors W hW Y hY C,(moebius D.val:ℂ)*f D := by
  rw [←Finset.sum_subset (show sourceDivisors W hW Y hY C⊆sourceDivisorUnion F W hW Y hY from
    fun D hD=>Finset.mem_biUnion.mpr ⟨C,hC,hD⟩) (by intro D hD hn;simp only [sourceMobiusWeight,ite_eq_right hn,zero_mul])]
  exact Finset.sum_congr rfl (fun D hD=>by rw [sourceMobiusWeight,ite_eq_left hD])

theorem originalCommonBlock_eq_rectangle (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (C : SupportedIdeal) (hC : C∈F)
    (k : GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    originalCommonBlock S hS σ C k W hW Y Q hY U v=
      ∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
        canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
          ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C))
          (Y/(gramIdealNorm C*gramIdealNorm D)) := by
  rw [sourceMobiusWeight_rectangle F W hW Y hY C hC]
  rw [originalCommonBlock_eq_lattice S hS hbad σ C k W hW Y Q hY hQ U v]
  rw [←sourceDivisors_sum W hW Y hY C]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  rw [frequencyScale_ratio]
  congr 1
  simp only [commonResidualScale,gramIdealNorm,div_div]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1622

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramTruncation
Source SHA256: f671f7fe38580c6519f4eee470de91986b0ddaad8b51db167a42c8b75a283b72
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1623


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion ConcreteTraceCRT
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

def sourceTruncation (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑k∈E,originalCommonBlock S hS σ C k W hW Y Q hY U v

def sourceCanonicalSum (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : SupportedIdeal→Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) : ℂ :=
  ((Q/Y^3:ℝ):ℂ)*∑C∈F,∑D∈sourceDivisorUnion F W hW Y hY,sourceMobiusWeight W hW Y hY C D*
    ∑k∈E C,canonicalLatticeBlock S hS σ C k (primaryGenerator D.val) W U v
      ((Ideal.absNorm (Ideal.span {k.val}):ℝ)/((Y^2/Q)/gramIdealNorm C)) (Y/(gramIdealNorm C*gramIdealNorm D))

theorem sourceTruncation_eq_canonical (S : Finset Id) (hS : ∀p∈S,p.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (F : Finset SupportedIdeal) (E : Finset GramFrequency)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q)
    (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceTruncation S hS σ F E W hW Y Q hY U v=sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v := by
  unfold sourceTruncation sourceCanonicalSum
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  simp_rw [originalCommonBlock_eq_rectangle S hS hbad σ F C hC _ W hW Y Q hY hQ U v]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun D hD=>(Finset.mul_sum ..).symm)

def exceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (ExceptionalFrequency S hS C)
def nonexceptionalFrequencies (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (E : Finset GramFrequency) (C : SupportedIdeal) : Finset GramFrequency :=
  E.filter (fun k=>¬ExceptionalFrequency S hS C k)

lemma sourceCanonicalSum_split (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (E : Finset GramFrequency) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    sourceCanonicalSum S hS σ F (fun _=>E) W hW Y Q hY U v=
      sourceCanonicalSum S hS σ F (exceptionalFrequencies S hS E) W hW Y Q hY U v+
      sourceCanonicalSum S hS σ F (nonexceptionalFrequencies S hS E) W hW Y Q hY U v := by
  unfold sourceCanonicalSum exceptionalFrequencies nonexceptionalFrequencies
  rw [←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro C hC
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro D hD
  rw [←mul_add,Finset.sum_filter_add_sum_filter_not]

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1623

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramSourceEstimate
Source SHA256: 5d49b2ca1d93ac56c69c18a85fc61d3e90317cbf852d58626d691c67b05ad913
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1624


namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem original_source_truncation_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (F : Finset SupportedIdeal)(E : Finset GramFrequency)(U : SchwartzMap ℝ ℂ)
      (v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖sourceTruncation S hS σ F E W hcompact Y Q hY U v‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,hgood⟩ := canonical_nonexceptional_ideal_sum δ hδ hδ1 3 (by norm_num) a b ha hab
  obtain ⟨K₁,hK₁,hgood⟩ := hgood W hs hW
  obtain ⟨H₂,K₂,hK₂,hbadbound⟩ := canonical_exceptional_ideal_sum ε hε hε1 a b M₀ ha (by linarith) hM₀
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ F E U v Y Q hY hQ
  let G:=sourceDivisorUnion F W hcompact Y hY
  have hα := fun (C : SupportedIdeal) (_ : C∈F) (D : SupportedIdeal) (_ : D∈G)=>sourceMobiusWeight_norm W hcompact Y hY C D
  have hg := hgood S hS σ F G (fun C _=>nonexceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  have hb := hbadbound W hcompact hs hWM S hS σ F G (fun C _=>exceptionalFrequencies S hS E C)
    (sourceMobiusWeight W hcompact Y hY) hα
    (by intro C hC D hD k hk;exact (Finset.mem_filter.mp hk).2)
    U v (Y^2/Q) Y Q (by positivity) hY hQ.le
  rw [sourceTruncation_eq_canonical S hS hbad σ F E W hcompact Y Q hY hQ U v,sourceCanonicalSum_split]
  exact (norm_add_le _ _).trans ((add_le_add hb hg).trans_eq (add_comm _ _))

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1624

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramInfiniteEstimate
Source SHA256: 6b6f5bd3bdd4784362cd406b891fc50d0bf36549626a73cc5d7db554cfa256a5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1625


namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff Topology
namespace SevenEighths.ProbeGramCommon
open Filter ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma sourceTruncation_tendsto (S : Finset Id) (hS : ∀p∈S,p.IsMaximal) (σ : RayRing)
    (F : Finset SupportedIdeal) (W : ℝ→ℂ) (hW : HasCompactSupport W)
    (Y Q : ℝ) (hY : 0<Y) (hQ : 0<Q) (U : SchwartzMap ℝ ℂ) (v : ℝ) :
    Tendsto (fun E : Finset GramFrequency=>sourceTruncation S hS σ F E W hW Y Q hY U v) atTop
      (𝓝 (((Q/Y^3:ℝ):ℂ)*∑C∈F,∑'k : GramFrequency,originalCommonBlock S hS σ C k W hW Y Q hY U v)) := by
  have hs (C : SupportedIdeal) : Summable (fun k : GramFrequency=>originalCommonBlock S hS σ C k W hW Y Q hY U v) :=
    originalCommonBlock_summable S hS σ C W hW Y Q hY hQ U v
  have hh := (summable_sum (s:=F) (fun C hC=>hs C)).hasSum.mul_left ((Q/Y^3:ℝ):ℂ)
  rw [Summable.tsum_finsetSum (fun C hC=>hs C)] at hh
  change Tendsto _ atTop (𝓝 _) at hh
  convert hh using 1
  funext E
  unfold sourceTruncation
  rw [←Finset.mul_sum,Finset.sum_comm]

theorem original_energy_nonzero_bound (δ ε : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (hε : 0<ε) (hε1 : ε<1/6) (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃(J : ℕ)(H₁ H₂ : Finset (ℕ×ℕ))(K₁ K₂ : ℝ),0<K₁ ∧ 0<K₂ ∧
      ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀(σ : RayRing)
      (U : SchwartzMap ℝ ℂ)(v Y Q : ℝ)(hY : 0<Y),0<Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y hY) (fun I=>primaryGenerator I.val)
        (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q-
        lowGramZeroMode (calibrationForSet S hS) W hcompact Y hY σ v U Q‖≤
        K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*(Y^2/Q)*
          (Y/((Ideal.absNorm (jointFixedModulus S hS):ℝ)*(Y^2/Q)))^(-1+δ)+
        K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(Q/Y)*
          (Ideal.absNorm (jointFixedModulus S hS):ℝ)^ε*(Y^2/Q)^(1/6:ℝ) := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_source_truncation_bound δ ε hδ hδ1 hε hε1 a b M₀ ha hab hM₀ W hcompact hs hW hWM
  refine ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,?_⟩
  intro S hS hbad σ U v Y Q hY hQ
  rw [original_energy_common_blocks S hS σ W hcompact Y Q hY hQ U v,add_sub_cancel_left]
  exact le_of_tendsto (sourceTruncation_tendsto S hS σ _ W hcompact Y Q hY hQ U v).norm
    (Eventually.of_forall (fun E=>hbound S hS hbad σ _ E U v Y Q hY hQ))

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1625

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramScaleLoss
Source SHA256: aa6276fcde446984a64de421676498db551dd84f8bd190c5ddba4dd16898ac32
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1626


namespace OAI

noncomputable section
namespace SevenEighths.ProbeGramCommon

lemma nonexceptional_scale_identity (M P Y δ : ℝ) (hM : 0<M) (hP : 0<P) (hY : 0<Y) :
    P*(Y/(M*P))^(-1+δ)=M^(1-δ)*P^(2-δ)*Y^(-1+δ) := by
  rw [Real.div_rpow hY.le (mul_pos hM hP).le,Real.mul_rpow hM.le hP.le,div_eq_mul_inv,mul_inv_rev,
    ←Real.rpow_neg hM.le,←Real.rpow_neg hP.le]
  have he : P*P^(-(-1+δ))=P^(2-δ) := by
    conv_lhs => lhs;rw [←Real.rpow_one P]
    rw [←Real.rpow_add hP]
    congr 1
    ring
  calc
    _=M^(1-δ)*(P*P^(-(-1+δ)))*Y^(-1+δ) := by rw [show -(-1+δ)=1-δ by ring];ring
    _=_ := by rw [he]

lemma nonexceptional_scale_loss (M P Y δ : ℝ) (hM : 1≤M) (hP : 1≤P) (hY : 0<Y)
    (hδ : 0≤δ) :
    P*(Y/(M*P))^(-1+δ)≤M*(P^2/Y)*Y^δ := by
  have hm : 0<M := lt_of_lt_of_le zero_lt_one hM
  have hp : 0<P := lt_of_lt_of_le zero_lt_one hP
  rw [nonexceptional_scale_identity M P Y δ hm hp hY]
  have hmp : M^(1-δ)≤M := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hM (show 1-δ≤1 by linarith)
  have hpp : P^(2-δ)≤P^2 := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le hP (show 2-δ≤2 by linarith)
  calc
    _≤M*P^2*Y^(-1+δ) := mul_le_mul_of_nonneg_right
      (mul_le_mul hmp hpp (by positivity) hm.le) (by positivity)
    _=_ := by rw [Real.rpow_add hY,Real.rpow_neg_one];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1626

/-! Original module: OAI.NumberTheory.DirichletL.Detector.GramBound
Source SHA256: 589051b4b1a3666c2a0a60bf05760c4def5f8f5e2544ef3cd2775f94894f36dc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1627


namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbeGramCommon
open ProbePhysical CanonicalQuadraticSieve CompletedGauss RayFourExpansion
open CenteredMomentGaussEnergy EisensteinSchwartzPoisson
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem actual_additive_gram_bound (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M₀ : ℝ) (ha : 0<a) (hab : a<b) (hM₀ : 0≤M₀)
    (W : ℝ→ℂ) (hcompact : HasCompactSupport W) (hs : Function.support W⊆Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (hWM : ∀x,‖W x‖≤M₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→∀U : SchwartzMap ℝ ℂ,
    ∃K : ℝ,0<K ∧ ∀(σ : RayRing)(v Y Q : ℝ)(hY : 1≤Y),0<Q→1≤Y^2/Q→
      ‖gaussEnergy (lowGaussColumns W hcompact Y (lt_of_lt_of_le zero_lt_one hY))
        (fun I=>primaryGenerator I.val) (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q‖≤
      K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ := by
  obtain ⟨J,H₁,H₂,K₁,K₂,hK₁,hK₂,hbound⟩ := original_energy_nonzero_bound δ (1/12) hδ hδ1
    (by norm_num) (by norm_num) a b M₀ ha hab hM₀ W hcompact hs hW hWM
  obtain ⟨K₀,hK₀,hzero⟩ := lowGramZeroMode_source_bound a b M₀ ha hM₀
  refine ⟨J,?_⟩
  intro S hS hbad U
  let M : ℝ := Ideal.absNorm (jointFixedModulus S hS)
  have hM : 1≤M := by dsimp [M];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (jointFixedModulus_nonzero S hS))
  let A₀ := K₀*‖paperRadialFourier U 0‖
  let A₁ := K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M
  let A₂ := K₂*H₂.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*M^(1/12:ℝ)
  have hA₀ : 0≤A₀ := by dsimp [A₀];positivity
  have hA₁ : 0≤A₁ := by dsimp [A₁];positivity
  have hA₂ : 0≤A₂ := by dsimp [A₂];positivity
  refine ⟨1+A₀+A₁+A₂,by positivity,?_⟩
  intro σ v Y Q hY hQ hP
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let P := Y^2/Q
  have hp : 1≤P := hP
  have hp0 : 0<P := lt_of_lt_of_le zero_lt_one hp
  let Z := lowGramZeroMode (calibrationForSet S hS) W hcompact Y hy σ v U Q
  let E := gaussEnergy (lowGaussColumns W hcompact Y hy) (fun I=>primaryGenerator I.val)
    (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
    (lowGaussColumn (calibrationForSet S hS) W Y σ v) U Q
  have hn := hbound S hS hbad σ U v Y Q hy hQ
  have hz : ‖Z‖≤A₀*(Q/Y) := by
    have hh := hzero S hS W hcompact hs hWM Y hY σ v U Q hQ.le
    convert hh using 1 ; dsimp [Z,A₀] ; ring
  have hgood : K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y)*P*
      (Y/(M*P))^(-1+δ)≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ := by
    have hh := mul_le_mul_of_nonneg_left (nonexceptional_scale_loss M P Y δ hM hp hy hδ.le)
      (show 0≤K₁*H₁.sup (schwartzSeminormFamily ℝ ℝ ℂ) U*(1+|v|)^J*(Q/Y) by positivity)
    convert hh using 1 <;> (try dsimp [A₁]) <;> ring
  have henergy : ‖E‖≤A₀*(Q/Y)+A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
    have hn' : ‖E-Z‖≤A₁*(1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ+A₂*(Q/Y)*P^(1/6:ℝ) := by
      apply hn.trans
      exact add_le_add hgood (by dsimp [A₂,M,P];ring_nf;exact le_rfl)
    calc
      ‖E‖=‖(E-Z)+Z‖ := by congr 1;ring
      _≤‖E-Z‖+‖Z‖ := norm_add_le _ _
      _≤_ := by linarith
  let B := (1+|v|)^J*(Q/Y)*(1+P^(1/6:ℝ)+P^2/Y)*Y^δ
  have hb : 0≤B := by dsimp [B];positivity
  have hh : 1≤(1+|v|)^J := one_le_pow₀ (by linarith [abs_nonneg v])
  have hyd : 1≤Y^δ := Real.one_le_rpow hY hδ.le
  have hshape : 1≤1+P^(1/6:ℝ)+P^2/Y := by
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    have hratio : 0≤P^2/Y := by positivity
    linarith
  have hb₀ : Q/Y≤B := by
    calc
      Q/Y=(1:ℝ)*(Q/Y)*1*1 := by ring
      _≤B := by dsimp [B];gcongr
  have hb₁ : (1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ≤B := by
    dsimp [B]
    gcongr
    have hpow : 0≤P^(1/6:ℝ) := by positivity
    linarith
  have hb₂ : (Q/Y)*P^(1/6:ℝ)≤B := by
    calc
      _=(1:ℝ)*(Q/Y)*P^(1/6:ℝ)*1 := by ring
      _≤B := by
        dsimp [B]
        gcongr
        have hratio : 0≤P^2/Y := by positivity
        linarith
  change ‖E‖≤_
  calc
    _≤A₀*(Q/Y)+A₁*((1+|v|)^J*(Q/Y)*(P^2/Y)*Y^δ)+A₂*((Q/Y)*P^(1/6:ℝ)) := by convert henergy using 1 ; ring
    _≤A₀*B+A₁*B+A₂*B := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hb₀ hA₀)
      (mul_le_mul_of_nonneg_left hb₁ hA₁)) (mul_le_mul_of_nonneg_left hb₂ hA₂)
    _≤(1+A₀+A₁+A₂)*B := by nlinarith
    _=_ := by dsimp [B,P];ring

end SevenEighths.ProbeGramCommon
end

end OAI
end OAIOriginalModule1627

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramApplied
Source SHA256: 871f9f2475260271be5c50cca3d77134c21a3e75fa9431b47039edbe297900a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1628



namespace OAI

noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion CenteredMomentGaussEnergy
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

theorem lowSeparatedIntegrand_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M : ℝ) (ha : 0<a) (hab : a<b) (hM : 0≤M)
    (W1 : ℝ→ℂ) (hW1c : HasCompactSupport W1) (hW1 : Function.support W1⊆Set.Icc a b)
    (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (hb₀ : 0<b₀) :
    ∃J : ℕ,∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
      ∃K : ℝ,0<K ∧ ∀(W0 : ℝ→ℂ)(X Y : ℝ)(hX : 0<X)(hY : 1≤Y)
        (B : RayRing→O→ℂ)(v : ℝ),1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y→
      ‖lowSeparatedIntegrand (calibrationForSet S hS) W0 W1 (lowOuterCutoff a₀ b₀) X Y B v‖≤
        ‖mellin W0 ((v:ℂ)*Complex.I)‖*
        Real.sqrt (K*(1+|v|)^J*(lowPhysicalScale (calibrationForSet S hS) X Y/Y)*
          (1+(Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^(1/6:ℝ)+
            (Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^2/Y)*Y^δ)*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀
          (lowPhysicalScale (calibrationForSet S hS) X Y)
          (lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)),‖B σ m‖^2) := by
  obtain ⟨J,hgram⟩ := ProbeGramCommon.actual_additive_gram_bound δ hδ hδ1 a b M ha hab hM
    W1 hW1c hW1 hW1s hWM
  refine ⟨J,?_⟩
  intro S hS hbad
  obtain ⟨K,hK,hgram⟩ := hgram S hS hbad (lowGaussMajorant a₀ b₀ ha₀ hb₀)
  refine ⟨K,hK,?_⟩
  intro W0 X Y hX hY B v hP
  have hy : 0<Y := lt_of_lt_of_le zero_lt_one hY
  let Q := lowPhysicalScale (calibrationForSet S hS) X Y
  have hQ : 0<Q := lowPhysicalScale_pos _ X Y hX hy
  let A := K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ
  have hbound (σ : RayRing) :
      (gaussEnergy (lowGaussColumns W1 hW1c Y hy) (fun I=>primaryGenerator I.val)
        (fun I=>(supported_span_primaryGenerator_iff _).mpr I.property)
        (lowGaussColumn (calibrationForSet S hS) W1 Y σ v) (lowGaussMajorant a₀ b₀ ha₀ hb₀) Q).re≤A :=
    (Complex.re_le_norm _).trans (hgram σ v Y Q hY hQ hP)
  apply (lowSeparatedIntegrand_actual_energies a₀ b₀ ha₀ hb₀ (calibrationForSet S hS)
    W0 W1 hW1c X Y hX hy B v).trans
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    _≤∑σ : RayRing,Real.sqrt A*Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀ Q hQ,‖B σ m‖^2) :=
      Finset.sum_le_sum (fun σ _=>mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (hbound σ)) (Real.sqrt_nonneg _))
    _=_ := (Finset.mul_sum ..).symm

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1628

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramIntegrated
Source SHA256: 0749a6bbfffa1b4717a81ff44abd54e2f21eba5a1538515e8810b8b0d8d7eaf1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1629


namespace OAI

noncomputable section
open scoped Classical ContDiff
open MeasureTheory
namespace SevenEighths.ProbePhysical
open CanonicalQuadraticSieve CompletedGauss RayFourExpansion
local notation "O" => ActualEisensteinCubic.O
local notation "Id" => Ideal O

lemma low_mellin_sqrt_weight_bound (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hW : Function.support W⊆Set.Icc a b) (hWs : ContDiff ℝ ∞ W) (J : ℕ) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,
      ‖mellin W ((v:ℂ)*Complex.I)‖*Real.sqrt ((1+|v|)^J)≤C/(1+v^2) := by
  obtain ⟨C,hC,hb⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W a b ha hW hWs 0 0 (J+2)
  refine ⟨C,hC,?_⟩
  intro v
  apply CubicReflectionKernel.weighted_two_to_cauchy (by positivity) v
  have hp : 1≤(1+|v|)^J := one_le_pow₀ (by linarith [abs_nonneg v])
  have hs : Real.sqrt ((1+|v|)^J)≤(1+|v|)^J := Real.sqrt_le_self_iff.mpr (Or.inr hp)
  have hb' := hb 0 (by simp) v
  simp only [Complex.ofReal_zero,zero_add] at hb'
  calc
    _≤(1+|v|)^2*(‖mellin W ((v:ℂ)*Complex.I)‖*(1+|v|)^J) := by gcongr
    _=(1+|v|)^(J+2)*‖mellin W ((v:ℂ)*Complex.I)‖ := by rw [pow_add];ring
    _≤C := hb'

theorem lowSeparatedIntegral_actual_gram (δ : ℝ) (hδ : 0<δ) (hδ1 : δ<1)
    (a b M : ℝ) (ha : 0<a) (hab : a<b) (hM : 0≤M)
    (W1 : ℝ→ℂ) (hW1c : HasCompactSupport W1) (hW1 : Function.support W1⊆Set.Icc a b)
    (hW1s : ContDiff ℝ ∞ W1) (hWM : ∀x,‖W1 x‖≤M)
    (a₀ b₀ : ℝ) (ha₀ : 0<a₀) (hb₀ : 0<b₀)
    (W0 : ℝ→ℂ) (a0 b0 : ℝ) (ha0 : 0<a0)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW0s : ContDiff ℝ ∞ W0) :
    ∀(S : Finset Id)(hS : ∀p∈S,p.IsMaximal),fixedBadPrimes⊆S→
      ∃C : ℝ,0<C ∧ ∀(X Y : ℝ)(hX : 0<X)(hY : 1≤Y)(B : RayRing→O→ℂ),
        1≤Y^2/lowPhysicalScale (calibrationForSet S hS) X Y→
      ‖∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
        (lowOuterCutoff a₀ b₀) X Y B v‖≤
        C*Real.sqrt ((lowPhysicalScale (calibrationForSet S hS) X Y/Y)*
          (1+(Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^(1/6:ℝ)+
            (Y^2/lowPhysicalScale (calibrationForSet S hS) X Y)^2/Y)*Y^δ)*
        ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀
          (lowPhysicalScale (calibrationForSet S hS) X Y)
          (lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)),‖B σ m‖^2) := by
  obtain ⟨J,hgram⟩ := lowSeparatedIntegrand_actual_gram δ hδ hδ1 a b M ha hab hM W1 hW1c hW1 hW1s hWM a₀ b₀ ha₀ hb₀
  obtain ⟨CM,hCM,hm⟩ := low_mellin_sqrt_weight_bound W0 a0 b0 ha0 hW0 hW0s J
  intro S hS hbad
  obtain ⟨K,hK,hgram⟩ := hgram S hS hbad
  refine ⟨CM*Real.sqrt K*Real.pi,by positivity,?_⟩
  intro X Y hX hY B hP
  let Q := lowPhysicalScale (calibrationForSet S hS) X Y
  have hQ : 0<Q := lowPhysicalScale_pos _ X Y hX (lt_of_lt_of_le zero_lt_one hY)
  let A := (Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ
  have hA : 0≤A := by dsimp [A]; positivity
  let E := ∑σ : RayRing,Real.sqrt (∑m∈lowNumeratorRows a₀ b₀ ha₀ hb₀ Q hQ,‖B σ m‖^2)
  have hE : 0≤E := Finset.sum_nonneg (fun _ _=>Real.sqrt_nonneg _)
  have hh (v : ℝ) : ‖lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff a₀ b₀) X Y B v‖≤(CM*Real.sqrt K*Real.sqrt A*E)*(1+v^2)⁻¹ := by
    have hg := hgram W0 X Y hX hY B v hP
    have he : K*(1+|v|)^J*(Q/Y)*(1+(Y^2/Q)^(1/6:ℝ)+(Y^2/Q)^2/Y)*Y^δ=
        (1+|v|)^J*(K*A) := by dsimp [A];ring
    rw [he,Real.sqrt_mul (by positivity),Real.sqrt_mul hK.le] at hg
    calc
      _≤(‖mellin W0 ((v:ℂ)*Complex.I)‖*Real.sqrt ((1+|v|)^J))*
          (Real.sqrt K*Real.sqrt A*E) := by convert hg using 1 ;ring
      _≤(CM/(1+v^2))*(Real.sqrt K*Real.sqrt A*E) :=
        mul_le_mul_of_nonneg_right (hm v) (by positivity)
      _=_ := by rw [div_eq_mul_inv];ring
  have hi := norm_integral_le_of_norm_le (integrable_inv_one_add_sq.const_mul
    (CM*Real.sqrt K*Real.sqrt A*E)) (Filter.Eventually.of_forall hh)
  rw [integral_const_mul,integral_univ_inv_one_add_sq] at hi
  convert hi using 1 ;ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1629

/-! Original module: OAI.NumberTheory.DirichletL.Detector.LowGramScale
Source SHA256: ca46b12dad51371b9b2c15393d6aa5d5a1d6c0586a2402ebc5bf7332e7435e90
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1630


namespace OAI

noncomputable section
namespace SevenEighths.ProbePhysical

lemma compensated_gram_ratio (q X Y L : ℝ) (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 0<L) :
    (Y/L)^2/(q*(X/L)*(Y/L))=Y/(q*X) := by
  field_simp

lemma compensated_gram_scale_bound (q X Y L δ : ℝ)
    (hq : 0<q) (hX : 0<X) (hY : 0<Y) (hL : 1≤L) (hδ : 0≤δ)
    (hP : q*X≤Y) (htail : L*Y≤q^2*X^2) :
    (q*(X/L)*(Y/L)/(Y/L))*
      (1+((Y/L)^2/(q*(X/L)*(Y/L)))^(1/6:ℝ)+
        ((Y/L)^2/(q*(X/L)*(Y/L)))^2/(Y/L))*(Y/L)^δ ≤
      3*(q*X/L)*(Y/(q*X))^(1/6:ℝ)*Y^δ := by
  have hl : 0<L := lt_of_lt_of_le zero_lt_one hL
  have hp : 1≤Y/(q*X) := (le_div_iff₀ (mul_pos hq hX)).mpr (by simpa using hP)
  have hr : 1≤(Y/(q*X))^(1/6:ℝ) := Real.one_le_rpow hp (by norm_num)
  have ht : (Y/(q*X))^2/(Y/L)≤1 := by
    have he : (Y/(q*X))^2/(Y/L)=L*Y/(q^2*X^2) := by field_simp
    rw [he]
    exact (div_le_one (by positivity)).mpr htail
  have hys : (Y/L)^δ≤Y^δ := Real.rpow_le_rpow (by positivity)
    ((div_le_self hY.le hL)) hδ
  rw [compensated_gram_ratio q X Y L hq hX hY hl]
  have he : q*(X/L)*(Y/L)/(Y/L)=q*X/L := by field_simp
  rw [he]
  calc
    _≤(q*X/L)*(3*(Y/(q*X))^(1/6:ℝ))*Y^δ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hys
        (by positivity) (by positivity)
    _=_ := by ring

lemma source_gram_power (Z δ : ℝ) (hZ : 0<Z) :
    Z^(17/48:ℝ)*(Z^(1/8:ℝ))^(1/6:ℝ)*(Z^(23/48:ℝ))^δ=
      Z^(3/8+(23/48)*δ:ℝ) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma source_gram_sqrt_power (Z δ : ℝ) (hZ : 0<Z) :
    Real.sqrt (Z^(3/8+(23/48)*δ:ℝ))=Z^(3/16+(23/96)*δ:ℝ) := by
  rw [Real.sqrt_eq_rpow,←Real.rpow_mul hZ.le]
  congr 1
  ring

end SevenEighths.ProbePhysical
end

end OAI
end OAIOriginalModule1630

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Unequal
Source SHA256: 1a5f2b03a5ae8c814582adeeee8f7a7dc38f486dda998a92099d8f7b44f15d35
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1631




namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentUnequal
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

theorem divisor_congruence (v t k : A) (hv : v ≠ 0)
    (x : Residue (v * t)) (y : Residue v) :
    scaledResidue (v * t) v ((v * t) * v) rfl x -
      scaledResidue v (v * t) ((v * t) * v) (mul_comm _ _) y =
      Ideal.Quotient.mk _ (v * k) ↔
      x = scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_congruence, scaledResidue_mk, ← map_add, Ideal.Quotient.eq, Ideal.mem_span_singleton]
  change (v * t) * v ∣ v * x - (v * t) * y - v * k ↔ v * t ∣ x - (t * y + k)
  rw [show (v * t) * v = v * (v * t) by ring,
    show v * x - (v * t) * y - v * k = v * (x - (t * y + k)) by ring]
  exact mul_dvd_mul_iff_left hv

theorem fullCorrelation_divisor (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      ∑ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) *
        star (χv y) := by
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [divisor_congruence v t k hv]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

theorem fullCorrelation_divisor_constant (v t k : A) (hv : v ≠ 0)
    [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (hχ : ∀ y : Residue v,
      χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) = χu (Ideal.Quotient.mk _ k)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) =
      χu (Ideal.Quotient.mk _ k) * star (∑ y : Residue v, χv y) := by
  rw [fullCorrelation_divisor v t k hv χu χv]
  simp_rw [hχ]
  rw [← Finset.mul_sum, star_sum]

omit [IsDomain A] in
theorem divisor_lift_constant (p v t k : A) (hpt : p ∣ t)
    (χu : MulChar (Residue (v * t)) ℂ) (χ : MulChar (Residue p) ℂ)
    (hχ : ∀ x : A, χu (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    ∀ y : Residue v, χu (scaledResidue v t (v * t) rfl y + Ideal.Quotient.mk _ k) =
      χu (Ideal.Quotient.mk _ k) := by
  intro y
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, ← map_add, hχ, hχ, map_add, map_mul]
  have ht : Ideal.Quotient.mk (Ideal.span {p}) t = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hpt)
  rw [ht, zero_mul, zero_add]

omit [IsDomain A] in
theorem lifted_character_sum_zero (p v : A) (hpv : p ∣ v)
    [Fintype (Residue p)] [Fintype (Residue v)]
    (χv : MulChar (Residue v) ℂ) (χ : MulChar (Residue p) ℂ) (hχ : χ ≠ 1)
    (hlift : ∀ x : A, χv (Ideal.Quotient.mk _ x) = χ (Ideal.Quotient.mk _ x)) :
    (∑ y : Residue v, χv y) = 0 := by
  let π : Residue v →+* Residue p :=
    Ideal.Quotient.factor (Ideal.span_singleton_le_span_singleton.mpr hpv)
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have he (y : Residue v) : χv y = χ (π y) := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    exact hlift y
  simp_rw [he]
  rw [sum_reduction π hπ χ, MulChar.sum_eq_zero_of_ne_one hχ, mul_zero]

theorem fullCorrelation_divisor_eq_zero (p v t k : A) (hv : v ≠ 0)
    (hpv : p ∣ v) (hpt : p ∣ t)
    [Fintype (Residue p)] [Fintype (Residue (v * t))] [Fintype (Residue v)]
    (χu : MulChar (Residue (v * t)) ℂ) (χv : MulChar (Residue v) ℂ)
    (ψu ψv : MulChar (Residue p) ℂ) (hψv : ψv ≠ 1)
    (hu : ∀ x : A, χu (Ideal.Quotient.mk _ x) = ψu (Ideal.Quotient.mk _ x))
    (hv' : ∀ x : A, χv (Ideal.Quotient.mk _ x) = ψv (Ideal.Quotient.mk _ x)) :
    fullModulusCorrelation (v * t) v χu χv (v * k) = 0 := by
  rw [fullCorrelation_divisor_constant v t k hv χu χv
    (divisor_lift_constant p v t k hpt χu ψu hu),
    lifted_character_sum_zero p v hpv χv ψv hψv hv', star_zero, mul_zero]

end Domain
section Eisenstein
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation CenteredMomentCanonical CompletedGauss
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem supported_power (p : O) (hp : Supported (Ideal.span {p})) (i : ℕ) :
    Supported (Ideal.span {p ^ i}) := by
  rw [← Ideal.span_singleton_pow]
  exact supported_pow hp i

theorem supported_power_character_mk (p : O) [ (Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {i : ℕ} (hi : 1 ≤ i) (x : O) :
    supportedModulusCharacter (p ^ i) (supported_power p hp i) (Ideal.Quotient.mk _ x) =
      (actualSextic (Ideal.span {p}) hg ^ i) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem supported_product_power_character_mk (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (x : O) :
    supportedModulusCharacter (p ^ j * p ^ d)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (Ideal.Quotient.mk _ x) =
      (actualSextic (Ideal.span {p}) hg ^ (j + d)) (Ideal.Quotient.mk _ x) := by
  rw [supportedModulusCharacter_mk, ← pow_add, ← Ideal.span_singleton_pow, map_pow,
    idealRowHom_prime x (Ideal.span {p}) hg, MulChar.pow_apply' _ (by omega)]

theorem unequal_prime_power_zero_of_not_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (hj6 : ¬ 6 ∣ j) (k : O) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) = 0 := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finite_quotient_span (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have hχ : actualSextic (Ideal.span {p}) hg ^ j ≠ 1 := by
    intro h
    apply hj6
    rw [← actualSextic_order_six (Ideal.span {p}) hg hchar]
    exact orderOf_dvd_of_pow_eq_one h
  exact fullCorrelation_divisor_eq_zero p (p ^ j) (p ^ d) k (pow_ne_zero j hp0)
    (dvd_pow_self p (by omega)) (dvd_pow_self p (by omega))
    (supportedModulusCharacter _ _ ) (supportedModulusCharacter _ _)
    (actualSextic (Ideal.span {p}) hg ^ (j + d)) (actualSextic (Ideal.span {p}) hg ^ j)
    hχ (supported_product_power_character_mk p hp hg hj)
    (supported_power_character_mk p hp hg hj)

theorem unequal_prime_power_factor (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) =
      (actualSextic (Ideal.span {p}) hg ^ (j + d)) (Ideal.Quotient.mk _ k) *
        star (∑' y : Residue (p ^ j), supportedModulusCharacter (p ^ j)
          (supported_power p hp j) y) := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finite_quotient_span (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have h := fullCorrelation_divisor_constant (p ^ j) (p ^ d) k (pow_ne_zero j hp0)
    (supportedModulusCharacter _ (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d)))
    (supportedModulusCharacter _ (supported_power p hp j))
    (divisor_lift_constant p (p ^ j) (p ^ d) k (dvd_pow_self p (by omega))
      _ (actualSextic (Ideal.span {p}) hg ^ (j + d))
      (supported_product_power_character_mk p hp hg hj))
  rw [supported_product_power_character_mk p hp hg hj k] at h
  simpa only [actualCorrelation, supportedCorrelation, tsum_fintype] using h

theorem unequal_prime_power_zero_of_nonunit (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) (hk : p ∣ k) :
    actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k) = 0 := by
  rw [unequal_prime_power_factor p hp hg hj hd k]
  have hk0 : Ideal.Quotient.mk (Ideal.span {p}) k = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hk)
  rw [hk0, MulChar.map_zero, zero_mul]

theorem unequal_prime_power_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (k : O) :
    ‖actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) (p ^ j * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ j := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  rw [unequal_prime_power_factor p hp hg hj hd k, norm_mul, norm_star, tsum_fintype]
  calc
    _ ≤ ‖∑ y : Residue (p ^ j), supportedModulusCharacter (p ^ j)
        (supported_power p hp j) y‖ := mul_le_of_le_one_left (norm_nonneg _)
      (QuadraticInitialBound.norm_finite_character_le_one _ _)
    _ ≤ ∑ y : Residue (p ^ j), ‖supportedModulusCharacter (p ^ j)
        (supported_power p hp j) y‖ := norm_sum_le _ _
    _ ≤ ∑ _y : Residue (p ^ j), (1 : ℝ) := Finset.sum_le_sum
      (fun y _ => QuadraticInitialBound.norm_finite_character_le_one _ _)
    _ = _ := by
      rw [← Nat.cast_pow, ← map_pow Ideal.absNorm,
        Ideal.span_singleton_pow]
      simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem unequal_prime_power_support (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {j d : ℕ} (hj : 1 ≤ j) (hd : 1 ≤ d) (h : O)
    (hne : actualCorrelation (p ^ j * p ^ d) (p ^ j)
      (supported_mul_elements _ _ (supported_power p hp j) (supported_power p hp d))
      (supported_power p hp j) h ≠ 0) :
    ∃ k : O, h = p ^ j * k ∧ 6 ∣ j ∧ ¬ p ∣ k := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span (pow_ne_zero j hp0)
  let : Fintype (Residue (p ^ j)) := Fintype.ofFinite _
  let := finite_quotient_span (mul_ne_zero (pow_ne_zero j hp0) (pow_ne_zero d hp0))
  let : Fintype (Residue (p ^ j * p ^ d)) := Fintype.ofFinite _
  have hdiv : p ^ j ∣ h := by
    by_contra hn
    exact hne (fullModulusCorrelation_eq_zero_of_common_not_dvd _ _ (p ^ j) h
      (supportedModulusCharacter _ _) (supportedModulusCharacter _ _)
      (dvd_mul_right _ _) dvd_rfl hn)
  obtain ⟨k, rfl⟩ := hdiv
  refine ⟨k, rfl, ?_, ?_⟩
  · by_contra hj6
    exact hne (unequal_prime_power_zero_of_not_six p hp hg hchar hj hd hj6 k)
  · intro hk
    exact hne (unequal_prime_power_zero_of_nonunit p hp hg hj hd k hk)

end Eisenstein

end SevenEighths.CenteredMomentUnequal

end

end OAI
end OAIOriginalModule1631

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Amplification
Source SHA256: 1246e38a3c1fbb39bada8a0517d55ac0fc785f7d927b81a434b0c45815fe1244
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1632





namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplification
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentUnequal
local notation "O" => ActualEisensteinCubic.O

theorem gauss_prime_power_one (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) 1 =
      if n = 0 then primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg]
  have ht := actualSextic_primePowerGauss_at_pow p hp hg hc (n+1) n 0
  simp only [pow_zero] at ht
  rw [ht]
  by_cases hn : n = 0
  · subst n
    norm_num
  · have hn0 : ¬0 = n := Ne.symm hn
    have hpos : ¬n ≤ 0 := by omega
    simp only [ite_eq_right hn,ite_eq_right hn0,ite_eq_right hpos,show ¬n+1 ≤ 0 by omega,ite_false,sub_self]
    split_ifs <;> rfl

theorem gauss_prime_power_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (p^6) =
      if n = 5 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^5 *
        ((Ideal.absNorm (Ideal.span {p}) : ℂ)-1)
      else if n = 6 then (Ideal.absNorm (Ideal.span {p}) : ℂ)^6 *
        primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 else 0 := by
  rw [sexticGauss_prime_power p hp hg,actualSextic_primePowerGauss_at_pow p hp hg hc]
  have h6 : actualSextic (Ideal.span {p}) hg ^ 6 = 1 :=
    (actualSextic_pow_eq_one_iff _ hg hc 6).mpr dvd_rfl
  by_cases hn5 : n = 5
  · subst n
    norm_num
    ring
  · by_cases hn6 : n = 6
    · subst n
      simp only [hn5,show ¬6 ∣ 6+1 by decide,ite_false,ite_true,
        pow_succ (actualSextic (Ideal.span {p}) hg) 6,h6,one_mul]
    · rw [ite_eq_right hn5,ite_eq_right hn6]
      by_cases hd : 6 ∣ n+1
      · have hlarge : 6 < n := by omega
        simp only [hd,ite_true,show ¬n+1 ≤ 6 by omega,ite_false,
          show ¬n ≤ 6 by omega,sub_self]
      · simp only [hd,ite_false,show ¬6=n from Ne.symm hn6]

theorem gauss_prime_power_unchanged (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn0 : n ≠ 0) (hn5 : n ≠ 5) (hn6 : n ≠ 6) (h : O) (hph : ¬p ∣ h) :
    sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) (h*p^6) =
      sexticGauss (p^(n+1)) (pow_ne_zero _ hp.ne_zero) h := by
  have hcop : IsCoprime h (p^(n+1)) :=
    (hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right
  have hsp := supported_power p hs (n+1)
  rw [sexticGauss_unit_scale _ hsp h (p^6) hcop,
    ← mul_one h, sexticGauss_unit_scale _ hsp h 1 hcop,
    gauss_prime_power_six p hp hg hc,gauss_prime_power_one p hp hg hc]
  simp only [hn0,hn5,hn6,ite_false,mul_zero]

theorem gauss_sixth_frequency (a : O) (ha : Supported (Ideal.span {a}))
    (p h : O) (hcop : IsCoprime p a) :
    sexticGauss a (supportedElement_ne_zero a ha) (p^6*h) =
      sexticGauss a (supportedElement_ne_zero a ha) h := by
  rw [sexticGauss_unit_scale a ha (p^6) h hcop.pow_left,
    supported_sixth_value a p ha hcop.symm,inv_one,one_mul]

theorem twelfth_power_mask (p : O) (hs : Supported (Ideal.span {p})) (u : O) :
    idealRowHom u (Ideal.span {p}) ^ 12 = coprimalityMask u p := by
  rw [show 12=6*2 by decide,pow_mul,← idealRowHom_argument_pow u 6 _ hs,
    idealRowHom_sixth_eq_mask u p hs]
  change (if IsCoprime u p then (1 : ℂ) else 0)^2 = if IsCoprime u p then 1 else 0
  split_ifs <;> norm_num

end SevenEighths.CenteredMomentAmplification

end

end OAI
end OAIOriginalModule1632

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationLocal
Source SHA256: 6788aa02350ace40c4f6d4ae3cfc450bc6f2c4902f9ffb63ae4a1c0c8defb36e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1633


namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationLocal
open ActualEisensteinCubic CompletedGauss ConcreteTraceCRT CanonicalRowCompletion
open CanonicalQuadraticSieve ConcretePrimeRowBridge ProbePrimePower ProbePhysical
open CenteredMomentUnequal CenteredMomentAmplification CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

def centralLocal (p : O) (hp : p ≠ 0) (n : ℕ) (h : O) : ℂ :=
  sexticGauss (p^(n+1)) (pow_ne_zero _ hp) h / (Ideal.absNorm (Ideal.span {p}) : ℂ)^(n+1)

theorem gauss_unit_scale_norm (a : O) (ha : Supported (Ideal.span {a}))
    (b h : O) (hcop : IsCoprime b a) :
    ‖sexticGauss a (supportedElement_ne_zero a ha) (b*h)‖ =
      ‖sexticGauss a (supportedElement_ne_zero a ha) h‖ := by
  let := finite_quotient_span (supportedElement_ne_zero a ha)
  let : Fintype (O ⧸ Ideal.span {a}) := Fintype.ofFinite _
  obtain ⟨u,hu⟩ := CenteredMomentCommonSupport.isUnit_residue_of_coprime a b hcop.symm
  have hn : ‖idealRowHom b (Ideal.span {a})‖ = 1 := by
    change ‖supportedModulusCharacter a ha (Ideal.Quotient.mk _ b)‖ = 1
    rw [← hu]
    exact FiniteRayExpansion.norm_char_unit _ u
  rw [sexticGauss_unit_scale a ha b h hcop,norm_mul,norm_inv,hn,inv_one,one_mul]

theorem primeGauss_actual_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    ‖primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1‖^2 =
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
  let : Field (O ⧸ Ideal.span {p}) := Ideal.Quotient.field _
  let : Finite (O ⧸ Ideal.span {p}) := finite_quotient_span hp.ne_zero
  let : Fintype (O ⧸ Ideal.span {p}) := Fintype.ofFinite _
  have hχ : actualSextic (Ideal.span {p}) hg ≠ 1 := by
    intro he
    have ho := CenteredMomentCanonical.actualSextic_order_six (Ideal.span {p}) hg hc
    rw [he,orderOf_one] at ho
    norm_num at ho
  have ht : (CubicEisenstein.quotientTrace p hp.ne_zero).IsPrimitive :=
    GeneralPrimitiveTrace.eisTraceModChar_breveE_primitive p hp.ne_zero
  have he : primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 =
      gaussSum (actualSextic (Ideal.span {p}) hg) (CubicEisenstein.quotientTrace p hp.ne_zero) := by
    simp [primeGauss,tsum_fintype,gaussSum]
  rw [he,FiniteFieldSieve.primitive_gauss_norm_sq _ _ hχ ht]
  norm_cast
  rw [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]

theorem centralLocal_six (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 5 (p^6) = 1 - (Ideal.absNorm (Ideal.span {p}) : ℂ)⁻¹ := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_seven (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hg : goodLambda ∉ Ideal.span {p}) (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) :
    centralLocal p hp.ne_zero 6 (p^6) =
      primeGauss p hp.ne_zero (actualSextic (Ideal.span {p}) hg) 1 /
        (Ideal.absNorm (Ideal.span {p}) : ℂ) := by
  rw [centralLocal,gauss_prime_power_six p hp hg hc]
  simp only [show ¬(6:ℕ)=5 by decide,ite_false,ite_true]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr hp.ne_zero))
  field_simp
  ring

theorem centralLocal_unit_norm (p : O) (hp : Prime p) (hs : Supported (Ideal.span {p}))
    (n : ℕ) (h k : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero n (h*k)‖ = ‖centralLocal p hp.ne_zero n k‖ := by
  unfold centralLocal
  rw [norm_div,norm_div,gauss_unit_scale_norm _ (supported_power p hs (n+1)) h k
    ((hp.irreducible.coprime_iff_not_dvd.mpr hph).symm.pow_right)]

theorem centralLocal_one_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 0 h‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [← mul_one h,centralLocal_unit_norm p hp hs 0 h 1 hph,centralLocal,
    gauss_prime_power_one p hp hg hc]
  simp only [ite_true,zero_add,pow_one,norm_div,Complex.norm_natCast,div_pow,
    primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_seven_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 6 (h*p^6)‖^2 = (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹ := by
  rw [centralLocal_unit_norm p hp hs 6 h (p^6) hph,centralLocal_seven p hp hg hc,
    norm_div,Complex.norm_natCast,div_pow,primeGauss_actual_norm_sq p hp hg hc]
  have hn : (Ideal.absNorm (Ideal.span {p}) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr hs.1)
  field_simp

theorem centralLocal_six_norm_sq (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    ‖centralLocal p hp.ne_zero 5 (h*p^6)‖^2 =
      (1 - (Ideal.absNorm (Ideal.span {p}) : ℝ)⁻¹)^2 := by
  rw [centralLocal_unit_norm p hp hs 5 h (p^6) hph,centralLocal_six p hp hg hc]
  rw [← Complex.ofReal_natCast,← Complex.ofReal_inv,← Complex.ofReal_one,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs,sq_abs]

end SevenEighths.CenteredMomentAmplificationLocal

end

end OAI
end OAIOriginalModule1633

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationGlobal
Source SHA256: f91dac31155eadad18f47ab01509cb5ce4887290c2191a7d8858c3e12b8d7b81
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1634




namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationGlobal
open CanonicalQuadraticSieve CanonicalRowCompletion ConcretePrimeRowBridge
open CenteredMomentSupportedCorrelation CenteredMomentUnequal CenteredMomentGaussEnergy
open CenteredMomentAmplification ProbePhysical
local notation "O" => ActualEisensteinCubic.O

theorem full_column_unchanged (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (n : ℕ)
    (hn1 : n ≠ 1) (hn6 : n ≠ 6) (hn7 : n ≠ 7)
    (a : O) (ha : Supported (Ideal.span {a})) (hcop : IsCoprime p a)
    (h : O) (hph : ¬p ∣ h) :
    sexticGauss (p^n*a) (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_element_ne_zero a ha))
      (p^6*h) =
    sexticGauss (p^n*a) (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (supported_element_ne_zero a ha)) h := by
  cases n with
  | zero =>
    simp only [pow_zero,one_mul]
    exact gauss_sixth_frequency a ha p h hcop
  | succ n =>
    rw [sexticGauss_coprime_product _ a (supported_power p hs (n+1)) ha hcop.pow_left,
      sexticGauss_coprime_product _ a (supported_power p hs (n+1)) ha hcop.pow_left,
      gauss_sixth_frequency a ha p h hcop,
      mul_comm (p^6) h,gauss_prime_power_unchanged p hp hs hg hc n
        (by omega) (by omega) (by omega) h hph]

def amplificationError {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (ν : α → ℕ) (p : O) (k : ℕ) (h : O) : ℂ :=
  ∑ i ∈ S, if ν i = k then c i *
    (gaussRow (a i) (ha i) h - gaussRow (a i) (ha i) (p^6*h)) else 0

theorem polynomial_amplification {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ν : α → ℕ) (r : α → O) (hr : ∀ i, Supported (Ideal.span {r i}))
    (hfactor : ∀ i ∈ S, a i = p^(ν i)*r i)
    (hcop : ∀ i ∈ S, IsCoprime p (r i)) (h : O) (hph : ¬p ∣ h) :
    gaussPolynomial S a ha c h = gaussPolynomial S a ha c (p^6*h) +
      amplificationError S a ha c ν p 1 h + amplificationError S a ha c ν p 6 h +
      amplificationError S a ha c ν p 7 h := by
  simp only [gaussPolynomial,amplificationError,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases h1 : ν i = 1
  · simp only [h1,ite_true,show ¬(1:ℕ)=6 by decide,show ¬(1:ℕ)=7 by decide,ite_false]
    ring
  · by_cases h6 : ν i = 6
    · simp only [h6,ite_true,show ¬(6:ℕ)=1 by decide,show ¬(6:ℕ)=7 by decide,ite_false]
      ring
    · by_cases h7 : ν i = 7
      · simp only [h7,ite_true,show ¬(7:ℕ)=1 by decide,show ¬(7:ℕ)=6 by decide,ite_false]
        ring
      · simp only [h1,h6,h7,ite_false,add_zero]
        congr 1
        unfold gaussRow
        congr 1
        have he := full_column_unchanged p hp hs hg hc (ν i) h1 h6 h7
          (r i) (hr i) (hcop i hi) h hph
        simpa only [hfactor i hi] using he.symm

def primeRemainder (p : O) (hp : Prime p) (a : O) (ha : a ≠ 0) : O :=
  Classical.choose ((FiniteMultiplicity.of_prime_left hp ha).exists_eq_pow_mul_and_not_dvd)

theorem primeRemainder_spec (p : O) (hp : Prime p) (a : O) (ha : a ≠ 0) :
    a = p^(multiplicity p a)*primeRemainder p hp a ha ∧ ¬p ∣ primeRemainder p hp a ha :=
  Classical.choose_spec ((FiniteMultiplicity.of_prime_left hp ha).exists_eq_pow_mul_and_not_dvd)

theorem primeRemainder_supported (p : O) (hp : Prime p) (a : O)
    (ha : Supported (Ideal.span {a})) :
    Supported (Ideal.span {primeRemainder p hp a (supported_element_ne_zero a ha)}) := by
  have hs := ha
  rw [(primeRemainder_spec p hp a (supported_element_ne_zero a ha)).1,
    ← Ideal.span_singleton_mul_span_singleton,supported_mul_iff] at hs
  exact hs.2

theorem polynomial_amplification_actual {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2) (h : O) (hph : ¬p ∣ h) :
    gaussPolynomial S a ha c h = gaussPolynomial S a ha c (p^6*h) +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h +
      amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h := by
  apply polynomial_amplification S a ha c p hp hs hg hc _
    (fun i => primeRemainder p hp (a i) (supported_element_ne_zero _ (ha i)))
    (fun i => primeRemainder_supported p hp (a i) (ha i))
  · exact fun i _ => (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).1
  · exact fun i _ => hp.irreducible.coprime_iff_not_dvd.mpr
      (primeRemainder_spec p hp (a i) (supported_element_ne_zero _ (ha i))).2
  · exact hph

theorem norm_four_sum_sq (a b c d : ℂ) :
    ‖a+b+c+d‖^2 ≤ 4*(‖a‖^2+‖b‖^2+‖c‖^2+‖d‖^2) := by
  have hn : ‖a+b+c+d‖ ≤ ‖a‖+‖b‖+‖c‖+‖d‖ := by
    calc
      _ ≤ ‖a+b+c‖ + ‖d‖ := norm_add_le _ _
      _ ≤ (‖a+b‖+‖c‖)+‖d‖ := add_le_add (norm_add_le _ _) le_rfl
      _ ≤ _ := add_le_add (add_le_add (norm_add_le a b) le_rfl) le_rfl
  have hs := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  nlinarith [sq_nonneg (‖a‖-‖b‖),sq_nonneg (‖a‖-‖c‖),sq_nonneg (‖a‖-‖d‖),
    sq_nonneg (‖b‖-‖c‖),sq_nonneg (‖b‖-‖d‖),sq_nonneg (‖c‖-‖d‖)]

theorem polynomial_amplification_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (p : O) (hp : Prime p) [(Ideal.span {p}).IsMaximal]
    (hs : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hc : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (ν : α → ℕ) (r : α → O) (hr : ∀ i, Supported (Ideal.span {r i}))
    (hfactor : ∀ i ∈ S, a i = p^(ν i)*r i)
    (hcop : ∀ i ∈ S, IsCoprime p (r i)) (h : O) (hph : ¬p ∣ h) :
    ‖gaussPolynomial S a ha c h‖^2 ≤ 4*(‖gaussPolynomial S a ha c (p^6*h)‖^2 +
      ‖amplificationError S a ha c ν p 1 h‖^2 +
      ‖amplificationError S a ha c ν p 6 h‖^2 +
      ‖amplificationError S a ha c ν p 7 h‖^2) := by
  rw [polynomial_amplification S a ha c p hp hs hg hc ν r hr hfactor hcop h hph]
  exact norm_four_sum_sq _ _ _ _

theorem eligible_pool_average {β : Type*} (P : Finset β) (hP : P.Nonempty)
    (H : ℂ) (A E₁ E₆ E₇ : β → ℂ)
    (hid : ∀ p ∈ P, H = A p + E₁ p + E₆ p + E₇ p) :
    ‖H‖^2 ≤ (4 / (P.card : ℝ)) *
      ∑ p ∈ P, (‖A p‖^2 + ‖E₁ p‖^2 + ‖E₆ p‖^2 + ‖E₇ p‖^2) := by
  have hc : (0 : ℝ) < P.card := Nat.cast_pos.mpr hP.card_pos
  have hb : (P.card : ℝ)*‖H‖^2 ≤ 4 *
      ∑ p ∈ P, (‖A p‖^2 + ‖E₁ p‖^2 + ‖E₆ p‖^2 + ‖E₇ p‖^2) := by
    have hb := Finset.sum_le_sum (s := P) (fun p hp => show ‖H‖^2 ≤
      4*(‖A p‖^2+‖E₁ p‖^2+‖E₆ p‖^2+‖E₇ p‖^2) by
        rw [hid p hp]
        exact norm_four_sum_sq _ _ _ _)
    simpa only [Finset.sum_const,nsmul_eq_mul,← Finset.mul_sum] using hb
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hc).mpr
  convert hb using 1 ; ring

theorem polynomial_pool_bound {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (P : Finset O) (hP : P.Nonempty) (hp : ∀ p ∈ P, Prime p)
    (hs : ∀ p ∈ P, Supported (Ideal.span {p}))
    (hgood : ∀ p ∈ P, goodLambda ∉ Ideal.span {p})
    (hc : ∀ p ∈ P, ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (h : O) (hph : ∀ p ∈ P, ¬p ∣ h) :
    ‖gaussPolynomial S a ha c h‖^2 ≤ (4 / (P.card : ℝ)) *
      ∑ p ∈ P, (‖gaussPolynomial S a ha c (p^6*h)‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 1 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 6 h‖^2 +
        ‖amplificationError S a ha c (fun i => multiplicity p (a i)) p 7 h‖^2) := by
  apply eligible_pool_average P hP
  intro p hpP
  let : (Ideal.span {p}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible (hp p hpP).irreducible
  exact polynomial_amplification_actual S a ha c p (hp p hpP) (hs p hpP)
    (hgood p hpP) (hc p hpP) h (hph p hpP)

end SevenEighths.CenteredMomentAmplificationGlobal

end

end OAI
end OAIOriginalModule1634

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AmplificationCount
Source SHA256: fa60d70ffaa73aa7e43bd0e43e4a7d86d437a1bab9f4dc2c0d8dedabc79ef9c2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1635



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentAmplificationCount
open UniqueFactorizationMonoid CenteredExceptionalCount
local notation "O" => ActualEisensteinCubic.O

theorem primeDivisors_product_dvd (S : Finset (Ideal O))
    (hP : ∀ P ∈ S, Prime P) (I : Ideal O) (hd : ∀ P ∈ S, P ∣ I) :
    (∏ P ∈ S, P) ∣ I := by
  apply Finset.prod_dvd_of_coprime _ hd
  intro P hPS Q hQS hPQ
  let : P.IsMaximal := (Ideal.isPrime_of_prime (hP P hPS)).isMaximal (hP P hPS).ne_zero
  let : Q.IsMaximal := (Ideal.isPrime_of_prime (hP Q hQS)).isMaximal (hP Q hQS).ne_zero
  exact Ideal.isCoprime_of_isMaximal hPQ

theorem large_prime_divisor_count (S : Finset (Ideal O)) (hP : ∀ P ∈ S, Prime P)
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ P ∈ S, P ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ P ∈ S, Z^ℓ ≤ (Ideal.absNorm P : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hpow : Z ^ (ℓ * (S.card : ℝ)) ≤ Z^B := by
    calc
      _ = (Z^ℓ)^S.card := Real.rpow_mul_natCast (zero_lt_one.trans hZ).le ℓ S.card
      _ = ∏ _P ∈ S, Z^ℓ := (Finset.prod_const _).symm
      _ ≤ ∏ P ∈ S, (Ideal.absNorm P : ℝ) := Finset.prod_le_prod₀
        (fun _ _ => Real.rpow_nonneg (zero_lt_one.trans hZ).le _) hlower
      _ = (Ideal.absNorm (∏ P ∈ S, P) : ℝ) := by simp only [map_prod,Nat.cast_prod]
      _ ≤ (Ideal.absNorm I : ℝ) := norm_le_of_dvd hI (primeDivisors_product_dvd S hP I hd)
      _ ≤ _ := hupper
  have he := (Real.rpow_le_rpow_left_iff hZ).mp hpow
  apply (le_div_iff₀ hℓ).mpr
  simpa only [mul_comm] using he

theorem indexed_large_prime_divisor_count {α : Type*} (S : Finset α) (P : α → Ideal O)
    (hinj : Set.InjOn P S) (hp : ∀ i ∈ S, Prime (P i))
    (I : Ideal O) (hI : I ≠ 0) (hd : ∀ i ∈ S, P i ∣ I)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ i ∈ S, Z^ℓ ≤ (Ideal.absNorm (P i) : ℝ))
    (hupper : (Ideal.absNorm I : ℝ) ≤ Z^B) : (S.card : ℝ) ≤ B/ℓ := by
  have hb := large_prime_divisor_count (S.image P) (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hp i hi) I hI (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hd i hi) Z ℓ B hZ hℓ (by
      intro Q hQ
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hQ
      exact hlower i hi) hupper
  simpa only [Finset.card_image_of_injOn hinj] using hb

theorem amplified_row_fiber_count (F : Finset (O × O)) (y : O) (hy : y ≠ 0)
    (hprime : ∀ x ∈ F, Prime x.2)
    (hprimary : ∀ x ∈ F, ConcretePrimeRowBridge.goodLambda^2 ∣ x.2-1)
    (hrow : ∀ x ∈ F, x.2^6*x.1 = y)
    (Z ℓ B : ℝ) (hZ : 1 < Z) (hℓ : 0 < ℓ)
    (hlower : ∀ x ∈ F, Z^ℓ ≤ (Ideal.absNorm (Ideal.span {x.2}) : ℝ))
    (hupper : (Ideal.absNorm (Ideal.span {y}) : ℝ) ≤ Z^B) : (F.card : ℝ) ≤ B/ℓ := by
  apply indexed_large_prime_divisor_count F (fun x => Ideal.span {x.2}) ?_
    (fun x hx => CubicEisenstein.gaussPrimeIdeal_prime x.2 (hprime x hx))
    (Ideal.span {y}) (Ideal.span_singleton_eq_bot.not.mpr hy) ?_ Z ℓ B hZ hℓ hlower hupper
  · intro x hx z hz heq
    have hp : x.2 = z.2 := by
      rw [← CompletedGauss.primaryGenerator_span x.2 (hprime x hx).ne_zero (hprimary x hx),
        ← CompletedGauss.primaryGenerator_span z.2 (hprime z hz).ne_zero (hprimary z hz)]
      exact congrArg CompletedGauss.primaryGenerator heq
    have hh : x.1 = z.1 := by
      apply mul_left_cancel₀ (pow_ne_zero 6 (hprime x hx).ne_zero)
      rw [hrow x hx,hp,hrow z hz]
    exact Prod.ext hh hp
  · intro x hx
    rw [Ideal.dvd_iff_le,Ideal.span_singleton_le_span_singleton,← hrow x hx]
    exact (dvd_pow_self x.2 (by decide : 6 ≠ 0)).trans (dvd_mul_right _ _)

theorem positive_pushforward_bound {α β : Type*} [DecidableEq β]
    (S : Finset α) (f : α → β) (g : β → ℝ) (C : ℝ)
    (hg : ∀ y ∈ S.image f, 0 ≤ g y)
    (hf : ∀ y ∈ S.image f, ((S.filter (fun x => f x = y)).card : ℝ) ≤ C) :
    (∑ x ∈ S, g (f x)) ≤ C * ∑ y ∈ S.image f, g y := by
  rw [← Finset.sum_fiberwise_of_maps_to (fun x hx => Finset.mem_image_of_mem f hx)]
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro y hy
  calc
    _ = ((S.filter (fun x => f x = y)).card : ℝ) * g y := by
      rw [← nsmul_eq_mul,← Finset.sum_const]
      apply Finset.sum_congr rfl
      intro x hx
      rw [(Finset.mem_filter.mp hx).2]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hf y hy) (hg y hy)

end SevenEighths.CenteredMomentAmplificationCount

end

end OAI
end OAIOriginalModule1635

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Local
Source SHA256: 308ebaddf5c1f81274c355cf2fa0a0cf7c1f2d9898429c060df21984dcedb966
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1636


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentLocal
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentUnequal

section Domain
variable {A : Type*} [CommRing A] [IsDomain A]

omit [IsDomain A] in
theorem scaledResidue_one (q : A) (x : Residue q) :
    scaledResidue q 1 q (mul_one q).symm x = x := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [scaledResidue_mk, one_mul]

theorem fullCorrelation_equal_divided (q k : A) (hq : q ≠ 0)
    [Fintype (Residue q)] (χ : MulChar (Residue q) ℂ) :
    fullModulusCorrelation q q χ χ (q * k) =
      fullCorrelation (fun x : Residue q => x) (fun y : Residue q => y) χ χ
        (Ideal.Quotient.mk _ k) := by
  have hs (x y : Residue q) :
      scaledResidue q q (q * q) rfl x - scaledResidue q q (q * q) (mul_comm _ _) y =
        Ideal.Quotient.mk _ (q * k) ↔ x - y = Ideal.Quotient.mk _ k := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [scaledResidue_congruence, ← map_sub, Ideal.Quotient.eq, Ideal.mem_span_singleton]
    rw [show q * x - q * y - q * k = q * (x - y - k) by ring]
    exact mul_dvd_mul_iff_left hq
  unfold fullModulusCorrelation fullCorrelation
  simp_rw [hs]

end Domain

open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation CenteredMomentCanonical CompletedGauss
open CenteredMomentFourier
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem powerReduction_multiplicity (p : O) (_hp : p ≠ 0) {i : ℕ} (hi : 1 ≤ i)
    [Fintype (Residue p)] [Fintype (Residue (p ^ i))] :
    reductionMultiplicity (frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))) =
      Ideal.absNorm (Ideal.span {p}) ^ (i - 1) := by
  have hcard (a : O) [Fintype (Residue a)] :
      Fintype.card (Residue a) = Ideal.absNorm (Ideal.span {a}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  apply reductionMultiplicity_eq_pow _ (Ideal.Quotient.factor_surjective _) (c := i)
  · rw [← hcard p]
    exact Fintype.card_pos
  · exact hi
  · rw [hcard, ← Ideal.span_singleton_pow, map_pow]
  · exact hcard p

theorem equal_prime_power_formula (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (k : O) :
    actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k) =
      (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) *
        (if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
         else if 6 ∣ i then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1) := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  let := finite_quotient_span (pow_ne_zero i hp0)
  let : Fintype (Residue (p ^ i)) := Fintype.ofFinite _
  let : Field (Residue p) := Ideal.Quotient.field (Ideal.span {p})
  let π := frequencyReduction p (p ^ i) (dvd_pow_self p (by omega))
  let χ := actualSextic (Ideal.span {p}) hg ^ i
  have hπ : Function.Surjective π := Ideal.Quotient.factor_surjective _
  have hχ (x : Residue (p ^ i)) :
      supportedModulusCharacter (p ^ i) (supported_power p hp i) x = χ (π x) := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact supported_power_character_mk p hp hg hi x
  have hred := fullCorrelation_reduction_unit_right π hπ
    (1 : (Residue (p ^ i))ˣ) 1 (Ideal.Quotient.mk _ k) χ χ
  simp only [Units.val_one, map_one, one_mul] at hred
  have hpow : χ = 1 ↔ 6 ∣ i := by
    dsimp only [χ]
    rw [← orderOf_dvd_iff_pow_eq_one, actualSextic_order_six (Ideal.span {p}) hg hchar]
  have hk : Ideal.Quotient.mk (Ideal.span {p}) k = 0 ↔ p ∣ k := by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  have hcard : Fintype.card (Residue p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  change fullModulusCorrelation _ _ _ _ _ = _
  rw [fullCorrelation_equal_divided _ _ (pow_ne_zero i hp0)]
  have hχfun : (supportedModulusCharacter (p ^ i) (supported_power p hp i) :
      Residue (p ^ i) → ℂ) = (fun x => χ (π x)) := funext hχ
  rw [hχfun, hred]
  have he : fullCorrelation (fun x : Residue p => x) (fun x => x) χ χ
      (π (Ideal.Quotient.mk _ k)) = localCorrelation χ 1 1 (Ideal.Quotient.mk _ k) := by
    simp only [localCorrelation, one_mul, π, frequencyReduction_mk]
  rw [he]
  rw [localCorrelation_units χ one_ne_zero one_ne_zero, div_self one_ne_zero, map_one, one_mul,
    hk, hpow, hcard]
  have hm : (reductionMultiplicity π : ℂ) = (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ (i - 1) := by
    rw [powerReduction_multiplicity p hp0 hi, Nat.cast_pow]
  rw [hm]
  split_ifs <;> rfl

theorem equal_prime_power_unit_norm (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (hi6 : ¬ 6 ∣ i) (k : O) (hk : ¬ p ∣ k) :
    ‖actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k)‖ = (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) := by
  rw [equal_prime_power_formula p hp hg hchar hi k, ite_eq_right hk, ite_eq_right hi6]
  simp

theorem equal_prime_power_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {i : ℕ} (hi : 1 ≤ i) (k : O) :
    ‖actualCorrelation (p ^ i) (p ^ i) (supported_power p hp i) (supported_power p hp i)
      (p ^ i * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ i := by
  have hp0 := supported_element_ne_zero p hp
  let := finite_quotient_span hp0
  let : Fintype (Residue p) := Fintype.ofFinite _
  have hcard : Fintype.card (Residue p) = Ideal.absNorm (Ideal.span {p}) := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hN : (2 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) := by
    exact_mod_cast (show 2 ≤ Ideal.absNorm (Ideal.span {p}) from by
      rw [← hcard]
      exact Fintype.one_lt_card)
  have hsub (a : ℝ) (ha : 0 ≤ a) (haN : a ≤ Ideal.absNorm (Ideal.span {p})) :
      ‖(Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    have he : (Ideal.absNorm (Ideal.span {p}) : ℂ) - (a : ℂ) =
        ((Ideal.absNorm (Ideal.span {p}) : ℝ) - a : ℝ) := by push_cast; rfl
    rw [he, Complex.norm_real, Real.norm_of_nonneg (sub_nonneg.mpr haN)]
    linarith
  rw [equal_prime_power_formula p hp hg hchar hi k, norm_mul, norm_pow]
  have hnorm : ‖(Ideal.absNorm (Ideal.span {p}) : ℂ)‖ = (Ideal.absNorm (Ideal.span {p}) : ℝ) := by simp
  rw [hnorm]
  have hb : ‖(if p ∣ k then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 1
      else if 6 ∣ i then (Ideal.absNorm (Ideal.span {p}) : ℂ) - 2 else -1)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) := by
    split_ifs
    · simpa using hsub 1 (by norm_num) (by linarith)
    · simpa using hsub 2 (by norm_num) hN
    · simpa using (show (1 : ℝ) ≤ Ideal.absNorm (Ideal.span {p}) by linarith)
  calc
    _ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (i - 1) * Ideal.absNorm (Ideal.span {p}) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by rw [← pow_succ, Nat.sub_add_cancel hi]

end SevenEighths.CenteredMomentLocal

end

end OAI
end OAIOriginalModule1636

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeterogeneousCRT
Source SHA256: cae82a0d109d3536368f186e0cd8be50688e9caf24e30fa39fb9f08f73417350
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1637


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentHeterogeneousCRT
open CenteredMomentCorrelation

theorem fullCorrelation_heterogeneous_pi {ι : Type*} [Fintype ι]
    {X Y R : ι → Type*} [∀ i, Fintype (X i)] [∀ i, Fintype (Y i)]
    [∀ i, CommRing (R i)]
    (left : ∀ i, X i → R i) (right : ∀ i, Y i → R i)
    (f : ∀ i, X i → ℂ) (g : ∀ i, Y i → ℂ) (k : ∀ i, R i) :
    fullCorrelation (fun (x : ∀ i, X i) i => left i (x i)) (fun (y : ∀ i, Y i) i => right i (y i))
        (fun x => ∏ i, f i (x i)) (fun y => ∏ i, g i (y i)) k =
      ∏ i, fullCorrelation (left i) (right i) (f i) (g i) (k i) := by
  have hterm (x : ∀ i, X i) (y : ∀ i, Y i) :
      (if (fun i => left i (x i)) - (fun i => right i (y i)) = k
       then (∏ i, f i (x i)) * star (∏ i, g i (y i)) else 0) =
      ∏ i, if left i (x i) - right i (y i) = k i then f i (x i) * star (g i (y i)) else 0 := by
    by_cases h : ∀ i, left i (x i) - right i (y i) = k i
    · have he : (fun i => left i (x i)) - (fun i => right i (y i)) = k := funext h
      simp only [he, ite_true, h, star_prod, Finset.prod_mul_distrib]
    · obtain ⟨i, hi⟩ := not_forall.mp h
      have he : (fun i => left i (x i)) - (fun i => right i (y i)) ≠ k :=
        fun h => hi (congrFun h i)
      rw [ite_eq_right he]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [hi, ite_false]
  simp only [fullCorrelation]
  simp_rw [hterm]
  calc
    _ = ∑ x : ∀ i, X i, ∏ i, ∑ y : Y i,
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      exact (Fintype.prod_sum (fun i (y : Y i) =>
        if left i (x i) - right i y = k i then f i (x i) * star (g i y) else (0 : ℂ))).symm
    _ = _ := (Fintype.prod_sum (fun i (x : X i) => ∑ y : Y i,
      if left i x - right i y = k i then f i x * star (g i y) else (0 : ℂ))).symm

theorem fullCorrelation_three_equiv {ι X Y R : Type*} [Fintype ι]
    [Fintype X] [Fintype Y] [CommRing R]
    {Xi Yi Ri : ι → Type*} [∀ i, Fintype (Xi i)] [∀ i, Fintype (Yi i)]
    [∀ i, CommRing (Ri i)]
    (eX : X ≃ ∀ i, Xi i) (eY : Y ≃ ∀ i, Yi i) (eR : R ≃+* ∀ i, Ri i)
    (left : X → R) (right : Y → R)
    (li : ∀ i, Xi i → Ri i) (ri : ∀ i, Yi i → Ri i)
    (hl : ∀ x i, eR (left x) i = li i (eX x i))
    (hr : ∀ y i, eR (right y) i = ri i (eY y i))
    (f : ∀ i, Xi i → ℂ) (g : ∀ i, Yi i → ℂ) (k : R) :
    fullCorrelation left right (fun x => ∏ i, f i (eX x i))
      (fun y => ∏ i, g i (eY y i)) k =
      ∏ i, fullCorrelation (li i) (ri i) (f i) (g i) (eR k i) := by
  rw [← fullCorrelation_heterogeneous_pi li ri f g (eR k)]
  unfold fullCorrelation
  apply Fintype.sum_equiv eX
  intro x
  apply Fintype.sum_equiv eY
  intro y
  have he : left x - right y = k ↔
      (fun i => li i (eX x i)) - (fun i => ri i (eY y i)) = eR k := by
    rw [← eR.injective.eq_iff, map_sub]
    have hleft : eR (left x) = fun i => li i (eX x i) := funext (hl x)
    have hright : eR (right y) = fun i => ri i (eY y i) := funext (hr y)
    rw [hleft, hright]
  simp only [he]

end SevenEighths.CenteredMomentHeterogeneousCRT

end

end OAI
end OAIOriginalModule1637

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ProductCRT
Source SHA256: 03f97852e16226a3db08dbf6811ddc25a64c63cb537dd0ed22497e8fb9ab4786
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1638


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentProductCRT
open CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentHeterogeneousCRT
variable {A ι : Type*} [CommRing A] [Fintype ι] [DecidableEq ι]

def productCRT (a : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) :
    Residue (∏ i, a i) ≃+* ∀ i, Residue (a i) :=
  (Ideal.quotEquivOfEq (Ideal.prod_span_singleton Finset.univ a).symm).trans
    (IdealGaussCRT.quotientProdEquivPi (fun i => Ideal.span {a i}) hcop)

omit [DecidableEq ι] in
@[simp] theorem productCRT_mk (a : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (x : A) (i : ι) :
    productCRT a hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [productCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    IdealGaussCRT.quotientProdEquivPi_mk]

def jointCRT (a b : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) :
    Residue ((∏ i, a i) * ∏ i, b i) ≃+* ∀ i, Residue (a i * b i) :=
  (Ideal.quotEquivOfEq (congrArg (fun x : A => Ideal.span {x})
    (Finset.prod_mul_distrib (s := Finset.univ) (f := a) (g := b)).symm)).trans
      (productCRT (fun i => a i * b i) hcop)

omit [DecidableEq ι] in
@[simp] theorem jointCRT_mk (a b : ι → A)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (x : A) (i : ι) :
    jointCRT a b hcop (Ideal.Quotient.mk _ x) i = Ideal.Quotient.mk _ x := by
  simp only [jointCRT, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk, productCRT_mk]

def cofactor (a : ι → A) (i : ι) : A := ∏ j ∈ Finset.univ.erase i, a j

theorem factor_mul_cofactor (a : ι → A) (i : ι) : a i * cofactor a i = ∏ j, a j :=
  Finset.mul_prod_erase Finset.univ a (Finset.mem_univ i)

theorem left_crt_component (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (x : Residue (∏ i, a i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl x) i =
      scaledResidue (a i) (b i) (a i * b i) rfl
        (Ideal.Quotient.mk _ (cofactor b i) * productCRT a ha x i) := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor b i]
  ring

theorem right_crt_component (a b : ι → A)
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (y : Residue (∏ i, b i)) (i : ι) :
    jointCRT a b hab
      (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _) y) i =
      scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
        (Ideal.Quotient.mk _ (cofactor a i) * productCRT b hb y i) := by
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [scaledResidue_mk, jointCRT_mk, productCRT_mk, ← map_mul, scaledResidue_mk]
  congr 1
  rw [← factor_mul_cofactor a i]
  ring

theorem fullModulusCorrelation_product (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h =
      ∏ i, fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h) := by
  have hcrt := fullCorrelation_three_equiv (productCRT a ha).toEquiv (productCRT b hb).toEquiv
    (jointCRT a b hab)
    (scaledResidue (∏ i, a i) (∏ i, b i) ((∏ i, a i) * ∏ i, b i) rfl)
    (scaledResidue (∏ i, b i) (∏ i, a i) ((∏ i, a i) * ∏ i, b i) (mul_comm _ _))
    (fun i x => scaledResidue (a i) (b i) (a i * b i) rfl
      (Ideal.Quotient.mk _ (cofactor b i) * x))
    (fun i y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
      (Ideal.Quotient.mk _ (cofactor a i) * y))
    (left_crt_component a b ha hab) (right_crt_component a b hb hab)
    (fun i => χ i) (fun i => ψ i) (Ideal.Quotient.mk _ h)
  simpa only [fullModulusCorrelation, fullCorrelation, crtCharacter_apply, jointCRT_mk,
    RingEquiv.toEquiv_eq_coe, EquivLike.coe_coe] using hcrt

theorem cross_cofactor_coprime (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    (i : ι) : IsCoprime (a i) (cofactor b i) := by
  unfold cofactor
  apply IsCoprime.prod_right
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hij := (Ideal.isCoprime_span_singleton_iff _ _).mp (hab hji.symm)
  exact (IsCoprime.mul_right_iff.mp (IsCoprime.mul_left_iff.mp hij).1).2

theorem local_cofactor_norm (a b : ι → A)
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ)
    (h : A) (i : ι) :
    ‖fullCorrelation
        (fun x => scaledResidue (a i) (b i) (a i * b i) rfl
          (Ideal.Quotient.mk _ (cofactor b i) * x))
        (fun y => scaledResidue (b i) (a i) (a i * b i) (mul_comm _ _)
          (Ideal.Quotient.mk _ (cofactor a i) * y))
        (χ i) (ψ i) (Ideal.Quotient.mk _ h)‖ =
      ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  obtain ⟨u, hu⟩ := isUnit_residue_of_coprime (a i) (cofactor b i)
    (cross_cofactor_coprime a b hab i)
  have hba : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i * a i})) := by
    simpa only [mul_comm] using hab
  obtain ⟨v, hv⟩ := isUnit_residue_of_coprime (b i) (cofactor a i)
    (cross_cofactor_coprime b a hba i)
  rw [← hu, ← hv, fullCorrelation_unit_change, norm_mul, norm_mul, norm_star,
    FiniteRayExpansion.norm_char_unit, FiniteRayExpansion.norm_char_unit, one_mul, one_mul]
  rfl

theorem fullModulusCorrelation_product_norm (a b : ι → A)
    (ha : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i})))
    [Fintype (Residue (∏ i, a i))] [Fintype (Residue (∏ i, b i))]
    [∀ i, Fintype (Residue (a i))] [∀ i, Fintype (Residue (b i))]
    (χ : ∀ i, MulChar (Residue (a i)) ℂ) (ψ : ∀ i, MulChar (Residue (b i)) ℂ) (h : A) :
    ‖fullModulusCorrelation (∏ i, a i) (∏ i, b i)
      (crtCharacter (productCRT a ha) χ) (crtCharacter (productCRT b hb) ψ) h‖ =
      ∏ i, ‖fullModulusCorrelation (a i) (b i) (χ i) (ψ i) h‖ := by
  rw [fullModulusCorrelation_product a b ha hb hab χ ψ h, norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  exact local_cofactor_norm a b hab χ ψ h i

section Eisenstein
open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve CanonicalRowCompletion
open CenteredMomentSupportedCorrelation
local notation "O" => ActualEisensteinCubic.O

omit [DecidableEq ι] in
theorem supported_character_product (a : ι → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hprod : Supported (Ideal.span {∏ i, a i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i}))) :
    supportedModulusCharacter (∏ i, a i) hprod =
      crtCharacter (productCRT a hcop) (fun i => supportedModulusCharacter (a i) (ha i)) := by
  apply DFunLike.ext
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  simp only [crtCharacter_apply, productCRT_mk, supportedModulusCharacter_mk]
  rw [← Ideal.prod_span_singleton Finset.univ a, map_prod]

theorem actualCorrelation_product_norm (a b : ι → O)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (hb : ∀ i, Supported (Ideal.span {b i}))
    (hA : Supported (Ideal.span {∏ i, a i}))
    (hB : Supported (Ideal.span {∏ i, b i}))
    (hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i})))
    (hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {b i})))
    (hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {a i * b i}))) (h : O) :
    ‖actualCorrelation (∏ i, a i) (∏ i, b i) hA hB h‖ =
      ∏ i, ‖actualCorrelation (a i) (b i) (ha i) (hb i) h‖ := by
  let : ∀ i, Finite (Residue (a i)) := fun i => finite_quotient_span (supported_element_ne_zero (a i) (ha i))
  let : ∀ i, Finite (Residue (b i)) := fun i => finite_quotient_span (supported_element_ne_zero (b i) (hb i))
  let : ∀ i, Fintype (Residue (a i)) := fun i => Fintype.ofFinite _
  let : ∀ i, Fintype (Residue (b i)) := fun i => Fintype.ofFinite _
  let := finite_quotient_span (supported_element_ne_zero _ hA)
  let := finite_quotient_span (supported_element_ne_zero _ hB)
  let : Fintype (Residue (∏ i, a i)) := Fintype.ofFinite _
  let : Fintype (Residue (∏ i, b i)) := Fintype.ofFinite _
  change ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ hA)
    (supportedModulusCharacter _ hB) h‖ =
    ∏ i, ‖fullModulusCorrelation _ _ (supportedModulusCharacter _ (ha i))
      (supportedModulusCharacter _ (hb i)) h‖
  rw [supported_character_product a ha hA hca, supported_character_product b hb hB hcb]
  exact fullModulusCorrelation_product_norm a b hca hcb hcab _ _ h

end Eisenstein

end SevenEighths.CenteredMomentProductCRT

end

end OAI
end OAIOriginalModule1638

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Partition
Source SHA256: bbccfb93b66807df79f34cebeb843d34d43a3bff509315b1ca46aa748866530b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1639


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartition
open CenteredMomentCorrelation CenteredMomentCommonSupport

section Domain
variable {A : Type*} [CommRing A]
theorem fullModulusCorrelation_swap (u v h : A)
    [Fintype (Residue u)] [Fintype (Residue v)]
    (χ : MulChar (Residue u) ℂ) (ψ : MulChar (Residue v) ℂ) :
    fullModulusCorrelation u v χ ψ h = star (fullModulusCorrelation v u ψ χ (-h)) := by
  simp only [fullModulusCorrelation, fullCorrelation, star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y hy
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have he : u * v ∣ v * x - u * y - h ↔ v * u ∣ u * y - v * x - (-h) := by
    rw [mul_comm v u, show u * y - v * x - (-h) = -(v * x - u * y - h) by ring,
      dvd_neg]
  simp only [scaledResidue_congruence]
  by_cases hc : u * v ∣ v * x - u * y - h
  · simp only [hc, he.mp hc, ite_true, star_mul, star_star]
  · simp only [hc, (not_congr he).mp hc, ite_false, star_zero]
end Domain

open ActualEisensteinCubic ConcreteTraceCRT CanonicalQuadraticSieve
open CenteredMomentSupportedCorrelation CenteredMomentUnequal CenteredMomentLocal
open CenteredMomentProductCRT
open ConcretePrimeRowBridge hiding O
local notation "O" => ActualEisensteinCubic.O

theorem actualCorrelation_norm_swap (u v : O)
    (hu : Supported (Ideal.span {u})) (hv : Supported (Ideal.span {v})) (h : O) :
    ‖actualCorrelation u v hu hv h‖ = ‖actualCorrelation v u hv hu (-h)‖ := by
  let := finite_quotient_span (supported_element_ne_zero u hu)
  let := finite_quotient_span (supported_element_ne_zero v hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  change ‖fullModulusCorrelation u v _ _ h‖ = ‖fullModulusCorrelation v u _ _ (-h)‖
  rw [fullModulusCorrelation_swap, norm_star]

theorem prime_power_norm_le_min (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤ (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ min c d := by
  rcases lt_trichotomy c d with hcd | heq | hdc
  · have he : c + (d - c) = d := Nat.add_sub_of_le hcd.le
    have h := unequal_prime_power_norm_le p hp hg hc (show 1 ≤ d - c by omega) (-k)
    rw [actualCorrelation_norm_swap]
    simpa only [← pow_add, he, min_eq_left hcd.le, mul_neg] using h
  · subst d
    simpa only [min_self] using equal_prime_power_norm_le p hp hg hchar hc k
  · have he : d + (c - d) = c := Nat.add_sub_of_le hdc.le
    have h := unequal_prime_power_norm_le p hp hg hd (show 1 ≤ c - d by omega) k
    simpa only [← pow_add, he, min_eq_right hdc.le] using h

theorem prime_power_partition_norm_le (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    {c d : ℕ} (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O) (save : Prop) [Decidable save]
    (hsave : save → c = d ∧ ¬ 6 ∣ c ∧ ¬ p ∣ k) :
    ‖actualCorrelation (p ^ c) (p ^ d) (supported_power p hp c) (supported_power p hp d)
      (p ^ min c d * k)‖ ≤
      (Ideal.absNorm (Ideal.span {p}) : ℝ) ^ (min c d - if save then 1 else 0) := by
  by_cases hs : save
  · obtain ⟨rfl, hc6, hk⟩ := hsave hs
    simp only [min_self, ite_eq_left hs]
    exact (equal_prime_power_unit_norm p hp hg hchar hc hc6 k hk).le
  · simpa only [ite_eq_right hs, Nat.sub_zero] using prime_power_norm_le_min p hp hg hchar hc hd k

section Product
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem supported_product (a : ι → O) (ha : ∀ i, Supported (Ideal.span {a i})) :
    Supported (Ideal.span {∏ i, a i}) := by
  have hs (S : Finset ι) : Supported (Ideal.span {∏ i ∈ S, a i}) := by
    induction S using Finset.induction_on with
    | empty =>
      simp only [Finset.prod_empty, Ideal.span_singleton_one]
      rw [← Ideal.one_eq_top]
      change Supported (1 : Ideal O)
      refine ⟨one_ne_zero, ?_⟩
      intro P hP
      simp only [UniqueFactorizationMonoid.normalizedFactors_one,
        Multiset.notMem_zero] at hP
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact supported_mul_elements _ _ (ha i) ih
  exact hs Finset.univ

def partitionNormalizer (p : ι → O) (c d : ι → ℕ) (U : Finset ι) : ℝ :=
  ∏ i, (Ideal.absNorm (Ideal.span {p i}) : ℝ) ^ (min (c i) (d i) - if i ∈ U then 1 else 0)

def dividedFrequency (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) : O :=
  cofactor (fun j => p j ^ min (c j) (d j)) i * w

theorem commonFrequency_factor (p : ι → O) (c d : ι → ℕ) (w : O) (i : ι) :
    (∏ j, p j ^ min (c j) (d j)) * w = p i ^ min (c i) (d i) * dividedFrequency p c d w i := by
  rw [dividedFrequency, ← mul_assoc, factor_mul_cofactor (fun j => p j ^ min (c j) (d j)) i]

theorem actual_partition_norm_le (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (w : O)
    (hU : ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i ^ min (c i) (d i)) * w)‖ ≤ partitionNormalizer p c d U := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ d i})) := by
    intro i j hij
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i ^ c i * p i ^ d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add, ← pow_add]
    apply (Ideal.isCoprime_span_singleton_iff _ _).mpr
    exact (hcop hij).pow
  rw [actualCorrelation_product_norm (fun i => p i ^ c i) (fun i => p i ^ d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab]
  unfold partitionNormalizer
  apply Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_)
  rw [commonFrequency_factor p c d w i]
  exact prime_power_partition_norm_le (p i) (hp i) (hg i) (hchar i) (hc i) (hd i)
    (dividedFrequency p c d w i) (i ∈ U) (hU i)

theorem normalized_partition_norm_le_one (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (part : O → Prop) (w : O)
    (hpart : part w → ∀ i ∈ U, c i = d i ∧ ¬ 6 ∣ c i ∧ ¬ p i ∣ dividedFrequency p c d w i) :
    ‖if part w then
      actualCorrelation (∏ i, p i ^ c i) (∏ i, p i ^ d i)
        (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
        (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
        ((∏ i, p i ^ min (c i) (d i)) * w) / (partitionNormalizer p c d U : ℂ)
      else 0‖ ≤ 1 := by
  by_cases hw : part w
  · rw [ite_eq_left hw, norm_div, Complex.norm_real]
    have hN : 0 < partitionNormalizer p c d U := by
      unfold partitionNormalizer
      apply Finset.prod_pos
      intro i hi
      apply pow_pos
      exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    rw [Real.norm_of_nonneg hN.le]
    exact (div_le_one hN).mpr (actual_partition_norm_le p hp hg hchar hcop c d hc hd U w (hpart hw))
  · simp only [ite_eq_right hw, norm_zero, zero_le_one]

end Product

end SevenEighths.CenteredMomentPartition

end

end OAI
end OAIOriginalModule1639

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PartitionNorm
Source SHA256: be00b6b10735e08e6a1c58533c0eb1e9e28f8c39fa5b17b6a97d68d50c2504b5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1640



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentPartitionNorm
open CenteredMomentPartition CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonIdeal (p : ι → O) (c d : ι → ℕ) : Ideal O :=
  ∏ i, Ideal.span {p i} ^ min (c i) (d i)

def unitIdeal (p : ι → O) (U : Finset ι) : Ideal O := ∏ i ∈ U, Ideal.span {p i}

omit [DecidableEq ι] in
theorem commonIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) : 0 < (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  apply Finset.prod_pos
  intro i hi
  apply pow_pos
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

omit [Fintype ι] [DecidableEq ι] in
theorem unitIdeal_norm_pos (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (U : Finset ι) : 0 < (Ideal.absNorm (unitIdeal p U) : ℝ) := by
  simp only [unitIdeal, map_prod, Nat.cast_prod]
  apply Finset.prod_pos
  intro i hi
  exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

theorem partitionNormalizer_mul_unit_norm (p : ι → O) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U * (Ideal.absNorm (unitIdeal p U) : ℝ) =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  simp only [unitIdeal, commonIdeal, map_prod, map_pow, Nat.cast_prod, Nat.cast_pow]
  have hU : (∏ i ∈ U, (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∏ i, if i ∈ U then (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 1 := by simp
  rw [hU, partitionNormalizer, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases hmem : i ∈ U
  · simp only [ite_eq_left hmem]
    rw [← pow_succ, Nat.sub_add_cancel (le_min (hc i) (hd i))]
  · simp only [ite_eq_right hmem, Nat.sub_zero, mul_one]

theorem partitionNormalizer_eq_norm_ratio (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι) :
    partitionNormalizer p c d U =
      (Ideal.absNorm (commonIdeal p c d) : ℝ) / Ideal.absNorm (unitIdeal p U) := by
  apply (eq_div_iff (unitIdeal_norm_pos p hp U).ne').mpr
  exact partitionNormalizer_mul_unit_norm p c d hc hd U

theorem partitionNormalizer_eq_log_scale (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (U : Finset ι)
    (Z : ℝ) (hZ : 1 < Z) :
    partitionNormalizer p c d U =
      Z ^ (Real.logb Z (Ideal.absNorm (commonIdeal p c d)) -
        Real.logb Z (Ideal.absNorm (unitIdeal p U))) := by
  rw [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (commonIdeal_norm_pos p hp c d),
    Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ) (unitIdeal_norm_pos p hp U)]
  exact partitionNormalizer_eq_norm_ratio p hp c d hc hd U

end SevenEighths.CenteredMomentPartitionNorm

end

end OAI
end OAIOriginalModule1640

/-! Original module: OAI.NumberTheory.DirichletL.Moments.Forcing
Source SHA256: a5d11ae37c132c6c743409ee2585827fb25a1e176aa64467f2a942f690161e7f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1641



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentForcing
open UniqueFactorizationMonoid CenteredExceptionalCount CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def movingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  (∏ i, P i ^ min (c i) (d i)) * ∏ i ∈ V, P i

def forcingSet (c d : ι → ℕ) (V : Finset ι) : Finset ι :=
  V.filter (fun i => c i = 1 ∧ d i = 1)

def forcingIdeal (P : ι → Ideal O) (c d : ι → ℕ) (V : Finset ι) : Ideal O :=
  ∏ i ∈ forcingSet c d V, P i

omit [Fintype ι] in
theorem valuation_product (S : Finset ι) (I : ι → Ideal O)
    (hI : ∀ i ∈ S, I i ≠ 0) (Q : Ideal O) :
    valuation (∏ i ∈ S, I i) Q = ∑ i ∈ S, valuation (I i) Q := by
  induction S using Finset.induction_on with
  | empty => simp only [Finset.prod_empty,Finset.sum_empty,valuation,normalizedFactors_one,Multiset.count_zero]
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      valuation_mul _ _ _ (hI i (Finset.mem_insert_self _ _))
        (Finset.prod_ne_zero_iff.mpr (fun j hj => hI j (Finset.mem_insert_of_mem hj))),
      ih (fun j hj => hI j (Finset.mem_insert_of_mem hj))]

theorem valuation_prime (P Q : Ideal O) (hP : Prime P) :
    valuation P Q = if P = Q then 1 else 0 := by
  have hf : normalizedFactors P = {P} := by
    simpa using (normalizedFactors_prod_of_prime (m := ({P} : Multiset (Ideal O)))
      (by intro R hR; simpa only [Multiset.mem_singleton.mp hR] using hP))
  simp only [valuation,hf,Multiset.count_singleton]
  simp only [eq_comm]

omit [Fintype ι] in
theorem valuation_prime_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (S : Finset ι) (i : ι) :
    valuation (∏ j ∈ S, P j) (P i) = if i ∈ S then 1 else 0 := by
  rw [valuation_product S P (fun j _ => (hp j).ne_zero)]
  simp only [valuation_prime _ _ (hp _), hinj.eq_iff]
  simp

theorem valuation_prime_power_product (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (n : ι → ℕ) (i : ι) :
    valuation (∏ j, P j ^ n j) (P i) = n i := by
  rw [valuation_product Finset.univ _ (fun j _ => pow_ne_zero _ (hp j).ne_zero)]
  simp only [valuation_pow,valuation_prime _ _ (hp _),hinj.eq_iff,mul_ite,mul_one,mul_zero]
  simp

omit [DecidableEq ι] in
theorem movingIdeal_ne_zero (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) : movingIdeal P c d V ≠ 0 := by
  unfold movingIdeal
  exact mul_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero))

theorem movingIdeal_valuation (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) (i : ι) :
    valuation (movingIdeal P c d V) (P i) = min (c i) (d i) + if i ∈ V then 1 else 0 := by
  rw [movingIdeal,valuation_mul _ _ _
    (Finset.prod_ne_zero_iff.mpr (fun i _ => pow_ne_zero _ (hp i).ne_zero))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)),
    valuation_prime_power_product P hp hinj, valuation_prime_product P hp hinj]

theorem forcing_valuation_two (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι)
    (i : ι) (hi : i ∈ forcingSet c d V) : valuation (movingIdeal P c d V) (P i) = 2 := by
  obtain ⟨hiV,hc,hd⟩ := Finset.mem_filter.mp hi
  rw [movingIdeal_valuation P hp hinj c d V i,hc,hd,ite_eq_left hiV]
  norm_num

omit [Fintype ι] [DecidableEq ι] in
theorem forcingIdeal_squarefree (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (hinj : Function.Injective P) (c d : ι → ℕ) (V : Finset ι) :
    Squarefree (forcingIdeal P c d V) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    let : (P i).IsMaximal := (Ideal.isPrime_of_prime (hp i)).isMaximal (hp i).ne_zero
    let : (P j).IsMaximal := (Ideal.isPrime_of_prime (hp j)).isMaximal (hp j).ne_zero
    exact (Ideal.isCoprime_of_isMaximal (hinj.ne hij)).isRelPrime
  · intro i hi
    exact (hp i).squarefree

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_prime_mem (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Q : Ideal O)
    (hQ : Q ∈ normalizedFactors (forcingIdeal P c d V)) :
    ∃ i ∈ forcingSet c d V, Q = P i := by
  have hf : normalizedFactors (forcingIdeal P c d V) =
      (forcingSet c d V).val.map P := by
    apply normalizedFactors_prod_of_prime
    intro R hR
    obtain ⟨i,hi,rfl⟩ := Multiset.mem_map.mp hR
    exact hp i
  rw [hf] at hQ
  obtain ⟨i,hi,hPi⟩ := Multiset.mem_map.mp hQ
  exact ⟨i,hi,hPi.symm⟩

omit [Fintype ι] [DecidableEq ι] in
theorem forcing_norm_scale (P : ι → Ideal O) (hp : ∀ i, Prime (P i))
    (c d : ι → ℕ) (V : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Z ^ ((2 * Real.logb Z (Ideal.absNorm (forcingIdeal P c d V))) / 2) =
      (Ideal.absNorm (forcingIdeal P c d V) : ℝ) := by
  rw [show (2 * Real.logb Z (Ideal.absNorm (forcingIdeal P c d V))) / 2 =
    Real.logb Z (Ideal.absNorm (forcingIdeal P c d V)) by ring]
  exact Real.rpow_logb (zero_lt_one.trans hZ) (ne_of_gt hZ)
    (norm_pos (Finset.prod_ne_zero_iff.mpr (fun i _ => (hp i).ne_zero)))

def movingElement (p : ι → O) (c d : ι → ℕ) (V : Finset ι) : O :=
  (∏ i, p i ^ min (c i) (d i)) * ∏ i ∈ V, p i

omit [DecidableEq ι] in
theorem movingElement_span (p : ι → O) (c d : ι → ℕ) (V : Finset ι) :
    Ideal.span {movingElement p c d V} = movingIdeal (fun i => Ideal.span {p i}) c d V := by
  simp only [movingElement,movingIdeal,Ideal.span_singleton_pow,
    Ideal.prod_span_singleton,Ideal.span_singleton_mul_span_singleton]

theorem actual_forcing_exceptional_count (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι)
    (η : HeckeFamily.Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72 : O)})
    (m e : O) (hm : m ≠ 0) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2 : O) ∣ m)
    (he : HeckeFamily.elementCoeff η e ≠ 0) (T : Finset O) (hT : ∀ z ∈ T, z ≠ 0)
    (hex : ∀ z ∈ T, CenteredExceptionalProfile.FixedInducingRow
      (CenteredMomentChildRows.childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2 : O) ∉ Ideal.span {p i} ∧
      IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e})
    (Z C M : ℝ) (hZ : 1 < Z) (hC : 0 ≤ C)
    (hN : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ C * Z ^ M) :
    (T.card : ℝ) ≤ 768 * (6 : ℝ) ^ (normalizedFactors Q).toFinset.card *
      C ^ (1 / 6 : ℝ) *
        Z ^ ((M - 4 * Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V))) / 6) := by
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  have hb := CenteredMomentChildRows.separated_exceptional_count η χ Q hQ0 hQ hQ72
    m (movingElement p c d V) e hm hA hmLam hm2 he T hT hex
    (forcingIdeal (fun i => Ideal.span {p i}) c d V)
    (forcingIdeal_squarefree _ hp hinj c d V) (by
      intro P hP
      obtain ⟨i,hi,rfl⟩ := forcing_prime_mem _ hp c d V P hP
      obtain ⟨hg,h2,hQP,hPe⟩ := hgood i hi
      refine ⟨hg,h2,hQP,hPe,?_⟩
      rw [movingElement_span,forcing_valuation_two _ hp hinj c d V i hi])
    Z C M (2 * Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))
    (zero_lt_one.trans hZ) hC (forcing_norm_scale _ hp c d V Z hZ).le hN
  convert hb using 1 ; congr 1 ; ring_nf

end SevenEighths.CenteredMomentForcing

end

end OAI
end OAIOriginalModule1641

/-! Original module: OAI.NumberTheory.DirichletL.Moments.HeckeExceptionalEnergy
Source SHA256: cedc30729530b22fcb396deae37405de3baae62aa968604bf2285387764b2265
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1642



namespace OAI

noncomputable section
open scoped BigOperators Classical SchwartzMap ContDiff
namespace SevenEighths.CenteredMomentHeckeExceptionalEnergy
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentForcing CenteredMomentChildRows UniqueFactorizationMonoid
local notation "O" => ActualEisensteinCubic.O
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

theorem forcing_finite_energy (p : ι → O)
    (hp : ∀ i, Prime (Ideal.span {p i})) (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter)
    (Q : Ideal O) (hQ0 : Q ≠ 0) (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (m e : O) (hm : m ≠ 0) (hmLam : ConcretePrimeRowBridge.goodLambda ∣ m) (hm2 : (2:O) ∣ m)
    (he : elementCoeff η e ≠ 0) (rows : Finset O) (hrows : ∀ z ∈ rows, z ≠ 0)
    (hex : ∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
      (childCharacter η χ) Q m (movingElement p c d V) z)
    (hgood : ∀ i ∈ forcingSet c d V,
      ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
      IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e})
    (Z C M D : ℝ) (hZ : 1 < Z) (hC : 0 ≤ C) (_hD : 0 ≤ D)
    (hN : ∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ C*Z^M)
    (f : O → ℂ) (hf : ∀ z ∈ rows, ‖f z‖ ≤ D) :
    (∑ z ∈ rows, ‖f z‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*C^(1/6:ℝ)*
        Z^((M-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*D^2 := by
  have hc := actual_forcing_exceptional_count p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z C M hZ hC hN
  calc
    _ ≤ ∑ _z ∈ rows, D^2 := Finset.sum_le_sum (fun z hz =>
      pow_le_pow_left₀ (norm_nonneg _) (hf z hz) 2)
    _ = (rows.card:ℝ)*D^2 := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hc (sq_nonneg D)

theorem exceptional_slots_energy (Q : Ideal O) (hQ0 : Q ≠ 0)
    (hQ : Q ≠ ⊤) (hQ72 : Q ≤ Ideal.span {(72:O)})
    (a₁ b₁ a₂ b₂ ε B : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂)
    (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂) (hε : 0 < ε) (hB : 0 ≤ B) :
    ∃ J : ℕ, ∀ W₁ W₂ : ℝ → ℂ,
      ∀ _hs₁ : Function.support W₁ ⊆ Set.Icc a₁ b₁,
      ∀ _hs₂ : Function.support W₂ ⊆ Set.Icc a₂ b₂,
      ∀ _hW₁ : ContDiff ℝ ∞ W₁, ∀ _hW₂ : ContDiff ℝ ∞ W₂,
      ∃ C : ℝ, 0 < C ∧ ∀ Z : ℝ, 1 < Z →
      ∀ (p : ι → O), (∀ i, Prime (Ideal.span {p i})) →
      Function.Injective (fun i => Ideal.span {p i}) →
      ∀ (c d : ι → ℕ) (V : Finset ι) (η : Character) (χ : RayFourExpansion.RayCharacter),
      ∀ m e : O, m ≠ 0 → (ConcretePrimeRowBridge.goodLambda ∣ m) → ((2:O) ∣ m) →
      elementCoeff η e ≠ 0 → ∀ rows : Finset O,
      (∀ z ∈ rows, z ≠ 0) →
      (∀ z ∈ rows, CenteredExceptionalProfile.FixedInducingRow
        (childCharacter η χ) Q m (movingElement p c d V) z) →
      (∀ z ∈ rows, (HeckeRowClosure.rowConductorBound (childCharacter η χ) m 1
        (movingElement p c d V*z):ℝ) ≤ Z^B) →
      (∀ i ∈ forcingSet c d V,
        ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {p i} ∧ (2:O) ∉ Ideal.span {p i} ∧
        IsCoprime Q (Ideal.span {p i}) ∧ Ideal.span {p i} ∣ Ideal.span {e}) →
      ∀ Cr Mrow : ℝ, 0 ≤ Cr →
      (∀ z ∈ rows, (Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Cr*Z^Mrow) →
      ∀ (S : κ → Finset (Ideal O)) (β : κ → Ideal O → ℂ) (P b Ms : κ → ℝ),
      (∀ i, 0 < P i) → (∀ i, 0 ≤ b i) → (∀ i, 0 ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, ‖β i I‖ ≤ Ms i) →
      (∀ i, ∀ I ∈ S i, β i I ≠ 0 → (Ideal.absNorm I:ℝ) ≤ b i*P i) →
      ∀ t X₁ X₂ Y₁ Y₂ T L : ℝ, 0 < L →
      L ≤ X₁ → L ≤ X₂ → L ≤ Y₁ → L ≤ Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      (∑ z ∈ rows, ‖centeredSlotRow (childCharacter η χ) m (movingElement p c d V) z
        W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      (768*(6:ℝ)^(normalizedFactors Q).toFinset.card*Cr^(1/6:ℝ)*
        Z^((Mrow-4*Real.logb Z (Ideal.absNorm (forcingIdeal (fun i => Ideal.span {p i}) c d V)))/6))*
        (C*Z^ε*(1+‖t‖)^J*(∏ i,128*b i*Ms i)*(Real.sqrt (T*∏ i,P i)/L))^2 := by
  obtain ⟨J,hJ⟩ := exceptional_slots_estimate (ι := κ) Q hQ0 a₁ b₁ a₂ b₂ ε B ha₁ ha₂ hb₁ hb₂ hε hB
  refine ⟨J,?_⟩
  intro W₁ W₂ hs₁ hs₂ hW₁ hW₂
  obtain ⟨C,hC,hbound⟩ := hJ W₁ W₂ hs₁ hs₂ hW₁ hW₂
  refine ⟨C,hC,?_⟩
  intro Z hZ p hp hinj c d V η χ m e hm hmLam hm2 he rows hrows hex hcond hgood
    Cr Mrow hCr hN S β P b Ms hP hb hMs hβ hNs t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY
  have hA : movingElement p c d V ≠ 0 := by
    apply Ideal.span_singleton_eq_bot.not.mp
    rw [movingElement_span]
    exact movingIdeal_ne_zero _ hp c d V
  refine forcing_finite_energy p hp hinj c d V η χ Q hQ0 hQ hQ72
    m e hm hmLam hm2 he rows hrows hex hgood Z Cr Mrow _ hZ hCr ?_ hN _ ?_
  · have hprod : 0 ≤ ∏ i,128*b i*Ms i :=
      Finset.prod_nonneg (fun i _ => mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hMs i))
    positivity
  · intro z hz
    exact hbound Z hZ.le (childCharacter η χ) m (movingElement p c d V) z hm hA (hrows z hz)
      hmLam hm2 (hcond z hz) (hex z hz) S β P b Ms hP hb hMs hβ hNs
      t X₁ X₂ Y₁ Y₂ T L hL hX₁ hX₂ hY₁ hY₂ hpX hpY

end SevenEighths.CenteredMomentHeckeExceptionalEnergy

end

end OAI
end OAIOriginalModule1642

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SecondLedger
Source SHA256: 10151c43e527a4db16ecd58bad278d9270ac1ac977b61c6819647b0a7e778927
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1643



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentSecondLedger
open CanonicalQuadraticSieve CenteredMomentSupportedCorrelation CenteredMomentUnequal
open CenteredMomentPartition CenteredMomentProductCRT ConcretePrimeRowBridge
local notation "O" => ActualEisensteinCubic.O

theorem nonzero_unequal_min_six (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (hcd : c ≠ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) : 6 ∣ min c d := by
  by_contra h6
  rcases lt_or_gt_of_ne hcd with hlt | hgt
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hc
      (show 1 ≤ d-c by omega) (by simpa only [min_eq_left hlt.le] using h6) (-k)
    have he : c+(d-c)=d := Nat.add_sub_of_le hlt.le
    have hn := norm_ne_zero_iff.mpr hne
    rw [actualCorrelation_norm_swap] at hn
    have hz' : actualCorrelation (p^d) (p^c) (supported_power p hp d) (supported_power p hp c)
        (-(p^min c d*k)) = 0 := by
      simpa only [← pow_add,he,min_eq_left hlt.le,mul_neg] using hz
    exact hn (by rw [hz',norm_zero])
  · have hz := unequal_prime_power_zero_of_not_six p hp hg hchar hd
      (show 1 ≤ c-d by omega) (by simpa only [min_eq_right hgt.le] using h6) k
    have he : d+(c-d)=c := Nat.add_sub_of_le hgt.le
    exact hne (by simpa only [← pow_add,he,min_eq_right hgt.le] using hz)

def localSaving (c d : ℕ) (nonunit : Prop) : ℝ :=
  (c+d : ℝ) - 5*(min c d : ℝ)/6 - 1 +
    (if c=d ∧ ¬6∣c ∧ ¬nonunit then 1 else 0) +
    (if c=d ∧ ¬6∣c ∧ nonunit then 1/6 else 0) +
    (if c=d ∧ c=1 ∧ nonunit then 1/3 else 0)

theorem localSaving_lower (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (huneq : c ≠ d → 6 ∣ min c d) (nonunit : Prop) :
    ((c:ℝ)+d)/3 ≤ localSaving c d nonunit := by
  by_cases hcd : c=d
  · subst d
    by_cases h6 : 6∣c
    · have hc6 : 6 ≤ c := Nat.le_of_dvd (by omega) h6
      have hn1 : c ≠ 1 := by omega
      simp only [localSaving,min_self,h6,not_true_eq_false,false_and,and_false,
        ite_false,hn1,add_zero]
      have hcr : (6:ℝ) ≤ c := by exact_mod_cast hc6
      linarith
    · by_cases hu : nonunit
      · by_cases hc1 : c=1
        · subst c
          norm_num [localSaving,hu]
        · have hc2 : 2 ≤ c := by omega
          simp only [localSaving,min_self,h6,not_false_eq_true,hu,not_true_eq_false,
            and_self,and_false,false_and,ite_false,ite_true,hc1,add_zero]
          have hcr : (2:ℝ) ≤ c := by exact_mod_cast hc2
          linarith
      · simp only [localSaving,min_self,h6,not_false_eq_true,hu,and_false,
          and_true,ite_false,ite_true,add_zero]
        have hcr : (1:ℝ) ≤ c := by exact_mod_cast hc
        linarith
  · have hmin : 6 ≤ min c d := Nat.le_of_dvd (lt_of_lt_of_le Nat.zero_lt_one (le_min hc hd)) (huneq hcd)
    have hmr : (6:ℝ) ≤ min c d := by exact_mod_cast hmin
    have hmc : ((min c d : ℕ) : ℝ) ≤ c := by exact_mod_cast min_le_left c d
    have hmd : ((min c d : ℕ) : ℝ) ≤ d := by exact_mod_cast min_le_right c d
    simp only [Nat.cast_min] at hmr hmc hmd
    simp only [localSaving,hcd,false_and,ite_false,add_zero]
    linarith

theorem actual_localSaving_lower (p : O) [(Ideal.span {p}).IsMaximal]
    (hp : Supported (Ideal.span {p})) (hg : goodLambda ∉ Ideal.span {p})
    (hchar : ringChar (O ⧸ Ideal.span {p}) ≠ 2)
    (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) (k : O)
    (hne : actualCorrelation (p^c) (p^d) (supported_power p hp c) (supported_power p hp d)
      (p^min c d*k) ≠ 0) :
    ((c:ℝ)+d)/3 ≤ localSaving c d (p ∣ k) :=
  localSaving_lower c d hc hd (fun hcd => nonzero_unequal_min_six p hp hg hchar c d hc hd hcd k hne) _

section Global
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem local_nonzero_of_global (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ) (w : O)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) (i : ι) :
    actualCorrelation (p i^c i) (p i^d i) (supported_power (p i) (hp i) (c i))
      (supported_power (p i) (hp i) (d i))
      (p i^min (c i) (d i)*dividedFrequency p c d w i) ≠ 0 := by
  have hca : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcb : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^d i})) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hcab : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i^c i*p i^d i})) := by
    intro i j hij
    dsimp only [Function.onFun]
    rw [← pow_add,← pow_add]
    exact (Ideal.isCoprime_span_singleton_iff _ _).mpr (hcop hij).pow
  have hn := norm_ne_zero_iff.mpr hne
  rw [actualCorrelation_product_norm (fun i => p i^c i) (fun i => p i^d i)
    (fun i => supported_power (p i) (hp i) (c i))
    (fun i => supported_power (p i) (hp i) (d i))
    (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
    (supported_product _ (fun i => supported_power (p i) (hp i) (d i))) hca hcb hcab] at hn
  have hi := (Finset.prod_ne_zero_iff.mp hn) i (Finset.mem_univ i)
  rw [commonFrequency_factor p c d w i] at hi
  exact norm_ne_zero_iff.mp hi

omit [DecidableEq ι] in
theorem log_norm_power_product (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c : ι → ℕ) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) =
      ∑ i, (c i : ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,map_pow,Nat.cast_prod,Nat.cast_pow]
  rw [Real.logb_prod _ _ (fun i _ => pow_ne_zero _ (Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)))]
  simp only [Real.logb_pow]

def secondSaving (p : ι → O) (c d : ι → ℕ) (w : O) (Z : ℝ) : ℝ :=
  ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) *
    localSaving (c i) (d i) (p i ∣ dividedFrequency p c d w i)

def actualUnitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ ¬p i∣dividedFrequency p c d w i)

def actualNonunitSet (p : ι → O) (c d : ι → ℕ) (w : O) : Finset ι :=
  Finset.univ.filter (fun i => c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i)

omit [Fintype ι] [DecidableEq ι] in
theorem log_norm_radical (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (S : Finset ι) (Z : ℝ) :
    Real.logb Z (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) =
      ∑ i ∈ S, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
  simp only [map_prod,Nat.cast_prod]
  exact Real.logb_prod _ _ (fun i _ => Nat.cast_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))

theorem secondSaving_eq_norm_ledger (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ) (w : O) (Z : ℝ) :
    secondSaving p c d w Z =
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ) -
      5*Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.commonIdeal p c d) : ℝ)/6 -
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualUnitSet p c d w)) : ℝ) +
      Real.logb Z (Ideal.absNorm (CenteredMomentPartitionNorm.unitIdeal p (actualNonunitSet p c d w)) : ℝ)/6 +
      Real.logb Z (Ideal.absNorm (CenteredMomentForcing.forcingIdeal
        (fun i => Ideal.span {p i}) c d (actualNonunitSet p c d w)) : ℝ)/3 := by
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d]
  simp only [CenteredMomentPartitionNorm.commonIdeal,CenteredMomentPartitionNorm.unitIdeal,
    CenteredMomentForcing.forcingIdeal]
  rw [log_norm_power_product p hp,log_norm_radical p hp,log_norm_radical p hp,
    log_norm_radical p hp,log_norm_radical p hp]
  simp only [actualUnitSet,actualNonunitSet,CenteredMomentForcing.forcingSet,
    Finset.filter_filter,Finset.sum_filter,]
  unfold secondSaving
  have hf (i : ι) :
      (if (c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) =
      (if c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i
       then Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) else 0) := by
    have he : ((c i=d i ∧ ¬6∣c i ∧ p i∣dividedFrequency p c d w i) ∧ c i=1 ∧ d i=1) ↔
        (c i=d i ∧ c i=1 ∧ p i∣dividedFrequency p c d w i) := by
      constructor
      · rintro ⟨⟨hcd,h6,hn⟩,hc,hd⟩
        exact ⟨hcd,hc,hn⟩
      · rintro ⟨hcd,hc,hn⟩
        exact ⟨⟨hcd,by omega,hn⟩,hc,by omega⟩
    simp only [he]
  simp_rw [hf]
  rw [show (∑ i, (c i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) +
      (∑ i, (d i:ℝ)*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)) =
      ∑ i, ((c i:ℝ)+(d i:ℝ))*Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) by
      simp only [add_mul,Finset.sum_add_distrib]]
  simp only [Finset.mul_sum,Finset.sum_div]
  rw [← Finset.sum_sub_distrib,← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [localSaving,Nat.cast_min]
  split_ifs <;> ring

theorem actual_secondSaving_lower (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hp : ∀ i, Supported (Ideal.span {p i})) (hg : ∀ i, goodLambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hcop : Pairwise (Function.onFun IsCoprime p)) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (w : O) (Z : ℝ) (hZ : 1 < Z)
    (hne : actualCorrelation (∏ i, p i^c i) (∏ i, p i^d i)
      (supported_product _ (fun i => supported_power (p i) (hp i) (c i)))
      (supported_product _ (fun i => supported_power (p i) (hp i) (d i)))
      ((∏ i, p i^min (c i) (d i))*w) ≠ 0) :
    (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ) +
      Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/3 ≤ secondSaving p c d w Z := by
  calc
    _ = ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ)*(((c i:ℝ)+d i)/3) := by
      rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
        ← Finset.sum_add_distrib,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_left
        (actual_localSaving_lower (p i) (hp i) (hg i) (hchar i) (c i) (d i) (hc i) (hd i)
          (dividedFrequency p c d w i) (local_nonzero_of_global p hp hcop c d w hne i))
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)

end Global

end SevenEighths.CenteredMomentSecondLedger

end

end OAI
end OAIOriginalModule1643

/-! Original module: OAI.NumberTheory.DirichletL.Moments.CommonAllowance
Source SHA256: cfb53306eee5439f00de7d632dd61b716b6a4e5141893106589943b855fdbb53
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1644



namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentCommonAllowance
open CenteredMomentActive CenteredMomentSecondLedger CanonicalQuadraticSieve
local notation "O" => ActualEisensteinCubic.O

def activeIndicator (c d : ℕ) : ℝ := if netExponent c d ≠ 0 then 1 else 0

theorem netExponent_self (c : ℕ) : netExponent c c = 0 := by
  unfold netExponent
  have h : c+5*c=6*c := by omega
  rw [h, Nat.mul_mod_right]

theorem local_allowance (c d : ℕ) (hc : 1 ≤ c) (hd : 1 ≤ d) :
    max (3*(c:ℝ)-5*(d:ℝ)-activeIndicator c d) 0 / 6 +
      max (3*(d:ℝ)-5*(c:ℝ)-activeIndicator c d) 0 / 6 ≤
      (c:ℝ)+(d:ℝ)-2-activeIndicator c d := by
  have hc' : (1:ℝ) ≤ c := by exact_mod_cast hc
  have hd' : (1:ℝ) ≤ d := by exact_mod_cast hd
  unfold activeIndicator
  split_ifs with he
  · have hne : c ≠ d := by rintro rfl; exact he (netExponent_self c)
    have hgap : (c:ℝ)+1 ≤ d ∨ (d:ℝ)+1 ≤ c := by
      rcases lt_or_gt_of_ne hne with h | h
      · left; exact_mod_cast h
      · right; exact_mod_cast h
    rcases hgap with hgap | hgap <;>
      rw [max_def,max_def] <;> split_ifs <;> linarith
  · rw [max_def,max_def]; split_ifs <;> linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem weighted_positive_part (a w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (∑ i, a i*w i) 0 ≤ ∑ i, max (a i) 0*w i := by
  apply max_le
  · exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_max_left _ _) (hw i)
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (le_max_right _ _) (hw i)

omit [DecidableEq ι] in
theorem weighted_allowance (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i)
    (hd : ∀ i, 1 ≤ d i) (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) :
    max (3*(∑ i, (c i:ℝ)*w i)-5*(∑ i, (d i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 +
    max (3*(∑ i, (d i:ℝ)*w i)-5*(∑ i, (c i:ℝ)*w i)-
      ∑ i, activeIndicator (c i) (d i)*w i) 0/6 ≤
      (∑ i, (c i:ℝ)*w i)+(∑ i, (d i:ℝ)*w i)-
        2*(∑ i, w i)-(∑ i, activeIndicator (c i) (d i)*w i) := by
  have h₁ := weighted_positive_part (fun i => 3*(c i:ℝ)-5*(d i:ℝ)-activeIndicator (c i) (d i)) w hw
  have h₂ := weighted_positive_part (fun i => 3*(d i:ℝ)-5*(c i:ℝ)-activeIndicator (c i) (d i)) w hw
  have hsum := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    mul_le_mul_of_nonneg_right (local_allowance (c i) (d i) (hc i) (hd i)) (hw i))
  simp only [sub_mul, add_mul, div_mul_eq_mul_div, mul_assoc,
    Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum,
    ] at h₁ h₂ hsum ⊢
  simp only [← Finset.sum_div] at hsum
  linarith

omit [DecidableEq ι] in
theorem actual_common_support_allowance (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i})) (c d : ι → ℕ)
    (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i) (Z : ℝ) (hZ : 1 < Z) :
    let C := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)
    let D := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ)
    let P := Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ)
    let R := Real.logb Z (Ideal.absNorm
      (∏ i ∈ activeSupport Finset.univ c d, Ideal.span {p i}) : ℝ)
    max (3*C-5*D-R) 0/6 + max (3*D-5*C-R) 0/6 ≤ C+D-2*P-R := by
  dsimp only
  rw [log_norm_power_product p hp c,log_norm_power_product p hp d,
    log_norm_radical p hp,log_norm_radical p hp]
  simpa only [activeSupport,Finset.sum_filter,activeIndicator,ite_mul,one_mul,zero_mul]
    using weighted_allowance c d hc hd
      (fun i => Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ))
      (fun i => Real.logb_nonneg hZ (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))))

end SevenEighths.CenteredMomentCommonAllowance

end

end OAI
end OAIOriginalModule1644

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DescentLedger
Source SHA256: 7970798e5301a73afce63b2733d2a8bef850cb2c702378e3415b42e98bbcbfcf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule1645


namespace OAI

noncomputable section
open scoped BigOperators Classical
namespace SevenEighths.CenteredMomentDescentLedger
open CanonicalQuadraticSieve CenteredMomentSecondLedger CenteredMomentPartitionNorm
local notation "O" => ActualEisensteinCubic.O

def firstSaving (c D₀ w q wo B g ell : ℝ) : ℝ :=
  c/6+5*D₀/6+w/3+q/6+wo+B-5*g/6+ell

theorem firstSaving_lower (c d D₀ w q R wo B g ell σ δ : ℝ)
    (hc : 0 ≤ c) (hw : 0 ≤ w) (hq : 0 ≤ q) (hwo : 0 ≤ wo)
    (hB : 0 ≤ B) (hσ : 0 ≤ σ) (hδ : 0 ≤ δ)
    (hR : R ≤ q) (hBcost : max (3*c-5*d-R) 0/6 ≤ B)
    (hD : d-δ ≤ D₀) (hg : g ≤ max (D₀-c-2*w+wo) 0+2*σ)
    (hell : 0 ≤ ell) (hwσ : w ≤ 7*σ/3) :
    2*(c+w)/3-3*σ-5*δ/6 ≤ firstSaving c D₀ w q wo B g ell := by
  have hraw : 3*c-5*d-R ≤ 6*B := by
    have hm := le_max_left (3*c-5*d-R) 0
    linarith
  have hmax : max (3*c-5*D₀) 0/6-5*δ/6 ≤ B+q/6 := by
    apply (max_le_iff.mpr ⟨?_,?_⟩ : max (3*c-5*D₀) 0 ≤ 6*(B+q/6)+5*δ) |> fun h => by linarith
    · linarith
    · positivity
  unfold firstSaving
  by_cases hJ : 0 ≤ D₀-c-2*w+wo
  · rw [max_eq_left hJ] at hg
    linarith
  · rw [max_eq_right (le_of_not_ge hJ)] at hg
    have hm := le_max_left (3*c-5*D₀) 0
    linarith

section ActualSecond
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem common_log_ge_unit (p : ι → O) (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (U : Finset ι) (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (unitIdeal p U) : ℝ) ≤
      Real.logb Z (Ideal.absNorm (commonIdeal p c d) : ℝ) := by
  rw [unitIdeal,log_norm_radical p hp,commonIdeal,log_norm_power_product p hp]
  calc
    _ ≤ ∑ i, Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ U)
      intro i hi hni
      apply Real.logb_nonneg hZ
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1)
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
        Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
      have hm : (1:ℝ) ≤ (min (c i) (d i) : ℕ) := by exact_mod_cast le_min (hc i) (hd i)
      nlinarith

omit [DecidableEq ι] in
theorem half_product_log_ge_radical (p : ι → O)
    (hp : ∀ i, Supported (Ideal.span {p i}))
    (c d : ι → ℕ) (hc : ∀ i, 1 ≤ c i) (hd : ∀ i, 1 ≤ d i)
    (Z : ℝ) (hZ : 1 < Z) :
    Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}) : ℝ) ≤
      (Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^c i) : ℝ)+
       Real.logb Z (Ideal.absNorm (∏ i, Ideal.span {p i}^d i) : ℝ))/2 := by
  rw [log_norm_radical p hp,log_norm_power_product p hp,log_norm_power_product p hp,
    ← Finset.sum_add_distrib,Finset.sum_div]
  apply Finset.sum_le_sum
  intro i hi
  have hn : 0 ≤ Real.logb Z (Ideal.absNorm (Ideal.span {p i}) : ℝ) :=
    Real.logb_nonneg hZ (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (hp i).1))
  have hcr : (1:ℝ) ≤ c i := by exact_mod_cast hc i
  have hdr : (1:ℝ) ≤ d i := by exact_mod_cast hd i
  nlinarith
end ActualSecond

theorem declared_width_drop (M J g g₂ t₂ σ m' q' δ : ℝ)
    (hwidth : m'+q'=M+J-g-g₂+t₂) (hg : J+σ ≤ g) (hcommon : t₂ ≤ g₂)
    (hnonempty : 0 ≤ m'+δ) :
    max 0 (m'+δ)+q' ≤ M-σ+δ := by
  rw [max_eq_right hnonempty]
  linarith

theorem child_allowance_lower (b₂ p₂ w B ell : ℝ)
    (hbp : p₂ ≤ b₂) (hB : 0 ≤ B) :
    w+ell ≤ b₂-p₂+w+B+ell := by linarith

theorem exceptional_excess_identity
    (A m q c d R E K w wo B g ell b₂ p₂ g₂ t₂ V f : ℝ) :
    let a₀ := A-c-w
    let K₀ := 2*A-c-d+R+E-m
    let m' := 2*a₀-K-g-g₂-V
    let q' := q+R+E+wo+t₂+V
    (m'-f)/6+a₀-b₂-(m'+q'+(b₂-p₂+w+B+ell)) =
      A-5*(m+q)/6-firstSaving c (d+K₀-K) w (q+R+E) wo B g ell -
        (2*b₂-5*g₂/6-p₂+t₂+V/6+f/6) := by
  dsimp only [firstSaving]
  ring

theorem inner_allowance_identity
    (a₀ q wo w B s₀ K g ell p₂ g₂ t₂ b₂ V : ℝ) :
    (a₀+q+wo+w+B-s₀)-(K+g-ell-a₀+p₂-s₀+g₂-t₂-b₂) =
      (2*a₀-K-g-g₂-V)+(q+wo+t₂+V)+(b₂-p₂+w+B+ell) := by ring

theorem exceptional_excess_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ A-5*M/6-2*(c+w+b₂)/3+3*σ+5*δ/6 := by linarith

theorem uncentered_exceptional_bound
    (A M c w b₂ F₁ F₂ σ δ : ℝ)
    (hA : A ≤ 5*M/6) (hc : 0 ≤ c) (hw : 0 ≤ w) (hb : 0 ≤ b₂)
    (hF₁ : 2*(c+w)/3-3*σ-5*δ/6 ≤ F₁)
    (hF₂ : 2*b₂/3 ≤ F₂) :
    A-5*M/6-F₁-F₂ ≤ 3*σ+5*δ/6 := by
  have hh := exceptional_excess_bound A M c w b₂ F₁ F₂ σ δ hF₁ hF₂
  linarith

end SevenEighths.CenteredMomentDescentLedger

end

end OAI
end OAIOriginalModule1645

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FinalStageLedger
Source SHA256: 408e0b5d9d808728cc40f886121e1da71119a2bf4aab0100c4a4d1312fc3983a
