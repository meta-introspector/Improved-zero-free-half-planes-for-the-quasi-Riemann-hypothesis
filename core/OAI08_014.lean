      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type*} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  obtain ⟨cB,κB,KB,hcB,hcB1,hκB,hKB,hbalanced⟩ := balanced_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb
  obtain ⟨cH,κH,KH,hcH,hcH1,hκH,hKH,hhigh⟩ := high_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb
  refine ⟨cB,κB,cH,κH,max KB KH,hcB,hcB1,hκB,hcH,hcH1,hκH,lt_of_lt_of_le hKB (le_max_left _ _),?_⟩
  filter_upwards [hbalanced,hhigh,eventually_ge_atTop (1:ℝ)] with Z hb hh hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2*a-1≤5/6
  · simp only [ite_eq_left hδ] at hmom
    have hc := hb d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    simp only [adaptiveRowExponent,ite_eq_left hδ]
    exact hc.trans (by gcongr;exact le_max_left _ _)
  · simp only [ite_eq_right hδ] at hmom
    have hc := hh d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    simp only [adaptiveRowExponent,ite_eq_right hδ]
    exact hc.trans (by gcongr;exact le_max_right _ _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2891

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblySourceCount
Source SHA256: e98e4fb99e2d1809acfbf2c7630d71c7a1ef1d37d19ce9be5a28e58959811f07
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2892



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Set Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorWitnessRows
open HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorRowCount HeckeDetectorAdaptiveCutoff
open ProbeHighRowFamily

theorem balanced_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M≤H) (_S : Finset (Ideal O))
    (φ : ℝ→ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ⊆Ioi 0) (_hφ0 : ∀y,0≤φ y) (_hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0<a₀) (_hab₀ : a₀≤b₀) (_hB₀ : 0<B₀)
    (_hφs : Function.support φ⊆Ioo a₀ b₀) (_hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (_hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → 2*a-1≤5/6 → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ counts.cB counts.kB (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(Endpoint.balancedRowCount (2*a-1) (1/2-q/(2*a-1))+Δ/4+159*ε+εm+B.mesh+7*ν) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.balanced
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ ν C q i hi ha haδ ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ ν
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha haδ hε hε' hΔ hΔ' hν (by positivity)
    (by positivity) (hfreq d hd' i hi) B hne hq hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem high_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (_hH : RayOrthogonality.globalUnits M≤H) (_S : Finset (Ideal O))
    (φ : ℝ→ℝ) (_hφ : ContDiff ℝ ∞ φ) (_hφc : HasCompactSupport φ)
    (_hφp : tsupport φ⊆Ioi 0) (_hφ0 : ∀y,0≤φ y) (_hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (_ha₀ : 0<a₀) (_hab₀ : a₀≤b₀) (_hB₀ : 0<B₀)
    (_hφs : Function.support φ⊆Ioo a₀ b₀) (_hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (_hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ C q : ℝ) (i : ℕ),i≤n → 5/6<2*a-1 → a≤1 → 0≤ε → ε≤1/1000 → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ counts.cH counts.kH (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(1-(2*a-1)+78*ε+εm) := by
  obtain ⟨K₀,hK₀,hcount⟩ := counts.high
  obtain ⟨K,hK,hpref⟩ := source_count_prefactor_eventually (Label:=Label)
    N dmin dmax logCost heightCost momentCost binWidth K₀ hdmin hdmax hl (by linarith) hb
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_all_rpow_ge hcount dmin hdmin,hpref,
    source_count_frequency_eventually n dmax τ heightCost hdmax hτ hh,
    eventually_all_rpow_ge (eventually_gt_atTop (1:ℝ)) dmin hdmin,
    eventually_ge_atTop (1:ℝ)] with Z hcount hpref hfreq hU hZ
  intro d hd hd' a ε Δ C q i hi ha ha' hε hε' hC Slot B hslots hbin hmom
  have hcard := hcount d hd a ε (Z^τ) ((Z^d)^(τ/(2*dmax))) Δ
    (C*Z^momentCost) (Z^heightCost) q i (hU d hd) ha ha' hε hε' (by positivity)
    (by positivity) (hfreq d hd' i hi) B hmom
  apply hcard.trans
  exact mul_le_mul_of_nonneg_right
    (hpref d hd hd' C a ε (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i
      hC ha' B hslots hbin) (Real.rpow_nonneg (Real.rpow_nonneg (by linarith) _) _)

theorem adaptive_source_count_from_raw_moments
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (hH : RayOrthogonality.globalUnits M≤H) (S : Finset (Ideal O))
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm : ℝ) (hεm : 0<εm)
    (Label : Type) [Fintype Label] (N n : ℕ)
    (dmin dmax τ logCost heightCost momentCost binWidth : ℝ)
    (hdmin : 0<dmin) (hdmax : 0<dmax) (hτ : 0<τ)
    (hl : 0<logCost) (hh : τ<heightCost) (hb : 0<binWidth) (counts : CountParameters M H εm) :
    ∃K : ℝ,0<K ∧ ∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax →
      ∀(a ε Δ ν C q : ℝ) (i : ℕ),i≤n → 51/100<a → a≤1 → 0≤ε → ε≤1/1000 →
      0≤Δ → Δ≤1/8 → 0<ν → 0≤C →
      ∀{Slot : Type} (B : Batch M H Label Slot (Z^d) a ε
        (cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i),
      B.slots.card≤N → B.binWidth=binWidth →
      B.rows.Nonempty →
      (∀u∈B.rows,rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (physical M H (fun u : FreeRow=>u.val) B.profile B.upper B.widths B.external (Z^d)) u=q) →
      (∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
        Moments (B.fiber bin j J K hne) Δ (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*Z^momentCost) (Z^heightCost) εm) →
      (B.rows.card:ℝ)≤K*C*Z^(logCost+heightCost+momentCost)*(Z^d)^(adaptiveRowExponent (2*a-1) q Δ ε εm B.mesh ν) := by
  obtain ⟨KB,hKB,hbalanced⟩ := balanced_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb counts
  obtain ⟨KH,hKH,hhigh⟩ := high_source_count_from_raw_moments
    M H hH S φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
    Label N n dmin dmax τ logCost heightCost momentCost binWidth hdmin hdmax hτ hl hh hb counts
  refine ⟨max KB KH,lt_of_lt_of_le hKB (le_max_left _ _),?_⟩
  filter_upwards [hbalanced,hhigh,eventually_ge_atTop (1:ℝ)] with Z hb hh hZ
  intro d hd hd' a ε Δ ν C q i hi ha ha' hε hε' hΔ hΔ' hν hC Slot B hslots hbin hne hq hmom
  by_cases hδ : 2*a-1≤5/6
  · simp only [ite_eq_left hδ] at hmom
    have hc := hb d hd hd' a ε Δ ν C q i hi ha hδ ha' hε hε' hΔ hΔ' hν hC B hslots hbin hne hq hmom
    simp only [adaptiveRowExponent,ite_eq_left hδ]
    exact hc.trans (by gcongr;exact le_max_left _ _)
  · simp only [ite_eq_right hδ] at hmom
    have hc := hh d hd hd' a ε Δ C q i hi (lt_of_not_ge hδ) ha' hε hε' hC B hslots hbin hmom
    simp only [adaptiveRowExponent,ite_eq_right hδ]
    exact hc.trans (by gcongr;exact le_max_right _ _)

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2892

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorExponent
Source SHA256: a8575c7e463a5a671a00c3a0a8ddc16f789d67767237d2ae7b8b37000f4127f3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2893


namespace OAI

noncomputable section
namespace SevenEighths.ProbeHighRowFamily

lemma adaptive_mixed_saving (N : ℕ) (a q Δ ε εm slotMesh ν ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1/2<a) (ha' : a≤1) (hq : 0≤q) (hq' : q≤(2*a-1)/2)
    (hΔ : 0≤Δ) (hΔ' : Δ≤1/8) (hε : 0≤ε) (hεm : 0≤εm)
    (hslot : 0≤slotMesh) (hν : 0≤ν)
    (hcount : 159*ε+εm+slotMesh+7*ν≤1/32)
    (hζ : 0≤ζ) (hζ' : ζ≤3/16) (hv : v≤13/16+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ) (he : 0≤e) (heps : 0≤eps)
    (hbudget : (13/16)*(159*ε+εm+slotMesh+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+overhead+saving≤49/440640) :
    mixedSourceExponent a v d (adaptiveRowExponent (2*a-1) q Δ ε εm slotMesh ν) q+
      ProbeCentralExponent.realLoss N v e eps loss mesh+overhead≤3/16+Δ-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hx : 0≤q/(2*a-1) := div_nonneg hq hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0≤159*ε+εm+slotMesh+7*ν := by positivity
  have haeq : (1+(2*a-1))/2=a := by ring
  have hqeq : (2*a-1)*(q/(2*a-1))=q := mul_div_cancel₀ q hδ.ne'
  have hr := ProbeCentralExponent.realLoss_bound N v e eps loss mesh (by linarith) he heps
  by_cases hd : 2*a-1≤5/6
  · have hb := balanced_mixed_saving (2*a-1) (q/(2*a-1)) Δ (159*ε+εm+slotMesh+7*ν)
      ζ μ v d (ProbeCentralExponent.realLoss N v e eps loss mesh+overhead) saving
      hδ.le hd hx hx' hΔ hΔ' hl hcount hζ hv hμ hdv (by linarith)
    rw [haeq,hqeq] at hb
    simpa only [adaptiveRowExponent,ite_eq_left hd,add_assoc] using hb
  · have hhl : 0≤78*ε+εm := by positivity
    have hh := high_mixed_margin (2*a-1) q Δ (78*ε+εm) ζ μ v d
      (le_of_lt (lt_of_not_ge hd)) (by linarith) hq' hhl (by linarith)
      hζ hv hμ hdv
    rw [haeq] at hh
    simp only [adaptiveRowExponent,ite_eq_right hd]
    simp only [add_assoc] at hh ⊢
    linarith

lemma central_class_exponent_identity (N : ℕ) (a v d R q e eps loss mesh overhead : ℝ) :
    ((25/48)*a-181/300+(105/8)*e)+
      (overhead+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6)=
    mixedSourceExponent a v d R q+ProbeCentralExponent.realLoss N v e eps loss mesh+overhead := by
  unfold mixedSourceExponent ProbeCentralExponent.sourceExponent ProbeCentralExponent.realLoss
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2893

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NormalizedTransport
Source SHA256: f015d2f28b576fdf9cf4be14fd34bb267c5cbb0e9a0d953b2372b632528d347b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2894



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem transportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

lemma normalized_central_transport (A P C F N : ℂ) (a b v : ℝ)
    (ha : ‖A-P-C‖≤a) (hb : ‖P/N-F‖≤b) (hv : ‖N⁻¹‖≤v) (ha0 : 0≤a) :
    ‖A/N-F-C/N‖≤a*v+b := by
  calc
    _ = ‖(A-P-C)*N⁻¹+(P/N-F)‖ := by congr 1;simp only [div_eq_mul_inv];ring
    _ ≤ ‖(A-P-C)*N⁻¹‖+‖P/N-F‖ := norm_add_le _ _
    _ ≤ a*v+b := by rw [norm_mul];gcongr

theorem actual_normalized_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := transportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha height/normer‖≤
        C*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+nu)+Z^(-saving+nu)+
          Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+
          Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨Ca,hCa,n,hn,hcanonical⟩ := canonical_probe_exists_ray_cube M H hH K e δ a b B ζ saving τ
    he he' hδ hδ' hζ hζ' hτ ha (ha.trans_le hab) hB hβ S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨Cn,hCn,hnormalizer⟩ := actual_ray_normalizer_inverse M H hH S hS a b ha hab ell
    (fun j=>hmin.trans_le (hell j)) hellsum W hW hcompact hsupp (fun j y=>(hWB j y).1) hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨n,hn,?_⟩
  intro η
  have hbetal := HeckeZeroSupremum.beta_le_one
  obtain ⟨Cp,hCp,hprincipal⟩ := ProbePrincipalNormalized.actual_ray_principal_comparison M H hH η S hS
    a b B ellMin ha hab hB hmin ell hell hellinj hellsum W hW hcompact hsupp hWB hne
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 e nu he he'.le hnu
    (by linarith) (by linarith)
  let D : ℝ := Ca*(η.modulus.absNorm:ℝ)^2*Cn
  have hD : 0≤D := by dsimp [D];positivity
  refine ⟨D+Cp,by positivity,?_⟩
  filter_upwards [hcanonical,hnormalizer,hprincipal,
    power_pool_tuples_eventually_injective (RayQuotient.identityClass M H) S
      (fun _ : Fin K=>a) (fun _=>b) ell (fun _=>ha) (fun _=>hab) hellinj,
    eventually_gt_atTop (0:ℝ)] with Z hcan hnorm hprincipal hdis hZ
  dsimp only at hnorm hprincipal ⊢
  let Yp : Fin K→ℝ := fun j=>Z^(ell j)
  let T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := transportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWS (j : Fin K) : Function.support (WC j)⊆Icc a b := by
    intro y hy
    apply Ioo_subset_Icc_self (hsupp j _)
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin K) (y : ℝ) : ‖WC j y‖≤B := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  have hpool (j : Fin K) (P : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P∈T j) : (P.val.absNorm:ℝ)≤b*Z^(ell j) := by
    have hh := (pool_norm_bounds (RayQuotient.identityClass M H) S ha.le hab
      (Real.rpow_pos_of_pos hZ (ell j)) P hP).2
    simpa only [mul_comm] using hh
  obtain ⟨idx,grid,hlabels,hbins,hray,herror⟩ := hcan η T hT hdis ell (fun j=>(hmin.trans_le (hell j)).le)
    hellsum hpool WC hWS hWCB
  refine ⟨hnorm.1,idx,grid,hlabels,hbins,hray,?_⟩
  have hh := normalized_central_transport _ _ _ _ _ _ _ _ herror hprincipal.2 hnorm.2 (by positivity)
  apply hh.trans
  have heq : (Ca*(η.modulus.absNorm:ℝ)^2*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e)+Z^(-saving)))*(Cn*Z^nu)=
      D*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+nu)+Z^(-saving+nu)) := by
    rw [Real.rpow_add hZ (HeckeZeroSupremum.beta-11/16-63/800+8*e) nu,
      Real.rpow_add hZ (-saving) nu]
    dsimp [D]
    ring
  rw [heq]
  have h1 : D≤D+Cp := by linarith
  have h2 : Cp≤D+Cp := by linarith
  calc
    _ ≤ (D+Cp)*(Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+nu)+Z^(-saving+nu))+
      (D+Cp)*(Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)+Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)) := by
      gcongr
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2894

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NormalizedTransportSaving
Source SHA256: e650227d9334b227c5c3417a26183a5782be3f8e2c59d2278b1bf68cb3ea740e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2895


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem transportSavingPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_normalized_probe_transport_saving (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0<sigma)
    (_hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*ellMin) (hlarge : sigma+nu≤saving+3/16) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := transportSavingPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z-
        finiteCentralCubeRows S hS hmax η (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) T hT WC Yp
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,hbound⟩ := actual_normalized_probe_transport M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨C,hC,hb⟩ := hbound η
  refine ⟨4*C,by positivity,?_⟩
  filter_upwards [hb,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  dsimp only at hb ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := hb
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,herror.trans ?_⟩
  have h1 : Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e+nu)≤Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h2 : Z^(-saving+nu)≤Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h3 : Z^(HeckeZeroSupremum.beta-11/16-17/48000+nu)≤Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have h4 : Z^(HeckeZeroSupremum.beta-11/16+e-(7/8)*ellMin)≤Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ C*(4*Z^(HeckeZeroSupremum.beta-11/16-sigma)) :=
      mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2895

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorTransport
Source SHA256: 43c466c09b82882eff832604a9371bfc03ac6894aaefbff9f8903bc7e680306e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2896




namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary CompletedGauss
open ProbeRaySlots PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
private theorem nonfloorTransportPoolOutside (S : Finset (Ideal O)) (K : ℕ) (a b : ℝ) (Y : Fin K→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S a b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S a b (Y j) P).mp hP |>.2.2.2

theorem actual_nonfloor_probe_transport (K : ℕ) (e δ a b B ζ saving τ ellMin nu : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2) (hζ : 0<ζ) (hζ' : ζ≤1/48) (hτ : 0<τ)
    (ha : 0<a) (hab : a≤b) (hB : 0≤B) (hmin : 0<ellMin) (hnu : 0<nu)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S)
    (ell : Fin K→ℝ) (hell : ∀j,ellMin≤ell j) (hellinj : Function.Injective ell) (hellsum : ∑j,ell j=1/6)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Ioo a b) (hWB : ∀j y,0≤W j y ∧ W j y≤B) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (sigma : ℝ) (hsigma : 0<sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*ellMin) (hlarge : sigma+nu≤saving+3/16)
    (eps R dmin dmax rmin ε κ cost mesh margin loss : ℝ)
    (heps : 0<eps) (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax)
    (hrmin : 0<rmin) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh) (hmargin : 0<margin)
    (hphasebudget : 8*e*R+κ≤ε) (hphasegap : ε<rmin*mesh)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (hcap : 13/16+ζ≤dmax-margin)
    (helllo : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (hfloorbudget : 2*ζ+26*e+(K+8)*eps+loss+mesh/6+nu+sigma≤7/1200) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
      let hT := nonfloorTransportPoolOutside M H S K a b Yp
      let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let alpha : FreeRow→ℝ := fun u=>51/100+e*grid u
      let height : FreeRow→ℝ := fun u=>(3*idx u+1:ℕ)*Z^τ
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z-
        finiteCentralCubeRows S hS hmax η
          (supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid) T hT WC Yp
          W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e alpha height/normer‖≤
        C*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨n,hn,htransport⟩ := actual_normalized_probe_transport_saving M H hH K e δ a b B ζ saving τ ellMin nu
    he he' hδ hδ' hζ hζ' hτ ha hab hB hmin hnu hβ S hS hmax hfirst ell hell hellinj hellsum
    W hW hcompact hsupp hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    sigma hsigma hgeometric hprincipal hwindow hlarge
  obtain ⟨Cf,hCf,hfloor⟩ := actual_floor_rows_saving M H hH K n e eps a b B R dmin dmax rmin τ ε κ cost mesh
    (1/100) margin loss he he' heps ha hab hB hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
    (by norm_num) hphasebudget hphasegap hmargin hheight hloss S hS hfirst hmax ell hellinj helllo hellhi
    W hsupp hW hWB hcompact hne hellsum W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1
    nu hnu ζ sigma hζ.le (by linarith) hsigma hfloorbudget
  refine ⟨n,hn,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  let C := Ct+Cf*(η.modulus.absNorm:ℝ)^(2*eps)
  have hC : 0<C := by dsimp [C];positivity
  refine ⟨C,hC,?_⟩
  filter_upwards [htransport,hfloor η,eventually_ge_atTop (1:ℝ)] with Z ht hf hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  let Yp : Fin K→ℝ := fun j=>Z^(ell j)
  let T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S a b (Yp j)
  let hT := nonfloorTransportPoolOutside M H S K a b Yp
  let WC : Fin K→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let rows := rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))
  let floors := supportedFloorRows S hmax rows grid
  have hrows : ∀u∈floors,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(dmax-margin) := by
    intro u hu
    rcases (mem_supportedFloorRows S hmax rows grid u).mp hu with ⟨hur,hcal,hg⟩
    have hm := mem_rowBand.mp hur
    exact ⟨hm.1,hm.2.1,hcal,hm.2.2.le.trans (Real.rpow_le_rpow_of_exponent_le hZ hcap)⟩
  have hnorms : ∀u∈floors,rowNorm u≤Z^((13/16:ℝ)+ζ) := by
    intro u hu
    exact (mem_rowBand.mp ((mem_supportedFloorRows S hmax rows grid u).mp hu).1).2.2.le
  have hfloorbin : ∀u∈floors,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+2*e := by
    intro u hu
    have hg := ((mem_supportedFloorRows S hmax rows grid u).mp hu).2.2
    have hh := (hbins u).2.2.2.2.1
    simpa only [hg,Nat.cast_zero,mul_zero,add_zero] using hh
  have hb := (hf dmax hdRange le_rfl (13/16+ζ) (by linarith) le_rfl floors hrows hnorms idx
    (fun u hu=>(hlabels u).2.1) hfloorbin).2
  have hsplit := finiteCentralCubeRows_supported_split S hS hmax η rows T hT WC Yp W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e grid (fun u=>(3*idx u+1:ℕ)*Z^τ)
  change _≤Ct*Z^(HeckeZeroSupremum.beta-11/16-sigma) at herror
  rw [hsplit] at herror
  have hh := normalized_nonfloor_error _ _ _ _ _ _ _ herror hb
  apply hh.trans
  have hp : Z^(3/16-sigma)≤Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  calc
    _ ≤ Ct*Z^(HeckeZeroSupremum.beta-11/16-sigma)+
      (Cf*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by gcongr
    _ = _ := by dsimp [C];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2896

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.TargetPrincipal
Source SHA256: f1a27c6555c3b0b9562b26ee1de00cc8e1f200dad3007b5daa7934827bc3ff27
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2897


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter UniqueFactorizationMonoid
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical CanonicalQuadraticSieve CanonicalRowCompletion
local notation "O" => HeckeFamily.O
local notation "λ₀" => ConcretePrimeRowBridge.goodLambda

def targetPrincipalSupport (η : Character) : Finset (Ideal O) :=
  (normalizedFactors (η.modulus*Ideal.span {rowMaskElement}*Ideal.span {(72:O)})).toFinset

lemma targetPrincipalSupport_prime (η : Character) : ∀P∈targetPrincipalSupport η,Prime P := by
  intro P hP
  exact prime_of_normalized_factor P (Multiset.mem_toFinset.mp hP)

lemma inverse_target_elementCoeff (η : Character) (u : FreeRow) (n : O) :
    elementCoeff (targetRow η u).inverse n=
      rowTwist (HeckeRowClosure.elementHom ((fixedSourcePrincipal ∅ (by simp)).product η.inverse))
        rowMaskElement 1 u.val n := by
  rw [elementCoeff_inverse]
  unfold targetRow
  rw [elementCoeff_product,elementCoeff_inverse,mul_inv_rev,inv_inv,rawRow_elementCoeff]
  change (elementCoeff (fixedSourcePrincipal ∅ (by simp)) n *
    idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})) * (elementCoeff η n)⁻¹=
    elementCoeff ((fixedSourcePrincipal ∅ (by simp)).product η.inverse) n *
      idealRowHom (rowMaskElement^6*1^4*u.val) (Ideal.span {n})
  rw [elementCoeff_product,elementCoeff_inverse]
  ring

theorem principal_target_row_norm_bound (η : Character) (u : FreeRow)
    (hs : Supported (Ideal.span {u.val})) (hp : (targetRow η u).residue=1) :
    rowNorm u≤(HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ) := by
  obtain ⟨v,hv⟩ := exists_supported_primary_unit u.val hs
  let r : O := (v:O)*u.val
  have hspan : (Ideal.span {r}:Ideal O)=Ideal.span {u.val} :=
    Ideal.span_singleton_mul_left_unit v.isUnit u.val
  have hr : Supported (Ideal.span {r}) := hspan.symm ▸ hs
  have hx : (1:O)^4*u.val=(v⁻¹:Oˣ).val*λ₀^0*(2:O)^0*r := by simp [r]
  let η0 := (fixedSourcePrincipal ∅ (by simp)).product η.inverse
  have hmod : η0.modulus=η.modulus := by
    change (1:Ideal O)⊓η.modulus=η.modulus
    simp
  have hinv : (targetRow η u).inverse.residue=1 := by
    change (targetRow η u).residue⁻¹=1
    rw [hp,inv_one]
  have hfixed := HeckeRowNonprincipal.principal_row_fixed_support η0 (targetRow η u).inverse
    rowMaskElement 1 u.val rowMaskElement_ne_zero (dvd_mul_left _ _) (dvd_mul_right _ _)
    v⁻¹ 0 0 r hr hv hx (inverse_target_elementCoeff η u) hinv (fun P _=>hspan.symm ▸ u.property.2 P)
  rw [hmod] at hfixed
  have hn := HeckeExceptionalRows.row_norm_bound (targetPrincipalSupport η) (targetPrincipalSupport_prime η) hfixed
  rw [hspan] at hn
  unfold rowNorm
  exact_mod_cast hn

theorem excluded_target_nonprincipal_eventually (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀u : FreeRow,Z^d≤rowNorm u →
      Supported (Ideal.span {u.val}) → ∀S : Finset (Ideal O),∀hS : ∀P∈S,Prime P,
      ((targetRow η u).excludePrimes S hS).residue≠1 := by
  filter_upwards [(tendsto_rpow_atTop hd).eventually
    (eventually_gt_atTop (HeckeExceptionalRows.bound (targetPrincipalSupport η):ℝ))]
    with Z hZ u hu hs S hS
  intro hp
  have hp' := (HeckeFiniteDeletion.principal_iff_of_mask _ _ (excludePrimes_mask (targetRow η u) S hS)).mp hp
  exact not_lt_of_ge (principal_target_row_norm_bound η u hs hp') (hZ.trans_le hu)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2897

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.DetectorReady
Source SHA256: 5609221f1f947d7cc23f18dfb933fec07bd3f30b2ccf744eaeb60c570be4c5a2
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2898


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def sourceConductorConstant (S : Finset (Ideal O)) (η : Character) : ℕ :=
  conductorConstant*(∏P∈S,P).absNorm*(η.modulus.absNorm+1)+conductorConstant*M.absNorm

theorem source_ray_conductor (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (u : FreeRow) (j : Sum Bool (RayQuotient.Characters M H)) :
    (sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm≤
      sourceConductorConstant M S η*(Ideal.span {u.val}:Ideal O).absNorm := by
  cases j with
  | inl b =>
    cases b with
    | false =>
      apply (targetRow_excluded_conductor S hS η u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
    | true =>
      apply (rowCharacter_conductor S hS u).trans
      unfold sourceConductorConstant
      ring_nf
      omega
  | inr θ =>
    apply (ProbeRayCharacterFamily.raw_twisted_conductor M H hH u θ).trans
    unfold sourceConductorConstant
    ring_nf
    omega

theorem source_ray_nonprincipal_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀U : ℝ,∀u∈rowBand (Z^d) U,
      (calibrationForSet S hmax).residueMonoid u.val≠0 →
      ∀j,(sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue≠1 := by
  filter_upwards [excluded_target_nonprincipal_eventually η d hd,
    ProbeRayCharacterFamily.large_supported_twists_eventually M d hd] with Z htarget hray
  intro U u hu hc j
  have hs := calibration_nonzero_supported S hmax hS.bad u.val hc
  have hnorm := (mem_rowBand.mp hu).2.1
  cases j with
  | inl b =>
    cases b with
    | false => exact htarget u hnorm hs S hS.prime
    | true => exact calibrated_row_nonprincipal S hS.prime hmax hS.bad u (mem_rowBand.mp hu).1 hc
  | inr θ => exact hray u hnorm hs H hH θ

theorem source_ray_maximum_eventually (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (d : ℝ) (hd : 0<d) :
    ∀ᶠ Z : ℝ in atTop,∀U : ℝ,∀u∈rowBand (Z^d) U,
      (calibrationForSet S hmax).residueMonoid u.val≠0 →
      ∃hnp : ∀j,(sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue≠1,
      ∀T : ℝ,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) T=
        HeckeDetectorZeros.zeroMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) hnp T := by
  filter_upwards [source_ray_nonprincipal_eventually M H hH S hS hmax η d hd] with Z hZ
  intro U u hu hc
  exact ⟨hZ U u hu hc,fun T=>detectorMaximum_eq_nonprincipal _ _ T⟩

theorem source_ray_conductor_eventually (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (ν : ℝ) (hν : 0<ν) :
    ∀ᶠ Z : ℝ in atTop,∀(u : FreeRow) (d : ℝ),rowNorm u≤Z^(d-ν) →
      ∀j,((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤Z^d := by
  have hh := HeckeDyadic.constant_absorbed_eventually (sourceConductorConstant M S η:ℝ) ν hν
  filter_upwards [hh,eventually_gt_atTop (0:ℝ)] with Z hC hZ
  intro u d hu j
  have hq : ((sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j).modulus.absNorm:ℝ)≤
      (sourceConductorConstant M S η:ℝ)*rowNorm u := by
    unfold rowNorm
    exact_mod_cast source_ray_conductor M H hH S hS η u j
  apply hq.trans
  calc
    _ ≤ Z^ν*Z^(d-ν) := mul_le_mul hC hu (by unfold rowNorm;positivity) (Real.rpow_nonneg hZ.le _)
    _ = Z^d := by rw [←Real.rpow_add hZ];congr 1;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2898

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CubeSupportedWitness
Source SHA256: e0745ae7b7c7d38c8f35cea95a919a5361d5a6193c07a978e4c6f0441addc478
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2899



namespace OAI

noncomputable section
open scoped Classical Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
open HeckeDetectorSupportedWitness
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
variable (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) (η : Character)

theorem supported_witnesses_from_source_cube (dmin dmax τ ε e κ heightCost margin : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin)
    (hbudget : 12*e*((22 : ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠ Z : ℝ in atTop,∀ d : ℝ,dmin≤d → d≤dmax →
      ∀ (U : ℝ) (rows : Finset FreeRow),rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
      let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
      ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
        (∀u : rows,detectorMaximum (χ u) (3*(i+1 : ℕ)*(Z^τ))<a+2*e) →
        (∀u : rows,a≤detectorMaximum (χ u) ((3*i : ℕ)*Z^τ)) →
        ∀ tstar : ℝ,1≤tstar → tstar≤3/2 →
          Nonempty (∀u : rows,SupportedWitness (χ u) (Z^d) a ε tstar (Z^τ)
            ((Z^d)^(τ/(2*dmax))) i) := by
  obtain ⟨Z0,hdet⟩ := actual_supported_witness_family dmin dmax τ ε e κ heightCost I
    hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hbudget
  filter_upwards [eventually_ge_atTop Z0,
    source_ray_nonprincipal_eventually M H hH S hS hmax η (1/100) (by norm_num),
    source_ray_conductor_eventually M H hH S hS.prime η margin hmargin] with Z hZ hnp hcond
  intro d hd hd' U rows hrows hcal hrow
  dsimp only
  intro a i hi ha ha' hnext hcurrent tstar ht ht'
  let χ := fun u : rows => sourceDetectorFamily S hS.prime η u.val (rayCubeFamily M H hH u.val)
  have hχ : ∀u j,(χ u j).residue≠1 := fun u=>hnp U u.val (hrows u.property) (hcal u.val u.property)
  have heq (u : rows) := detectorMaximum_eq_nonprincipal (χ u) (hχ u)
  exact hdet Z hZ d hd hd' χ hχ a i hi ha ha'
    (fun u=>by rw [←heq u];exact hnext u)
    (fun u=>by rw [←heq u];exact hcurrent u)
    (fun u=>hcond u.val d (hrow u.val u.property)) tstar ht ht'

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2899

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourceBatch
Source SHA256: 39c56d463054b01be89d79179a73e6efc74c4ffcc41aacf2cbd33565e04b0b84
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2900



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_source_batch (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin) (hm : 0≤mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw,eventually_ge_atTop (1:ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u=>hnext u.val u.property) (fun u=>hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0,h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u∈rows) : rowNorm u≤Z^d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp,hwm,hsp⟩ := physical_slot_widths ell d dmin mesh hdmin hd (hd'.trans hdtop) hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z^d) a ε tstar (Z^τ)
    ((Z^d)^(τ/(2*dmax))) i (fun u hu=>w ⟨u,hu⟩) hnorm
    Finset.univ W upper (fun j=>ell j/d) z mesh binWidth hm hb (fun j _=>hwp j) (fun j _=>hwm j) hsp
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro u hu j
  dsimp [B,retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2900

/-! Original module: OAI.NumberTheory.DirichletL.Detector.SourceAmplitudeClasses
Source SHA256: f5ac6fcdf19de4d801affcfb69e5102f40e624c56dca678eda6a16e45c447291
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2901



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_source_amplitude_batches (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0<dmin) (hdmax : dmin≤dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*heightCost)
    (hε : 0<ε) (he : 0<e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤heightCost)
    (hmargin : 0<margin) (hm : 0≤mesh) (hb : 0<binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤d → d≤dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤I → 51/100<a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0<ell j) → (∀j,ell j≤dmin*mesh) → (∑j,ell j)=1/6 →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
      W upper (fun j=>ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=>ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=>ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=>ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hdtop hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=>u.val)
    W upper (fun j=>ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=>ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=>ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hcut := HeckeDetectorAdaptiveCutoff.cutoff_bounds (2*a-1) q (by linarith)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=>hcal u (hsub hu)) (fun u hu=>hrow u (hsub hu)) a i hi ha ha'
      (fun u hu=>hnext u (hsub hu)) (fun u hu=>hcurrent u (hsub hu))
      (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=>ell j/d) Q bin u hu'
end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2901

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDictionary
Source SHA256: 44a8d09efc3e3ac4a43786d42f9ca4ad7e48849fd26f10681c54994536077ede
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2902



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorPhysicalSelection
open HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O)
variable (H : Subgroup (O ⧸ M)ˣ)

lemma source_physical_amplitude {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) (j : Fin N) :
    physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d) u j=
      HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z := by
  unfold physical
  rw [physical_slot_scale ell Z d hZ hd j]

lemma source_rowMean_eq {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (u : FreeRow) :
    rowMean Finset.univ (Z^d) ((2*a-1)/2) mesh (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) u=
      weightedMean Finset.univ (fun j=>ell j/d)
        (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z)) := by
  unfold rowMean
  simp_rw [physical_slot_scale ell Z d hZ hd,source_physical_amplitude M H ell W Z d b z hZ hd]
  rw [show (2*a-1)/2=a-1/2 by ring]

lemma source_amplitude_class_mean {N : ℕ} (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d b a mesh : ℝ) (z : ℂ) (hZ : 0<Z) (hd : d≠0) (hm : 0<mesh)
    (rows : Finset FreeRow) (bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh)
    (u : FreeRow)
    (hu : u∈amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d)
      (physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)) bin) :
    weightedMean Finset.univ (fun j=>ell j/d)
      (fun j=>HeckePrimeAmplitudeBins.amplitude (Z^(ell j)) (a-1/2) mesh
        (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Z^(ell j)) z))=
      classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin := by
  rw [←source_rowMean_eq M H ell W Z d b a mesh z hZ hd u]
  exact rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2) mesh hm (fun j=>ell j/d) _ bin u hu

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2902

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorMoments
Source SHA256: 1a858768eee8f4568ac011680d3ec6b742228f75b21e8a24f39d5d28f759788c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2903



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

def SourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C height εm : ℝ) : Prop :=
  ∀q : ℝ,∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=>ell j/d) → B.profile=W → B.upper=(fun _=>b) → B.external=(fun _=>z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Moments (B.fiber bin j J K hne) Δ c κ C height εm

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2903

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentMono
Source SHA256: b73a12c3687d88a54255a725941263e24c42712db94bb17f07d5f6890a4d97d7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2904


namespace OAI

noncomputable section
open scoped Classical BigOperators
open Set
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeHighRowFamily

lemma rawMoment_mono_constant {data : RowData} {W : ℝ→ℂ} {c κ C D : ℝ}
    (h : RawMoment data W c κ C) (hCD : C≤D) : RawMoment data W c κ D := by
  intro H X hH hX hsize rows hrows
  apply (h H X hH hX hsize rows hrows).trans
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCD (by linarith)) (by positivity)

lemma moments_mono_constant {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ}
    {Label Slot : Type*} {U a ε tstar T allowance : ℝ} {i : ℕ}
    {F : Fiber M H Label Slot U a ε tstar T allowance i}
    {Δ c κ C D height εm : ℝ} (hU : 0≤U) (h : Moments F Δ c κ C height εm) (hCD : C≤D) :
    Moments F Δ c κ D height εm := by
  constructor
  · intro n hn s hs t ht
    exact ⟨rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).1 hCD,
      rawMoment_mono_constant (h.inverse_raw n hn s hs t ht).2 hCD⟩
  · intro selected hsel hcap1 hcap2 n hn s hs t ht
    exact (h.inverse_marked selected hsel hcap1 hcap2 n hn s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  · intro selected hsel hcap j k hj s hs t ht
    exact (h.plain_marked selected hsel hcap j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))
  · intro j k hj s hs t ht
    exact (h.plain_unmarked j k hj s hs t ht).trans
      (mul_le_mul_of_nonneg_right hCD (Real.rpow_nonneg hU _))

lemma sourceMomentsAt_mono_constant (M : Ideal O) [NeZero M]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)
    {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (Δ c κ C D height εm : ℝ) (hZ : 0≤Z) (hCD : C≤D)
    (h : SourceMomentsAt M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z Δ c κ C height εm) :
    SourceMomentsAt M H hH S hS η rows ell W Z d a ε τ dmax b slotMesh binWidth i z Δ c κ D height εm := by
  intro q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  exact moments_mono_constant (Real.rpow_nonneg hZ _)
    (h q B hrows hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne) hCD

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2904

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyMomentInput
Source SHA256: 74edb2e0b51c5913639bde386c51c45083817dabfd1e7fbf4afa46f693436ba7
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2905



namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
  ∀rows : Finset FreeRow,∀d a : ℝ, (1/200:ℝ)≤d → d≤7/8 → 51/100<a → a≤1 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im|≤height →
    SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z Δ
      (if 2*a-1≤5/6 then counts.cB else counts.cH)
      (if 2*a-1≤5/6 then counts.kB else counts.kH) C height D.t

lemma SourceMomentBound.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : CountParameters F.modulus ⊤ D.t} {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤Z) (h : SourceMomentBound F counts η Z τ C height) (hC : C≤C') :
    SourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh
  exact sourceMomentsAt_mono_constant F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell
    (fun _ y=>(F.w y:ℂ)) Z d a D.ε τ (7/8) 2 D.t D.t i z Δ _ _ C C' height D.t
    hZ hC (h rows d a hd hd' ha ha' hrows i z hz hzh)

def RawMomentInput : Prop :=
  ∀_hβ : (7/8:ℝ)<HeckeZeroSupremum.beta,
    ∀D : HighData (HeckeZeroSupremum.beta-7/8),∀F : SourceData D,
    ∀counts : CountParameters F.modulus ⊤ D.t,
    ∃J : ℝ,0≤J ∧ ∀η : Character,∃C : ℝ,0<C ∧
      ∀τ : ℝ,0<τ → τ≤1 → ∀ᶠZ : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

lemma polynomial_height_absorption (C Z τ J t : ℝ)
    (hC : 0≤C) (hZ : 1≤Z) (hτ : 0≤τ) (hJ : 0≤J) (hbudget : 2*τ*(1+J)≤t) :
    C*(1+Z^(2*τ))^J≤(C*2^J)*Z^t := by
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hscale : 1≤Z^(2*τ) := Real.one_le_rpow hZ (by positivity)
  calc
    _≤C*(2*Z^(2*τ))^J := by gcongr;linarith
    _=(C*2^J)*Z^(2*τ*J) := by
      rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) (Real.rpow_nonneg hZp.le _),←Real.rpow_mul hZp.le]
      ring
    _≤(C*2^J)*Z^t := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

theorem raw_input_chosen_height (h : RawMomentInput) (hβ : (7/8:ℝ)<HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-7/8)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) :
    ∃τ : ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200:ℝ)*D.cost ∧ τ<D.t ∧
      2*τ≤D.t ∧ τ*(2+4*D.eps)<D.t ∧
      ∀η : Character,∃C : ℝ,0<C ∧ ∀ᶠZ : ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)) := by
  obtain ⟨J,hJ,hbound⟩ := h hβ D F counts
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩ := D.height_choice J hJ
  have htau1 : τ≤1 := by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩ := hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith) (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ hτJ)

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2905

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorClass
Source SHA256: 83326184c6165e3c99f93c957f60af2c99d21ac557d0a10be0cce485a55cfb73
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2906



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

omit [NeZero M] in
lemma nonfloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem actual_nonfloor_class_from_raw_moments (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost) :
    ∃cB κB cH κH C : ℝ,0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → 51/100<a → a≤1 → 0≤C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z Δ
        (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=>ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
      rows'.Nonempty → 0≤q ∧ q≤(2*a-1)/2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(logCost+heightCost+momentCost+
            d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
            v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) := by
  have hdmax0 : 0<dmax := hdmin.trans_le hdRange
  obtain ⟨cB,κB,cH,κH,K,hcB,hcB1,hκB,hcH,hcH1,hκH,hK,hcount⟩ :=
    adaptive_source_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
      hdmin hdmax0 hτ hlog hMomentHeight hmesh
  obtain ⟨C,hC,hphysical⟩ := actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1/100) margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh (by norm_num)
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  refine ⟨cB,κB,cH,κH,C*K,hcB,hcB1,hκB,hcH,hcH1,hκH,mul_pos hC hK,?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η,hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=>ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0<ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
      (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi hellsum W (fun _=>b) (fun _=>z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0 B
    (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) mesh hmesh (fun j=>ell j/d) Q bin
    (by linarith) (fun j _=>div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum Finset.univ ell d hellsum];positivity) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
    (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu=>hrows u (hsub hu)) (fun u hu=>hnorm u (hsub hu)) hcard i hi
    (fun u hu=>hnext u (hsub hu)) t ht
    (fun u hu=>source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost+heightCost+momentCost+
      d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6=
      (logCost+heightCost+momentCost)+(d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) by ring,
    Real.rpow_add hZp (logCost+heightCost+momentCost)]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2906

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyClass
Source SHA256: 344795c52e44f4f3dcafe367e387a30d6a78c9dabd5a0c69c16f35b60498d5c0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2907



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_class_from_raw_moments (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost) (counts : CountParameters M H εm) :
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → 51/100<a → a≤1 → 0≤C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=>ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
      rows'.Nonempty → 0≤q ∧ q≤(2*a-1)/2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(logCost+heightCost+momentCost+
            d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
            v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) := by
  have hdmax0 : 0<dmax := hdmin.trans_le hdRange
  obtain ⟨K,hK,hcount⟩ :=
    adaptive_source_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C,hC,hphysical⟩ := actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1/100) margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh (by norm_num)
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro η
  have hbatches := actual_source_amplitude_batches M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η,hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  have hd0 : 0<d := hdmin.trans_le hd
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=>ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0<ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
      (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi hellsum W (fun _=>b) (fun _=>z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0 B
    (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) mesh hmesh (fun j=>ell j/d) Q bin
    (by linarith) (fun j _=>div_nonneg (hellpos j).le hd0.le)
    (by rw [source_slot_length_sum Finset.univ ell d hellsum];positivity) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
    (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu=>hrows u (hsub hu)) (fun u hu=>hnorm u (hsub hu)) hcard i hi
    (fun u hu=>hnext u (hsub hu)) t ht
    (fun u hu=>source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost+heightCost+momentCost+
      d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6=
      (logCost+heightCost+momentCost)+(d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-2/75+q/6+mesh/6) by ring,
    Real.rpow_add hZp (logCost+heightCost+momentCost)]
  ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2907

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorArithmetic
Source SHA256: 6fb297201464d508daf2d948f089fadf908b2a8622c2d2d893c079a27188b068
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2908


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640) :
    ∃cB κB cH κH C : ℝ,0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤13/16+ζ → d-v≤μ →
      51/100<a → a≤1 → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e)) := by
  obtain ⟨cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,hclass⟩ :=
    actual_nonfloor_class_from_raw_moments M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0≤cardCost := by dsimp [cardCost];positivity
  refine ⟨cB,κB,cH,κH,(cardCost+1)*C,hcB,hcB1,hκB,hcH,hcH1,hκH,by positivity,?_⟩
  intro η
  filter_upwards [hclass η,eventually_gt_atTop (1:ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))
  have hb : 0≤bound := by dsimp [bound];positivity
  have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
    (nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
    (by linarith) (fun j=>ell j/d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent t ht hmom bin hne
      dsimp only at hp
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
      have hs := adaptive_mixed_saving N a q Δ ε εm R ν ζ μ v d e eps loss mesh
        (logCost+heightCost+momentCost) saving (by linarith) ha' hp.1 hp.2.1 hΔ hΔ1 hε.le hεm.le
        hR hν.le hcount hζ hζ1 hv' hμ hdv he.le heps.le hfinal
      have hid := central_class_exponent_identity N a v d
        (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) q e eps loss mesh (logCost+heightCost+momentCost)
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost*bound := hpart
    _ ≤ (cardCost+1)*bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2908

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyArithmetic
Source SHA256: c5211fe2bbd37895cbad269e5f4508776e71781c28fc00461b2f3d654cf50c18
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2909



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640) (counts : CountParameters M H εm) :
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤13/16+ζ → d-v≤μ →
      51/100<a → a≤1 → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e)) := by
  obtain ⟨C,hC,hclass⟩ :=
    actual_nonfloor_class_from_raw_moments M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0≤cardCost := by dsimp [cardCost];positivity
  refine ⟨(cardCost+1)*C,by positivity,?_⟩
  intro η
  filter_upwards [hclass η,eventually_gt_atTop (1:ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow=>u.val) W (fun _=>b) (fun j=>ell j/d) (fun _=>z) (Z^d)
  let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))
  have hb : 0≤bound := by dsimp [bound];positivity
  have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
    (nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
    (by linarith) (fun j=>ell j/d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent t ht hmom bin hne
      dsimp only at hp
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=>ell j/d) bin
      have hs := adaptive_mixed_saving N a q Δ ε εm R ν ζ μ v d e eps loss mesh
        (logCost+heightCost+momentCost) saving (by linarith) ha' hp.1 hp.2.1 hΔ hΔ1 hε.le hεm.le
        hR hν.le hcount hζ hζ1 hv' hμ hdv he.le heps.le hfinal
      have hid := central_class_exponent_identity N a v d
        (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) q e eps loss mesh (logCost+heightCost+momentCost)
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost*bound := hpart
    _ ≤ (cardCost+1)*bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound];ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2909

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorIntegral
Source SHA256: 8673f068cc71a6464e9d87c379c4721872a43220f5157f99475f2937edc11228
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2910


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃cB κB cH κH C : ℝ,0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤13/16+ζ → d-v≤μ →
      51/100<a → a≤1 → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving) := by
  obtain ⟨cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,harith⟩ :=
    actual_nonfloor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨cB,κB,cH,κH,D*C,hcB,hcB1,hκB,hcH,hcH1,hκH,mul_pos hD hC,?_⟩
  intro η
  filter_upwards [harith η,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z harith hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro hmom
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let A : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))
  have hA : 0≤A := by dsimp [A];positivity
  have hp := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha.le ha' hT
    (by gcongr;omega) S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1)
    T (nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hnext W Y
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp A hA
    (fun t ht=>harith d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
      t ht (hmom t ht))
  apply hp.trans_eq
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZp]
  dsimp only [A]
  calc
    _ = (D*C)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
        (Z^((25/48)*a-181/300+(105/8)*e)*Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))) := by ring
    _ = _ := by rw [←Real.rpow_add hZp];congr 2;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2910

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyIntegral
Source SHA256: 171b9c78de833f76c7a82b31acacbda7c662bc16ee0b624475e7f507a0c69897
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2911



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤A)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) (counts : CountParameters M H εm) :
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤13/16+ζ → d-v≤μ →
      51/100<a → a≤1 → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) W Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving) := by
  obtain ⟨C,hC,harith⟩ :=
    actual_nonfloor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal counts
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro η
  filter_upwards [harith η,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z harith hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro hmom
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let A : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))
  have hA : 0≤A := by dsimp [A];positivity
  have hp := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha.le ha' hT
    (by gcongr;omega) S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1)
    T (nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hnext W Y
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (by positivity) (by positivity) hZp A hA
    (fun t ht=>harith d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
      t ht (hmom t ht))
  apply hp.trans_eq
  rw [ProbeCentralExponent.physical_scale_identity Z a e hZp]
  dsimp only [A]
  calc
    _ = (D*C)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
        (Z^((25/48)*a-181/300+(105/8)*e)*Z^(3/16+Δ-saving-((25/48)*a-181/300+(105/8)*e))) := by ring
    _ = _ := by rw [←Real.rpow_add hZp];congr 2;ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2911

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorNormalized
Source SHA256: bb3f4f1fecfe5e63e55127d3f24888447a01336bca2545dcbb24c0c3da928b09
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2912



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_normalized_nonfloor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃cB κB cH κH C : ℝ,0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤13/16+ζ → d-v≤μ →
      51/100<a → a≤1 → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell (fun j y=>(W j y:ℂ)) Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then cB else cH) (if 2*a-1≤5/6 then κB else κH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) (fun j y=>(W j y:ℂ)) Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,hbound⟩ :=
    actual_nonfloor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨cB,κB,cH,κH,C*Cn,hcB,hcB1,hκB,hcH,hcH1,hκH,mul_pos hC hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only at hn ⊢
  intro hmom
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent hmom
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (3/16+Δ-saving) nu]
  ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2912

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyNormalized
Source SHA256: 2a7b16ed73fe873328ef130b532f6a5f98e2ed7e09aa697d7fc9355c1deba300
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2913



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_normalized_nonfloor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤d → d≤dmax → ∀(v a C0 : ℝ),0≤v → v≤13/16+ζ → d-v≤μ →
      51/100<a → a≤1 → 0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(d-margin)) →
      (∀u∈rows,Z^v≤rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)<a+2*e) →
      (∀u∈rows,a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell (fun j y=>(W j y:ℂ)) Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y) (fun j y=>(W j y:ℂ)) Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (fun _=>a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨C,hC,hbound⟩ :=
    actual_nonfloor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 counts
  have hellpos (j : Fin N) : 0<ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  refine ⟨C*Cn,mul_pos hC hCn,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,eventually_gt_atTop (0:ℝ)] with Z hb hn hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only at hn ⊢
  intro hmom
  refine ⟨hn.1,?_⟩
  have hh := hb d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent hmom
  rw [div_eq_mul_inv,norm_mul]
  have hm := mul_le_mul hh hn.2 (norm_nonneg _) (by positivity)
  apply hm.trans_eq
  rw [Real.rpow_add hZ (3/16+Δ-saving) nu]
  ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2913

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorDyadic
Source SHA256: 3f7c0fad89128f2e05762b2f5f5c13d60ba9e14f9b2f06e30a2c8fff509ff3b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2914




namespace OAI

noncomputable section
open scoped Classical BigOperators
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical

def sourceDyadExponent (Z : ℝ) (k : ℕ) : ℝ := Real.logb Z ((2:ℝ)^k)
def sourceDyadConductor (Z margin : ℝ) (k : ℕ) : ℝ := sourceDyadExponent Z k+2*margin

lemma sourceDyad_scale {Z : ℝ} (hZ : 1<Z) (k : ℕ) :
    Z^(sourceDyadExponent Z k)=(2:ℝ)^k :=
  Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' (by positivity)

lemma canonical_dyad_cost (loss : ℝ) (hl : 0<loss) :
    ∃C : ℝ,0<C ∧ ∀(Z v : ℝ),1≤Z → v≤1 →
      ((smallDyadicIndices (Z^v)).card:ℝ)≤C*Z^loss := by
  obtain ⟨C,hC,hbound⟩ := bounded_dyadic_power_sum loss hl
  refine ⟨C,hC,?_⟩
  intro Z v hZ hv
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  calc
    _ = ∑k∈smallDyadicIndices (Z^v),(1:ℝ) := by simp
    _ ≤ ∑k∈smallDyadicIndices (Z^v),((2:ℝ)^k)^loss := by
      apply Finset.sum_le_sum
      intro k hk
      exact Real.one_le_rpow (one_le_pow₀ (by norm_num : (1:ℝ)≤2)) hl.le
    _ ≤ C*(Z^v)^loss := hbound _ (by positivity) _ (fun k hk=>mem_smallDyadicIndices.mp hk)
    _ ≤ C*Z^loss := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      rw [←Real.rpow_mul hZp.le]
      exact Real.rpow_le_rpow_of_exponent_le hZ (by nlinarith)

lemma sourceDyad_geometry_eventually (dmin dmax margin vmax : ℝ)
    (_hdmin : 0<dmin) (hdmin1 : dmin<1/100) (hmargin : 0<margin)
    (hdmax : vmax+2*margin≤dmax) :
    ∀ᶠZ : ℝ in atTop,∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^vmax) →
      ∀k : ℕ,(rows∩dyadicRows 1 k).Nonempty →
        0≤sourceDyadExponent Z k ∧ sourceDyadExponent Z k≤vmax ∧
        dmin≤sourceDyadConductor Z margin k ∧ sourceDyadConductor Z margin k≤dmax ∧
        (∀u∈rows∩dyadicRows 1 k,
          Z^(sourceDyadExponent Z k)≤rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k)) ∧
        (∀u∈rows∩dyadicRows 1 k,rowNorm u≤Z^(sourceDyadConductor Z margin k-margin)) := by
  filter_upwards [eventually_gt_atTop (1:ℝ),
    (tendsto_rpow_atTop (show 0<(1/100:ℝ)-dmin by linarith)).eventually (eventually_ge_atTop (2:ℝ)),
    (tendsto_rpow_atTop hmargin).eventually (eventually_ge_atTop (2:ℝ))] with Z hZ hsmall hmarginZ
  intro rows hrows k hne
  have hZp : 0<Z := zero_lt_one.trans hZ
  obtain ⟨u,hu⟩ := hne
  have hur := (Finset.mem_inter.mp hu).1
  have hud := mem_dyadicRows.mp (Finset.mem_inter.mp hu).2
  have hlow : (2:ℝ)^k≤rowNorm u := by simpa only [one_mul] using hud.2.1
  have hhigh : rowNorm u<2*(2:ℝ)^k := by simpa only [one_mul] using hud.2.2
  have hv0 : 0≤sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ,Real.rpow_zero]
    exact one_le_pow₀ (by norm_num)
  have hvmax : sourceDyadExponent Z k≤vmax := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    exact hlow.trans (hrows u hur).2.2
  have hvmin : dmin≤sourceDyadExponent Z k := by
    apply (Real.rpow_le_rpow_left_iff hZ).mp
    rw [sourceDyad_scale hZ]
    have hh : 2*Z^dmin≤Z^(1/100:ℝ) := by
      calc
        _ ≤ Z^((1/100:ℝ)-dmin)*Z^dmin := mul_le_mul_of_nonneg_right hsmall (by positivity)
        _ = _ := by rw [←Real.rpow_add hZp];congr 1;ring
    linarith [(hrows u hur).2.1]
  have hnorm : ∀u∈rows∩dyadicRows 1 k,
      Z^(sourceDyadExponent Z k)≤rowNorm u ∧ rowNorm u≤2*Z^(sourceDyadExponent Z k) := by
    intro u hu
    rw [sourceDyad_scale hZ]
    have hh := (mem_dyadicRows.mp (Finset.mem_inter.mp hu).2).2
    simpa only [one_mul] using And.intro hh.1 hh.2.le
  refine ⟨hv0,hvmax,?_,?_,hnorm,?_⟩
  · unfold sourceDyadConductor;linarith
  · unfold sourceDyadConductor;linarith
  · exact dyad_conductor_margin Z (sourceDyadExponent Z k) margin hZp hmarginZ _ (fun u hu=>(hnorm u hu).2)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2914

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonfloorCollected
Source SHA256: 158f5a3d94c14d6f927d5aba0323785d4e7f843d41ef905bb04535741b79ca4a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2915


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0<dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤dmax)
    (hmuMargin : 2*margin≤μ) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃cB κB cH κH C : ℝ,0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+ζ)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u≤n ∧ grid u≤m ∧ grid u≠0 ∧ 51/100+e*grid u≤1) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) Δ
          (if 2*(51/100+e*j)-1≤5/6 then cB else cH)
          (if 2*(51/100+e*j)-1≤5/6 then κB else κH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,hbound⟩ :=
    actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  have hellpos (j : Fin N) : 0<ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨cB,κB,cH,κH,Cd*(n+1:ℕ)*(m+1:ℕ)*C,hcB,hcB1,hκB,hcH,hcH1,hκH,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (13/16+ζ) hdmin hdmin1 hmargin hconductor,
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu)
  have hD : 0≤D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(13/16+ζ)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤D := by
    let Rk := rows∩dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij⊆Rk := Finset.filter_subset _ _
    have hsub : Rij⊆rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
        (hne'.mono hsubk)
      obtain ⟨u,hu⟩ := hne'
      have huj : grid u=j := ((mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j≠0 := huj ▸ (hlabels u (hsub hu)).2.2.1
      have ha : 51/100<51/100+e*j := by
        have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51/100+e*j≤1 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j≤detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hbounded := hb (sourceDyadConductor Z margin k) hgeo.2.2.1 hgeo.2.2.2.1
        (sourceDyadExponent Z k) (51/100+e*j) C0 hgeo.1 hgeo.2.1
        (by unfold sourceDyadConductor;linarith) ha ha' hC0 Rij
        (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
        (fun u hu=>hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        hnext' hcurrent' (fun t ht=>hmom k hk i hi j hj ⟨u,hu⟩ t ht)
      exact hbounded.2
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(13/16+ζ)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(13/16+ζ)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (Z^τ) idx grid n m
        (fun u hu=>⟨(hlabels u (Finset.mem_inter.mp hu).1).1,(hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
      dsimp only [F]
      rw [hpart,Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=>hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(13/16+ζ))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (13/16+ζ) hZ.le (by linarith)) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (3/16+Δ-saving+nu) dyadCost];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2915

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCollected
Source SHA256: 4fa961e930f14f25d4567262636b362300052804c2be761a190770182b2978a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2916



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤3/16) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0<dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤dmax)
    (hmuMargin : 2*margin≤μ) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,0≤C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+ζ)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u≤n ∧ grid u≤m ∧ grid u≠0 ∧ 51/100+e*grid u≤1) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) Δ
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=>Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ :=
    actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu counts
  have hellpos (j : Fin N) : 0<ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (13/16+ζ) hdmin hdmin1 hmargin hconductor,
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0<Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=>Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=>pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (1/6)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(3/16+Δ-saving+nu)
  have hD : 0≤D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(13/16+ζ)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤D := by
    let Rk := rows∩dyadicRows 1 k
    let Rij := cubeBinRows Rk idx grid i j
    have hsubk : Rij⊆Rk := Finset.filter_subset _ _
    have hsub : Rij⊆rows := hsubk.trans Finset.inter_subset_left
    by_cases hne' : Rij.Nonempty
    · have hgeo := hg rows (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.1,(hrows u hu).2.2.2⟩) k
        (hne'.mono hsubk)
      obtain ⟨u,hu⟩ := hne'
      have huj : grid u=j := ((mem_cubeBinRows Rk idx grid i j u).mp hu).2.2
      have hju : j≠0 := huj ▸ (hlabels u (hsub hu)).2.2.1
      have ha : 51/100<51/100+e*j := by
        have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51/100+e*j≤1 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j≤detectorMaximum
          (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ) := by
        intro u hu
        have hh := hcurrent u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hbounded := hb (sourceDyadConductor Z margin k) hgeo.2.2.1 hgeo.2.2.2.1
        (sourceDyadExponent Z k) (51/100+e*j) C0 hgeo.1 hgeo.2.1
        (by unfold sourceDyadConductor;linarith) ha ha' hC0 Rij
        (fun u hu=>⟨(hrows u (hsub hu)).1,(hrows u (hsub hu)).2.1,
          (hrows u (hsub hu)).2.2.1,hgeo.2.2.2.2.2 u (hsubk hu)⟩)
        (fun u hu=>hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        hnext' hcurrent' (fun t ht=>hmom k hk i hi j hj ⟨u,hu⟩ t ht)
      exact hbounded.2
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(13/16+ζ)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(13/16+ζ)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z e (Z^τ) idx grid n m
        (fun u hu=>⟨(hlabels u (Finset.mem_inter.mp hu).1).1,(hlabels u (Finset.mem_inter.mp hu).1).2.1⟩)
      change ‖F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
      dsimp only [F]
      rw [hpart,Finset.sum_div]
      apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑i∈Finset.range (n+1),∑j∈Finset.range (m+1),D := by
          apply Finset.sum_le_sum
          intro i hi
          rw [Finset.sum_div]
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=>hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(13/16+ζ))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (13/16+ζ) hZ.le (by linarith)) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (3/16+Δ-saving+nu) dyadCost];ring

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2916

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.HighFromMoments
Source SHA256: f4cd678e0f726d2d08f51bc8f45db8035411e121954067a8cd42face02304d80
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2917



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_high_probe_from_raw_moments (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu)
    (dyadCost : ℝ) (hdyadCost : 0<dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤dmax)
    (hmuMargin : 2*margin≤μ)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0<sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*(dmax*rmin))
    (hfloorbudget : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+sigma≤7/1200)
    (hcentral : sigma+nu+dyadCost≤saving) :
    let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∃cB κB cH κH C : ℝ,
      0<cB ∧ cB≤1 ∧ 0<κB ∧ 0<cH ∧ cH≤1 ∧ 0<κH ∧ 0<C ∧
    ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤C0 →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) (HeckeZeroSupremum.beta-7/8)
          (if 2*(51/100+e*j)-1≤5/6 then cB else cH)
          (if 2*(51/100+e*j)-1≤5/6 then κB else κH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0<dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith)
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi hfloorbudget
  have hΔ : 0≤HeckeZeroSupremum.beta-7/8 := by linarith
  have hΔ1 : HeckeZeroSupremum.beta-7/8≤1/8 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,hbound⟩ :=
    actual_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm (HeckeZeroSupremum.beta-7/8) ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ.le (by linarith) hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hmuMargin
  refine ⟨n,hn,cB,κB,cH,κH,C,hcB,hcB1,hκB,hcH,hcH1,hκH,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤1 := by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2,(hbins u).2.1⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u≤detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 rows hrows idx grid hlabel hnext hcurrent hmom).2
  have hexp : Z^(3/16+(HeckeZeroSupremum.beta-7/8)-saving+nu+dyadCost)≤
      Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2917

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyHigh
Source SHA256: 51fff0db37a0e2cab919256b87ac4456ca601991e02fbf8543e2d4e1573cb5e4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2918



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
namespace SevenEighths.ProbeFinalAssembly
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
open PrincipalMellinResidues PrincipalSignalComparison ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤H)

theorem actual_high_probe_from_raw_moments (N : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps) (hc : 0<c) (hcb : c≤b) (hA : 0≤A)
    (hR : 0≤R) (hdmin : 0<dmin) (hdmax : 0≤dmax) (hdRange : dmin≤dmax) (hrmin : 0<rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤cost) (hmesh : 0<mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε<rmin*mesh) (hmargin : 0<margin)
    (hheight : 2*τ<dmin*cost) (hloss : τ*(2+4*eps)<loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ell j) (hellhi : ∀j,ell j≤dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤W j t ∧ W j t≤A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=1/6)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ<dmin/2) (hτheight : 4*τ<dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0<a₀) (hab₀ : a₀≤b₀) (hB₀ : 0<B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤B₀)
    (εm ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hν : 0<ν)
    (hlog : 0<logCost) (hMomentHeight : τ<heightCost)
    (ζ μ saving : ℝ) (hζ : 0<ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (13/16)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+mesh/6)+(logCost+heightCost+momentCost)+saving≤49/440640)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0<nu)
    (dyadCost : ℝ) (hdyadCost : 0<dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 13/16+ζ+2*margin≤dmax)
    (hmuMargin : 2*margin≤μ)
    (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (sigma : ℝ) (hsigma : 0<sigma)
    (hgeometric : sigma+8*e+nu≤63/800) (hprincipal : sigma+nu≤17/48000)
    (hwindow : sigma+e≤(7/8)*(dmax*rmin))
    (hfloorbudget : 2*ζ+26*e+(N+8)*eps+loss+mesh/6+nu+sigma≤7/1200)
    (hcentral : sigma+nu+dyadCost≤saving) (counts : CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃n : ℕ,0<n ∧ ∃C : ℝ,
      0<C ∧
    ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      let Yp := fun j=>Z^(ell j)
      let T := fun j=>pool (RayQuotient.identityClass M H) S c b (Yp j)
      let _hT := nonfloorPoolOutside M H S N c b Yp
      let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (1/6) (slotMass T (residueWeights W Yp)) : ℂ)
      normer≠0 ∧ ∃idx grid : FreeRow→ℕ,
      (∀u,1 ≤ idx u ∧ idx u ≤ n ∧ grid u ≤ ⌊(49/100:ℝ)/e⌋₊ ∧
        ((3*idx u+1:ℕ):ℝ)*Z^τ+Z^τ/2≤(3*idx u+2:ℕ)*Z^τ) ∧
      (∀u, let a : ℝ := 51/100+e*grid u
        (51/100:ℝ)≤a ∧ a≤1 ∧
        a≤detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ) ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*idx u*Z^τ)<a+e ∧
        detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(idx u+1:ℕ)*Z^τ)<a+2*e ∧
        (51/100<a → ∃j s,LFunction (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) s=0 ∧
          ¬((sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j).residue=1 ∧ s=1) ∧
          a≤s.re ∧ s.re<a+e ∧ |s.im|≤3*idx u*Z^τ)) ∧
      (∀u∈rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ)),
        (calibrationForSet S hmax).residueMonoid u.val≠0 →
        (∀θ,(rayCubeFamily M H hH u θ).residue≠1) ∧
        (∀θ,(rayCubeFamily M H hH u θ).modulus.absNorm≤
          conductorConstant*M.absNorm*(Ideal.span {u.val}:Ideal O).absNorm) ∧
        ∀hnp : ∀θ,(rayCubeFamily M H hH u θ).residue≠1,
        HeckeDetectorZeros.zeroMaximum (rayCubeFamily M H hH u) hnp
          (3*(idx u+1:ℕ)*Z^τ)<(51/100:ℝ)+e*grid u+2*e) ∧
      let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
      ∀C0 : ℝ,0≤C0 →
      (∀k∈smallDyadicIndices (Z^(13/16+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (⌊(49/100:ℝ)/e⌋₊+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell WC Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) (HeckeZeroSupremum.beta-7/8)
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖compensatedPhysicalProbe η (calibrationForSet S hmax) W0 W1
          (fun j=>canonicalSlotSupport (T j)) WC Yp (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z/normer-
        HeckeSignal.signal (η.excludePrimes S hS.prime) (sourceCorrection η S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*eps))*Z^(HeckeZeroSupremum.beta-11/16-sigma) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hmin : 0<dmax*rmin := mul_pos (hdmin.trans_le hdRange) hrmin
  obtain ⟨n,hn,htransport⟩ := actual_nonfloor_probe_transport M H hH N e (1/4) c b A ζ 1 τ (dmax*rmin) nu
    he he1 (by norm_num) (by norm_num) hζ hζ1 hτ hc hcb hA hmin hnu hβ S hS hmax hfirst
    ell hello hell hellsum W hW hcompact hWs hWB hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 sigma hsigma hgeometric hprincipal hwindow (by linarith)
    eps R dmin dmax rmin ε κ cost mesh margin loss heps hR hdmin hdmax hdRange hrmin hε hκ hcost hmesh hmargin
    hbudget hgap hheight hloss (by linarith) hello hellhi hfloorbudget
  have hΔ : 0≤HeckeZeroSupremum.beta-7/8 := by linarith
  have hΔ1 : HeckeZeroSupremum.beta-7/8≤1/8 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨C,hC,hbound⟩ :=
    actual_nonfloor_rows_saving M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm (HeckeZeroSupremum.beta-7/8) ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight
      ζ μ saving hζ.le (by linarith) hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu ⌊(49/100:ℝ)/e⌋₊ dyadCost hdyadCost hdmin1 hconductor hmuMargin counts
  refine ⟨n,hn,C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,htransport⟩ := htransport η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [htransport,hbound η,eventually_ge_atTop (1:ℝ)] with Z ht hb hZ
  dsimp only at ht ⊢
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,herror⟩ := ht
  refine ⟨hnorm,idx,grid,hlabels,hbins,hray,?_⟩
  intro C0 hC0 hmom
  let rows := supportedNonfloorRows S hmax (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+ζ))) grid
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧
      (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤Z^(13/16+ζ) := by
    intro u hu
    rcases (mem_supportedNonfloorRows S hmax _ grid u).mp hu with ⟨hur,hcal,hg⟩
    have hh := mem_rowBand.mp hur
    exact ⟨hh.1,hh.2.1,hcal,hh.2.2.le⟩
  have hlabel : ∀u∈rows,idx u≤n ∧ grid u≤⌊(49/100:ℝ)/e⌋₊ ∧ grid u≠0 ∧ 51/100+e*grid u≤1 := by
    intro u hu
    exact ⟨(hlabels u).2.1,(hlabels u).2.2.1,
      ((mem_supportedNonfloorRows S hmax _ grid u).mp hu).2.2,(hbins u).2.1⟩
  have hnext : ∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
      (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e := fun u _=>(hbins u).2.2.2.2.1
  have hcurrent : ∀u∈rows,51/100+e*grid u≤detectorMaximum
      (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*idx u:ℕ)*Z^τ) := by
    intro u hu
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using (hbins u).2.2.1
  have hglobal := (hb C0 hC0 rows hrows idx grid hlabel hnext hcurrent hmom).2
  have hexp : Z^(3/16+(HeckeZeroSupremum.beta-7/8)-saving+nu+dyadCost)≤
      Z^(HeckeZeroSupremum.beta-11/16-sigma) :=
    Real.rpow_le_rpow_of_exponent_le hZ (by linarith)
  have hcentral' := hglobal.trans (mul_le_mul_of_nonneg_left hexp (by positivity))
  have hsum := (norm_add_le _ _).trans (add_le_add herror hcentral')
  simpa only [rows,sub_add_cancel,add_mul] using hsum

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2918

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyFixedHigh
Source SHA256: 1bc465b2b62cc50a3ad6a8c701ba1944691b2d2e41652f13e36e608b64d629bf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2919



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison
open HeckeInverseAmplification HeckeDetectorPhysicalSelection HeckeDetectorFiberPartition
open ProbeMellinBoundary

theorem fixed_high_bound (hβ : (7/8:ℝ)<HeckeZeroSupremum.beta)
    (D : HighData (HeckeZeroSupremum.beta-7/8)) (F : SourceData D)
    (counts : CountParameters F.modulus ⊤ D.t) (τ : ℝ)
    (hτ : 0<τ) (hτd : τ<(1/200:ℝ)/2) (hτcost : 4*τ<(1/200:ℝ)*D.cost)
    (hτt : τ<D.t) (hτ2 : 2*τ≤D.t) (hτeps : τ*(2+4*D.eps)<D.t) :
    ∃C : ℝ,0<C ∧ ∀η : Character,∃Ct : ℝ,0<Ct ∧ ∀ᶠZ : ℝ in atTop,
      ∀C0 : ℝ,0≤C0 → SourceMomentBound F counts η Z τ (C0*Z^D.t) (Z^(2*τ)) →
      ‖F.probe η Z-HeckeSignal.signal (η.excludePrimes F.S F.exclusions.prime)
        (sourceCorrection η F.S) (-11/16) Z‖≤
        (Ct+C*C0*(η.modulus.absNorm:ℝ)^(2*D.eps))*Z^(HeckeZeroSupremum.beta-11/16-D.sigma) := by
  let : NeZero (∏P∈F.S,P) := ⟨fixedPrimeProduct_ne_zero F.S F.exclusions.prime⟩
  have ht := D.t_pos
  have ht1 := D.t_small
  have hconductor : (13/16:ℝ)+D.t+2*D.t≤7/8 := by linarith
  obtain ⟨n,hn,C,hC,hbound⟩ := actual_high_probe_from_raw_moments F.modulus ⊤ le_top D.N
    D.e D.eps 1 2 1 D.t (1/200) (7/8) D.rmin τ D.ε D.κ D.cost D.t D.t D.t
    D.e_pos D.e_small D.eps_pos (by norm_num) (by norm_num) (by norm_num)
    ht.le (by norm_num) (by norm_num) (by norm_num) D.rmin_pos hτ D.epsilon_pos D.kappa_pos
    D.cost_pos.le ht D.phase_budget D.epsilon_gap ht (by linarith) hτeps
    F.S F.exclusions F.first F.maximal D.ell D.slots_injective
    (fun j=>(D.slots_bounds j).2.1) (fun j=>(D.slots_bounds j).2.2)
    (fun _=>F.w) (fun _=>F.support) (fun _=>F.smooth) (fun _=>F.bounded)
    (fun _=>F.compact) (fun _=>F.nonzero) D.slots_sum
    (by norm_num) D.epsilon_small D.kappa_small hτd hτcost (by nlinarith [D.detector_budget])
    F.w F.smooth F.compact F.positive_support (fun y=>(F.bounded y).1) F.nonzero
    1 2 1 (by norm_num) (by norm_num) (by norm_num) F.support (fun y=>(F.bounded y).2)
    D.t D.t D.t (2*τ) D.t ht ht ht (by linarith)
    D.t (2*D.t) D.t ht (by linarith) (by positivity) D.count_budget (by nlinarith [D.central_budget])
    F.W F.W 1 2 1 2 (by norm_num) (by norm_num) F.complex_support F.complex_support
    F.real F.real F.nonnegative F.nonnegative F.complex_nonzero F.complex_nonzero
    (D.t/8) (by positivity) (D.t/8) (by positivity) (by norm_num) hconductor (by linarith) hβ.le
    D.sigma D.sigma_pos D.geometric_budget D.principal_budget D.window_budget D.floor_budget D.high_saving counts
  refine ⟨C,hC,?_⟩
  intro η
  obtain ⟨Ct,hCt,hb⟩ := hbound η
  refine ⟨Ct,hCt,?_⟩
  filter_upwards [hb,sourceDyad_geometry_eventually (1/200) (7/8) D.t (13/16+D.t)
    (by norm_num) (by norm_num) ht hconductor,
    HeckeDyadic.constant_absorbed_eventually (3*(n:ℝ)+1) τ hτ,
    eventually_gt_atTop (1:ℝ)] with Z hb hgeo hnheight hZ
  intro C0 hC0 hmom
  obtain ⟨hnorm,idx,grid,hlabels,hbins,hray,hestimate⟩ := hb
  apply hestimate C0 hC0
  intro k hk i hi j hj
  dsimp only
  intro hne t htheight
  let rows := supportedNonfloorRows F.S F.maximal (rowBand (Z^(1/100:ℝ)) (Z^((13/16:ℝ)+D.t))) grid
  let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
  have hsub : rows'⊆rows∩dyadicRows 1 k := Finset.filter_subset _ _
  have hsubr : rows'⊆rows := hsub.trans Finset.inter_subset_left
  have hrows : ∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm u ∧ rowNorm u≤Z^(13/16+D.t) := by
    intro u hu
    have hh := mem_rowBand.mp ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp hu).1
    exact ⟨hh.1,hh.2.1,hh.2.2.le⟩
  have hg := hgeo rows hrows k (hne.mono hsub)
  obtain ⟨u,hu⟩ := hne
  have huj : grid u=j := ((mem_cubeBinRows _ idx grid i j u).mp hu).2.2
  have hjne : j≠0 := huj ▸ ((mem_supportedNonfloorRows F.S F.maximal _ grid u).mp (hsubr hu)).2.2
  have ha : (51/100:ℝ)<51/100+D.e*j := by
    have hjp : (0:ℝ)<j := by exact_mod_cast Nat.pos_of_ne_zero hjne
    nlinarith [D.e_pos]
  have ha' : (51/100:ℝ)+D.e*j≤1 := by simpa only [huj] using (hbins u).2.1
  have hrow' : ∀v∈rows',v.val≠1 ∧ Z^(1/100:ℝ)≤rowNorm v ∧
      (calibrationForSet F.S F.maximal).residueMonoid v.val≠0 ∧
      rowNorm v≤Z^(sourceDyadConductor Z D.t k-D.t) := by
    intro v hv
    exact ⟨(hrows v (hsubr hv)).1,(hrows v (hsubr hv)).2.1,
      ((mem_supportedNonfloorRows F.S F.maximal _ grid v).mp (hsubr hv)).2.1,hg.2.2.2.2.2 v (hsub hv)⟩
  have hi' : (i:ℝ)≤n := by exact_mod_cast Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hheight : (3*i+1:ℕ)*Z^τ≤Z^(2*τ) := by
    have hZp : 0<Z := zero_lt_one.trans hZ
    calc
      _≤(3*(n:ℝ)+1)*Z^τ := by push_cast;gcongr
      _≤Z^τ*Z^τ := mul_le_mul_of_nonneg_right hnheight (by positivity)
      _=Z^(2*τ) := by rw [←Real.rpow_add hZp];congr 1;ring
  apply hmom rows' (sourceDyadConductor Z D.t k) (51/100+D.e*j) hg.2.2.1 hg.2.2.2.1 ha ha' hrow' i
    ((17/50:ℂ)+t.1.2*Complex.I)
  · simp
  · simpa using htheight.2.trans hheight

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2919

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssembly
Source SHA256: e16f7a984e46edcda6c21efe9c21d4798d421ff332cc81ec394998102af53490
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2920


namespace OAI

noncomputable section
open scoped Classical
open Filter
namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

theorem common_probe_of_raw_moments (hmom : RawMomentInput) : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  have hgap : 0<HeckeZeroSupremum.beta-7/8 := by linarith
  obtain ⟨D⟩ := exists_high_data (HeckeZeroSupremum.beta-7/8) hgap
  obtain ⟨F⟩ := exists_source_data D
  obtain ⟨counts⟩ := source_count_parameters F
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := raw_input_chosen_height hmom hβ D F counts
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-7/8)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hlossgap : loss<HeckeZeroSupremum.beta-7/8 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    hmask,hH,hHbound,F.probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

theorem dirichlet_of_raw_moments (hmom : RawMomentInput) (q : ℕ) (hq : q≠0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8:ℝ)<s.re)
    (hexc : ¬(χ=1 ∧ s=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s≠0 :=
  HeckeCommonProbe.dirichlet_of_common_probe (common_probe_of_raw_moments hmom) q hq χ s hs hexc

theorem zeta_of_raw_moments (hmom : RawMomentInput) (s : ℂ) (hs : (7/8:ℝ)<s.re) :
    riemannZeta s≠0 :=
  HeckeCommonProbe.zeta_of_common_probe (common_probe_of_raw_moments hmom) s hs

theorem hecke_of_raw_moments (hmom : RawMomentInput) (χ : Character) (s : ℂ)
    (hs : (7/8:ℝ)<s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeCommonProbe.hecke_ne_zero_of_common_probe (common_probe_of_raw_moments hmom) χ s hs hpole

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2920

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyChosenData
Source SHA256: 3bba00cc2d9fd6a48badfac7e69be7bb2785f887b3b0c689b6c3660b18ce9450
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2921



namespace OAI

noncomputable section
open scoped Classical
open Filter

namespace SevenEighths.ProbeFinalAssembly
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters PrincipalSignalComparison

def ChosenMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
    ∃D:HighData (HeckeZeroSupremum.beta-7/8),∃F:SourceData D,
    ∃counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

def FineMomentInput:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
    ∃mesh:ℝ→ℝ,(∀t:ℝ,0<t→0<mesh t) ∧
    ∀D:HighData (HeckeZeroSupremum.beta-7/8),(∀j,D.ell j≤mesh D.t/200)→
    ∀F:SourceData D,∀counts:CountParameters F.modulus ⊤ D.t,
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))

theorem chosen_input_of_fine (h:FineMomentInput):ChosenMomentInput:=by
  intro hβ
  obtain ⟨mesh,hmesh,hmom⟩:=h hβ
  obtain ⟨D,hD⟩:=exists_high_data_fine (HeckeZeroSupremum.beta-7/8) (by linarith) mesh hmesh
  obtain ⟨F⟩:=exists_source_data D
  obtain ⟨counts⟩:=source_count_parameters F
  exact ⟨D,F,counts,hmom D hD F counts⟩

theorem chosen_data_height {Δ:ℝ}(D:HighData Δ)(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(J:ℝ)(hJ:0≤J)
    (hbound:∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ))):
    ∃τ:ℝ,0<τ ∧ τ<(1/200:ℝ)/2 ∧ 4*τ<(1/200)*D.cost ∧ τ<D.t ∧
      2*τ≤D.t ∧ τ*(2+4*D.eps)<D.t ∧
      ∀η:Character,∃C:ℝ,0<C ∧ ∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*Z^D.t) (Z^(2*τ)):=by
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτJ,hτeps⟩:=D.height_choice J hJ
  have htau1:τ≤1:=by linarith
  refine ⟨τ,hτ,hτd,hτcost,hτt,by nlinarith,hτeps,?_⟩
  intro η
  obtain ⟨C,hC,hbound⟩:=hbound η
  refine ⟨C*2^J,by positivity,?_⟩
  filter_upwards [hbound τ hτ htau1,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  exact hb.mono_constant (by linarith)
    (polynomial_height_absorption C Z τ J D.t hC.le hZ hτ.le hJ (by linarith))

theorem common_probe_of_chosen_moments (hmom : ChosenMomentInput) : HeckeCommonProbe.UniformCommonProbe := by
  intro hβ
  obtain ⟨D,F,counts,J,hJ,hmom⟩:=hmom hβ
  obtain ⟨τ,hτ,hτd,hτcost,hτt,hτ2,hτeps,hsource⟩ := chosen_data_height D F counts J hJ hmom
  obtain ⟨C,hC,hhigh⟩ := fixed_high_bound hβ D F counts τ hτ hτd hτcost hτt hτ2 hτeps
  let loss := (HeckeZeroSupremum.beta-7/8)/2
  have hloss : 0<loss := by dsimp [loss];linarith
  have hlossgap : loss<HeckeZeroSupremum.beta-7/8 := by dsimp [loss];linarith
  refine ⟨loss,D.sigma,hloss,hlossgap,D.sigma_pos,?_⟩
  intro η hprimitive
  obtain ⟨hmask,hH,hHbound⟩ := actual_source_analytic F.S F.exclusions η
  refine ⟨η.excludePrimes F.S F.exclusions.prime,sourceCorrection η F.S,F.probe η,
    hmask,hH,hHbound,F.probe_low loss hloss η,?_⟩
  obtain ⟨Ct,hCt,hhigh⟩ := hhigh η
  obtain ⟨Cm,hCm,hsource⟩ := hsource η
  apply isBigO_rpow_of_eventual_norm_bound
  refine ⟨Ct+C*Cm*(η.modulus.absNorm:ℝ)^(2*D.eps),by positivity,?_⟩
  filter_upwards [hhigh,hsource] with Z hh hs
  exact hh Cm hCm.le hs

theorem dirichlet_of_chosen_moments (hmom : ChosenMomentInput) (q : ℕ) (hq : q≠0)
    (χ : DirichletCharacter ℂ q) (s : ℂ) (hs : (7/8:ℝ)<s.re)
    (hexc : ¬(χ=1 ∧ s=1)) :
    letI : NeZero q := ⟨hq⟩
    DirichletCharacter.LFunction χ s≠0 :=
  HeckeCommonProbe.dirichlet_of_common_probe (common_probe_of_chosen_moments hmom) q hq χ s hs hexc

theorem zeta_of_chosen_moments (hmom : ChosenMomentInput) (s : ℂ) (hs : (7/8:ℝ)<s.re) :
    riemannZeta s≠0 :=
  HeckeCommonProbe.zeta_of_common_probe (common_probe_of_chosen_moments hmom) s hs

theorem hecke_of_chosen_moments (hmom : ChosenMomentInput) (χ : Character) (s : ℂ)
    (hs : (7/8:ℝ)<s.re) (hpole : s≠1 ∨ χ.residue≠1) : LFunction χ s≠0 :=
  HeckeCommonProbe.hecke_ne_zero_of_common_probe (common_probe_of_chosen_moments hmom) χ s hs hpole

end SevenEighths.ProbeFinalAssembly

end

end OAI
end OAIOriginalModule2921

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyCertifiedBands
Source SHA256: d41f3d2a7fc675a1e72e02ff0be668a774120dc97ff007f04593d4a28c7e0675
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2922






namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.ProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorEnergyInitialState CenteredMomentNaturalFixedRaySource
open ProbeDetectorPlainMarkedFineField ProbeDetectorPlainUnmarkedField
local notation "O"=>HeckeFamily.O

def detectorMesh (Δ t:ℝ):ℝ:=fineMesh 2 0 1 (3/4+2*Δ) (t/4)

lemma detectorMesh_pos {Δ t:ℝ}(hΔ:0<Δ)(ht:0<t):0<detectorMesh Δ t:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (3/4+2*Δ) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by linarith) (by positivity)).2.2.2.2.1

def DetectorCertifiedBands:Prop:=
  ∀_hβ:(7/8:ℝ)<HeckeZeroSupremum.beta,
  ∀D:HighData (HeckeZeroSupremum.beta-7/8),
    (∀j,D.ell j≤detectorMesh (HeckeZeroSupremum.beta-7/8) D.t/200)→
  ∀F:SourceData D,∀bΦ:ℝ,0<bΦ→
    CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (count 2 (stageError D))

theorem plain_inputs {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (hcert:∀bΦ:ℝ,0<bΦ→CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=>conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D) (count 2 (stageError D))):
    PositiveFineSourceInput F (detectorMesh Δ D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):=by
  have hp:=fixed_parameters D
  have ht (bΦ:ℝ)(hbΦ:0<bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=>conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1 (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0<bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0<Czero ∧ 0<Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 1 2
        (stageError D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=>conj (F.W x))
        2 (1/4) (9/4) bΦ 0 1 (detectorMesh Δ D.t) (33/50) (33/50) 2
        (stageError D) (kappaPlain D) U η₀ (sourceFixedIdeal F) degree control Cpositive:=by
    obtain ⟨degree,control,hbound⟩:=ht bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,hbound⟩:=hbound η₀ (sourceFixedIdeal F)
      (sourceFixedIdeal_le_modulus F) (source_fixed_gates F η₀).1
      (internalQ_ne_top _ (sourceFixedIdeal_ne_top F) η₀) (source_fixed_gates F η₀).2.2.2
    exact ⟨Cz,Cp,hCz,hCp,hbound.mono (fun U h=>⟨h.2.1,h.2.2⟩)⟩
  constructor
  · intro bΦ hbΦ
    obtain ⟨degree,control,h⟩:=hactual bΦ hbΦ
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cp,hCp,h.mono (fun U h=>h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=>h.1)⟩

theorem source_moments {Δ:ℝ}{D:HighData Δ}(F:SourceData D)
    (counts:CountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0<mesh)
    (hfine:∀j,D.ell j≤mesh/200)
    (hpositive:PositiveFineSourceInput F mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0<A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0≤J ∧ ∀η:Character,∃C:ℝ,0<C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=ProbeDetectorInverseFields.source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=source_batch_plain_marked_fine F mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=ProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0<Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0≤height:=Real.rpow_nonneg hZ.le _
  have hbase:1≤1+height:=by linarith
  have hCi':Ci*(1+height)^Ji≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCm':Cm*(1+height)^Jm≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  have hCu':Cu*(1+height)^Ju≤(Ci+Cm+Cu)*(1+height)^(Ji+Jm+Ju):=by
    apply mul_le_mul (by linarith) (pow_le_pow_right₀ hbase (by omega)) (by positivity) (by positivity)
  simp only [Real.rpow_natCast]
  intro rows d a hd hdmax ha hamax hrows i z hz hzim q B hB hdata hreverse hslots hwidth
    hprofile hupper hexternal hslotMesh hbinWidth hfamily bin label left right hne
  have hrows':∀u∈rows,Z^(1/100:ℝ)≤rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im|≤height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=>by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0≤Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected hcap j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))

theorem fine_moments_of_certified (h:DetectorCertifiedBands):FineMomentInput:=by
  intro hβ
  let Δ:=HeckeZeroSupremum.beta-7/8
  have hΔ:0<Δ:=by dsimp [Δ];linarith
  refine ⟨detectorMesh Δ,fun t ht=>detectorMesh_pos hΔ ht,?_⟩
  intro D hfine F counts
  obtain ⟨hp,hz⟩:=plain_inputs F (h hβ D hfine F)
  exact source_moments F counts (detectorMesh Δ D.t) (detectorMesh_pos hΔ D.t_pos) hfine hp hz

theorem chosen_moments_of_certified (h:DetectorCertifiedBands):ChosenMomentInput:=
  chosen_input_of_fine (fine_moments_of_certified h)

theorem dirichlet_of_certified (h:DetectorCertifiedBands)(q:ℕ)(hq:q≠0)
    (χ:DirichletCharacter ℂ q)(s:ℂ)(hs:(7/8:ℝ)<s.re)(hexc:¬(χ=1 ∧ s=1)):
    letI:NeZero q:=⟨hq⟩
    DirichletCharacter.LFunction χ s≠0:=
  dirichlet_of_chosen_moments (chosen_moments_of_certified h) q hq χ s hs hexc

theorem zeta_of_certified (h:DetectorCertifiedBands)(s:ℂ)(hs:(7/8:ℝ)<s.re):riemannZeta s≠0:=
  zeta_of_chosen_moments (chosen_moments_of_certified h) s hs

end SevenEighths.ProbeFinalAssemblyCertifiedBands

end

end OAI
end OAIOriginalModule2922

/-! Original module: OAI.NumberTheory.DirichletL.Detector.FinalAssemblyUnconditional
Source SHA256: 0f52159a2929e7b20646f8394589d25a1a637c2f78746ad9d1447871577af615
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2923




namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

namespace SevenEighths.ProbeFinalAssemblyUnconditional
open ProbeFinalAssembly ProbeFinalAssemblyCertifiedBands
open CenteredMomentEnergyCertifiedExistence CenteredMomentDetectorPlainMomentParameters
open CenteredMomentDetectorPlainSlotProfile

theorem detector_certified_bands:DetectorCertifiedBands:=by
  intro hβ D _hfine F bΦ hbΦ
  have hp:=fixed_parameters D
  apply terminal_certificate (α:=Fin D.N) F.modulus ⊤ le_top
    (fun x=>conj (F.W x)) 1 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D)
  · norm_num
  · exact conjugate_source_support F
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · exact hp.2.2.2.2.1.le
  · exact hp.2.2.1
  · linarith
  · unfold kappaPlain
    linarith

theorem dirichlet_nonzero (q:ℕ)(hq:q≠0)(χ:DirichletCharacter ℂ q)(s:ℂ)
    (hs:(7/8:ℝ)<s.re)(hexc:¬(χ=1 ∧ s=1)):
    letI:NeZero q:=⟨hq⟩
    DirichletCharacter.LFunction χ s≠0:=
  dirichlet_of_certified detector_certified_bands q hq χ s hs hexc

theorem zeta_nonzero (s:ℂ)(hs:(7/8:ℝ)<s.re):riemannZeta s≠0:=
  zeta_of_certified detector_certified_bands s hs

end SevenEighths.ProbeFinalAssemblyUnconditional

end

end OAI
end OAIOriginalModule2923

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.ConditionalNonvanishing
Source SHA256: b628ed950a6e85f6fc8014c951a1450b965f11c36539bd6830a577fa9c470804
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2924


namespace OAI

/-! The seven-eighths Hecke nonvanishing theorem from certified moment estimates. -/

namespace SevenEighths.HeckeFamily

theorem LFunction_ne_zero_of_certified_bands
    (h : ProbeFinalAssemblyCertifiedBands.DetectorCertifiedBands)
    (χ : Character) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0 := by
  apply ProbeFinalAssembly.hecke_of_chosen_moments
    (ProbeFinalAssemblyCertifiedBands.chosen_moments_of_certified h) χ s hs
  by_cases hs1 : s = 1
  · exact Or.inr (fun hχ => hpole ⟨hχ, hs1⟩)
  · exact Or.inl hs1

end SevenEighths.HeckeFamily

end OAI
end OAIOriginalModule2924

/-! Original module: OAI.NumberTheory.DirichletL.Hecke.Nonvanishing
Source SHA256: 9e120752d0067e9b645f173846833396de6282dfa83dff7dc83b7fd500af47d5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2925




namespace OAI

/-! Finite-order Hecke L-functions over the Eisenstein number field are nonzero to the right of seven eighths, away from the principal pole. -/

noncomputable section

namespace SevenEighths.HeckeFamily

theorem LFunction_ne_zero_of_seven_eighths_lt_re
    (χ : Character) {s : ℂ} (hs : (7 / 8 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_certified_bands
    ProbeFinalAssemblyUnconditional.detector_certified_bands χ hs hpole

theorem LFunction_ofResidue_ne_zero_of_seven_eighths_lt_re
    (M : Ideal O) (hM : M ≠ ⊥) (χ : MulChar (O ⧸ M) ℂ)
    (hu : ∀ u : Oˣ, χ (Ideal.Quotient.mk M (u : O)) = 1)
    {s : ℂ} (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    LFunction (Character.ofResidue M hM χ hu) s ≠ 0 :=
  LFunction_ne_zero_of_seven_eighths_lt_re _ hs hpole

end SevenEighths.HeckeFamily

namespace SevenEighths.HeckeRayFamily

variable (M : Ideal HeckeFamily.O) [NeZero M]

local instance : Finite (HeckeFamily.O ⧸ M) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)

theorem LFunction_ne_zero_of_seven_eighths_lt_re
    (χ : RayOrthogonality.rayCharacters M) {s : ℂ}
    (hs : (7 / 8 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    HeckeFamily.LFunction (character M χ) s ≠ 0 := by
  apply HeckeFamily.LFunction_ne_zero_of_seven_eighths_lt_re _ hs
  rintro ⟨hχ, hs1⟩
  exact hpole ⟨(principal_iff M χ).mp hχ, hs1⟩

end SevenEighths.HeckeRayFamily

end

end OAI
end OAIOriginalModule2925
