  refine ⟨hm.2.2.2.2,hm.2.2.1,hcap,Real.one_le_rpow hU.le hm.2.2.2.2,?_,?_⟩
  · simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le hU.le (show F.m≤1 by linarith)
  · exact IVCenteredMomentDetectorPlainMarkedState.plain_length_eq F hU

theorem batch_fiber_parameters (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(Z d:ℝ)
    (hZ:1< Z)(hd:(1/200:ℝ)≤ d)
    (B:Batch M H Label (Fin D.N) (Z^d) a D.ε tstar T heightAllowance i)
    (hwidth:B.widths=(fun s=> D.ell s/d))
    (bin label J K)(hne:(B.fiberRows bin label J K).Nonempty):
    let F:=B.fiber bin label J K hne;
    1< Z^d ∧ 0≤ F.m ∧ F.m≤1/2+75*D.ε ∧ F.m≤23/40 ∧
    1≤(Z^d)^F.m ∧ (Z^d)^F.m≤ Z^d ∧ length (Z^d) ((Z^d)^F.m)=F.m ∧
    (∀s,0< F.widths s ∧ F.widths s≤ D.t) ∧
    (∀selected:Finset (Fin D.N),∀s:selected,0< F.widths s.val ∧ F.widths s.val≤ D.t) := by
  dsimp only
  have hU:=source_base_gt_one D Z d hZ hd
  have hf:=actual_fiber_lengths D (B.fiber bin label J K hne) hU
  have hw:∀s,0<(B.fiber bin label J K hne).widths s ∧
      (B.fiber bin label J K hne).widths s≤ D.t:=by
    intro s
    change 0< B.widths s ∧ B.widths s≤ D.t
    rw [hwidth]
    exact original_width_bounds D d hd s
  exact ⟨hU,hf.1,hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2.1,hf.2.2.2.2.2,
    hw,fun _ s=> hw s.val⟩

lemma width_bands (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(m:ℝ)(hm:m≤23/40):
    1≤1+delta D ∧ 1+delta D≤2 ∧
    1≤ max 1 (2*m)+delta D ∧ max 1 (2*m)+delta D≤2 := by
  have hδ:0< delta D:=(fixed_parameters D).1
  have hd:delta D≤1/4:=(fixed_parameters D).2.1
  have hmax:max 1 (2*m)≤23/20:=max_le (by norm_num) (by linarith)
  have hlo:=le_max_left (1:ℝ) (2*m)
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

theorem marked_state_admission (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D))
    (selected:Finset (Fin D.N))
    (hcap:2*F.m+6*(kappaPlain D)*(∑s∈selected,F.widths s)≤1):
    let s:=initialState η Q Φ bΦ U (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=1+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧
    length U (U^F.m)+length U (U^F.m)+
      6*(kappaPlain D)*(∑s:selected,F.widths s.val)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,hw.1,hw.2.1,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  exact IVCenteredMomentDetectorPlainMarkedState.marked_capacity F hU selected (kappaPlain D) (delta D) (fixed_parameters D).1.le hcap

theorem unmarked_state_admission (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(Φ:𝓢(ℝ,ℂ))(bΦ:ℝ)(hU:1< U)
    (hs:Function.support (Φ:ℝ→ℂ)⊆Set.Iic bΦ)(hp:∀x,0≤(Φ x).re)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D)):
    let s:=state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη;
    s.character=η ∧ s.fixedModulus=Q ∧ s.puncture=1 ∧
    s.radial.profile=Φ ∧ s.radial.scale=U ∧ s.radial.keep=initialKeep η Q ∧
    s.width=max 1 (2*F.m)+delta D ∧ 1≤ s.width ∧ s.width≤2 ∧
    1≤ U^F.m ∧ U^F.m≤ U ∧ 2*length U (U^F.m)≤ s.width := by
  dsimp only
  have hf:=actual_fiber_lengths D F hU
  have hw:=width_bands D F.m hf.2.2.1
  have he:(state F η Q Φ bΦ (delta D) hU.le (fixed_parameters D).1.le hs hp hη).width=
      max 1 (2*F.m)+delta D:=padded_width _ _
  refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,he,?_,?_,hf.2.2.2.1,hf.2.2.2.2.1,?_⟩
  · rw [he];exact hw.2.2.1
  · rw [he];exact hw.2.2.2
  · rw [he,hf.2.2.2.2.2]
    exact (le_max_right 1 (2*F.m)).trans (le_add_of_nonneg_right (fixed_parameters D).1.le)

theorem source_label_fixed_allowance (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(η:Character):
    ∀ᶠZ:ℝ in atTop,1< Z ∧
      ∀label:Sum Bool (RayQuotient.Characters S.modulus ⊤),∀d:ℝ,(1/200:ℝ)≤ d→
      ((sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label).modulus.absNorm:ℝ)
        ≤(Z^d)^(delta D) :=
  source_label_modulus_eventually S η (delta D) (fixed_parameters D).1

lemma final_exponent_budget (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)(base:ℝ):
    base+delta D+stageError D≤ base+D.t := by
  linarith [(fixed_parameters D).2.2.2.1]

end SevenEighths.IVCenteredMomentDetectorPlainMomentParameters

end

end OAI

-- Adapted data-generic source wrapper from DetectorInverseMarkedField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.ProbeDetectorInverseMarkedField
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators Topology SchwartzMap ContDiff
namespace SevenEighths.IVProbeDetectorInverseMarkedField
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
open DetectorDictionaryInverseMarkedReference DetectorDictionaryInverseClippedUniform
local notation "O"=> HeckeFamily.O

variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

theorem source_batch_inverse_marked {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀d:ℝ,(1/200:ℝ)≤ d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=> D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height →
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
    ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) true
        ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
        ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t) := by
  obtain ⟨Jref,hreference⟩:=IVDetectorDictionaryInverseMarkedReference.fiber_reference_energy S referenceWindow (1/18) (13/4)
    (by norm_num) (by norm_num)
    (fun x hx=> referenceWindow_support (subset_tsupport _ hx)) (referenceWindow.smooth ⊤)
    D.t D.t_pos D.N
  obtain ⟨J,Cfourier,hCfourier,hfourier⟩:=DetectorDictionaryInverseMarkedUniform.fiber_inverse_height_uniform Jref
  refine ⟨J,?_⟩
  intro η
  let data:=sourceMomentData M H hH S.S S.exclusions.prime η
  choose C U₀ hC hU₀ hb using fun label=> hreference (data label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0< Csum:=by
    have hh:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤ Csum:=by
    have hh:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le) (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d → U₀ label≤ Z^d := by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  refine ⟨Cfourier*Csum,mul_pos hCfourier hCsum,?_⟩
  filter_upwards [eventually_gt_atTop (1:ℝ),hscale,
    deleted_large_eventually data D.ell (fun s=>(D.slots_bounds s).1),
    IVHeckeDetectorMomentPrimeGeometry.sourceMoment_fiber_prime_geometry_eventually M H hH S η D.t D.t_pos] with Z hZ hscale hlarge hgeom
  refine ⟨hZ,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz bin label left right hne
    height hheight F selected hselected hfirst hsecond n hn s hs t ht
  have hd0:0< d:=by linarith
  have hUone:1< Z^d:=Real.one_lt_rpow hZ hd0
  have hUp:0< Z^d:=zero_lt_one.trans hUone
  have hprofile:B.profile=(fun _=>(S.W:ℝ→ℂ)) := by
    rw [hprofile0]
    funext j x
    exact (S.complex_eq x).symm
  have hfd:F.rowData=data label:=by change B.data label=data label;rw [hdata]
  have hfp (j):F.profile j=S.W:=by change B.profile j=S.W;rw [hprofile]
  have hfu (j):F.upper j=2:=by change B.upper j=2;rw [hupper]
  have hfw (j):F.widths j=D.ell j/d:=by change B.widths j=_;rw [hwidths]
  have hfe (j):(F.external j).re≤1:=by change (B.external j).re≤1;rw [hz j];norm_num
  have hdis:((Finset.univ:Finset selected):Set selected).PairwiseDisjoint (fiberLists F selected) := by
    intro j hj k hk hjk
    exact (hgeom.2 d hd a ε tstar T allowance i B hdata hprofile0 hupper hwidths hz
      bin label left right hne).1 j k (fun he=> hjk (Subtype.ext he))
  have hlargeF:∀j∈selected,((DetectorDictionaryInverseRawInitialGates.deletedBase (data label)).modulus.absNorm:ℝ)<
      (Z^d)^(F.widths j) := by
    intro j hj
    rw [hfw]
    exact hlarge.2 d hd0 label j
  have hr:0≤ F.r:=Real.logb_nonneg hUone (one_le_pow₀ (by norm_num : (1:ℝ)≤2))
  have href (v:ℝ):
      (∑u∈F.rows,‖polynomial (F.family u F.label) true (childLogTest referenceWindow v)
        ((Z^d)^F.r) 0 0*F.physicalProduct selected u‖^2)≤
      (Csum*(Z^d)^(1+D.t))*(1+‖v‖)^(2*Jref) := by
    have hh:=hb label (Z^d) (hscale label d hd) M H F selected hfd
      (by simpa using Finset.card_le_univ selected) (fun j _=> hfp j) (fun j _=> hfu j)
      (fun j hj=>(F.widths_pos j (hselected hj)).le) (fun j _=> hfe j) hdis hlargeF hr hfirst hsecond v
    rw [(show 2*Jref=Jref*2 by omega),pow_mul]

    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right (hClabel label) (Real.rpow_nonneg hUp.le _)
  have hh:=hfourier F selected hUp (Csum*(Z^d)^(1+D.t)) (by positivity) href
    n hn s hs height t hheight ht
  convert hh using 1 ; ring

end SevenEighths.IVProbeDetectorInverseMarkedField

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainMarkedFineField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMarkedState
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainMarkedFineField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.IVProbeDetectorPlainMarkedFineField
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles ProbeHighRowFamily ProbeFinalAssembly
open QuadraticInitialBound CenteredMomentDetectorDictionary
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentInductionEnergy
open IVCenteredMomentDetectorEnergyInitialState IVCenteredMomentDetectorPlainMarkedState
open IVCenteredMomentDetectorPlainMomentParameters IVCenteredMomentNaturalFixedRaySource
open CenteredMomentFiniteProfileExceptional CenteredMomentDetectorPlainFiberSource
local notation "O"=> HeckeFamily.O

def PositiveFineSourceInput {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}(S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(mesh:ℝ):Prop:=
  ∀bΦ:ℝ,0< bΦ→∃degree:ℕ,∃seminorms:Finset (ℕ×ℕ),
    ∀η₀:Character,∃C:ℝ,0< C ∧ ∀ᶠU:ℝ in atTop,
      PositiveAt (α:=Fin D.N) S.modulus ⊤ le_top (fun x=> conj (S.W x))
        2 (1/4) (9/4) bΦ 0 1 mesh (33/50) (33/50) 2 (stageError D)
        (kappaPlain D) U η₀ (sourceFixedIdeal S) degree seminorms C

theorem source_batch_plain_marked_fine {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(mesh:ℝ)(hmesh:0< mesh)(hfine:∀j,D.ell j≤ mesh/200)
    (henergy:PositiveFineSourceInput S mesh):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀rows:Finset FreeRow,(∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
    ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T allowance:ℝ)(i:ℕ)
    (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
      (Z^d) a D.ε tstar T allowance i),B.rows⊆rows→
    B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
    B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
    (∀s,B.upper s=2)→(∀s,(B.external s).re=17/50)→
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height→(∀s,|(B.external s).im|≤ height)→
    let F:=B.fiber bin label left right hne;
    ∀selected:Finset (Fin D.N),selected⊆F.slots→
      2*F.m+6*(RHIVProbe.momentKappa)*(∑s∈selected,F.widths s)≤1→
    ∀j k:ℕ,j+k≤2→∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      (∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t*F.physicalProduct selected u‖^2)≤
        (C*(1+height)^J)*(Z^d)^(1+D.t):=by
  obtain ⟨bΦ,hbΦ,hsource⟩:=source_batch_marked_initial S
  obtain ⟨degree,seminorms,henergy⟩:=henergy bΦ hbΦ
  obtain ⟨J,Cprofile,hCprofile,hprofile⟩:=
    CenteredMomentDetectorPlainProfileControl.source_height_factor seminorms
  refine ⟨J+degree,?_⟩
  intro η
  let data:=sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η
  choose C hC hbound using fun label=> henergy (data label)
  choose U₀ hU₀ using fun label=> Filter.eventually_atTop.mp (hbound label)
  let Csum:ℝ:=1+∑label,C label
  have hCsum:0< Csum:=by
    have h:=Finset.sum_nonneg (fun label (_:label∈Finset.univ)=>(hC label).le)
    dsimp [Csum];linarith
  have hClabel (label):C label≤ Csum:=by
    have h:=Finset.single_le_sum (fun label (_:label∈Finset.univ)=>(hC label).le)
      (Finset.mem_univ label)
    dsimp [Csum];linarith
  have hscale:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→U₀ label≤ Z^d:=by
    apply Filter.eventually_all.mpr
    intro label
    exact HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) (U₀ label) (by norm_num)
  let Cfinal:=Csum*(1+diagonalControl radialMajorant)*Cprofile
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  refine ⟨Cfinal,by dsimp [Cfinal];positivity,?_⟩
  filter_upwards [hsource η (delta D) (fixed_parameters D).1,hscale] with Z hs hscale
  refine ⟨hs.1,?_⟩
  intro rows hrows d hd a tstar T allowance i B hB hdata hprof hwidth hupper hreal
    bin label left right hne height hheight hexternal F selected hselected hcap j k hjk σ hσ t ht
  have hU:1< Z^d:=source_base_gt_one D Z d hs.1 hd
  obtain ⟨state,hchar,hQ,hpuncture,hΦ,hK,hkeep,hwidthstate,hcapacity,hwidths,hrow⟩:=
    hs.2 rows hrows d hd a D.ε tstar T allowance i B hB hdata hprof hwidth hupper hreal
      bin label left right hne selected hselected hcap
  have hf:=actual_fiber_lengths D F hU
  have hstate:state.width≤2:=by rw [hwidthstate];exact (width_bands D F.m hf.2.2.1).2.1
  have hw (s:selected):0≤ F.widths s.val:=(hwidths s).1.le
  have hwcap (s:selected):F.widths s.val≤ mesh:=by
    change B.widths s.val≤ mesh
    rw [hwidth]
    exact (RHZeroFreeExtension.AnalyticHigh.IV.fine_slot_widths D (fun _=> mesh) hmesh hfine d hd s.val).2
  have hpos:=hU₀ label (Z^d) (hscale label d hd) selected (fun _=>1)
    (fun s=> F.widths s.val) (fun _=>(33/50:ℝ)) (fun s=>-(F.external s.val).im)
    0 height hw hwcap (fun _=> le_rfl) (fun _=> le_rfl) hheight
    (fun s=> by change |-(B.external s.val).im|≤ height; simpa only [abs_neg] using hexternal s.val)
    state hQ hstate (detectorProfiles F.reverse j k σ t) ((Z^d)^F.m) ((Z^d)^F.m)
    (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _) (Real.rpow_pos_of_pos (zero_lt_one.trans hU) _)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1)
    (by simpa only [Real.rpow_one] using hf.2.2.2.2.1) hcapacity
  have heq:=CenteredMomentDetectorPlainRelativeClass.energy_eq S.modulus ⊤ le_top
    state.character (data label) (fun (_:selected)=>1) state.mask 1
    ((detectorProfiles F.reverse j k σ t).profile 0)
    ((detectorProfiles F.reverse j k σ t).profile 1)
    (fun _=>2) (fun s:selected=>(Z^d)^(F.widths s.val))
    (fun s I=> HeckePrimeAnnular.annularWeight (fun x=> conj (S.W x))
      ((Z^d)^(F.widths s.val)) (33/50) (-(F.external s.val).im) I)
    0 ((Z^d)^F.m) ((Z^d)^F.m) state.radial.keep state.radial.profile state.radial.scale
  have hnorm:=hprofile degree F.reverse j k hjk σ hσ height t hheight (abs_le.mpr ht)
  have hp:0≤(detectorProfiles F.reverse j k σ t).control seminorms ^2:=sq_nonneg _
  have hexp:state.width+stageError D≤1+D.t:=by
    rw [hwidthstate];linarith [(fixed_parameters D).2.2.2.1]
  calc
    _≤_:=hrow j k σ t
    _≤ C label*diagonalControl state.radial.profile*
        (detectorProfiles F.reverse j k σ t).control seminorms ^2*
        (1+|(0:ℝ)|+height)^degree*(Z^d)^(state.width+stageError D):=by
      exact heq.le.trans hpos
    _≤(Cfinal*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
      rw [hΦ]
      have hpow:=Real.rpow_le_rpow_of_exponent_le hU.le hexp
      calc
        _=(C label*diagonalControl radialMajorant)*
          ((detectorProfiles F.reverse j k σ t).control seminorms ^2*
            (1+|(0:ℝ)|+height)^degree)*(Z^d)^(state.width+stageError D):=by ring
        _≤(Csum*(1+diagonalControl radialMajorant))*
          (Cprofile*(1+height)^(J+degree))*(Z^d)^(1+D.t):=by
          apply mul_le_mul _ hpow (Real.rpow_nonneg (zero_lt_one.trans hU).le _) (by positivity)
          apply mul_le_mul _ hnorm (by positivity) (by positivity)
          exact mul_le_mul (hClabel label) (by linarith) hdiag hCsum.le
        _=_:=by dsimp [Cfinal];ring
end SevenEighths.IVProbeDetectorPlainMarkedFineField

end

end OAI

-- Adapted data-generic source wrapper from DetectorInverseFields.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.ProbeDetectorInverseFields
open RHZeroFreeExtension.AnalyticHigh

open scoped Classical BigOperators Topology
namespace SevenEighths.IVProbeDetectorInverseFields
open HeckeFamily HeckeDyadic HeckeInverseAmplification InverseMoment
open HeckeDetectorRawFiber HeckeDetectorBatch HeckeDetectorCoefficientTransfer
open ProbeHighRowFamily ProbeFinalAssembly Filter
local notation "O"=> HeckeFamily.O
variable (M:Ideal O)[NeZero M]
local instance:Finite (O⧸M):=Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ)(hH:RayOrthogonality.globalUnits M≤ H)
local instance:Fintype (Sum Bool (RayQuotient.Characters M H)):=Fintype.ofFinite _

private lemma raw_mono (data:RowData)(W:ℝ→ℂ)(c κ A B:ℝ)
    (hAB:A≤ B)(h:RawMoment data W c κ A):RawMoment data W c κ B:=by
  intro X D hX hD hcap rows hrows
  apply (h X D hX hD hcap rows hrows).trans
  gcongr

theorem source_batch_inverse_fields {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)(counts:IVRawCountParameters M H D.t):
    ∃J:ℕ,∀η:Character,∃C:ℝ,0< C ∧ ∀ᶠZ:ℝ in atTop,
    1< Z ∧ ∀d:ℝ,(1/200:ℝ)≤ d →
    ∀(a ε tstar T allowance:ℝ)(i:ℕ)
      (B:Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin D.N)
        (Z^d) a ε tstar T allowance i),
      B.data=sourceMomentData M H hH S.S S.exclusions.prime η →
      B.profile=(fun _ x=>(S.w x:ℂ)) → B.upper=(fun _=>2) →
      B.widths=(fun s=> D.ell s/d) → (∀s,(B.external s).re=17/50) →
    ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
    ∀height:ℝ,0≤ height →
    let F:=B.fiber bin label left right hne;
    (∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let W:=twistProfile (logTest (orientedProfile F.reverse F.inverseProfile) n) s t;
      RawMoment F.rowData W (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J) ∧
      RawMoment F.rowData (scaleProfile W) (if 2*a-1≤5/6 then counts.cB else counts.cH)
        (if 2*a-1≤5/6 then counts.kB else counts.kH) (C*(1+height)^J)) ∧
    (∀selected:Finset (Fin D.N),selected⊆F.slots →
      F.r+2*(∑s∈selected,F.widths s)<1 → 2*F.r+8*(∑s∈selected,F.widths s)<3 →
      ∀n:ℕ,n≤2 → ∀s∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
        (∑u∈F.rows,‖polynomial (F.family u F.label) true
          ((HeckeDetectorRowwisePolynomial.logProfile^[n]) F.inverseProfile)
          ((Z^d)^F.r) s t*F.physicalProduct selected u‖^2)≤
          (C*(1+height)^J)*(Z^d)^(1+D.t)) := by
  obtain ⟨Jr,hr⟩ := IVProbeDetectorInverseRawField.source_batch_inverse_raw
    M H hH S.S S.exclusions.prime D.t counts
  obtain ⟨Jm,hm⟩ := IVProbeDetectorInverseMarkedField.source_batch_inverse_marked M H hH S
  refine ⟨Jr+Jm,?_⟩
  intro η
  obtain ⟨Cr,hCr,hr⟩ := hr η
  obtain ⟨Cm,hCm,hm⟩ := hm η
  refine ⟨Cr+Cm,add_pos hCr hCm,?_⟩
  filter_upwards [hm] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
    bin label left right hne height hheight F
  have hU:0< Z^d := Real.rpow_pos_of_pos (zero_lt_one.trans hZ.1) _
  have hscale:1≤1+height := by linarith
  have hraw:Cr*(1+height)^Jr≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_right _ _)
    · positivity
    · positivity
  have hmarked:Cm*(1+height)^Jm≤(Cr+Cm)*(1+height)^(Jr+Jm) := by
    apply mul_le_mul
    · linarith
    · exact pow_le_pow_right₀ hscale (Nat.le_add_left _ _)
    · positivity
    · positivity
  constructor
  · intro n hn s hs t ht
    have hh:=hr hU B hdata bin label left right hne height hheight n hn s hs t ht
    exact ⟨raw_mono _ _ _ _ _ _ hraw hh.1,raw_mono _ _ _ _ _ _ hraw hh.2⟩
  · intro selected hselected hfirst hsecond n hn s hs t ht
    have hh:=hZ.2 d hd a ε tstar T allowance i B hdata hprofile hupper hwidths hex
      bin label left right hne height hheight selected hselected hfirst hsecond n hn s hs t ht
    exact hh.trans (mul_le_mul_of_nonneg_right hmarked (Real.rpow_nonneg hU.le _))

end SevenEighths.IVProbeDetectorInverseFields

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainUnmarkedField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainProfileControl
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.IVProbeDetectorPlainUnmarkedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary IVCenteredMomentDetectorEnergyInitialState
open IVCenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open IVCenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands IVCenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

def radialSupportUpper : ℝ := Classical.choose radialMajorant_support_bound

theorem radialSupportUpper_spec : 0< radialSupportUpper ∧
    Function.support (radialMajorant:ℝ→ℂ)⊆Set.Iic radialSupportUpper :=
  Classical.choose_spec radialMajorant_support_bound

lemma unmarked_power_eq (U m e:ℝ)(hU:1≤ U):
    U^(max 1 (2*m)+e)=max U ((U^m)^2)*U^e := by
  have hpos:0< U:=zero_lt_one.trans_le hU
  rw [Real.rpow_add hpos]
  congr 1
  have hs:(U^m)^2=U^(2*m):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hpos.le]
    congr 1
    norm_num
    ring
  rw [hs]
  by_cases hm:1≤2*m
  · rw [max_eq_right hm,max_eq_right]
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm
  · have hm':2*m≤1:=le_of_not_ge hm
    rw [max_eq_left hm',max_eq_left]
    · exact Real.rpow_one U
    · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hU hm'

variable {Δ:ℝ}

theorem retained_unmarked_bound (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    {M:Ideal O}[NeZero M]{H:Subgroup (O⧸M)ˣ}{Label:Type*}
    {U a tstar T heightAllowance:ℝ}{i:ℕ}
    (F:Fiber M H Label (Fin D.N) U a D.ε tstar T heightAllowance i)
    (η:Character)(Q:Ideal O)(hU:1< U)
    (hη:(η.modulus.absNorm:ℝ)≤ U^(delta D))
    (degree:ℕ)(S:Finset (ℕ×ℕ))(A:ℝ)
    (hzero:ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D) U degree S A)
    (j k:ℕ)(σ t:ℝ):
    CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep η Q) F η ∅ j k σ t radialMajorant ≤
      A*diagonalControl radialMajorant*(detectorProfiles F.reverse j k σ t).control S ^2*
        U^(max 1 (2*F.m)+delta D+stageError D) := by
  let s:=state F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hs:=unmarked_state_admission D F η Q radialMajorant radialSupportUpper hU
    radialSupportUpper_spec.2 radialMajorant_nonneg hη
  have hwidth:s.width=max 1 (2*F.m)+delta D:=hs.2.2.2.2.2.2.1
  have hband:s.width≤2:=hs.2.2.2.2.2.2.2.2.1
  have hscale:1≤ U^F.m ∧ U^F.m≤ U:=⟨hs.2.2.2.2.2.2.2.2.2.1,hs.2.2.2.2.2.2.2.2.2.2.1⟩
  have hz:=hzero s rfl hband (detectorProfiles F.reverse j k σ t) 0 (U^F.m) (U^F.m)
    (zero_lt_one.trans_le hscale.1) (zero_lt_one.trans_le hscale.1)
    (by simpa only [Real.rpow_one] using hscale.2)
    (by simpa only [Real.rpow_one] using hscale.2)
  change CenteredMomentDetectorPlainExceptional.retainedSourceEnergy
    (CenteredMomentDetectorEnergyInitialState.initialKeep η Q) F η ∅ j k σ t radialMajorant ≤ _
  rw [actual_source_eq F η Q radialMajorant radialSupportUpper (delta D) hU.le
    (fixed_parameters D).1.le radialSupportUpper_spec.2 radialMajorant_nonneg hη j k σ t]
  have hrad:s.radial.profile=radialMajorant:=rfl
  simpa only [hwidth,hrad,norm_zero,add_zero,one_pow,mul_one,
    CenteredMomentDetectorEnergyInitialState.detectorProfiles,
    IVCenteredMomentDetectorEnergyInitialState.detectorProfiles] using hz

theorem source_batch_plain_unmarked (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀Q:Ideal O,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt Q (1/4) (9/4) radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤ height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=> sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=> internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=> henergy (Q label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0≤∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0< Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0< C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→
      ZeroAt (Q label) (1/4) (9/4) radialSupportUpper 0 1 2 (stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained S η,source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1< Z^d:=source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤ CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one,
      CenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      IVCenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      CenteredMomentDetectorEnergyInitialState.initialKeep,
      IVCenteredMomentDetectorEnergyInitialState.initialKeep] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+delta D+stageError D)≤
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget D _)
  have hfinal:value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.IVProbeDetectorPlainUnmarkedField

end

end OAI

-- Adapted data-generic source wrapper from DetectorPlainUnmarkedRestrictedField.lean

namespace OAI

noncomputable section
open OAI.SevenEighths
open OAI.SevenEighths.CenteredMomentDetectorPlainExceptional
open OAI.SevenEighths.CenteredMomentDetectorPlainFiberSource
open OAI.SevenEighths.CenteredMomentDetectorPlainMomentParameters
open OAI.SevenEighths.CenteredMomentDetectorPlainProfileControl
open OAI.SevenEighths.CenteredMomentDetectorPlainUnmarkedState
open OAI.SevenEighths.CenteredMomentNaturalFixedRaySource
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedField
open OAI.SevenEighths.ProbeDetectorPlainUnmarkedRestrictedField
open RHZeroFreeExtension.AnalyticHigh
open scoped Classical BigOperators SchwartzMap
open Filter

namespace SevenEighths.IVProbeDetectorPlainUnmarkedRestrictedField
open HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentDetectorPlainFiberSource
open HeckeFamily HeckeDetectorRawFiber HeckeDetectorBatch ProbeHighRowFamily
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles
open CenteredMomentDetectorDictionary IVCenteredMomentDetectorEnergyInitialState
open IVCenteredMomentDetectorPlainExceptional CenteredMomentDetectorPlainUnmarkedState
open IVCenteredMomentDetectorPlainMomentParameters CenteredMomentDetectorPlainProfileControl
open CenteredMomentEnergyState CenteredMomentEnergyBands IVCenteredMomentNaturalFixedRaySource
open QuadraticInitialBound
local notation "O" => HeckeFamily.O

open IVProbeDetectorPlainUnmarkedField
variable {Δ:ℝ}

theorem source_zero_from_gated (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∀Q:Ideal O,
      Q≤ S.modulus→internalQ Q η₀≠0→internalQ Q η₀≠⊤→
      internalQ Q η₀≤ Ideal.span {(72:O)}→
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ Q η₀) (1/4) (9/4) IVProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (D.t/4)
          U degree control A):
    ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) IVProbeDetectorPlainUnmarkedField.radialSupportUpper
          0 1 2 (D.t/4) U degree control A:=by
  obtain ⟨degree,control,henergy⟩:=henergy
  refine ⟨degree,control,?_⟩
  intro η₀
  exact henergy η₀ (sourceFixedIdeal S) (sourceFixedIdeal_le_modulus S)
    (source_fixed_gates S η₀).1
    (internalQ_ne_top _ (sourceFixedIdeal_ne_top S) η₀)
    (source_fixed_gates S η₀).2.2.2

theorem source_batch_plain_unmarked (D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ)
    (S:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (henergy:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
        ZeroAt (internalQ (sourceFixedIdeal S) η₀) (1/4) (9/4) IVProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (D.t/4) U degree control A):
    ∃Jheight:ℕ,∀η:Character,∃C:ℝ,0< C ∧
    ∀ᶠZ:ℝ in atTop,1< Z ∧ ∀rows:Finset FreeRow,
      (∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u)→
      ∀d:ℝ,(1/200:ℝ)≤ d→∀(a tstar T heightAllowance:ℝ)(i:ℕ)
      (B:Batch S.modulus ⊤ (Sum Bool (RayQuotient.Characters S.modulus ⊤)) (Fin D.N)
        (Z^d) a D.ε tstar T heightAllowance i),B.rows⊆rows→
      B.data=sourceMomentData S.modulus ⊤ le_top S.S S.exclusions.prime η→
      B.profile=(fun _ x=>(S.w x:ℂ))→B.widths=(fun s=> D.ell s/d)→
      ∀bin label left right,∀hne:(B.fiberRows bin label left right).Nonempty,
      ∀height:ℝ,0≤ height→∀j k:ℕ,j+k≤2→
      ∀σ∈Set.Icc (0:ℝ) 1,∀t∈Set.Icc (-height) height,
      let F:=B.fiber bin label left right hne;
      let value:=∑u∈F.rows,‖polynomial (F.family u F.label) false ((logProfile^[j]) positiveAnnular)
        ((Z^d)^F.m) σ t*polynomial (F.family u F.label) false ((logProfile^[k]) positiveAnnular)
        ((Z^d)^F.m) σ t‖^2;
      value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t) ∧
      value≤ C*(1+height)^Jheight*max (Z^d) (((Z^d)^F.m)^2)*(Z^d)^D.t := by
  obtain ⟨degree,control,henergy⟩:=henergy
  obtain ⟨Jheight,Cp,hCp,hprofiles⟩:=paired_control control
  refine ⟨Jheight,?_⟩
  intro η
  let :Fintype (Sum Bool (RayQuotient.Characters S.modulus ⊤)):=Fintype.ofFinite _
  let η₀:=fun label=> sourceMomentBase S.modulus ⊤ le_top S.S S.exclusions.prime η label
  let Q:=fun label=> internalQ (sourceFixedIdeal S) (η₀ label)
  choose A hA hzero using (fun label=> henergy (η₀ label))
  let Amax:ℝ:=1+∑label,A label
  have hsum:0≤∑label,A label:=Finset.sum_nonneg (fun j _=>(hA j).le)
  have hAmax:0< Amax:=by dsimp [Amax];linarith
  have hA_bound (label):A label≤ Amax:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hA j).le) (Finset.mem_univ label)
    dsimp [Amax];linarith
  let C:=Amax*(1+diagonalControl radialMajorant)*Cp
  have hdiag:0≤ diagonalControl radialMajorant:=diagonalControl_nonneg _
  have hC:0< C:=mul_pos (mul_pos hAmax (by linarith)) hCp
  have hC_bound (label):A label*diagonalControl radialMajorant*Cp≤ C:=by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul (hA_bound label) (by linarith) hdiag hAmax.le) hCp.le
  have hscales:∀ᶠZ:ℝ in atTop,∀label,∀d:ℝ,(1/200:ℝ)≤ d→
      ZeroAt (Q label) (1/4) (9/4) IVProbeDetectorPlainUnmarkedField.radialSupportUpper 0 1 2 (stageError D)
        (Z^d) degree control (A label):=by
    apply Filter.eventually_all.mpr
    intro label
    obtain ⟨U₀,hU₀⟩:=eventually_atTop.mp (hzero label)
    filter_upwards [HeckeDetectorDyadicGeometry.uniform_scale_threshold (1/200) U₀ (by norm_num)]
      with Z hz
    intro d hd
    exact hU₀ (Z^d) (hz d hd)
  refine ⟨C,hC,?_⟩
  filter_upwards [source_batch_plain_retained S η,source_label_fixed_allowance D S η,hscales]
    with Z hret hmod hscales
  refine ⟨hret.1,?_⟩
  intro rows hrows d hd a tstar T heightAllowance i B hB hdata hprofile hwidth
    bin label left right hne height hheight j k hjk σ hσ t ht F value
  have hU:1< Z^d:=source_base_gt_one D Z d hret.1 hd
  have hnorm:‖t‖≤ height:=by simpa only [Real.norm_eq_abs] using abs_le.mpr ht
  have hp:(detectorProfiles F.reverse j k σ t).control control ^2≤ Cp*(1+height)^Jheight:=by
    apply (hprofiles F.reverse j k hjk σ hσ t).trans
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) (add_le_add le_rfl hnorm) Jheight) hCp.le
  have hcompare:value≤ CenteredMomentDetectorPlainExceptional.retainedSourceEnergy (initialKeep (η₀ label) (Q label))
      F (η₀ label) ∅ j k σ t radialMajorant:=by
    simpa only [Fiber.physicalProduct,Finset.prod_empty,mul_one,
      CenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      IVCenteredMomentDetectorPlainExceptional.retainedSourceEnergy,
      CenteredMomentDetectorEnergyInitialState.initialKeep,
      IVCenteredMomentDetectorEnergyInitialState.initialKeep] using
      hret.2 rows hrows d (by linarith) a D.ε tstar T heightAllowance i B hB hdata hprofile hwidth
        bin label left right hne ∅ j k σ t
  have hb:=retained_unmarked_bound D F (η₀ label) (Q label) hU (hmod.2 label d hd)
    degree control (A label) (hscales label d hd) j k σ t
  have hpow:(Z^d)^(max 1 (2*F.m)+delta D+stageError D)≤
      (Z^d)^(max 1 (2*F.m)+D.t):=
    Real.rpow_le_rpow_of_exponent_le hU.le (final_exponent_budget D _)
  have hfinal:value≤ C*(1+height)^Jheight*(Z^d)^(max 1 (2*F.m)+D.t):=by
    apply hcompare.trans (hb.trans ?_)
    calc
      _≤(A label*diagonalControl radialMajorant*(Cp*(1+height)^Jheight))*
          (Z^d)^(max 1 (2*F.m)+D.t):=by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hp (mul_nonneg (hA label).le hdiag)
        · exact hpow
        · exact Real.rpow_nonneg (zero_lt_one.trans hU).le _
        · exact mul_nonneg (mul_nonneg (hA label).le hdiag)
            (mul_nonneg hCp.le (by positivity))
      _=(A label*diagonalControl radialMajorant*Cp)*(1+height)^Jheight*
          (Z^d)^(max 1 (2*F.m)+D.t):=by ring
      _≤_:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hC_bound label) (by positivity)) (by positivity)
  refine ⟨hfinal,?_⟩
  simpa only [IVProbeDetectorPlainUnmarkedField.unmarked_power_eq _ _ _ hU.le,mul_assoc] using hfinal

end SevenEighths.IVProbeDetectorPlainUnmarkedRestrictedField

end

end OAI

set_option linter.unusedVariables false
namespace OAI

noncomputable section
open OAI.SevenEighths
open RHZeroFreeExtension.AnalyticHigh.IV
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.IVProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule IVCenteredMomentDetectorPlainMomentParameters
open CenteredMomentNaturalFixedRaySource
open IVCenteredMomentDetectorEnergyInitialState IVCenteredMomentNaturalFixedRaySource
open IVProbeDetectorPlainMarkedFineField IVProbeDetectorPlainUnmarkedField
local notation "O"=> HeckeFamily.O

def detectorMesh (_Δ t:ℝ):ℝ:=fineMesh 2 0 1 (RHIVProbe.momentKappa) (t/4)

lemma detectorMesh_pos {Δ t:ℝ}(_hΔ:0<Δ)(ht:0< t):0< detectorMesh Δ t:=by
  exact (bounds 2 (finalSourceCap 2 0 1 (t/4)) (RHIVProbe.momentKappa) (t/4)
    (by norm_num) (sourceCap_nonneg 2 0 1 (by norm_num) (by norm_num) _)
    (by linarith [RHIVProbe.moment_range.1]) (by positivity)).2.2.2.2.1

theorem plain_inputs {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}(F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (hcert:∀bΦ:ℝ,0< bΦ→CertifiedBand (α:=Fin D.N) F.modulus ⊤ le_top
      (fun x=> conj (F.W x)) 2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2
      (kappaPlain D) (stageError D) (count 2 (stageError D))):
    PositiveFineSourceInput F (detectorMesh Δ D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):=by
  have hp:=fixed_parameters D
  have ht (bΦ:ℝ)(hbΦ:0< bΦ):=
    certified_terminal F.modulus ⊤ le_top (fun x=> conj (F.W x))
      2 (1/4) (9/4) bΦ 0 1 (33/50) (33/50) 2 (kappaPlain D) (stageError D)
      (by norm_num) (by norm_num) hp.2.2.2.2.2.le hp.2.2.1 (hcert bΦ hbΦ)
  have hactual (bΦ:ℝ)(hbΦ:0< bΦ):
      ∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,
      ∃Czero Cpositive:ℝ,0< Czero ∧ 0< Cpositive ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) bΦ 0 1 2
        (stageError D) U degree control Czero ∧
      PositiveAt (α:=Fin D.N) F.modulus ⊤ le_top (fun x=> conj (F.W x))
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
    exact ⟨Cp,hCp,h.mono (fun U h=> h.2)⟩
  · obtain ⟨degree,control,h⟩:=hactual radialSupportUpper radialSupportUpper_spec.1
    refine ⟨degree,control,?_⟩
    intro η₀
    obtain ⟨Cz,Cp,hCz,hCp,h⟩:=h η₀
    exact ⟨Cz,hCz,h.mono (fun U h=> h.1)⟩


end SevenEighths.IVProbeFinalAssemblyCertifiedBands
end
end OAI

#print axioms OAI.SevenEighths.IVProbeDetectorPlainMarkedFineField.source_batch_plain_marked_fine

#print axioms OAI.SevenEighths.IVProbeFinalAssemblyCertifiedBands.plain_inputs

namespace RHZeroFreeExtension.AnalyticHigh.IV
open scoped Classical BigOperators ContDiff ComplexConjugate
open OAI OAI.SevenEighths
open CenteredMomentEnergyCertifiedExistenceIV CenteredMomentEnergyWidthSchedule
open CenteredMomentEnergyCappedWidthInduction

theorem variable_kappa_terminal_certificate {gap : ℝ} (D : HighData gap)
    (F : SourceData D) (hOld : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2)
    (hBeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) (bPhi : ℝ) (hbPhi : 0 < bPhi) :
    CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top (fun x => conj (F.W x))
      2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 RHIVProbe.momentKappa (D.t/4)
      (count 2 (D.t/4)) := by
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1/4) (9/4) bPhi 0 1 (33/50) (33/50) 2 RHIVProbe.momentKappa (D.t/4)
  · norm_num
  · intro x hx
    have hh : x ∈ Function.support (F.W : ℝ → ℂ) := by
      change conj (F.W x) ≠ 0 at hx
      change F.W x ≠ 0
      intro hz
      exact hx (by rw [hz]; simp)
    exact F.complex_support hh
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbPhi
  · norm_num
  · norm_num
  · exact RHIVProbe.moment_range.1
  · exact div_pos D.t_pos (by norm_num)
  · exact hBeta
  · linarith
end RHZeroFreeExtension.AnalyticHigh.IV

namespace OAI.SevenEighths.IVProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState CenteredMomentNaturalFixedRaySource
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges CenteredMomentEnergyWidthSchedule
open IVCenteredMomentDetectorPlainMomentParameters IVProbeDetectorPlainMarkedFineField
open IVProbeDetectorPlainUnmarkedField IVCenteredMomentNaturalFixedRaySource
open IVCenteredMomentDetectorEnergyInitialState
open Filter
open scoped BigOperators

theorem plain_inputs_of_premise {gap : ℝ}
    {D : RHZeroFreeExtension.AnalyticHigh.IV.HighData gap}
    (F : RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (hOld : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2)
    (hBeta : (51/100 : ℝ) ≤ HeckeZeroSupremum.beta) :
    PositiveFineSourceInput F (detectorMesh gap D.t) ∧
    (∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A) := by
  apply plain_inputs F
  intro bPhi hbPhi
  simpa only [kappaPlain,stageError] using
    RHZeroFreeExtension.AnalyticHigh.IV.variable_kappa_terminal_certificate D F hOld hBeta bPhi hbPhi
end OAI.SevenEighths.IVProbeFinalAssemblyCertifiedBands
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.variable_kappa_terminal_certificate
#print axioms OAI.SevenEighths.IVProbeFinalAssemblyCertifiedBands.plain_inputs_of_premise


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch HeckeDetectorRawFiber
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

def IVSourceMomentsAt {N : ℕ} (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
    (η : Character) (rows : Finset FreeRow) (ell : Fin N→ℝ) (W : Fin N→ℝ→ℂ)
    (Z d a ε τ dmax b slotMesh binWidth : ℝ) (i : ℕ) (z : ℂ)
    (tstar Δ c κ C height εm : ℝ) : Prop :=
  ∀B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
      (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
    B.rows⊆rows → B.data=sourceMomentData M H hH S hS η →
    B.reverse=sourceMomentReverse M H → B.slots=Finset.univ →
    B.widths=(fun j=> ell j/d) → B.profile=W → B.upper=(fun _=> b) → B.external=(fun _=> z) →
    B.mesh=slotMesh → B.binWidth=binWidth →
    (∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS η u (rayCubeFamily M H hH u) j) →
    ∀bin j J K,∀hne : (B.fiberRows bin j J K).Nonempty,
      Moments (B.fiber bin j J K hne) Δ c κ C height εm

end SevenEighths.ProbeHighRowFamily

end

end OAI



noncomputable section
open scoped Classical BigOperators
open Filter
namespace RHZeroFreeExtension.AnalyticHigh.IV
open OAI.SevenEighths.ProbeFinalAssembly
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters
open HeckeInverseAmplification

def SourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : IVRawCountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
   ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1/200:ℝ) ≤ d  →  d ≤ 7/8  →  51/100 < a  →  a ≤ 1  → 
    ( ∀ u∈rows,u.val≠1  ∧  Z^(1/100:ℝ) ≤ rowNorm u  ∧ 
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0  ∧  rowNorm u ≤ Z^(d-D.t))  → 
     ∀ i : ℕ, ∀ z : ℂ,z.re=17/50  →  |z.im| ≤ height  → 
    ∀tstar:ℝ,IVSourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z tstar ((RHIVProbe.momentKappa-3/4)/2)
      (if 2*a-1 ≤ 5/6 then counts.cB else counts.cH)
      (if 2*a-1 ≤ 5/6 then counts.kB else counts.kH) C height D.t


end RHZeroFreeExtension.AnalyticHigh.IV
end

namespace OAI

noncomputable section
open OAI.SevenEighths
open RHZeroFreeExtension.AnalyticHigh.IV
open scoped Classical BigOperators SchwartzMap ComplexConjugate
open Filter

namespace SevenEighths.IVProbeFinalAssemblyCertifiedBands
open HeckeFamily HeckeDyadic HeckeInverseAmplification HeckeDetectorRawFiber HeckeDetectorBatch
open ProbeFinalAssembly ProbeHighRowFamily Parameters
open CenteredMomentEnergyBands CenteredMomentEnergyState
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthRanges
open CenteredMomentEnergyWidthSchedule IVCenteredMomentDetectorPlainMomentParameters
open CenteredMomentNaturalFixedRaySource
open IVCenteredMomentDetectorEnergyInitialState IVCenteredMomentNaturalFixedRaySource
open IVProbeDetectorPlainMarkedFineField IVProbeDetectorPlainUnmarkedField
local notation "O"=> HeckeFamily.O

theorem source_moments {Δ:ℝ}{D:RHZeroFreeExtension.AnalyticHigh.IV.HighData Δ}(F:RHZeroFreeExtension.AnalyticHigh.IV.SourceData D)
    (counts:IVRawCountParameters F.modulus ⊤ D.t)(mesh:ℝ)(hmesh:0< mesh)
    (hfine:∀j,D.ell j≤ mesh/200)
    (hpositive:PositiveFineSourceInput F mesh)
    (hzero:∃degree:ℕ,∃control:Finset (ℕ×ℕ),∀η₀:Character,∃A:ℝ,0< A ∧ ∀ᶠU:ℝ in atTop,
      ZeroAt (internalQ (sourceFixedIdeal F) η₀) (1/4) (9/4) radialSupportUpper
        0 1 2 (D.t/4) U degree control A):
    ∃J:ℝ,0≤ J ∧ ∀η:Character,∃C:ℝ,0< C ∧
      ∀τ:ℝ,0<τ→τ≤1→∀ᶠZ:ℝ in atTop,
        RHZeroFreeExtension.AnalyticHigh.IV.SourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)):=by
  obtain ⟨Ji,hi⟩:=IVProbeDetectorInverseFields.source_batch_inverse_fields F.modulus ⊤ le_top F counts
  obtain ⟨Jm,hm⟩:=source_batch_plain_marked_fine F mesh hmesh hfine hpositive
  obtain ⟨Ju,hu⟩:=IVProbeDetectorPlainUnmarkedRestrictedField.source_batch_plain_unmarked D F hzero
  refine ⟨(Ji+Jm+Ju:ℕ),by positivity,?_⟩
  intro η
  obtain ⟨Ci,hCi,hi⟩:=hi η
  obtain ⟨Cm,hCm,hm⟩:=hm η
  obtain ⟨Cu,hCu,hu⟩:=hu η
  refine ⟨Ci+Cm+Cu,by positivity,?_⟩
  intro τ hτ hτ1
  filter_upwards [hi,hm,hu] with Z hi hm hu
  have hZ:0< Z:=zero_lt_one.trans hi.1
  let height:ℝ:=Z^(2*τ)
  have hh:0≤ height:=Real.rpow_nonneg hZ.le _
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
  have hrows':∀u∈rows,Z^(1/100:ℝ)≤ rowNorm u:=fun u hu=>(hrows u hu).2.1
  have hext:∀s,(B.external s).re=17/50:=by intro s;rw [hexternal];exact hz
  have hheight:∀s,|(B.external s).im|≤ height:=by intro s;rw [hexternal];exact hzim
  have hinv:=hi.2 d hd a D.ε _ _ _ i B hdata hprofile hupper hwidth hext
    bin label left right hne height hh
  have hmarked:=hm.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    (fun s=> by rw [hupper]) hext bin label left right hne height hh hheight
  have hunmarked:=hu.2 rows hrows' d hd a _ _ _ i B hB hdata hprofile hwidth
    bin label left right hne height hh
  have hU:0≤ Z^d:=Real.rpow_nonneg hZ.le _
  constructor
  · intro n hn σ hσ t ht
    exact ⟨rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).1 hCi',
      rawMoment_mono_constant (hinv.1 n hn σ hσ t ht).2 hCi'⟩
  · intro selected hselected hfirst hsecond n hn σ hσ t ht
    exact (hinv.2 selected hselected hfirst hsecond n hn σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCi' (Real.rpow_nonneg hU _))
  · intro selected hselected hcap j k hjk σ hσ t ht
    exact (hmarked selected hselected (by
      have heq : (3/4:ℝ)+2*((RHIVProbe.momentKappa-3/4)/2)=RHIVProbe.momentKappa := by ring
      simpa only [heq] using hcap) j k hjk σ hσ t ht).trans
      (mul_le_mul_of_nonneg_right hCm' (Real.rpow_nonneg hU _))
  · intro j k hjk σ hσ t ht
    exact (hunmarked j k hjk σ hσ t ht).1.trans
      (mul_le_mul_of_nonneg_right hCu' (Real.rpow_nonneg hU _))


end SevenEighths.IVProbeFinalAssemblyCertifiedBands
end
end OAI

#print axioms OAI.SevenEighths.IVProbeFinalAssemblyCertifiedBands.source_moments

end

end PartIVBlock8

/- BEGIN consolidated probe/FullAssembly.lean -/
section PartIVBlock9
set_option linter.unusedSectionVars false

noncomputable section
open scoped Classical BigOperators
open Filter
namespace OAI.SevenEighths.IVProbeFinalAssembly
open HeckeFamily

def CountParameters.raw {M : Ideal O} [NeZero M] {H : Subgroup (O ⧸ M)ˣ} {εm : ℝ}
    (counts : CountParameters M H εm) : ProbeFinalAssembly.IVRawCountParameters M H εm :=
  ⟨counts.cB,counts.kB,counts.cH,counts.kH,counts.cB_pos,counts.cB_one,
    counts.kB_pos,counts.cH_pos,counts.cH_one,counts.kH_pos⟩
end OAI.SevenEighths.IVProbeFinalAssembly

namespace RHZeroFreeExtension.AnalyticHigh.IV
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeHighRowFamily Parameters HeckeInverseAmplification
variable [RHIVProbe.Geometry] [RHIVProbe.MomentParameter]

def AdaptiveSourceMomentBound {Δ : ℝ} {D : HighData Δ} (F : SourceData D)
    (counts : IVProbeFinalAssembly.CountParameters F.modulus ⊤ D.t) (η : Character)
    (Z τ C height : ℝ) : Prop :=
   ∀ rows : Finset FreeRow, ∀ d a : ℝ, (1/200:ℝ) ≤ d → d ≤ 7/8 → 51/100 < a → a ≤ 1 →
    (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ) ≤ rowNorm u ∧
      (calibrationForSet F.S F.maximal).residueMonoid u.val≠0 ∧ rowNorm u ≤ Z^(d-D.t)) →
    ∀i : ℕ,∀z : ℂ,z.re=17/50 → |z.im|≤ height →
    IVProbeHighRowFamily.SourceMomentsAt F.modulus ⊤ le_top F.S F.exclusions.prime η rows D.ell (fun _ y=>(F.w y:ℂ))
      Z d a D.ε τ (7/8) 2 D.t D.t i z RHIVProbe.momentKappa
      (if 2*a-1≤5/6 then counts.cB else counts.cH)
      (if 2*a-1≤5/6 then counts.kB else counts.kH) C height D.t

lemma AdaptiveSourceMomentBound.mono_constant {Δ : ℝ} {D : HighData Δ} {F : SourceData D}
    {counts : IVProbeFinalAssembly.CountParameters F.modulus ⊤ D.t}
    {η : Character} {Z τ C C' height : ℝ}
    (hZ : 0≤ Z) (h : AdaptiveSourceMomentBound F counts η Z τ C height) (hC : C≤ C') :
    AdaptiveSourceMomentBound F counts η Z τ C' height := by
  intro rows d a hd hd' ha ha' hrows i z hz hzh q B hB hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne
  exact ProbeFinalAssembly.moments_mono_constant (Real.rpow_nonneg hZ _)
    (h rows d a hd hd' ha ha' hrows i z hz hzh q B hB hdata hrev hslots hwidth hprof hupp hext hmesh hbin hfam bin j J K hne) hC

theorem variable_source_count_parameters {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (IVProbeFinalAssembly.CountParameters F.modulus ⊤ D.t) := by
  exact IVProbeFinalAssembly.exists_count_parameters F.modulus ⊤ le_top F.S F.w F.smooth F.compact
    F.positive_support (fun x=>(F.bounded x).1) F.nonzero 1 2 1 (by norm_num) (by norm_num)
    (by norm_num) F.support (fun x=>(F.bounded x).2) D.t D.t_pos

theorem SourceData.full_count_parameters {Δ : ℝ} {D : HighData Δ} (F : SourceData D) :
    Nonempty (IVProbeFinalAssembly.CountParameters F.modulus ⊤ D.t) :=
  variable_source_count_parameters F

theorem actual_source_moments {gap : ℝ} (hgap : 0< gap) {D : HighData gap} (F : SourceData D)
    (counts : IVProbeFinalAssembly.CountParameters F.modulus ⊤ D.t)
    (hOld : HeckeZeroSupremum.beta ≤ (1+RHIVProbe.momentKappa)/2)
    (hBeta : (51/100:ℝ) ≤ HeckeZeroSupremum.beta)
    (hfine : ∀j,D.ell j≤ IVProbeFinalAssemblyCertifiedBands.detectorMesh gap D.t/200) :
    ∃J : ℝ,0≤ J ∧ ∀η : Character,∃C : ℝ,0< C ∧
      ∀τ : ℝ,0<τ→τ≤1→∀ᶠZ : ℝ in atTop,
        AdaptiveSourceMomentBound F counts η Z τ (C*(1+Z^(2*τ))^J) (Z^(2*τ)) := by
  obtain ⟨hp,hz⟩ := IVProbeFinalAssemblyCertifiedBands.plain_inputs_of_premise F hOld hBeta
  obtain ⟨J,hJ,hmom⟩ := IVProbeFinalAssemblyCertifiedBands.source_moments F counts.raw
    (IVProbeFinalAssemblyCertifiedBands.detectorMesh gap D.t)
    (IVProbeFinalAssemblyCertifiedBands.detectorMesh_pos hgap D.t_pos) hfine hp hz
  refine ⟨J,hJ,?_⟩
  intro η
  obtain ⟨C,hC,hmom⟩ := hmom η
  refine ⟨C,hC,?_⟩
  intro τ hτ hτ1
  filter_upwards [hmom τ hτ hτ1] with Z hmom
  intro rows d a hd hd' ha ha' hrows i z hz hzh q
  exact hmom rows d a hd hd' ha ha' hrows i z hz hzh
    (IVAdaptiveCutoff.cutoff RHIVProbe.momentKappa (2*a-1) q)

end RHZeroFreeExtension.AnalyticHigh.IV
end
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.actual_source_moments

#print axioms RHZeroFreeExtension.AnalyticHigh.IV.SourceData.full_count_parameters
#print axioms RHZeroFreeExtension.AnalyticHigh.IV.AdaptiveSourceMomentBound.mono_constant

namespace RHBootstrapCount
noncomputable section
lemma countR_bounds (c delta u : ℝ) (hc0 : 0< c) (hc1 : c<1)
    (hd0 : 0≤ delta) (hd1 : delta≤5/6) (hu0 : 0≤ u) (hu1 : u≤1/2) :
    1-delta≤ countR (5/6) c delta u ∧ countR (5/6) c delta u≤17/12-3*delta/2 := by
  by_cases he : delta=5/6
  · subst delta
    norm_num [countR]
  have hd : delta<5/6 := lt_of_le_of_ne hd1 he
  have hj := J_pos (5/6) c delta u hc0 hc1 hu0 hu1 hd0 hd
  have ht := tstar_range (5/6) c delta u hc0 hc1 hu0 hu1 hd0 hd
  rw [← count_identity (5/6) c delta u (ne_of_gt hj)]
  have hm0 := mul_nonneg (show 0≤5/6-delta by linarith) (show 0≤ tstar (5/6) c delta u-1 by linarith)
  have hm1 := mul_nonneg (show 0≤5/6-delta by linarith) (show 0≤3/2-tstar (5/6) c delta u by linarith)
  unfold longCount
  constructor <;> nlinarith
lemma countR_loss_range (c delta u loss : ℝ) (hc0 : 0< c) (hc1 : c<1)
    (hd0 : 0≤ delta) (hd1 : delta≤5/6) (hu0 : 0≤ u) (hu1 : u≤1/2)
    (hl0 : 0≤ loss) (hl1 : loss≤1/32) :
    0≤ countR (5/6) c delta u+loss ∧ countR (5/6) c delta u+loss≤3/2 ∧
    0≤ countR (5/6) c delta u+loss+delta/2-17/50 ∧
    countR (5/6) c delta u+loss+delta/2-17/50≤2 := by
  obtain ⟨h0,h1⟩ := countR_bounds c delta u hc0 hc1 hd0 hd1 hu0 hu1
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith
end
end RHBootstrapCount
#print axioms RHBootstrapCount.countR_bounds
#print axioms RHBootstrapCount.countR_loss_range

noncomputable section
variable [RHIVProbe.Geometry] [RHIVProbe.MomentParameter]
namespace RHIVProbe
class HighGeometry [Geometry] : Prop where
  ell_lower : 1/6 < ell
variable [HighGeometry]
lemma gate_h_positive : 0 < h := by iv_geometry
end RHIVProbe
variable [RHIVProbe.HighGeometry]
macro "iv_high_geometry" : tactic => `(tactic|
 first
 | (solve | iv_geometry)
 | (solve | try dsimp only [RHIVProbe.x,RHIVProbe.y,RHIVProbe.h,
     RHIVProbe.lowExponent,RHIVProbe.gramExponent,RHIVProbe.boundary]
            obtain ⟨hl,hu,el,eu⟩ := RHIVProbe.scalar_bounds
            have he := RHIVProbe.HighGeometry.ell_lower
            nlinarith only [hl,hu,el,eu,he]))

-- Parametric high adaptation: V2TransportGeometry
namespace RHIVProbe
noncomputable section
def canonicalOffset : ℝ := 7/8-boundary
def sourceSaving : ℝ := y/2-(13/75)*h-canonicalOffset
def smallSaving : ℝ := sourceSaving-1/50
def largeConstant : ℝ := x/2+1+y
lemma transport_geometry : 0 < canonicalOffset ∧ 0 < smallSaving ∧
    h < 9/10 ∧ 4/5 < h ∧ ell < 1 ∧ 0 < x ∧ x < 1 ∧ 0 < y ∧ y < 1 ∧
    5/6 < boundary ∧ boundary < 7/8 := by
  dsimp only [canonicalOffset, sourceSaving, smallSaving, h, x, y, boundary]
  obtain ⟨hl, hu, el, eu⟩ := scalar_bounds
  have he := HighGeometry.ell_lower
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith
lemma smallSaving_lower : (1/20 : ℝ) ≤ smallSaving := by
  dsimp only [smallSaving, sourceSaving, canonicalOffset, h, x, y, boundary]
  obtain ⟨hl, hu, el, eu⟩ := scalar_bounds
  have he := HighGeometry.ell_lower
  linarith only [hl, hu, el, eu]
end
end RHIVProbe

-- Parametric high adaptation: V2CubeNormalizer
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily ProbePhysical ProbeRaySlots PrincipalSignalComparison
open PrincipalMellinResidues ProbePrincipalResidueActual
local notation "O" => HeckeFamily.O

theorem iv_actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0< c) (hcb : c≤ b)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hellsum : ∑j,ell j=RHIVProbe.ell)
    (W : Fin K→ℝ→ℝ) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hcompact : ∀j,HasCompactSupport (W j))
    (hsupp : ∀j,Function.support (W j)⊆Set.Ioo c b) (hp : ∀j y,0≤ W j y) (hne : ∀j,W j≠0)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧ ∀ᶠZ : ℝ in atTop,
      let T := fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j))
      let normer := sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
          (slotMass T (residueWeights W (fun j=> Z^(ell j)))) : ℂ)
      normer≠0 ∧ ‖normer⁻¹‖≤ C*Z^nu := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let cs := sourceResidueConstant W0 W1 (∏P∈S,P)
  refine ⟨‖cs⁻¹‖+1,by positivity,?_⟩
  have hpos (j : Fin K) : tsupport (W j)⊆Set.Ioi 0 := by
    apply Set.Subset.trans (closure_minimal (Set.Subset.trans (hsupp j) Set.Ioo_subset_Icc_self) isClosed_Icc)
    intro y hy
    exact lt_of_lt_of_le hc hy.1
  filter_upwards [power_ray_mass_and_normalizer M H hH S W c b hc hcb hsupp hW hcompact hpos hp hne ell hell nu hnu,
    eventually_gt_atTop (0:ℝ)] with Z hmass hZ
  dsimp only
  refine ⟨ProbePrincipalNormalizer.signed_source_normalizer_ne_zero (∏P∈S,P)
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hr0 hr1 hp0 hp1 hn0 hn1 Finset.univ
    (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
    (residueWeights W (fun j=> Z^(ell j))) Z (RHIVProbe.ell) hZ (fun j _=> hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (RHIVProbe.ell)
        (slotMass (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=> Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end

end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2PrincipalDomain

set_option linter.unusedVariables false

/-! Actual local Euler formulas on the perturbed x-half-plane.
The proofs use upstream coordinate norm estimates and rational denominator
bounds; no perturbed local bound is assumed. The broad summable17/10 bound
is retained, and the narrower second rectangle has exact decay72599/40000.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler

theorem iv_principalDomain_unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (RHIVProbe.boundary:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(24/25:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(11/5:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(9/10:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(87/100:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(77/100:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(9/10:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(17/10:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(17/10:ℝ)) : a*b ≤ T := by
    calc
      a*b ≤ Q^a' * Q^b' := mul_le_mul haa hbb hb (Real.rpow_nonneg hQ0.le _)
      _ = Q^(a'+b') := (Real.rpow_add hQ0 _ _).symm
      _ ≤ T := Real.rpow_le_rpow_of_exponent_le hQ1 he
  have hKV : ‖K‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hK hV (by norm_num)
  have hDV : ‖D‖*‖V‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hV (by norm_num)
  have hDW : ‖D‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hD hW (by norm_num)
  have hVW : ‖V‖*‖W‖ ≤ T := hprod _ _ _ _ (norm_nonneg _) (norm_nonneg _) hV hW (by norm_num)
  have hDVW : ‖D‖*‖V‖*‖W‖ ≤ T :=
    (mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hWh).trans hDV
  let P := markedFactor R V (Q:ℂ)⁻¹ K (-D+W*R) 1
  have hE : ‖P+D‖ ≤ 28*T := by
    have h := ProbeLocal.unramified_marked_error_bound R V (Q:ℂ)⁻¹ K W D hRh hVh hqi hDh
    have hrw : ‖R‖*(1+‖W‖) ≤ 2*T := by
      calc
        _ ≤ ‖R‖*2 := mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg _)
        _ ≤ _ := by nlinarith
    dsimp only [P]
    nlinarith
  have h := ProbeLocal.continuedCorrection_defect_bound V W D P hVh hDh
  change ‖ProbeLocal.continuedCorrection V W D P-1‖ ≤ 240*T
  have hWE : (1+‖W‖)*‖P+D‖ ≤ 56*T := by
    calc
      _ ≤ 2*(28*T) := mul_le_mul (by linarith) hE (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  nlinarith


lemma iv_principalDomain_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : RHIVProbe.boundary≤ x.re) (hz : 4/25≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0< Q := by linarith
  have hQ1 : 1≤ Q := by linarith
  have hR : ‖coordR Q A x z‖≤1/2 := by
    apply (coordR_norm_le Q hQ0 A x z hA).trans
    apply rpow_le_half Q _ hQ
    linarith
  have hV : ‖coordV Q z‖≤1/2 := by
    rw [coordV_norm Q hQ0]
    apply rpow_le_half Q _ hQ
    linarith
  have hD : ‖coordD Q eta v x‖≤1/2 := by
    apply (coordD_norm_le Q hQ0 eta v x he hv).trans
    apply rpow_le_half Q _ hQ
    linarith
  exact ⟨ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hR,
    ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hV,ProbeLocal.one_sub_ne_zero_of_norm_le_half _ hD⟩

theorem iv_principalDomain_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedClosed Q A eta v x w z) {x : ℂ|RHIVProbe.boundary< x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := iv_principalDomain_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem iv_principalDomain_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : RHIVProbe.boundary≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedClosed Q A eta v x w z) {w : ℂ|9/10< w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := iv_principalDomain_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem iv_principalDomain_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : RHIVProbe.boundary≤ x.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedClosed Q A eta v x w z) {z : ℂ|4/25< z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := iv_principalDomain_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


end
end RHZeroFreeExtension.AnalyticHigh

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbePhysical OAI.ActualEisensteinCubic
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma iv_principalDomain_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : RHIVProbe.boundary≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply iv_principalDomain_unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem iv_principalDomain_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : RHIVProbe.boundary≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=> iv_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma iv_principalDomain_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : RHIVProbe.boundary≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    Multipliable (fun P : {P : OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z
  let B := fun P : {P : OAI.SevenEighths.ProbePhysical.PrimeIdeal // P.val∉S}=> globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    iv_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem iv_principalDomain_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> globalClosedCorrection η S x w z) {x : ℂ|RHIVProbe.boundary< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply iv_principalDomain_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact iv_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem iv_principalDomain_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : RHIVProbe.boundary≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> globalClosedCorrection η S x w z) {w : ℂ|9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply iv_principalDomain_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact iv_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem iv_principalDomain_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : RHIVProbe.boundary≤ x.re) (hw : 9/10≤ w.re) :
    AnalyticOnNhd ℂ (fun z=> globalClosedCorrection η S x w z) {z : ℂ|4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply iv_principalDomain_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact iv_principalDomain_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_principalDomain_globalClosedCorrection_analytic_x

-- Parametric high adaptation: V2FiniteProduct

set_option linter.unusedVariables false

/-! Actual selected Euler factors and ordered contour shifts on the perturbed
half-plane. Every localMultiplier/slotMultiplier/sourceMultiplier below is
upstream's genuine function. We reprove the domain-dependent bounds from
coordinates and the new proved correction estimate; we reuse generic Mellin
boundary/residue theorems, keeping both ordered principal poles.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
open OAI OAI.SevenEighths
open OAI.ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeMellinBoundary ProbeFiniteProductBounds
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

theorem iv_correction_lower_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hb := (iv_principalDomain_idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem iv_correction_ne_zero (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (iv_correction_lower_bound η S hS P hP x w z hx hw hz))

theorem iv_correction_inverse_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hh := iv_correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma iv_marked_differentiableAt_w (η : Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : RHIVProbe.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := iv_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma iv_marked_differentiableAt_z (η : Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : RHIVProbe.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := iv_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem iv_local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := iv_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := iv_principalDomain_unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := iv_marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := iv_correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem iv_local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := iv_principalDomain_unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := iv_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := iv_marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := iv_correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma iv_marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : RHIVProbe.boundary ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hR : ‖coordR Q A x z‖ ≤ 1/2 :=
    (coordR_norm_le Q hQ0 A x z hA).trans (rpow_le_half Q _ hQ (by linarith))
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith)
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by
    apply (coordW_norm_le Q hQ0 1 w (by simp)).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hD : ‖coordD Q η 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 η 1 x hη (by simp)).trans (rpow_le_half Q _ hQ (by linarith))
  have hK : ‖coordK Q η x w‖ ≤ 1 := by
    apply (coordK_norm_le Q hQ1 η x w hη).trans
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : 1-x.re-w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hqi : ‖(Q : ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0]
    exact inv_le_one_of_one_le₀ hQ1
  have he := unramified_marked_error_bound (coordR Q A x z) (coordV Q z) (Q : ℂ)⁻¹
    (coordK Q η x w) (coordW Q 1 w) (coordD Q η 1 x) hR hV hqi hD
  have h1 : 12*‖coordR Q A x z‖*(1+‖coordW Q 1 w‖) ≤ 12 := by
    calc
      _ ≤ 12*(1/2:ℝ)*(1+1) := by gcongr
      _ = _ := by norm_num
  have h2 : 4*‖coordK Q η x w‖*‖coordV Q z‖ ≤ 2 := by
    calc
      _ ≤ 4*1*(1/2:ℝ) := by gcongr
      _ = _ := by norm_num
  have hn := norm_sub_le (PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x)
    (coordD Q η 1 x)
  rw [add_sub_cancel_right] at hn
  change ‖PrincipalSlotEstimate.regionMarked Q A η x w z + coordD Q η 1 x‖ ≤ _ at he
  linarith

lemma iv_replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hV1 : ‖1-V‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) V
    simp only [norm_one] at this
    linarith
  have hW1 : ‖1-W‖ ≤ 2 := by
    have := norm_sub_le (1 : ℂ) W
    simp only [norm_one] at this
    linarith
  have hBq : ‖B-q‖ ≤ R+1 := (norm_sub_le B q).trans (add_le_add hB hq)
  have hVW : ‖1-V*W‖ ≤ 2 := by
    have hn := norm_sub_le (1 : ℂ) (V*W)
    rw [norm_one,norm_mul] at hn
    have hm : ‖V‖*‖W‖ ≤ 1/2 := by
      calc
        _ ≤ (1/2:ℝ)*1 := by gcongr
        _ = _ := by ring
    linarith
  have hi := inv_one_sub_norm_le_two D hD
  unfold compensatedReplacement
  rw [div_eq_mul_inv,norm_mul]
  calc
    _ ≤ (‖B-q‖*‖1-V‖*‖1-W‖*‖P‖ + ‖q‖*‖1-V*W‖)*2 := by
      apply mul_le_mul _ hi (norm_nonneg _) (by positivity)
      simpa only [norm_mul] using norm_sub_le ((B-q)*(1-V)*(1-W)*P) (q*(1-V*W))
    _ ≤ ((R+1)*2*2*16+1*2)*2 := by gcongr
    _ ≤ 200*(1+R) := by linarith

lemma iv_localBound_nonneg (Bx Bz : ℝ) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold localBound
  positivity

theorem iv_local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHIVProbe.boundary) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let Q : ℝ := Ideal.absNorm P.val
  have hQ : 4 ≤ Q := by dsimp [Q]; exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  have hB : ‖star (idealCoeff η P.val)*(Q : ℂ)^x‖ ≤ Q^Bx := by
    rw [norm_mul,norm_star,Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    exact (mul_le_of_le_one_left (Real.rpow_nonneg hQ0.le _) (idealCoeff_norm_le_one η _)).trans
      (Real.rpow_le_rpow_of_exponent_le hQ1 hx.2)
  have hq : ‖(Q : ℂ)^(-w)‖ ≤ 1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0,Complex.neg_re]
    exact (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith : -w.re ≤ 0)).trans_eq (Real.rpow_zero Q)
  have hV : ‖coordV Q z‖ ≤ 1/2 := by
    rw [coordV_norm Q hQ0]; exact rpow_le_half Q _ hQ (by linarith [hz.1])
  have hW : ‖coordW Q 1 w‖ ≤ 1 := by simpa only [coordW,one_mul] using hq
  have hD : ‖coordD Q (idealCoeff η P.val) 1 x‖ ≤ 1/2 :=
    (coordD_norm_le Q hQ0 _ 1 x (idealCoeff_norm_le_one η _) (by simp)).trans
      (rpow_le_half Q _ hQ (by linarith [hx.1]))
  have hm : ‖idealMarkedClosed η P x w z‖ ≤ 16 :=
    iv_marked_bound Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := iv_replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := iv_correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
  have hp : ‖(Q : ℂ)^(z-1)‖ ≤ Q^(Bz-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hQ0]
    apply Real.rpow_le_rpow_of_exponent_le hQ1
    simpa only [Complex.sub_re,Complex.one_re] using sub_le_sub_right hz.2 1
  unfold localMultiplier
  dsimp only
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  change _ ≤ Q^(Bz-1)*(400*(1+Q^Bx))
  calc
    _ ≤ Q^(Bz-1)*(200*(1+Q^Bx)*2) := by gcongr
    _ = _ := by ring

lemma iv_selectedBound_nonneg (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => iv_localBound_nonneg Bx Bz P)

lemma iv_slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (iv_localBound_nonneg Bx Bz P))

theorem iv_selected_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => iv_local_analytic_w η S hS P (hT P hp) x z hx hz)

theorem iv_selected_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => iv_local_analytic_z η S hS P (hT P hp) x w hx hw)

theorem iv_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (iv_local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem iv_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (iv_local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem iv_selected_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHIVProbe.boundary) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun P hp => iv_local_norm_bound η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem iv_slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHIVProbe.boundary) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (iv_local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma iv_global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hb := iv_principalDomain_globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem iv_combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (iv_principalDomain_globalClosedCorrection_analytic_w η S hS x z hx hz).mul (iv_slot_analytic_w η S hS J T b hT x z hx hz)

theorem iv_combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : RHIVProbe.boundary ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (iv_principalDomain_globalClosedCorrection_analytic_z η S hS x w hx hw).mul (iv_slot_analytic_z η S hS J T b hT x w hx hw)

theorem iv_combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (RHIVProbe.boundary) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [norm_mul]
  exact mul_le_mul (iv_global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (iv_slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem iv_selected_initial_identity (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ)
    (hx : 3/2 < x.re) (hw : 2 < w.re) (hz : 1/6 < z.re) :
    (∏ P ∈ T, (Ideal.absNorm P.val : ℂ)^(z-1)) *
      spectralCompensatedHigh S T η x w z
        (fun P => star (idealCoeff η P.val)*(Ideal.absNorm P.val : ℂ)^x)
        (fun P => (Ideal.absNorm P.val : ℂ)^(-w)) =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w /
        LFunction (η.excludePrimes S hS.prime) x) *
        (globalClosedCorrection η S x w z * selectedMultiplier η T x w z) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [spectralCompensatedHigh_continued S hS T hT η x w z _ _ hx hw hz]
  simp only [selectedMultiplier,localMultiplier,Finset.prod_mul_distrib,Complex.ofReal_natCast]
  ring_nf

theorem iv_source_w_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : RHIVProbe.boundary ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1< cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (iv_slotBound_nonneg J T b _ _)) 0
  · exact (iv_combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using iv_combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem iv_source_z_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : RHIVProbe.boundary ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
        LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ
    (η.excludePrimes S hS.prime) s hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) he he'
    (mul_nonneg (by norm_num) (iv_slotBound_nonneg J T b _ _)) 0
  · exact (iv_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using iv_combined_slot_bound η S hS.tail J T b hT s
      1 ((x : ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)

theorem iv_source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : RHIVProbe.boundary ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (iv_combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
  have hYn : (Y : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hY.ne'
  have he : (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun w => ((X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z /
      LFunction (η.excludePrimes S hS.prime) s) * (Y:ℂ)^(w-1) * mellin W1 w *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext w; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hYn)

theorem iv_source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : RHIVProbe.boundary ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (iv_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hXn : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hZn : (Z : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have he : (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) =
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w / LFunction (η.excludePrimes S hS.prime) s) *
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z *
        (globalClosedCorrection η S s w z * slotMultiplier η J T b s w z)) := by
    funext z; unfold sourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hXn | exact Or.inl hZn)

theorem iv_source_w_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : RHIVProbe.boundary ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0) {cw : ℝ} (hcw : 1< cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (iv_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY s z hs (by linarith)).mono (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · exact iv_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1 M X Y Z hY s z hs hz hEta hcw

theorem iv_source_residue_z_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : RHIVProbe.boundary ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1/6+e) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) =
      verticalIntegral (33/200) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) +
        K 1 (1/6) * fixedPrincipalResidue M / 6 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (iv_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · exact iv_source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ s hs hEta he he'


theorem iv_fixed_source_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : RHIVProbe.boundary ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  constructor
  · intro z hz
    exact iv_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY s z hs (by rw [hz]; linarith) hEta hcw
  · exact iv_source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0
      (∏ P ∈ S, P) X Y Z hX hZ s hs hEta he he'

lemma iv_boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

theorem iv_fixed_source_ordered_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : RHIVProbe.boundary ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hh := iv_fixed_source_boundaries S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ η s hs hEta hcw he he'
  dsimp only at hh ⊢
  refine ⟨?_,hh.2⟩
  intro z hz
  convert iv_boundary_mul_const _ _ _ (hh.1 z hz) (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
  funext w
  ring

theorem iv_uniform_closed_box_bound {ι : Type*} (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (s w z : ℂ),
      s.re ∈ Icc (RHIVProbe.boundary) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (iv_slotBound_nonneg J T b Bx Bz),
    fun η s w z hs hw hz => iv_combined_slot_bound η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩

end
end RHZeroFreeExtension.AnalyticHigh

-- Parametric high adaptation: V2FiniteProductX

set_option linter.unusedVariables false

/-! Domain continuation of the genuine source multiplier, including its
regular reciprocal at the principal point. No improved continuation is
postulated: the proofs combine new proved Euler analyticity with the generic
actual Hecke reciprocal on Re(s)> beta.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory
open OAI OAI.SevenEighths
open OAI.ActualEisensteinCubic CompletedGauss ProbePhysical ProbeEuler ProbeLocal
open HeckeFamily PrincipalMellinResidues ProbeFiniteProductBounds ProbeFiniteProductX
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma iv_marked_differentiableAt_x (η : Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : RHIVProbe.boundary ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := iv_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem iv_local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | RHIVProbe.boundary < x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := iv_principalDomain_unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := iv_principalDomain_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := iv_marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := iv_correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem iv_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | RHIVProbe.boundary < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => iv_local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem iv_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | RHIVProbe.boundary < x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (iv_local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem iv_window_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | RHIVProbe.boundary < x.re} :=
  iv_slot_analytic_x η S hS J T _ hT w z hw hz

theorem iv_combined_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | RHIVProbe.boundary < x.re} :=
  (iv_principalDomain_globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (iv_selected_analytic_x η S hS T hT w z hw hz)

theorem iv_combined_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | RHIVProbe.boundary < x.re} :=
  (iv_principalDomain_globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (iv_slot_analytic_x η S hS J T b hT w z hw hz)

theorem iv_continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (RHIVProbe.boundary : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (RHIVProbe.boundary : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (iv_principalDomain_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (iv_slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem iv_continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem iv_continued_source_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply iv_continued_source_eq_raw
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem iv_source_analytic_x_off_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (RHIVProbe.boundary : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (RHIVProbe.boundary : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; linarith
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (iv_principalDomain_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (iv_slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem iv_continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : RHIVProbe.boundary< a) (hβ : HeckeZeroSupremum.beta< a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤ x.re ∧ x.re≤ c} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply (iv_continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

theorem iv_continued_source_principal_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (w z : ℂ)
    (hχ : (η.excludePrimes S hS).residue=1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z 1 w z=0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp only [continuedSourceMultiplier,HeckeReciprocal.reciprocal_principal_one _ hχ,mul_zero,zero_mul]

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_continued_source_analytic_x

-- Parametric high adaptation: V2PrincipalContours

set_option linter.unusedVariables false

/-! Full actual ordered Mellin-contour, Fubini, and uniform-tail interface
on the perturbed x-domain. All functions, including arithmeticMultiplier and
continuedSourceMultiplier, remain upstream definitions. Domain-dependent
calls are supplied by newly proved bounds; the generic Mellin/Hecke APIs are
reused. The double residue retains the square of the principal residue.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O
local instance : Countable OAI.ActualEisensteinCubic.O := OAI.ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : Countable Id := ConcretePrimeRowBridge.idealGenerator_injective.countable

@[fun_prop] lemma iv_measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0< Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

lemma iv_ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma iv_global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => iv_ideal_correction_measurable η P.val x w z hx hw hz)

lemma iv_local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : OAI.SevenEighths.ProbePhysical.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := iv_ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma iv_slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (iv_local_multiplier_measurable η P x w z hx hw hz)

lemma iv_zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0≤ zBoxAmplitude M Bz := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma iv_fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤ zBoxAmplitude M Bz*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hb := principal_poleRemoved_growth (fixedPrincipal M) rfl
    (show (19/20 : ℝ)≤(6*((ξ:ℂ)+t*I) : ℂ).re by simp; linarith [hξ.1])
  have hn : ‖6*((ξ:ℂ)+t*I)+1‖≤ max 6 (6*Bz+1)*height t := by
    apply (Complex.norm_le_abs_re_add_abs_im _).trans
    have hm : (6:ℝ)≤ max 6 (6*Bz+1) := le_max_left _ _
    have hm' : 6*ξ+1≤ max 6 (6*Bz+1) := (by linarith [hξ.2] : 6*ξ+1≤6*Bz+1).trans (le_max_right _ _)
    simp only [add_re,add_im,ofReal_re,ofReal_im,mul_re,mul_im,I_re,I_im,
      mul_zero,sub_zero,add_zero,zero_add,mul_one,one_re,one_im]
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero,add_zero]
    rw [abs_of_pos (by linarith [hξ.1] : 0<6*ξ+1),abs_mul]
    norm_num
    unfold height
    nlinarith [mul_le_mul_of_nonneg_right hm (abs_nonneg t)]
  have hi : |(6*((ξ:ℂ)+t*I) : ℂ).im|=6*|t| := by simp [abs_mul]
  have ht : (3+6*|t|)^2≤36*height t^2 := by
    have hh : 3+6*|t|≤6*height t := by unfold height; linarith
    have hp := pow_le_pow_left₀ (by positivity : 0≤3+6*|t|) hh 2
    simpa only [mul_pow,show (6:ℝ)^2=36 by norm_num] using hp
  have hC := (principalConstant_pos M).le
  have hmax : 0≤ max (6:ℝ) (6*Bz+1) := le_trans (by norm_num) (le_max_left _ _)
  have hh := (height_pos t).le
  rw [hi] at hb
  calc
    _ ≤ principalConstant M*‖6*((ξ:ℂ)+t*I)+1‖*(3+6*|t|)^2 := hb
    _ ≤ principalConstant M*(max 6 (6*Bz+1)*height t)*(36*height t^2) := by
      gcongr
    _ = _ := by unfold zBoxAmplitude; ring

lemma iv_LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma iv_LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (iv_LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma iv_reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta< a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma iv_LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ≤‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖≤ A) :
    ‖LFunction χ s‖≤ A/δ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _ ≤ A := hA

lemma iv_fixed_principal_w_bound (M : Id) [NeZero M] {cw υ : ℝ} (hcw : 1< cw)
    (hυ : υ∈Icc (19/20 : ℝ) cw) (hυ1 : υ≠1) (t : ℝ) :
    ‖LFunction (fixedPrincipal M) ((υ:ℂ)+t*I)‖≤
      (wAmplitude M cw/|υ-1|)*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h0 : (υ:ℂ)+t*I≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hυ.1]
  have h1 : (υ:ℂ)+t*I≠1 := by intro h; exact hυ1 (by simpa using congrArg Complex.re h)
  have hδ : 0 < |υ-1| := abs_pos.mpr (sub_ne_zero.mpr hυ1)
  have h := iv_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ
    (pole_distance_vertical 1 υ t) (fixed_principal_w_growth M hcw hυ t)
  convert h using 1
  ring

lemma iv_fixed_principal_z_bound (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) (hξ1 : 6*ξ≠1) :
    ‖LFunction (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤
      (zBoxAmplitude M Bz/|6*ξ-1|)*height t^3 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h0 : (6*((ξ:ℂ)+t*I) : ℂ)≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hξ.1]
  have h1 : (6*((ξ:ℂ)+t*I) : ℂ)≠1 := by intro h; exact hξ1 (by simpa using congrArg Complex.re h)
  have hd : |6*ξ-1|≤‖6*((ξ:ℂ)+t*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+t*I)-1)
  have hδ : 0 < |6*ξ-1| := abs_pos.mpr (sub_ne_zero.mpr hξ1)
  have h := iv_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ hd
    (iv_fixed_principal_z_box_growth M Bz ξ t hξ)
  convert h using 1
  ring

lemma iv_arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma iv_arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hH := iv_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := iv_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (iv_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (iv_LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (iv_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun p : HeightSpace => 6*p.1.2))
  have hZL' : Measurable (fun p : HeightSpace => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+p.1.2*I))) := by
    convert hZL using 1
    funext p
    congr 1
    push_cast
    ring
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma iv_boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0< boxScale X Y Z a Bs Bz cw := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

lemma iv_height_le_joint_s (t v u : ℝ) : height t≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]
lemma iv_height_le_joint_z (t v u : ℝ) : height v≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]
lemma iv_height_le_joint_w (t v u : ℝ) : height u≤ jointHeight t v u := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

lemma iv_arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0<δw) (hdz : 0<δz)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw≤‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz≤‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hx := cpow_le_scaleBound hX (1/2-((ξ:ℂ)+p.1.2*I))
    (show (1/2-((ξ:ℂ)+p.1.2*I) : ℂ).re∈Icc (1/2-Bz) (1/2-33/200) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero]
      norm_num only [show (1/2:ℂ).re=1/2 by norm_num]
      constructor <;> linarith [hξ.1,hξ.2])
  have hz := cpow_le_scaleBound hZ (((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)
    (show ((((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1) : ℂ).re∈Icc (a+33/200-1) (Bs+Bz-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hσ.1,hσ.2,hξ.1,hξ.2])
  have hy := cpow_le_scaleBound hY (((υ:ℂ)+p.2*I)-1)
    (show (((υ:ℂ)+p.2*I)-1 : ℂ).re∈Icc (19/20-1) (cw-1) by
      simp only [sub_re,add_re,ofReal_re,mul_re,ofReal_im,I_re,I_im,mul_zero,zero_mul,sub_self,add_zero,one_re]; constructor <;> linarith [hυ.1,hυ.2])
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖≤ C*height p.1.1^2 := by
    apply (hR _ (by simpa using hσ.1)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg p.1.1]
  have hh := iv_combined_slot_bound η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
    ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) Bs Bz
    (by simpa using And.intro (ha.trans hσ.1) hσ.2) (by simpa using hυ.1) (by simpa using hξ)
  have hw0 : (υ:ℂ)+p.2*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hυ.1]
  have hw1 : (υ:ℂ)+p.2*I≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hwgap; linarith
  have hz0 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith [hξ.1]
  have hz1 : (6*((ξ:ℂ)+p.1.2*I) : ℂ)≠1 := by
    intro h; rw [h,sub_self,norm_zero] at hzgap; linarith
  have hlz0 := iv_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (iv_fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := iv_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
    (fixed_principal_w_growth (∏P∈S,P) hcw hυ p.2)
  have hlz : ‖LFunction (fixedPrincipal (∏P∈S,P)) (6*((ξ:ℂ)+p.1.2*I))‖≤
      (zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3 := by convert hlz0 using 1; ring
  have hlw : ‖LFunction (fixedPrincipal (∏P∈S,P)) ((υ:ℂ)+p.2*I)‖≤
      (wAmplitude (∏P∈S,P) cw/δw)*height p.2^3 := by convert hlw0 using 1; ring
  have hp1 := (height_pos p.1.1).le
  have hp2 := (height_pos p.1.2).le
  have hp3 := (height_pos p.2).le
  have hpJ := (jointHeight_pos p.1.1 p.1.2 p.2).le
  have hsX := (scaleBound_pos X (1/2-Bz) (1/2-33/200)).le
  have hsY := (scaleBound_pos Y (19/20-1) (cw-1)).le
  have hsZ := (scaleBound_pos Z (a+33/200-1) (Bs+Bz-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (iv_slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (iv_zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
  have hAW := div_nonneg (wAmplitude_pos (∏P∈S,P) hcw).le hdw.le
  calc
    _ = ‖(X:ℂ)^(1/2-((ξ:ℂ)+p.1.2*I))‖ *
        ‖(Z:ℂ)^(((σ:ℂ)+p.1.1*I)+((ξ:ℂ)+p.1.2*I)-1)‖ *
        ‖(Y:ℂ)^(((υ:ℂ)+p.2*I)-1)‖ *
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)‖ *
        ‖globalClosedCorrection η S ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          slotMultiplier η J T b ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ := by
      simp only [arithmeticMultiplier,norm_mul]
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*height p.1.1^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*height p.1.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*height p.2^3) := by
      gcongr <;> first | positivity | exact hlz | exact hlw
    _ ≤ scaleBound X (1/2-Bz) (1/2-33/200)*scaleBound Z (a+33/200-1) (Bs+Bz-1)*
        scaleBound Y (19/20-1) (cw-1)*(C*jointHeight p.1.1 p.1.2 p.2^2)*((3/2)*slotBound J T b Bs Bz)*
        ((zBoxAmplitude (∏P∈S,P) Bz/δz)*jointHeight p.1.1 p.1.2 p.2^3)*
        ((wAmplitude (∏P∈S,P) cw/δw)*jointHeight p.1.1 p.1.2 p.2^3) := by
      gcongr <;> first | positivity | exact iv_height_le_joint_s _ _ _ | exact iv_height_le_joint_z _ _ _ | exact iv_height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma iv_arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply iv_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem iv_continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I))
    (iv_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|) 8
    (iv_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall (fun p => iv_arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

lemma iv_outer_height_ne_zero_ae : ∀ᵐp : HeightSpace ∂heightMeasure, p.1.1≠0 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hh : ∀ᵐp : ℝ×ℝ ∂volume.prod volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  exact Measure.quasiMeasurePreserving_fst.ae hh

lemma iv_continued_joint_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    (fun p : HeightSpace => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) =ᵐ[heightMeasure]
    (fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
      ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
      (slotMultiplier η J T b ((a:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  filter_upwards [iv_outer_height_ne_zero_ae] with p hp
  apply iv_continued_source_eq_raw
  · intro h; exact hp (by simpa using congrArg Complex.im h)
  · intro h; exact hp (by simpa using congrArg Complex.im h)

theorem iv_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply (iv_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [iv_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem iv_source_joint_fubini {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    ((∫p, F p ∂heightMeasure)=∫t : ℝ,∫v : ℝ,∫u : ℝ,F ((t,v),u)) ∧
    ((∫p, F p ∂heightMeasure)=∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((t,v),u)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  have hi := iv_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

lemma iv_arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1< cw) (hC : 0≤ C) (hw : 0≤δw) (hz : 0≤δz) :
    0≤ arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (iv_boxScale_pos X Y Z a Bs Bz cw).le
  have hb := iv_slotBound_nonneg J T b Bs Bz
  have hza := iv_zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

theorem iv_continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) (N : ℕ) :
    ∃ C K : ℝ, 0≤ C ∧ 0< K ∧ ∀axis : SliceAxis,∀R : ℝ,
      let F := fun p : HeightSpace =>
        continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume)≤
        arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1| *K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := iv_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := iv_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (iv_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,iv_arithmetic_profile_eq_source] using hh

theorem iv_source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,K,hC,hK,hslice⟩ := iv_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
    ha0 ha1 hW0 hW1 X Y Z a (1/6+e) (19/20) 3 hX hY hZ ha hβ
    (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  have hi := (hslice .s t).1
  have hs0 : (a:ℂ)+t*I≠0 := by
    intro h; have hh := congrArg Complex.re h; simp at hh; linarith
  have hpair : Integrable (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I))
        ((19/20:ℝ)+q.2*I) ((1/6+e:ℝ)+q.1*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((1/6+e:ℝ)+q.1*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((19/20:ℝ)+q.2*I)) (volume.prod volume) := by
    simpa only [sliceMap,iv_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem iv_source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : RHIVProbe.boundary≤ s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0< e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (iv_slotBound_nonneg J T b _ _))
    (iv_zBoxAmplitude_nonneg _ _) 0 3
  · exact (iv_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using iv_combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact iv_fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem iv_source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
    verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
    HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
    (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (RHIVProbe.boundary : ℝ)≤(((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := iv_source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (iv_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9/10 : ℝ)< w.re
    linarith [hw.1]
  · intro z hz
    have hh := iv_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith) hη hcw
    convert iv_boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (iv_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num)).mono
    intro z hz
    change (4/25 : ℝ)< z.re
    linarith [hz.1]
  · exact hzb
  · exact iv_source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem iv_source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
    ∀ᵐt : ℝ, let s : ℂ := (a:ℂ)+t*I
      let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s)
      let π := fixedSourcePrincipal S hS.prime
      verticalIntegral (1/6+e) (fun z => verticalIntegral cw
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) =
      verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
        (fun w => K w z*LFunction π (6*z)*LFunction π w)) +
      HeckeReciprocal.regularizedL π 1*verticalIntegral (33/200) (fun z => K 1 z*LFunction π (6*z)) +
      (HeckeReciprocal.regularizedL π 1)^2/6*K 1 (1/6) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply iv_source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

lemma iv_residue_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s z : ℂ) :
    residueArithmetic η S hS J T b X Z s z*profile W0 W1 s 1 z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s 1 z *
        LFunction (fixedSourcePrincipal S hS) (6*z) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold residueArithmetic profile continuedSourceMultiplier
  simp only [sub_self,Complex.cpow_zero,mul_one]
  ring

lemma iv_residue_arithmetic_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (hβ : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) :
    Measurable (fun q : ℝ×ℝ => residueArithmetic η S hS J T b X Z
      ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hH := iv_global_correction_measurable η S (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := iv_slot_multiplier_measurable η J T b (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (iv_reciprocal_vertical_continuous (η.excludePrimes S hS) a hβ).measurable.comp
    (by fun_prop : Measurable (fun q : ℝ×ℝ => q.1))
  have hL := (iv_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
    (mul_ne_zero (by norm_num) hξ0) hξ1).measurable.comp
      (by fun_prop : Measurable (fun q : ℝ×ℝ => 6*q.2))
  have hL' : Measurable (fun q : ℝ×ℝ => LFunction (fixedSourcePrincipal S hS)
      (6*((ξ:ℂ)+q.2*I))) := by
    convert hL using 1
    funext q
    congr 1
    push_cast
    ring
  unfold residueArithmetic
  fun_prop (disch := aesop)

lemma iv_residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Z a ξ C : ℝ) (hX : 0< X) (hZ : 0< Z) (ha : RHIVProbe.boundary≤ a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (q : ℝ×ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)‖≤
      residueAmplitude S J T b X Z a ξ C*jointHeight q.1 q.2 0^5 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖≤ C*height q.1^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := iv_combined_slot_bound η S hS.tail J T b hT ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := iv_fixed_principal_z_bound (∏P∈S,P) ξ ξ q.2 ⟨hξ,le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1/2-ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a+ξ-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (iv_slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (iv_zBoxAmplitude_nonneg (∏P∈S,P) ξ) (abs_nonneg (6*ξ-1))
  have hq1 := (height_pos q.1).le
  have hq2 := (height_pos q.2).le
  have hqJ := (jointHeight_pos q.1 q.2 0).le
  calc
    _ = X^(1/2-ξ)*Z^(a+ξ-1)*
        ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖ *
        ‖globalClosedCorrection η S ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
          slotMultiplier η J T b ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)‖ *
        ‖LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))‖ := by
      simp only [residueArithmetic,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos hX,
        Complex.norm_cpow_eq_rpow_re_of_pos hZ]
      norm_num
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*height q.1^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*height q.2^3) := by
      gcongr
      first | positivity | exact hL
    _ ≤ X^(1/2-ξ)*Z^(a+ξ-1)*(C*jointHeight q.1 q.2 0^2)*((3/2)*slotBound J T b a ξ)*
        ((zBoxAmplitude (∏P∈S,P) ξ/|6*ξ-1|)*jointHeight q.1 q.2 0^3) := by
      gcongr <;> first | positivity | exact iv_height_le_joint_s _ _ _ | exact iv_height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

lemma iv_residueAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal) (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Z a ξ C : ℝ)
    (hX : 0≤ X) (hZ : 0≤ Z) (hC : 0≤ C) : 0≤ residueAmplitude S J T b X Z a ξ C := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hb := iv_slotBound_nonneg J T b a ξ
  have hza := iv_zBoxAmplitude_nonneg (∏P∈S,P) ξ
  unfold residueAmplitude
  positivity

theorem iv_continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) 5 0
  have hm := iv_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hb := iv_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (iv_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ×ℝ => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap,onLines,ofReal_one,ofReal_zero,zero_mul,add_zero] using
    iv_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)

theorem iv_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  apply (iv_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [iv_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem iv_source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hi := iv_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral,integral_const_mul,mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))).const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem iv_residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hi := iv_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem iv_source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral a (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral a (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
  let π := fixedSourcePrincipal S hS.prime
  let R := HeckeReciprocal.regularizedL π 1
  let A := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral cw
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let B := fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral (19/20)
    (fun w => K s w z*LFunction π (6*z)*LFunction π w))
  let D := fun s => R*verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))
  let E := fun s => R^2/6*K s 1 (1/6)
  have hA : Integrable (fun t : ℝ => A ((a:ℂ)+t*I)) :=
    iv_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) cw cw hX hY hZ ha hβ (by linarith) hcw ⟨by linarith,le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a:ℂ)+t*I)) :=
    iv_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) (19/20) cw hX hY hZ ha hβ (by linarith) hcw ⟨le_rfl,by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a:ℂ)+t*I)) :=
    (iv_residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33/200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐt : ℝ,A ((a:ℂ)+t*I)=B ((a:ℂ)+t*I)+D ((a:ℂ)+t*I)+E ((a:ℂ)+t*I) :=
    iv_source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e cw hX hY hZ ha hβ hcw he
  have hE : Integrable (fun t : ℝ => E ((a:ℂ)+t*I)) := by
    apply ((hA.sub hB).sub hD).congr
    filter_upwards [hp] with t ht
    change A ((a:ℂ)+t*I)-B ((a:ℂ)+t*I)-D ((a:ℂ)+t*I)=E ((a:ℂ)+t*I)
    rw [ht]
    ring
  have heq : verticalIntegral a A=verticalIntegral a (fun s => B s+D s+E s) := by
    unfold verticalIntegral
    congr 1
    exact integral_congr_ae hp
  rw [verticalIntegral_add a _ _ (hB.add hD) hE,verticalIntegral_add a _ _ hB hD] at heq
  change verticalIntegral a A=verticalIntegral a B+R*verticalIntegral a _+R^2/6*verticalIntegral a _
  rw [heq]
  simp only [D,E,verticalIntegral,integral_const_mul]
  ring

theorem iv_source_initial_ordered {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    let R := HeckeReciprocal.regularizedL π 1
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) =
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral (19/20)
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) +
    R*verticalIntegral 3 (fun s => verticalIntegral (33/200) (fun z => K s 1 z*LFunction π (6*z))) +
    R^2/6*verticalIntegral 3 (fun s => K s 1 (1/6)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simpa only [show (1/6+11/6:ℝ)=2 by norm_num] using
    iv_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z 3 (11/6) 3 hX hY hZ (by iv_high_geometry)
      (by linarith [HeckeZeroSupremum.beta_le_one]) (by iv_high_geometry) (by norm_num)

theorem iv_source_uniform_joint_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      6*ξ≠1→υ≠1→∀R : ℝ,0≤ R→
      (∫p : HeightSpace in outsideBox R,
        ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
          (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
          ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
          LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
          LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ∂heightMeasure) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| * K/(1+R)^N := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := profile_uniform_tails W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  obtain ⟨K0,hK0,hm⟩ := profile_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ hξ1 hυ1 R hR0
  let A := arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1|
  have hA : 0≤ A := iv_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
    (abs_nonneg _) (abs_nonneg _)
  have hi := iv_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z σ ξ υ cw hX hY hZ (ha.trans hσ.1) (hβ.trans_le hσ.1) hξ.1 hcw hυ hξ1 hυ1
  have hmi := (hm σ hσ ξ hξ υ hυ).1
  have hbound := iv_arithmetic_onLines_bound η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ hξ1 hυ1 hC hR
  have hdom : ∀ᵐp : HeightSpace ∂heightMeasure,
      ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
      A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) := by
    filter_upwards [iv_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ] with p hp
    rw [←hp,←iv_arithmetic_profile_eq_source]
    rw [norm_mul]
    simpa only [mul_assoc,A,onLines] using mul_le_mul_of_nonneg_right (hbound p) (norm_nonneg (onLines W0 W1 σ ξ υ p))
  calc
    _ ≤ ∫p : HeightSpace in outsideBox R,
        A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) ∂heightMeasure :=
      integral_mono_ae hi.norm.integrableOn (hmi.const_mul A).integrableOn (ae_restrict_of_ae hdom)
    _ = A*(∫p : HeightSpace in outsideBox R,
        jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖ ∂heightMeasure) := integral_const_mul _ _
    _ ≤ A*(K/(1+R)^N) := mul_le_mul_of_nonneg_left (hk σ hσ ξ hξ υ hυ R hR0) hA
    _ = _ := by dsimp [A]; ring

lemma iv_LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  classical
  have hm := ((HeckeOrigin.poleRemoved_entire χ).continuous.measurable).div
    (measurable_id.sub_const (1:ℂ))
  have h1 : Measurable (fun s : ℂ => if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (1:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 1)) hm
  have h0 : Measurable (fun s : ℂ => if s=0 then LFunction χ 0 else
      if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (0:ℂ))
    (measurable_const : Measurable (fun _ : ℂ => LFunction χ 0)) h1
  convert h0 using 1
  funext s
  split_ifs with hs0 hs1
  · subst s; rfl
  · subst s; rfl
  · exact iv_LFunction_eq_pole_quotient χ hs0 hs1

lemma iv_arithmetic_onLines_measurable_all {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hH := iv_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := iv_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (iv_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (iv_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => (υ:ℂ)+p.2*I))
  have hZL := (iv_LFunction_measurable (fixedSourcePrincipal S hS)).comp
    (by fun_prop : Measurable (fun p : HeightSpace => 6*((ξ:ℂ)+p.1.2*I)))
  unfold arithmeticMultiplier
  fun_prop (disch := aesop)

lemma iv_joinWGap_pos (axis : SliceAxis) (υ : ℝ) (hυ : axis≠.w→υ≠1) : 0< joinWGap axis υ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold joinWGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hυ h))
lemma iv_joinZGap_pos (axis : SliceAxis) (ξ : ℝ) (hξ : axis≠.z→6*ξ≠1) : 0< joinZGap axis ξ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold joinZGap
  split_ifs with h
  · norm_num
  · exact abs_pos.mpr (sub_ne_zero.mpr (hξ h))

lemma iv_slice_w_gap (axis : SliceAxis) (R υ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinWGap axis υ≤‖((υ:ℂ)+(sliceMap axis R q).2*I)-1‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  cases axis
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using pole_distance_vertical 1 υ q.2
  · simpa [joinWGap,sliceMap] using hR.trans (pole_distance_horizontal 1 υ R)
lemma iv_slice_z_gap (axis : SliceAxis) (R ξ : ℝ) (hR : 1≤|R|) (q : ℝ×ℝ) :
    joinZGap axis ξ≤‖6*((ξ:ℂ)+(sliceMap axis R q).1.2*I)-1‖ := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  cases axis
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.1*I)-1)
  · have hi : 6*|R|≤‖6*((ξ:ℂ)+R*I)-1‖ := by
      simpa [abs_mul] using Complex.abs_im_le_norm (6*((ξ:ℂ)+R*I)-1)
    simpa [joinZGap,sliceMap] using (by linarith : (6:ℝ)≤6*|R|).trans hi
  · simpa [joinZGap,sliceMap] using Complex.abs_re_le_norm (6*((ξ:ℂ)+q.2*I)-1)

theorem iv_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs (33/200) Bz (19/20) cw (by norm_num) 8 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR0
  have hm := iv_arithmetic_onLines_measurable_all η S hS.prime J T b X Y Z σ ξ υ hX hY hZ (hβ.trans_le hσ.1)
  have hb (q : ℝ×ℝ) := iv_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C
    hX hY hZ ha hσ hξ hcw hυ (joinWGap axis υ) (joinZGap axis ξ)
    (iv_joinWGap_pos axis υ hυ1) (iv_joinZGap_pos axis ξ hξ1) hC hR (sliceMap axis R q)
    (iv_slice_w_gap axis R υ hR0 q) (iv_slice_z_gap axis R ξ hR0 q)
  have hh := hk σ hσ ξ hξ υ hυ axis R
    (arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ))
    (iv_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
      (iv_joinWGap_pos axis υ hυ1).le (iv_joinZGap_pos axis ξ hξ1).le)
    (fun q : ℝ×ℝ => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((σ:ℂ)+(sliceMap axis R q).1.1*I) ((υ:ℂ)+(sliceMap axis R q).2*I)
      ((ξ:ℂ)+(sliceMap axis R q).1.2*I))
    (hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable hb
  simpa only [onLines,iv_arithmetic_profile_eq_source] using hh

theorem iv_residue_uniform_moments {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ residueAmplitude S J T b X Z a ξ C*K := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := profile_uniform_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) (5+N) 0
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  refine ⟨C,hC,?_⟩
  let A := residueAmplitude S J T b X Z a ξ C
  have hA : 0≤ A := iv_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC
  let F : ℝ×ℝ → ℂ := fun q => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) *
    onLines W0 W1 a ξ 1 (sliceMap .w 0 q)
  have hm := iv_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hFc : AEStronglyMeasurable F (volume.prod volume) := hm.aestronglyMeasurable.mul
    (((onLines_continuous W0 W1 a1 b1 ha1 hW1 a ξ 1 (by linarith)).comp
      (sliceMap_continuous .w 0)).aestronglyMeasurable)
  have hb := iv_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hmom := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
  have hdom (q : ℝ×ℝ) : jointHeight q.1 q.2 0^N*‖F q‖≤
      A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) := by
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ jointHeight q.1 q.2 0^N * ((A*jointHeight q.1 q.2 0^5)*
          ‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (hb q) (norm_nonneg _))
          (pow_nonneg (jointHeight_pos _ _ _).le _)
      _ = _ := by rw [pow_add]; ring
  have hi : Integrable (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N*‖F q‖) (volume.prod volume) := by
    apply (hmom.1.const_mul A).mono'
    · exact (by unfold jointHeight; fun_prop : Continuous (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)).aestronglyMeasurable.mul hFc.norm
    · apply Eventually.of_forall
      intro q
      simpa only [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)),sliceMap] using hdom q
  have hn : (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)≤ A*K := by
    calc
      _ ≤ ∫q : ℝ×ℝ,A*(jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖)
          ∂volume.prod volume := integral_mono hi (hmom.1.const_mul A) hdom
      _ = A*(∫q : ℝ×ℝ,jointHeight q.1 q.2 0^(5+N)*‖onLines W0 W1 a ξ 1 (sliceMap .w 0 q)‖
          ∂volume.prod volume) := integral_const_mul _ _
      _ ≤ A*K := mul_le_mul_of_nonneg_left (by simpa only [sliceMap,pow_zero,div_one] using hmom.2) hA
  have heq : F =ᵐ[volume.prod volume] (fun q : ℝ×ℝ =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
        (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
        1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) := by
    have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
      Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    filter_upwards [hh] with q hq
    have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
    dsimp only [F,onLines,sliceMap]
    simp only [ofReal_one,ofReal_zero,zero_mul,add_zero]
    rw [iv_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z,
      iv_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]
  have hweight : (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N)=ᵐ[volume.prod volume]
      (fun q : ℝ×ℝ => jointHeight q.1 q.2 0^N) := Eventually.of_forall (fun _ => rfl)
  have heqw := hweight.mul (heq.fun_comp (fun z : ℂ => ‖z‖))
  exact ⟨hi.congr heqw, (integral_congr_ae heqw).symm.trans_le hn⟩

lemma iv_residueOutside_measurable (R : ℝ) : MeasurableSet (residueOutside R) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold residueOutside
  measurability

theorem iv_residue_uniform_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a ξ : ℝ) (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀R : ℝ,0≤ R→
      let F := fun q : ℝ×ℝ =>
        sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
          (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
          1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
      (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤
        residueAmplitude S J T b X Z a ξ C*K/(1+R)^N := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := iv_residue_uniform_moments W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ ha hβ hξ hξ1 N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hZ
  obtain ⟨C,hC,hi,hb⟩ := hk η S hS J T b hT X Y Z hX hZ
  refine ⟨C,hC,?_⟩
  intro R hR
  let F := fun q : ℝ×ℝ =>
    sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)
      (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))
  have hF := iv_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  have hdom (q : ℝ×ℝ) (hq : q∈residueOutside R) :
      ‖F q‖≤ jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N := by
    have hh : 1+R≤ jointHeight q.1 q.2 0 := by
      rcases hq with h|h <;> unfold jointHeight <;> simp only [abs_zero,add_zero] <;>
        linarith [abs_nonneg q.1,abs_nonneg q.2]
    have hp := pow_le_pow_left₀ (by linarith : 0≤1+R) hh N
    apply (le_div_iff₀ (pow_pos (by linarith : 0<1+R) N)).mpr
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hp (norm_nonneg (F q))
  change (∫q : ℝ×ℝ in residueOutside R,‖F q‖ ∂volume.prod volume)≤_
  calc
    _ ≤ ∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖/(1+R)^N
        ∂volume.prod volume := setIntegral_mono_on hF.norm.integrableOn (hi.div_const _).integrableOn
          (iv_residueOutside_measurable R) hdom
    _ = (∫q : ℝ×ℝ in residueOutside R,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := integral_div _ _
    _ ≤ (∫q : ℝ×ℝ,jointHeight q.1 q.2 0^N*‖F q‖ ∂volume.prod volume)/(1+R)^N := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact setIntegral_le_integral hi (Eventually.of_forall (fun q =>
        mul_nonneg (pow_nonneg (jointHeight_pos _ _ _).le _) (norm_nonneg _)))
    _ ≤ _ := div_le_div_of_nonneg_right hb (by positivity)

lemma iv_continued_high_slice_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ ξ υ : ℝ)
    (axis : SliceAxis) (R : ℝ) (hR : R≠0) :
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) =ᵐ[volume.prod volume]
    (fun q : ℝ×ℝ => let p := sliceMap axis R q
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS) (6*((ξ:ℂ)+p.1.2*I))*
      LFunction (fixedSourcePrincipal S hS) ((υ:ℂ)+p.2*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,(sliceMap axis R q).1.1≠0 := by
    cases axis
    · exact Eventually.of_forall (fun _ => hR)
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
    · exact Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠0 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (σ:ℂ)+(sliceMap axis R q).1.1*I≠1 := by
    intro h; exact hq (by simpa using congrArg Complex.im h)
  dsimp only
  rw [iv_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

lemma iv_source_axis_gaps {e : ℝ} (he : 0< e) :
    |(19/20:ℝ)-1|=1/20 ∧ |6*(1/6+e)-1|=6*e ∧ |6*(33/200:ℝ)-1|=1/100 := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  constructor
  · norm_num
  constructor
  · rw [show 6*(1/6+e)-1=6*e by ring,abs_of_pos (by positivity)]
  · norm_num

theorem iv_raw_source_uniform_high_slices {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)(b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ),
      (∀j∈J,∀P∈T j,P.val∉S) → ∀X Y Z : ℝ,0< X→0< Y→0< Z→
      ∃C : ℝ,0≤ C ∧ ∀σ∈Icc a Bs,∀ξ∈Icc (33/200 : ℝ) Bz,∀υ∈Icc (19/20 : ℝ) cw,
      ∀axis : SliceAxis, (axis≠.w→υ≠1)→(axis≠.z→6*ξ≠1)→∀R : ℝ,1≤|R|→
      let F := fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
        ((σ:ℂ)+p.1.1*I) (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I))
        (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
      Integrable (fun q : ℝ×ℝ => F (sliceMap axis R q)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖F (sliceMap axis R q)‖ ∂volume.prod volume) ≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C (joinWGap axis υ) (joinZGap axis ξ) * K/height R^N := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨K,hK,hk⟩ := iv_source_uniform_high_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a Bs Bz cw ha hβ hcw N
  refine ⟨K,hK,?_⟩
  intro η S hS J T b hT X Y Z hX hY hZ
  obtain ⟨C,hC,hc⟩ := hk η S hS J T b hT X Y Z hX hY hZ
  refine ⟨C,hC,?_⟩
  intro σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have hh := hc σ hσ ξ hξ υ hυ axis hυ1 hξ1 R hR
  have heq := iv_continued_high_slice_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ axis R
    (by intro h; norm_num [h] at hR)
  exact ⟨hh.1.congr heq,(integral_congr_ae (heq.fun_comp norm)).symm.trans_le hh.2⟩

end
end RHZeroFreeExtension.AnalyticHigh

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_source_uniform_joint_tails

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_residue_uniform_moments

#print axioms RHZeroFreeExtension.AnalyticHigh.iv_raw_source_uniform_high_slices

-- Parametric high adaptation: V2PrincipalTransport

set_option linter.unusedVariables false

/-! Actual ordered principal transport at the perturbed endpoint. The source
functions and positive Gaussian/tail measures are unchanged. Domain inputs
are supplied by freshly proved Euler and contour bounds; this file assumes
no improved transport theorem or physical high bound.
-/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators Topology
open Complex Set MeasureTheory Filter
open OAI OAI.SevenEighths
open HeckeFamily ProbePhysical ProbeEuler ProbeLocal CompletedGauss
open ProbeFiniteProductBounds ProbeFiniteProductX PrincipalMellinResidues
open PrincipalMellinGrowth ProbeMellinBoundary ProbePrincipalContours ProbePrincipalTransport
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma iv_gaussianMoment_tendsto (n : ℕ) : Tendsto (gaussianMoment n) atTop (𝓝 0) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hb (t : ℝ) : gaussianMoment n t ≤ (2:ℝ)^(n-1)*Continuation.polynomialGaussian n t := by
    have h := add_pow_le (by norm_num : (0:ℝ)≤1) (abs_nonneg t) n
    unfold gaussianMoment height Continuation.polynomialGaussian
    calc
      _ ≤ ((2:ℝ)^(n-1)*(1^n+|t|^n))*Real.exp (-(t^2)) :=
        mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
      _ = _ := by simp only [one_pow]; ring
  exact squeeze_zero (gaussianMoment_nonneg n) hb
    (by simpa using (Continuation.polynomialGaussian_tendsto n).const_mul ((2:ℝ)^(n-1)))

lemma iv_gaussianMoment_even (n : ℕ) (t : ℝ) : gaussianMoment n (-t)=gaussianMoment n t := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp [gaussianMoment,height]

lemma iv_gaussianMoment_tendsto_bot (n : ℕ) : Tendsto (gaussianMoment n) atBot (𝓝 0) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h := (iv_gaussianMoment_tendsto n).comp tendsto_neg_atBot_atTop
  simpa only [Function.comp_def,iv_gaussianMoment_even] using h

lemma iv_shifted_gaussian_integrable (n : ℕ) (v : ℝ) :
    Integrable (fun t : ℝ => gaussianMoment n (t+v)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  exact (measurePreserving_add_right volume v).integrable_comp_of_integrable (gaussianMoment_integrable n)

lemma iv_shifted_gaussian_top (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (t+v)) atTop (𝓝 0) :=
  (iv_gaussianMoment_tendsto n).comp (tendsto_atTop_add_const_right _ v tendsto_id)

lemma iv_shifted_gaussian_bottom (n : ℕ) (v : ℝ) :
    Tendsto (fun t : ℝ => gaussianMoment n (-t+v)) atTop (𝓝 0) :=
by
  convert iv_shifted_gaussian_top n (-v) using 1
  funext t
  rw [←iv_gaussianMoment_even n (t + -v)]
  congr 1
  ring

theorem iv_verticalIntegral_eq_of_shifted_gaussian (F : ℂ → ℂ) {a c A : ℝ}
    (n : ℕ) (v : ℝ) (hac : a≤ c)
    (hF : DifferentiableOn ℂ F {s : ℂ | a≤ s.re ∧ s.re≤ c})
    (hb : ∀σ∈Icc a c,∀t : ℝ,‖F ((σ:ℂ)+t*I)‖≤ A*gaussianMoment n (t+v)) :
    verticalIntegral a F=verticalIntegral c F := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hc (σ : ℝ) (hσ : σ∈Icc a c) : Continuous (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    hF.continuousOn.comp_continuous (by fun_prop) (by intro t; simpa using hσ)
  have hi (σ : ℝ) (hσ : σ∈Icc a c) : Integrable (fun t : ℝ => F ((σ:ℂ)+t*I)) :=
    ((iv_shifted_gaussian_integrable n v).const_mul A).mono' (hc σ hσ).aestronglyMeasurable
      (Eventually.of_forall (hb σ hσ))
  have hj (T : ℝ) : ‖∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)‖≤ A*gaussianMoment n (T+v)*|c-a| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro σ hσ
    exact hb σ (by simpa [uIcc_of_le hac] using uIoc_subset_uIcc hσ) T
  have ht : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+T*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) hj
      (by simpa using ((iv_shifted_gaussian_top n v).const_mul A).mul_const |c-a|)
  have hbot : Tendsto (fun T : ℝ => ∫σ : ℝ in a..c,F ((σ:ℂ)+(-T)*I)) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    exact squeeze_zero (fun _ => norm_nonneg _) (fun T => by simpa only [Complex.ofReal_neg] using hj (-T))
      (by simpa using ((iv_shifted_gaussian_bottom n v).const_mul A).mul_const |c-a|)
  unfold verticalIntegral
  congr 1
  exact Continuation.vertical_integral_eq_of_horizontal_vanish F hac hF
    (hi a ⟨le_rfl,hac⟩) (hi c ⟨hac,le_rfl⟩) hbot ht

theorem iv_principal_box_majorant {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξlo : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξlo : 1/6<ξlo) :
    ∃ A : ℝ,0≤ A ∧ ∀σ∈Icc a 3,∀ξ∈Icc ξlo 2,∀p : HeightSpace,
      ‖continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+p.2*I)‖≤ A*jointEnvelope 8 p := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound
    (η.excludePrimes S hS.prime) a hβ
  obtain ⟨D,hD,hd⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a0 b0 ha0 hW0 ξlo 2
    (by linarith) 10
  obtain ⟨E,hE,he⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a1 b1 ha1 hW1
    (W1.smooth ⊤) 3 3 10
  let A := arithmeticAmplitude S J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
  let B := realGaussianBound a 3 ξlo 2*2^8*D*E
  have hA : 0≤ A := iv_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a 3 2 3 C 2 (6*ξlo-1)
    (by norm_num) hC (by norm_num) (by linarith)
  have hB : 0≤ B := by dsimp [B]; have := (realGaussianBound_pos a 3 ξlo 2).le; positivity
  refine ⟨A*B,mul_nonneg hA hB,?_⟩
  intro σ hσ ξ hξ p
  have hξ' : ξ∈Icc (33/200 : ℝ) 2 := ⟨by linarith [hξ.1],hξ.2⟩
  have hw : (2:ℝ)≤‖((3:ℂ)+p.2*I)-1‖ := by
    convert pole_distance_vertical 1 3 p.2 using 1; norm_num
  have hz : 6*ξlo-1≤‖6*((ξ:ℂ)+p.1.2*I)-1‖ := by
    have h := Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)
    have hh : 0≤6*ξ-1 := by linarith [hξ.1]
    simp only [sub_re,mul_re,ofReal_re,ofReal_im,add_re,I_re,I_im,mul_zero,
      zero_mul,sub_zero,add_zero,one_re] at h
    norm_num only [show (6:ℂ).re=6 by norm_num,show (6:ℂ).im=0 by norm_num,zero_mul,sub_zero] at h
    rw [abs_of_nonneg hh] at h
    exact le_trans (by linarith [hξ.1]) h
  have hb := iv_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a 3 2 3 σ ξ 3 C
    hX hY hZ ha hσ hξ' (by norm_num) (by norm_num) 2 (6*ξlo-1)
    (by norm_num) (by linarith) hC hR p hw hz
  have hp := profile_moment_majorant W0 W1 8 hσ hξ hD.le hE.le (hd ξ hξ)
    (he 3 ⟨le_rfl,le_rfl⟩) p
  rw [←iv_arithmetic_profile_eq_source,norm_mul]
  calc
    _ ≤ (A*jointHeight p.1.1 p.1.2 p.2^8)*‖profile W0 W1
        ((σ:ℂ)+p.1.1*I) ((3:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖ :=
      mul_le_mul_of_nonneg_right hb (norm_nonneg _)
    _ = A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ 3 p‖) := by
      simp only [onLines,ofReal_ofNat]; ring
    _ ≤ A*(B*jointEnvelope 8 p) := mul_le_mul_of_nonneg_left hp hA
    _ = _ := by ring

theorem iv_continued_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (v u : ℝ) :
    verticalIntegral a (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 3 (fun s => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      s ((3:ℂ)+u*I) ((ξ:ℂ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+v*I))*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨A,hA,hb⟩ := iv_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha.le hβ hξ
  have hh := iv_continued_source_differentiable_strip η S hS J T b hT W0 W1 X Y Z hZ
    ((3:ℂ)+u*I) ((ξ:ℂ)+v*I) (by norm_num) (by simpa using (show (4/25:ℝ)≤ξ by linarith)) ha hβ
    (c:=3)
  apply iv_verticalIntegral_eq_of_shifted_gaussian _ 8 v ha3
    ((hh.mul_const _).mul_const _) (A:=A*cauchy v*cauchy u)
  intro σ hσ t
  have h := hb σ hσ ξ ⟨le_rfl,hξ2⟩ ((t,v),u)
  simpa only [jointEnvelope,Prod.fst,Prod.snd,mul_assoc,mul_left_comm,mul_comm] using h

lemma iv_continued_source_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : RHIVProbe.boundary≤ s.re) (hw : 9/10≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)
      {z : ℂ | 4/25< z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25< z.re} := (ProbeRadialMellin.radial_mellin_differentiable W0).mono
        (by intro z hz; change 0< z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (iv_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
  have hnX : (X:ℂ)≠0 := by exact_mod_cast hX.ne'
  have hnZ : (Z:ℂ)≠0 := by exact_mod_cast hZ.ne'
  have he : (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z)=
    (fun z => ((Y:ℂ)^(w-1)*mellin W1 w*HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s)*
      (X:ℂ)^(1/2-z)*(Z:ℂ)^(s+z-1)*Complex.exp ((s+z-1)^2)*
      mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (globalClosedCorrection η S s w z*slotMultiplier η J T b s w z)) := by
    funext z; unfold continuedSourceMultiplier; ring
  rw [he]
  fun_prop (disch := first | assumption | exact Or.inl hnX | exact Or.inl hnZ)

lemma iv_continued_principal_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : RHIVProbe.boundary≤ s.re) (hw : 9/10≤ w.re) :
    DifferentiableOn ℂ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w)
      {z : ℂ | 1/6< z.re} := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have hK := iv_continued_source_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s w hs hw
  apply ((hK.mono (by intro z hz; change (4/25:ℝ)< z.re; change (1/6:ℝ)< z.re at hz; linarith)).mul ?_).mul_const
  intro z hz
  have h0 : (6*z:ℂ)≠0 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith
  have h1 : (6*z:ℂ)≠1 := by
    intro he; have hh := congrArg Complex.re he; norm_num at hh; change (1/6:ℝ)< z.re at hz; linarith
  exact ((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) h0 (Or.inl h1)).comp z
    (differentiableAt_id.const_mul 6)).differentiableWithinAt

theorem iv_continued_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a)
    (hξ : 1/6<ξ) (hξ2 : ξ≤2) (t u : ℝ) :
    verticalIntegral ξ (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) =
    verticalIntegral 2 (fun z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+t*I) ((3:ℂ)+u*I) z*LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        LFunction (fixedSourcePrincipal S hS.prime) ((3:ℂ)+u*I)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  obtain ⟨A,hA,hb⟩ := iv_principal_box_majorant η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha hβ hξ
  have hh := iv_continued_principal_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
    ((a:ℂ)+t*I) ((3:ℂ)+u*I) (by simpa using ha) (by norm_num)
  apply iv_verticalIntegral_eq_of_shifted_gaussian _ 8 t hξ2
    (hh.mono (by intro z hz; change (1/6:ℝ)< z.re; exact hξ.trans_le hz.1)) (A:=A*cauchy u)
  intro ζ hζ v
  have h := hb a ⟨le_rfl,ha3⟩ ζ hζ ((t,v),u)
  calc
    _ ≤ A*(gaussianMoment 8 (t+v)*cauchy v*cauchy u) := h
    _ ≤ A*(gaussianMoment 8 (t+v)*1*cauchy u) := by
      have hgu := gaussianMoment_nonneg 8 (t+v)
      have hcu := cauchy_nonneg u
      gcongr
      exact cauchy_le_one v
    _ = _ := by rw [add_comm t v]; ring

lemma iv_verticalIntegral_swap (F : ℂ → ℂ → ℂ) (a b : ℝ)
    (hi : Integrable (fun q : ℝ×ℝ => F ((a:ℂ)+q.1*I) ((b:ℂ)+q.2*I)) (volume.prod volume)) :
    verticalIntegral a (fun z => verticalIntegral b (F z))=
      verticalIntegral b (fun w => verticalIntegral a (fun z => F z w)) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  simp only [verticalIntegral,integral_const_mul]
  congr 2
  exact integral_integral_swap (f:=fun t u : ℝ => F ((a:ℂ)+t*I) ((b:ℂ)+u*I)) hi

lemma iv_verticalIntegral_triple_reverse (F : ℂ → ℂ → ℂ → ℂ) (a ξ υ : ℝ)
    (hi : Integrable (fun p : HeightSpace => F ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I)
      ((ξ:ℂ)+p.1.2*I)) heightMeasure) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w => F s w z)))=
      verticalIntegral υ (fun w => verticalIntegral ξ (fun z => verticalIntegral a (fun s => F s w z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  have h1 := integral_prod _ hi
  have h2 := integral_prod _ hi.integral_prod_left
  have h3 := integral_prod_symm _ hi
  have h4 : (∫u : ℝ,∫q : ℝ×ℝ,F ((a:ℂ)+q.1*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+q.2*I) ∂volume.prod volume)=
      ∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((a:ℂ)+t*I) ((υ:ℂ)+u*I) ((ξ:ℂ)+v*I) := by
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu
  have he := h2.symm.trans (h1.symm.trans (h3.trans h4))
  simp only [verticalIntegral,integral_const_mul]
  congr 3

lemma iv_verticalIntegral_congr_line (F G : ℂ → ℂ) (a : ℝ)
    (h : ∀t : ℝ,F ((a:ℂ)+t*I)=G ((a:ℂ)+t*I)) : verticalIntegral a F=verticalIntegral a G := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold verticalIntegral
  congr 1
  exact integral_congr_ae (Eventually.of_forall h)

theorem iv_continued_triple_x_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral 3 (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  have hiA := iv_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha.le hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num)
  have hi3 := iv_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z 3 ξ 3 3 hX hY hZ (by iv_high_geometry) (hβ.trans_le ha3) (by linarith)
    (by norm_num) (by norm_num) (by linarith) (by norm_num)
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  rw [iv_verticalIntegral_triple_reverse F a ξ 3 hiA,iv_verticalIntegral_triple_reverse F 3 ξ 3 hi3]
  apply iv_verticalIntegral_congr_line
  intro u
  apply iv_verticalIntegral_congr_line
  intro v
  exact iv_continued_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 v u

theorem iv_continued_triple_z_shift {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary≤ a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (hξ : 1/6<ξ) (hξ2 : ξ≤2) :
    let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=
      verticalIntegral a (fun s => verticalIntegral 2 (fun z => verticalIntegral 3 (fun w => F s w z))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  let F := fun s w z => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z s w z*
    LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w
  obtain ⟨Cξ,Kξ,hCξ,hKξ,hξi⟩ := iv_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ 3 3 hX hY hZ ha hβ (by linarith) (by norm_num) (by norm_num) (by linarith) (by norm_num) 0
  obtain ⟨C2,K2,hC2,hK2,h2i⟩ := iv_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 3 3 hX hY hZ ha hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 0
  change verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral 3 (fun w => F s w z)))=_
  apply iv_verticalIntegral_congr_line
  intro t
  have hiξ := (hξi .s t).1
  have hi2 := (h2i .s t).1
  rw [iv_verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) ξ 3 hiξ,
    iv_verticalIntegral_swap (fun z w => F ((a:ℂ)+t*I) w z) 2 3 hi2]
  apply iv_verticalIntegral_congr_line
  intro u
  exact iv_continued_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hY hZ ha ha3 hβ hξ hξ2 t u

lemma iv_continued_triple_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w)))=
    verticalIntegral a (fun s => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) s
        (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z*
      LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  unfold verticalIntegral
  congr 1
  apply integral_congr_ae
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  have h0 : (a:ℂ)+t*I≠0 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+t*I≠1 := by intro h; exact ht (by simpa using congrArg Complex.im h)
  simp_rw [iv_continued_source_eq_raw η S hS J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem iv_source_initial_placement {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : RHIVProbe.boundary< a) (ha3 : a≤3) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e) (he2 : e≤11/6) :
    let K := fun s => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    let π := fixedSourcePrincipal S hS.prime
    verticalIntegral 3 (fun s => verticalIntegral 2 (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w)))=
    verticalIntegral a (fun s => verticalIntegral (1/6+e) (fun z => verticalIntegral 3
      (fun w => K s w z*LFunction π (6*z)*LFunction π w))) := by
  have hBlo : (437/500 : ℝ) ≤ RHIVProbe.boundary := by iv_high_geometry
  have hBhi : RHIVProbe.boundary ≤ (9/10 : ℝ) := by iv_high_geometry
  dsimp only
  rw [←iv_continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z 3 2 3,
    ←iv_continued_triple_eq_raw η S hS.prime J T b W0 W1 X Y Z a (1/6+e) 3]
  have hx := iv_continued_triple_x_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a 2 hX hY hZ ha ha3 hβ (by norm_num) le_rfl
  have hz := iv_continued_triple_z_shift η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a (1/6+e) hX hY hZ ha.le ha3 hβ (by linarith) (by linarith)
  exact hx.symm.trans hz.symm

theorem iv_source_initial_ordered_at_a {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (b : ι → OAI.SevenEighths.ProbePhysical.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
