import core.OAI08
import Mathlib
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
/-! Consolidated exact local import closure of Parts I--III. Each original module is enclosed in a section to keep local options and notation scoped. OAI foundations are consolidated in OAI01--OAI08; pinned mathlib dependencies remain external. -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedCubeSlotExponent -/
section LocalModule0

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI OAI.SevenEighths
open ProbeHighRowFamily HeckeDetectorPhysicalSelection

lemma perturbed_source_slot_length_sum {Slot : Type*} (slots : Finset Slot) (ell : Slot→ℝ)
    (d : ℝ) (hell : ∑j∈slots,ell j=5003/30000) :
    (∑j∈slots,ell j/d)=5003/(30000*d) := by
  rw [←Finset.sum_div,hell]
  ring

lemma perturbed_source_slot_weightedMean {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (d : ℝ) (hd : d≠0) (hell : ∑j∈slots,ell j=5003/30000) :
    weightedMean slots (fun j=> ell j/d) g=(30000/5003)*(∑j∈slots,ell j*g j) := by
  unfold weightedMean
  simp_rw [div_mul_eq_mul_div]
  rw [←Finset.sum_div,←Finset.sum_div,hell]
  field_simp

lemma perturbed_source_slot_product {Slot : Type*} (slots : Finset Slot) (ell g : Slot→ℝ)
    (Z d mesh : ℝ) (hZ : 0< Z) (hd : d≠0) (hell : ∑j∈slots,ell j=5003/30000) :
    (∏j∈slots,(Z^(ell j))^(-(4/25:ℝ)+g j+mesh))=
      Z^(-(5003/187500:ℝ)+(5003/30000)*weightedMean slots (fun j=> ell j/d) g+
        (5003/30000)*mesh) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_sum_of_pos hZ]
  congr 1
  rw [perturbed_source_slot_weightedMean slots ell g d hd hell]
  simp_rw [mul_add,Finset.sum_add_distrib]
  rw [←Finset.sum_mul,←Finset.sum_mul,hell]
  ring

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule0
/- END RHZeroFreeExtension.analytic_high.PerturbedCubeSlotExponent -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedCentralClassArithmetic -/
section LocalModule1
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
private theorem perturbed_classPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem perturbed_actual_class_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh) (hδ : 0<δ)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=5003/30000) :
    ∃C : ℝ,0< C ∧ ∀η : Character,∀ᶠ Z : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a q D Rcount : ℝ),0≤ v → 51/100≤ a → a≤1 → 0≤ D → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^δ≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      (rows.card:ℝ)≤ D*(Z^d)^Rcount →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      (∀u∈rows,weightedMean Finset.univ (fun j=> ell j/d)
        (fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
          (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) ((17/50:ℂ)+t.1.2*Complex.I)))=q) →
      ‖cubeArithmeticSum S hS hmax η rows T (perturbed_classPoolOutside M H S N c b Y) W Y a e t‖≤
        C*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-5003/187500+(5003/30000)*q+(5003/30000)*mesh) := by
  obtain ⟨C,hC,hbound⟩ := actual_fixed_cube_prime_bound M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh δ margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh hδ hbudget hgap hmargin hheight hloss
    S hS hfirst hmax ell hell hello hellhi W hWs hW hWB
  let AA : ℝ := max 1 ((2:ℝ)^(4/25+12*e+eps*(N+8)))
  have hAA : 0< AA := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C*AA,mul_pos hC hAA,?_⟩
  intro η
  filter_upwards [hbound η,eventually_ge_atTop (1:ℝ)] with Z hb hZ
  intro d hd hd' v a q D Rcount hv ha ha' hD rows hrows hnorm hcard i hi hbin
  dsimp only
  intro t ht hq
  have hZp : 0< Z := zero_lt_one.trans_le hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let α : ℝ := a-1/2+12*e+eps*(N+8)
  let F : FreeRow→ℝ := fun u=>‖∑P:(∀j,T j),calibratedTupleValue S hS hmax η u (fun j=>(P j).val)
    (fun j=> perturbed_classPoolOutside M H S N c b Y j _ (P j).property) W Y
    (((a+16*e:ℝ):ℂ)+t.1.1*Complex.I) (((1-a-6*e:ℝ):ℂ)+t.2*Complex.I) z‖
  let E : ℝ := C*(η.modulus.absNorm:ℝ)^(2*eps)*Z^loss*Z^(-5003/187500+(5003/30000)*q+(5003/30000)*mesh)
  have hE : 0≤ E := by dsimp [E];positivity
  have hF (u : FreeRow) (hu : u∈rows) : F u≤ E*rowNorm u^α := by
    rcases hrows u hu with ⟨hu1,hulo,hcal,huhi⟩
    have hh := hb d hd hd' u hu1 hulo hcal huhi a i hi ha ha' (hbin u hu) t ht
    dsimp only at hh
    let g : Fin N→ℝ := fun j=> HeckePrimeAmplitudeBins.amplitude (Y j) (a-1/2) mesh
      (HeckePrimeRow.canonicalPrimeAmplitude M H u.val (W j) b (Y j) z)
    have hp : (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=Z^(-5003/187500+(5003/30000)*q+(5003/30000)*mesh) := by
      rw [show (∏j,(Y j)^(-(4/25:ℝ)+g j+mesh))=
        Z^(-(5003/187500:ℝ)+(5003/30000)*weightedMean Finset.univ (fun j=> ell j/d) g+(5003/30000)*mesh) from
        perturbed_source_slot_product Finset.univ ell g Z d mesh hZp hd0.ne' hellsum]
      rw [show weightedMean Finset.univ (fun j=> ell j/d) g=q from hq u hu]
      congr 1 ; ring
    have hh' := hh.2
    rw [hp] at hh'
    convert hh' using 1 ; dsimp [F,E,α,Y,z,g] ; ring
  have hh := dyadic_weighted_rows_card α (17/50) E (Z^v) (D*(Z^d)^Rcount) hE
    (Real.rpow_pos_of_pos hZp _) rows hcard hnorm F hF z (by simp [z])
  have hsum : ‖cubeArithmeticSum S hS hmax η rows T (perturbed_classPoolOutside M H S N c b Y) W Y a e t‖≤
      ∑u∈rows,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    unfold cubeArithmeticSum
    exact (norm_sum_le _ _).trans_eq (by apply Finset.sum_congr rfl;intro u hu;rw [norm_mul])
  have hAp : ProbeSelectedPrimeSums.annularPower 1 2 (α-17/50)≤ AA :=
    annular_power_uniform _ _ (by dsimp [α];linarith)
  apply (hsum.trans hh).trans
  have hpow : (Z^d)^Rcount*Z^loss*Z^(-5003/187500+(5003/30000)*q+(5003/30000)*mesh)*(Z^v)^(α-17/50)=
      Z^(d*Rcount+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-5003/187500+(5003/30000)*q+(5003/30000)*mesh) := by
    simp_rw [←Real.rpow_mul hZp.le]
    rw [←Real.rpow_add hZp,←Real.rpow_add hZp,←Real.rpow_add hZp]
    congr 1
    dsimp [α]
    ring
  calc
    _ ≤ (D*(Z^d)^Rcount)*E*AA*(Z^v)^(α-17/50) := by gcongr
    _ = _ := by
      dsimp [E]
      calc
        _ = (C*AA)*D*(η.modulus.absNorm:ℝ)^(2*eps)*
          ((Z^d)^Rcount*Z^loss*Z^(-5003/187500+(5003/30000)*q+(5003/30000)*mesh)*(Z^v)^(α-17/50)) := by ring
        _ = _ := by rw [hpow]

end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule1
/- END RHZeroFreeExtension.analytic_high.PerturbedCentralClassArithmetic -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedSourceBatch -/
section LocalModule2

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

/-- Actual source physical widths: increasing the total only helps supply. -/
lemma perturbed_physical_slot_widths {N : ℕ} (ell : Fin N→ℝ) (d dmin mesh : ℝ)
    (hdmin : 0< dmin) (hd : dmin≤ d) (hdtop : d≤37/42)
    (hell : ∀j,0< ell j) (hsmall : ∀j,ell j≤ dmin*mesh)
    (hsum : 1/6≤∑j,ell j) :
    (∀j,0< ell j/d) ∧ (∀j,ell j/d≤ mesh) ∧ 7/37≤∑j,ell j/d := by
  have hd0 : 0< d := hdmin.trans_le hd
  have hm : 0≤ mesh := by
    by_contra hn
    have hm : mesh<0 := lt_of_not_ge hn
    have hn : (∑j,ell j)≤0 := Finset.sum_nonpos fun j _=>
      (hsmall j).trans (mul_nonpos_of_nonneg_of_nonpos hdmin.le hm.le)
    linarith
  refine ⟨fun j=> div_pos (hell j) hd0,fun j=>?_,?_⟩
  · apply (div_le_iff₀ hd0).mpr
    exact (hsmall j).trans (by nlinarith)
  · rw [←Finset.sum_div]
    apply (le_div_iff₀ hd0).mpr
    nlinarith

theorem perturbed_actual_source_batch (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀tstar : ℝ,1≤ tstar → tstar≤3/2 →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → 1/6≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε tstar (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) := by
  have hw := supported_witnesses_from_source_cube M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin I hdmin hdmax hτ hτzero hτheight hε he he' hκ hκ' hheightCost hmargin hbudget
  filter_upwards [hw,eventually_ge_atTop (1:ℝ)] with Z hw hZ
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent tstar ht ht' N ell hell hsmall hsum W upper z
  obtain ⟨w⟩ := hw d hd hd' U rows hrows hcal hrow a i hi ha ha'
    (fun u=> hnext u.val u.property) (fun u=> hcurrent u.val u.property) tstar ht ht'
  obtain ⟨u0,h0⟩ := hne
  have hnorm (u : FreeRow) (hu : u∈rows) : rowNorm u≤ Z^d :=
    (hrow u hu).trans (Real.rpow_le_rpow_of_exponent_le hZ (by linarith))
  obtain ⟨hwp,hwm,hsp⟩ := perturbed_physical_slot_widths ell d dmin mesh hdmin hd (hd'.trans hdtop) hell hsmall hsum
  let B := retainedSourceBatch M H hH S hS η rows u0 h0 (Z^d) a ε tstar (Z^τ)
    ((Z^d)^(τ/(2*dmax))) i (fun u hu=> w ⟨u,hu⟩) hnorm
    Finset.univ W upper (fun j=> ell j/d) z mesh binWidth hm hb (fun j _=> hwp j) (fun j _=> hwm j) hsp
  refine ⟨B,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  intro u hu j
  dsimp [B,retainedSourceBatch]
  rw [retainedProjection_of_mem rows u0 u hu]
#print axioms perturbed_physical_slot_widths
#print axioms perturbed_actual_source_batch

end SevenEighths.ProbeHighRowFamily

end

end OAI

end LocalModule2
/- END RHZeroFreeExtension.analytic_high.PerturbedSourceBatch -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedSourceAmplitudeClasses -/
section LocalModule3

namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification HeckeDetectorBatch ProbePhysical
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem perturbed_actual_source_amplitude_batches (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character)
    (dmin dmax τ ε e κ heightCost margin mesh binWidth : ℝ) (I : ℕ)
    (hdmin : 0< dmin) (hdmax : dmin≤ dmax) (hdtop : dmax≤37/42) (hτ : 0<τ)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*heightCost)
    (hε : 0<ε) (he : 0< e) (he' : e<1/1000) (hκ : 0<κ) (hκ' : κ≤1) (hheightCost : 0≤ heightCost)
    (hmargin : 0< margin) (hm : 0≤ mesh) (hb : 0< binWidth)
    (hbudget : 12*e*((22:ℝ)+2)+8*κ+2*heightCost≤ε/2) :
    ∀ᶠZ : ℝ in atTop,∀d : ℝ,dmin≤ d → d≤ dmax →
    ∀(U : ℝ) (rows : Finset FreeRow),rows.Nonempty → rows⊆rowBand (Z^(1/100:ℝ)) U →
      (∀u∈rows,(calibrationForSet S hmax).residueMonoid u.val≠0) →
      (∀u∈rows,rowNorm u≤ Z^(d-margin)) →
    ∀(a : ℝ) (i : ℕ),i≤ I → 51/100< a → a≤1 →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u)) ((3*i:ℕ)*Z^τ)) →
    ∀(N : ℕ) (ell : Fin N→ℝ),(∀j,0< ell j) → (∀j,ell j≤ dmin*mesh) → 1/6≤∑j,ell j →
    ∀(W : Fin N→ℝ→ℂ) (upper : Fin N→ℝ) (z : Fin N→ℂ),
    let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
      W upper (fun j=> ell j/d) z (Z^d)
    ∀bin : HeckeDetectorFiberPartition.BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) binWidth,
    let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
      (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
    rows'.Nonempty →
    let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
    ∃B : Batch M H (Sum Bool (RayQuotient.Characters M H)) (Fin N)
        (Z^d) a ε (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) (Z^τ) ((Z^d)^(τ/(2*dmax))) i,
      B.rows=rows' ∧ B.data=sourceMomentData M H hH S hS.prime η ∧
      B.reverse=sourceMomentReverse M H ∧ B.slots=Finset.univ ∧
      B.widths=(fun j=> ell j/d) ∧ B.profile=W ∧ B.upper=upper ∧ B.external=z ∧
      B.mesh=mesh ∧ B.binWidth=binWidth ∧
      (∀u∈rows',∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j) ∧
      (∀u∈B.rows,HeckeDetectorAmplitudeFirst.rowMean B.slots (Z^d) ((2*a-1)/2) B.binWidth B.widths
        (HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
          B.profile B.upper B.widths B.external (Z^d)) u=q) := by
  have hbatches := perturbed_actual_source_batch M H hH S hS hmax η
    dmin dmax τ ε e κ heightCost margin mesh binWidth I hdmin hdmax hdtop hτ hτzero hτheight
    hε he he' hκ hκ' hheightCost hmargin hm hb hbudget
  filter_upwards [hbatches] with Z hbatch
  intro d hd hd' U rows hne hrows hcal hrow a i hi ha ha' hnext hcurrent N ell hell hsmall hsum W upper z
  dsimp only
  intro bin hne'
  let Q := HeckeDetectorPhysicalSelection.physical M H (fun u : FreeRow=> u.val)
    W upper (fun j=> ell j/d) z (Z^d)
  let rows' := HeckeDetectorAmplitudeFirst.amplitudeRows rows Finset.univ
    (Z^d) ((2*a-1)/2) binWidth hb (fun j=> ell j/d) Q bin
  let q := HeckeDetectorAmplitudeFirst.classMean Finset.univ ((2*a-1)/2) binWidth (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hcut := HeckeDetectorAdaptiveCutoff.cutoff_bounds (2*a-1) q (by linarith)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam⟩ :=
    hbatch d hd hd' U rows' hne' (hsub.trans hrows)
      (fun u hu=> hcal u (hsub hu)) (fun u hu=> hrow u (hsub hu)) a i hi ha ha'
      (fun u hu=> hnext u (hsub hu)) (fun u hu=> hcurrent u (hsub hu))
      (HeckeDetectorAdaptiveCutoff.cutoff (2*a-1) q) hcut.1 hcut.2 N ell hell hsmall hsum W upper z
  refine ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW,hUpper,hZ,hMesh,hBin,hFam,?_⟩
  intro u hu
  have hu' : u∈rows' := hBr ▸ hu
  rw [hSlots,hWidths,hW,hUpper,hZ,hBin]
  exact HeckeDetectorAmplitudeFirst.rowMean_eq rows Finset.univ (Z^d) ((2*a-1)/2)
    binWidth hb (fun j=> ell j/d) Q bin u hu'
#print axioms perturbed_actual_source_amplitude_batches

end SevenEighths.ProbeHighRowFamily

end

end OAI

end LocalModule3
/- END RHZeroFreeExtension.analytic_high.PerturbedSourceAmplitudeClasses -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorClass -/
section LocalModule4
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

omit [NeZero M] in
lemma fixed_nonfloorPoolOutside (S : Finset (Ideal O)) (N : ℕ) (c b : ℝ) (Y : Fin N→ℝ) :
    ∀j P,P∈pool (RayQuotient.identityClass M H) S c b (Y j) → P.val∉S :=
  fun j P hP=>(mem_pool _ S c b (Y j) P).mp hP |>.2.2.2

theorem perturbed_fixed_actual_nonfloor_class_from_raw_moments (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=5003/30000)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost) (counts : ProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → 51/100< a → a≤1 → 0≤ C0 →
      ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i z Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
      ∀bin : BinLabel (Finset.univ : Finset (Fin N)) ((2*a-1)/2) mesh,
      let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=> ell j/d) Q bin
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
      rows'.Nonempty → 0≤ q ∧ q≤(2*a-1)/2 ∧
      ‖cubeArithmeticSum S hS hmax η rows' T (fixed_nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(logCost+heightCost+momentCost+
            d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
            v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-5003/187500+(5003/30000)*q+(5003/30000)*mesh) := by
  have hdmax0 : 0< dmax := hdmin.trans_le hdRange
  obtain ⟨K,hK,hcount⟩ :=
    ProbeFinalAssembly.adaptive_source_count_from_raw_moments M H hH S φ hφ hφc hφp hφ0 hφne
      a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB εm hεm
      (Sum Bool (RayQuotient.Characters M H)) N n dmin dmax τ logCost heightCost momentCost mesh
      hdmin hdmax0 hτ hlog hMomentHeight hmesh counts
  obtain ⟨C,hC,hphysical⟩ := perturbed_actual_class_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh (1/100) margin loss
    he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh (by norm_num)
    hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
  refine ⟨C*K,mul_pos hC hK,?_⟩
  intro η
  have hbatches := perturbed_actual_source_amplitude_batches M H hH S hS hmax η
    dmin dmax τ ε e κ cost margin R mesh n hdmin hdRange hdtop hτ hτzero hτheight
    hε he he1 hκ hκ1 hcost hmargin hR hmesh hwbudget
  filter_upwards [hphysical η,hcount,hbatches,eventually_gt_atTop (1:ℝ)] with Z hphysical hcount hbatch hZ
  intro d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom bin hne
  have hZp : 0< Z := zero_lt_one.trans hZ
  have hd0 : 0< d := hdmin.trans_le hd
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
  let rows' := amplitudeRows rows Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh (fun j=> ell j/d) Q bin
  let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
  have hsub : rows'⊆rows := Finset.filter_subset _ _
  have hrowne : rows.Nonempty := hne.mono hsub
  have hband : rows⊆rowBand (Z^(1/100:ℝ)) (2*Z^v+1) := by
    intro u hu
    exact mem_rowBand.mpr ⟨(hrows u hu).1,(hrows u hu).2.1,by linarith [(hnorm u hu).2]⟩
  have hellpos (j : Fin N) : 0< ell j := (mul_pos hdmax0 hrmin).trans_le (hello j)
  obtain ⟨B,hBr,hBd,hRev,hSlots,hWidths,hW',hUpper,hExternal,hMesh,hBin,hFam,hMean⟩ :=
    hbatch d hd hd' (2*Z^v+1) rows hrowne hband (fun u hu=>(hrows u hu).2.2.1)
      (fun u hu=>(hrows u hu).2.2.2) a i hi ha ha' hnext hcurrent
      N ell hellpos hellhi (by rw [hellsum];norm_num) W (fun _=> b) (fun _=> z) bin hne
  have hBsub : B.rows⊆rows := hBr ▸ hsub
  have hBfam : ∀u∈B.rows,∀j,B.family u j=sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u) j := by
    intro u hu j
    exact hFam u (hBr ▸ hu) j
  have hraw := hmom q B hBsub hBd hRev hSlots hWidths hW' hUpper hExternal hMesh hBin hBfam
  have hcard := hcount d hd hd' a ε Δ ν C0 q i hi ha ha' hε.le hε1 hΔ hΔ1 hν hC0 B
    (by rw [hSlots];simp) hBin (hBr.symm ▸ hne) hMean hraw
  rw [hBr,hMesh] at hcard
  have hqb := classMean_bounds rows Finset.univ (Z^d) (2*a-1) mesh hmesh (fun j=> ell j/d) Q bin
    (by linarith) (fun j _=> div_nonneg (hellpos j).le hd0.le)
    (by rw [perturbed_source_slot_length_sum Finset.univ ell d hellsum];positivity) hne
  refine ⟨hqb.1,hqb.2,?_⟩
  have hp := hphysical d hd hd' v a q (K*C0*Z^(logCost+heightCost+momentCost))
    (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) hv ha.le ha' (by positivity) rows'
    (fun u hu=> hrows u (hsub hu)) (fun u hu=> hnorm u (hsub hu)) hcard i hi
    (fun u hu=> hnext u (hsub hu)) t ht
    (fun u hu=> source_amplitude_class_mean M H ell W Z d b a mesh z hZp hd0.ne' hmesh rows bin u hu)
  apply hp.trans_eq
  rw [show logCost+heightCost+momentCost+
      d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-5003/187500+(5003/30000)*q+(5003/30000)*mesh=
      (logCost+heightCost+momentCost)+(d*adaptiveRowExponent (2*a-1) q Δ ε εm R ν+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-5003/187500+(5003/30000)*q+(5003/30000)*mesh) by ring,
    Real.rpow_add hZp (logCost+heightCost+momentCost)]
  ring


end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule4
/- END RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorClass -/

/- BEGIN original module geometry.Endpoint -/
section LocalModule5
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace RHGeometry
noncomputable section

def Q (δ y : ℝ) : ℝ :=
  10*(37+34*y)-8*(237+377*y+26*y^2)*δ +
  48*(51+131*y+94*y^2+32*y^3)*δ^2 -
  96*(185+170*y+(-138+12*y+96*y^2)*δ)/5000

lemma box0 (δ y : ℝ) (ha : (0 : ℝ) ≤ δ) (hb : δ ≤ (5 / 24 : ℝ))
    (hc : (0 : ℝ) ≤ y) (hd : y ≤ (1 / 4 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(0 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 24 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(0 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 4 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (1688592384 / 3125 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(0 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (5453697024 / 3125 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(0 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (5841616896 / 3125 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(0 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (2076512256 / 3125 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(0 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 +
    (1559568384 / 3125 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(0 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (189225984 / 125 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(0 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (4770003456 / 3125 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(0 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (319784448 / 625 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(0 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 +
    (2884608 / 25 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(0 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (1060152576 / 3125 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(0 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (216477312 / 625 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(0 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (387609984 / 3125 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(0 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box1 (δ y : ℝ) (ha : (5 / 24 : ℝ) ≤ δ) (hb : δ ≤ (5 / 16 : ℝ))
    (hc : (0 : ℝ) ≤ y) (hd : y ≤ (1 / 8 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 24 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 16 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(0 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 8 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (92307456 / 25 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(0 : ℝ))^0 * ((1 / 8 : ℝ)-y)^3 +
    (34270089216 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(0 : ℝ))^1 * ((1 / 8 : ℝ)-y)^2 +
    (34275357696 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(0 : ℝ))^2 * ((1 / 8 : ℝ)-y)^1 +
    (2312580096 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(0 : ℝ))^3 * ((1 / 8 : ℝ)-y)^0 +
    (9662201856 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(0 : ℝ))^0 * ((1 / 8 : ℝ)-y)^3 +
    (27535429632 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(0 : ℝ))^1 * ((1 / 8 : ℝ)-y)^2 +
    (27186041856 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(0 : ℝ))^2 * ((1 / 8 : ℝ)-y)^1 +
    (1874082816 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(0 : ℝ))^3 * ((1 / 8 : ℝ)-y)^0 +
    (2040569856 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(0 : ℝ))^0 * ((1 / 8 : ℝ)-y)^3 +
    (6273340416 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(0 : ℝ))^1 * ((1 / 8 : ℝ)-y)^2 +
    (1457816832 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(0 : ℝ))^2 * ((1 / 8 : ℝ)-y)^1 +
    (123980544 / 125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(0 : ℝ))^3 * ((1 / 8 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box2 (δ y : ℝ) (ha : (5 / 16 : ℝ) ≤ δ) (hb : δ ≤ (35 / 96 : ℝ))
    (hc : (0 : ℝ) ≤ y) (hd : y ≤ (1 / 16 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 16 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (35 / 96 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(0 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 16 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (65298235392 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((35 / 96 : ℝ)-δ)^2 * (y-(0 : ℝ))^0 * ((1 / 16 : ℝ)-y)^3 +
    (198320799744 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((35 / 96 : ℝ)-δ)^2 * (y-(0 : ℝ))^1 * ((1 / 16 : ℝ)-y)^2 +
    (41531959296 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((35 / 96 : ℝ)-δ)^2 * (y-(0 : ℝ))^2 * ((1 / 16 : ℝ)-y)^1 +
    (74810032128 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((35 / 96 : ℝ)-δ)^2 * (y-(0 : ℝ))^3 * ((1 / 16 : ℝ)-y)^0 +
    (8259895296 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((35 / 96 : ℝ)-δ)^1 * (y-(0 : ℝ))^0 * ((1 / 16 : ℝ)-y)^3 +
    (142786117632 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((35 / 96 : ℝ)-δ)^1 * (y-(0 : ℝ))^1 * ((1 / 16 : ℝ)-y)^2 +
    (178005362688 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((35 / 96 : ℝ)-δ)^1 * (y-(0 : ℝ))^2 * ((1 / 16 : ℝ)-y)^1 +
    (76921921536 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((35 / 96 : ℝ)-δ)^1 * (y-(0 : ℝ))^3 * ((1 / 16 : ℝ)-y)^0 +
    (7335641088 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((35 / 96 : ℝ)-δ)^0 * (y-(0 : ℝ))^0 * ((1 / 16 : ℝ)-y)^3 +
    (43498917888 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((35 / 96 : ℝ)-δ)^0 * (y-(0 : ℝ))^1 * ((1 / 16 : ℝ)-y)^2 +
    (74635166208 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((35 / 96 : ℝ)-δ)^0 * (y-(0 : ℝ))^2 * ((1 / 16 : ℝ)-y)^1 +
    (38707089408 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((35 / 96 : ℝ)-δ)^0 * (y-(0 : ℝ))^3 * ((1 / 16 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box3 (δ y : ℝ) (ha : (35 / 96 : ℝ) ≤ δ) (hb : δ ≤ (25 / 64 : ℝ))
    (hc : (0 : ℝ) ≤ y) (hd : y ≤ (1 / 32 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(35 / 96 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (25 / 64 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(0 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 32 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (234740514816 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((25 / 64 : ℝ)-δ)^2 * (y-(0 : ℝ))^0 * ((1 / 32 : ℝ)-y)^3 +
    (1048093458432 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((25 / 64 : ℝ)-δ)^2 * (y-(0 : ℝ))^1 * ((1 / 32 : ℝ)-y)^2 +
    (1469119401984 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((25 / 64 : ℝ)-δ)^2 * (y-(0 : ℝ))^2 * ((1 / 32 : ℝ)-y)^1 +
    (656707258368 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((25 / 64 : ℝ)-δ)^2 * (y-(0 : ℝ))^3 * ((1 / 32 : ℝ)-y)^0 +
    (43429920768 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((25 / 64 : ℝ)-δ)^1 * (y-(0 : ℝ))^0 * ((1 / 32 : ℝ)-y)^3 +
    (202160799744 / 625 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((25 / 64 : ℝ)-δ)^1 * (y-(0 : ℝ))^1 * ((1 / 32 : ℝ)-y)^2 +
    (2057454096384 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((25 / 64 : ℝ)-δ)^1 * (y-(0 : ℝ))^2 * ((1 / 32 : ℝ)-y)^1 +
    (1092096018432 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((25 / 64 : ℝ)-δ)^1 * (y-(0 : ℝ))^3 * ((1 / 32 : ℝ)-y)^0 +
    (59364605952 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((25 / 64 : ℝ)-δ)^0 * (y-(0 : ℝ))^0 * ((1 / 32 : ℝ)-y)^3 +
    (734857740288 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((25 / 64 : ℝ)-δ)^0 * (y-(0 : ℝ))^1 * ((1 / 32 : ℝ)-y)^2 +
    (55242187776 / 125 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((25 / 64 : ℝ)-δ)^0 * (y-(0 : ℝ))^2 * ((1 / 32 : ℝ)-y)^1 +
    (706641560064 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((25 / 64 : ℝ)-δ)^0 * (y-(0 : ℝ))^3 * ((1 / 32 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box4 (δ y : ℝ) (ha : (25 / 64 : ℝ) ≤ δ) (hb : δ ≤ (5 / 12 : ℝ))
    (hc : (0 : ℝ) ≤ y) (hd : y ≤ (1 / 32 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(25 / 64 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 12 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(0 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 32 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (59364605952 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(0 : ℝ))^0 * ((1 / 32 : ℝ)-y)^3 +
    (734857740288 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(0 : ℝ))^1 * ((1 / 32 : ℝ)-y)^2 +
    (55242187776 / 125 : ℝ) * (δ-(25 / 64 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(0 : ℝ))^2 * ((1 / 32 : ℝ)-y)^1 +
    (706641560064 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(0 : ℝ))^3 * ((1 / 32 : ℝ)-y)^0 +
    (38805700608 / 625 : ℝ) * (δ-(25 / 64 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(0 : ℝ))^0 * ((1 / 32 : ℝ)-y)^3 +
    (1928626962432 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(0 : ℝ))^1 * ((1 / 32 : ℝ)-y)^2 +
    (3466764681216 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(0 : ℝ))^2 * ((1 / 32 : ℝ)-y)^1 +
    (1734470221824 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(0 : ℝ))^3 * ((1 / 32 : ℝ)-y)^0 +
    (385339097088 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(0 : ℝ))^0 * ((1 / 32 : ℝ)-y)^3 +
    (1965916422144 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(0 : ℝ))^1 * ((1 / 32 : ℝ)-y)^2 +
    (2878429986816 / 3125 : ℝ) * (δ-(25 / 64 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(0 : ℝ))^2 * ((1 / 32 : ℝ)-y)^1 +
    (259816292352 / 625 : ℝ) * (δ-(25 / 64 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(0 : ℝ))^3 * ((1 / 32 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box5 (δ y : ℝ) (ha : (35 / 96 : ℝ) ≤ δ) (hb : δ ≤ (5 / 12 : ℝ))
    (hc : (1 / 32 : ℝ) ≤ y) (hd : y ≤ (1 / 16 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(35 / 96 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 12 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(1 / 32 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 16 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (164176814592 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 32 : ℝ))^0 * ((1 / 16 : ℝ)-y)^3 +
    (617781037056 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 32 : ℝ))^1 * ((1 / 16 : ℝ)-y)^2 +
    (763025737728 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 32 : ℝ))^2 * ((1 / 16 : ℝ)-y)^1 +
    (309656715264 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 32 : ℝ))^3 * ((1 / 16 : ℝ)-y)^0 +
    (217694380032 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 32 : ℝ))^0 * ((1 / 16 : ℝ)-y)^3 +
    (1011998932992 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 32 : ℝ))^1 * ((1 / 16 : ℝ)-y)^2 +
    (1417018441728 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 32 : ℝ))^2 * ((1 / 16 : ℝ)-y)^1 +
    (623251488768 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 32 : ℝ))^3 * ((1 / 16 : ℝ)-y)^0 +
    (64954073088 / 625 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 32 : ℝ))^0 * ((1 / 16 : ℝ)-y)^3 +
    (1229014695936 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 32 : ℝ))^1 * ((1 / 16 : ℝ)-y)^2 +
    (12082348032 / 25 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 32 : ℝ))^2 * ((1 / 16 : ℝ)-y)^1 +
    (606356373504 / 3125 : ℝ) * (δ-(35 / 96 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 32 : ℝ))^3 * ((1 / 16 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box6 (δ y : ℝ) (ha : (5 / 16 : ℝ) ≤ δ) (hb : δ ≤ (5 / 12 : ℝ))
    (hc : (1 / 16 : ℝ) ≤ y) (hd : y ≤ (1 / 8 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 16 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 12 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(1 / 16 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 8 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (18702508032 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 16 : ℝ))^0 * ((1 / 8 : ℝ)-y)^3 +
    (60300099072 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 16 : ℝ))^1 * ((1 / 8 : ℝ)-y)^2 +
    (13270099968 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 16 : ℝ))^2 * ((1 / 8 : ℝ)-y)^1 +
    (991844352 / 125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 16 : ℝ))^3 * ((1 / 8 : ℝ)-y)^0 +
    (1055944704 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 16 : ℝ))^0 * ((1 / 8 : ℝ)-y)^3 +
    (4232577024 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 16 : ℝ))^1 * ((1 / 8 : ℝ)-y)^2 +
    (44212862976 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 16 : ℝ))^2 * ((1 / 8 : ℝ)-y)^1 +
    (4844224512 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 16 : ℝ))^3 * ((1 / 8 : ℝ)-y)^0 +
    (18948636672 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 16 : ℝ))^0 * ((1 / 8 : ℝ)-y)^3 +
    (76144386048 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 16 : ℝ))^1 * ((1 / 8 : ℝ)-y)^2 +
    (98879963136 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 16 : ℝ))^2 * ((1 / 8 : ℝ)-y)^1 +
    (8352202752 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 16 : ℝ))^3 * ((1 / 8 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box7 (δ y : ℝ) (ha : (5 / 24 : ℝ) ≤ δ) (hb : δ ≤ (5 / 16 : ℝ))
    (hc : (1 / 8 : ℝ) ≤ y) (hd : y ≤ (1 / 4 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 24 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 16 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(1 / 8 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 4 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (2312580096 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (35102045184 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (35923464192 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (12403519488 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 +
    (1874082816 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (29036442624 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (31236231168 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (11627802624 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 +
    (123980544 / 125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (2261599488 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (14311166976 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (6145883136 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box8 (δ y : ℝ) (ha : (5 / 16 : ℝ) ≤ δ) (hb : δ ≤ (5 / 12 : ℝ))
    (hc : (1 / 8 : ℝ) ≤ y) (hd : y ≤ (1 / 4 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 16 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 12 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(1 / 8 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 4 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (123980544 / 125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (2261599488 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (14311166976 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (6145883136 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 8 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 +
    (605528064 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (16195547136 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (26008436736 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (2591145984 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 8 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 +
    (1044025344 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^0 * ((1 / 4 : ℝ)-y)^3 +
    (22261149696 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^1 * ((1 / 4 : ℝ)-y)^2 +
    (6139133952 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^2 * ((1 / 4 : ℝ)-y)^1 +
    (13731446784 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 8 : ℝ))^3 * ((1 / 4 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box9 (δ y : ℝ) (ha : (0 : ℝ) ≤ δ) (hb : δ ≤ (5 / 24 : ℝ))
    (hc : (1 / 4 : ℝ) ≤ y) (hd : y ≤ (1 / 2 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(0 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 24 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(1 / 4 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 2 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (2076512256 / 3125 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (1323491328 / 625 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (7005376512 / 3125 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (2464432128 / 3125 : ℝ) * (δ-(0 : ℝ))^0 * ((5 / 24 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 +
    (319784448 / 625 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (4823529984 / 3125 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (4837702656 / 3125 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (1613094912 / 3125 : ℝ) * (δ-(0 : ℝ))^1 * ((5 / 24 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 +
    (387609984 / 3125 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (1243273344 / 3125 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (1381926144 / 3125 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (531062784 / 3125 : ℝ) * (δ-(0 : ℝ))^2 * ((5 / 24 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box10 (δ y : ℝ) (ha : (5 / 24 : ℝ) ≤ δ) (hb : δ ≤ (5 / 16 : ℝ))
    (hc : (1 / 4 : ℝ) ≤ y) (hd : y ≤ (3 / 8 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 24 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 16 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(1 / 4 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (3 / 8 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (12403519488 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^0 * ((3 / 8 : ℝ)-y)^3 +
    (38497652736 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^1 * ((3 / 8 : ℝ)-y)^2 +
    (40250422272 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^2 * ((3 / 8 : ℝ)-y)^1 +
    (14175489024 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 16 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^3 * ((3 / 8 : ℝ)-y)^0 +
    (11627802624 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^0 * ((3 / 8 : ℝ)-y)^3 +
    (38530584576 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^1 * ((3 / 8 : ℝ)-y)^2 +
    (8725029888 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^2 * ((3 / 8 : ℝ)-y)^1 +
    (16779967488 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 16 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^3 * ((3 / 8 : ℝ)-y)^0 +
    (6145883136 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^0 * ((3 / 8 : ℝ)-y)^3 +
    (4512826368 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^1 * ((3 / 8 : ℝ)-y)^2 +
    (27813927168 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^2 * ((3 / 8 : ℝ)-y)^1 +
    (11438878464 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 16 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^3 * ((3 / 8 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box11 (δ y : ℝ) (ha : (5 / 16 : ℝ) ≤ δ) (hb : δ ≤ (5 / 12 : ℝ))
    (hc : (1 / 4 : ℝ) ≤ y) (hd : y ≤ (3 / 8 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 16 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 12 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(1 / 4 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (3 / 8 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (6145883136 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^0 * ((3 / 8 : ℝ)-y)^3 +
    (4512826368 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^1 * ((3 / 8 : ℝ)-y)^2 +
    (27813927168 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^2 * ((3 / 8 : ℝ)-y)^1 +
    (11438878464 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(1 / 4 : ℝ))^3 * ((3 / 8 : ℝ)-y)^0 +
    (2591145984 / 625 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^0 * ((3 / 8 : ℝ)-y)^3 +
    (51725942784 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^1 * ((3 / 8 : ℝ)-y)^2 +
    (67630559232 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^2 * ((3 / 8 : ℝ)-y)^1 +
    (28975546368 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(1 / 4 : ℝ))^3 * ((3 / 8 : ℝ)-y)^0 +
    (13731446784 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^0 * ((3 / 8 : ℝ)-y)^3 +
    (51693010944 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^1 * ((3 / 8 : ℝ)-y)^2 +
    (64255832064 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^2 * ((3 / 8 : ℝ)-y)^1 +
    (26371067904 / 3125 : ℝ) * (δ-(5 / 16 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(1 / 4 : ℝ))^3 * ((3 / 8 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box12 (δ y : ℝ) (ha : (5 / 24 : ℝ) ≤ δ) (hb : δ ≤ (5 / 12 : ℝ))
    (hc : (3 / 8 : ℝ) ≤ y) (hd : y ≤ (1 / 2 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 24 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 12 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(3 / 8 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 2 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (3543872256 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(3 / 8 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (11200627968 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(3 / 8 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (11900457984 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(3 / 8 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (4248502272 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^0 * ((5 / 12 : ℝ)-δ)^2 * (y-(3 / 8 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 +
    (1302239232 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(3 / 8 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (6126071808 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(3 / 8 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (8893882368 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(3 / 8 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (4089249792 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^1 * ((5 / 12 : ℝ)-δ)^1 * (y-(3 / 8 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 +
    (6592766976 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(3 / 8 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (4698528768 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(3 / 8 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (27780624384 / 3125 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(3 / 8 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (2179989504 / 625 : ℝ) * (δ-(5 / 24 : ℝ))^2 * ((5 / 12 : ℝ)-δ)^0 * (y-(3 / 8 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

lemma box13 (δ y : ℝ) (ha : (5 / 12 : ℝ) ≤ δ) (hb : δ ≤ (5 / 6 : ℝ))
    (hc : (0 : ℝ) ≤ y) (hd : y ≤ (1 / 2 : ℝ)) : 0 ≤ Q δ y := by
  have h₁ : 0 ≤ δ-(5 / 12 : ℝ) := sub_nonneg.mpr ha
  have h₂ : 0 ≤ (5 / 6 : ℝ)-δ := sub_nonneg.mpr hb
  have h₃ : 0 ≤ y-(0 : ℝ) := sub_nonneg.mpr hc
  have h₄ : 0 ≤ (1 / 2 : ℝ)-y := sub_nonneg.mpr hd
  have hid : Q δ y =
    (367488 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^0 * ((5 / 6 : ℝ)-δ)^2 * (y-(0 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (13460544 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^0 * ((5 / 6 : ℝ)-δ)^2 * (y-(0 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (50870976 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^0 * ((5 / 6 : ℝ)-δ)^2 * (y-(0 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (8515584 / 625 : ℝ) * (δ-(5 / 12 : ℝ))^0 * ((5 / 6 : ℝ)-δ)^2 * (y-(0 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 +
    (9533952 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^1 * ((5 / 6 : ℝ)-δ)^1 * (y-(0 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (120031104 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^1 * ((5 / 6 : ℝ)-δ)^1 * (y-(0 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (314817408 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^1 * ((5 / 6 : ℝ)-δ)^1 * (y-(0 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (223520256 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^1 * ((5 / 6 : ℝ)-δ)^1 * (y-(0 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 +
    (70366464 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^2 * ((5 / 6 : ℝ)-δ)^0 * (y-(0 : ℝ))^0 * ((1 / 2 : ℝ)-y)^3 +
    (73754112 / 625 : ℝ) * (δ-(5 / 12 : ℝ))^2 * ((5 / 6 : ℝ)-δ)^0 * (y-(0 : ℝ))^1 * ((1 / 2 : ℝ)-y)^2 +
    (632946432 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^2 * ((5 / 6 : ℝ)-δ)^0 * (y-(0 : ℝ))^2 * ((1 / 2 : ℝ)-y)^1 +
    (353742336 / 3125 : ℝ) * (δ-(5 / 12 : ℝ))^2 * ((5 / 6 : ℝ)-δ)^0 * (y-(0 : ℝ))^3 * ((1 / 2 : ℝ)-y)^0 := by unfold Q; ring
  rw [hid]
  positivity

theorem Q_nonneg (δ y : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1/2) : 0 ≤ Q δ y := by
  rcases le_total δ (5 / 12 : ℝ) with h1 | h1
  · rcases le_total y (1 / 4 : ℝ) with h2 | h2
    · rcases le_total δ (5 / 24 : ℝ) with h3 | h3
      · exact box0 δ y hδ0 h3 hy0 h2
      · rcases le_total y (1 / 8 : ℝ) with h4 | h4
        · rcases le_total δ (5 / 16 : ℝ) with h5 | h5
          · exact box1 δ y h3 h5 hy0 h4
          · rcases le_total y (1 / 16 : ℝ) with h6 | h6
            · rcases le_total δ (35 / 96 : ℝ) with h7 | h7
              · exact box2 δ y h5 h7 hy0 h6
              · rcases le_total y (1 / 32 : ℝ) with h8 | h8
                · rcases le_total δ (25 / 64 : ℝ) with h9 | h9
                  · exact box3 δ y h7 h9 hy0 h8
                  · exact box4 δ y h9 h1 hy0 h8
                · exact box5 δ y h7 h1 h8 h6
            · exact box6 δ y h5 h1 h6 h4
        · rcases le_total δ (5 / 16 : ℝ) with h5 | h5
          · exact box7 δ y h3 h5 h4 h2
          · exact box8 δ y h5 h1 h4 h2
    · rcases le_total δ (5 / 24 : ℝ) with h3 | h3
      · exact box9 δ y hδ0 h3 h2 hy1
      · rcases le_total y (3 / 8 : ℝ) with h4 | h4
        · rcases le_total δ (5 / 16 : ℝ) with h5 | h5
          · exact box10 δ y h3 h5 h2 h4
          · exact box11 δ y h5 h1 h2 h4
        · exact box12 δ y h3 h1 h4 hy1
  · exact box13 δ y h1 hδ1 hy0 hy1


def D (x : ℝ) : ℝ := 3-17*x/9
def P (x : ℝ) : ℝ := (2-8*x/9)*(1-x)
def J (δ x : ℝ) : ℝ := (5/6-δ)*D x+δ*P x
def R (δ x : ℝ) : ℝ := 1-δ+(5/6-δ)*δ*P x/(2*J δ x)
def E (ℓ δ x : ℝ) : ℝ :=
  -1/4+(1/8)/6+5*ℓ/4+(1/2+ℓ)*δ+ℓ*(δ*x)-
  ((1+1/8+3*ℓ)/2)*(1-R δ x)

lemma P_lower (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 7/9 ≤ P x := by
  unfold P
  nlinarith [mul_nonneg _hx0 _hx0]

lemma D_ge_P (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : P x ≤ D x := by
  unfold P D
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]

lemma J_lower (δ x : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 35/54 ≤ J δ x := by
  have hp := P_lower x hx0 hx1
  have hd := D_ge_P x hx0 hx1
  have hm := mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr hd)
  unfold J at *
  nlinarith

lemma baseline_identity (δ x : ℝ) (hJ : J δ x ≠ 0) :
    Q δ (1/2-x) = 10368*J δ x*(-E (1/6) δ x-1/5000) := by
  unfold Q E R
  field_simp [hJ]
  unfold J D P
  ring

theorem baseline_endpoint (δ x : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 1/5000 ≤ -E (1/6) δ x := by
  have hjl := J_lower δ x hδ0 hδ1 hx0 hx1
  have hj : 0 < J δ x := by linarith
  have hc := Q_nonneg δ (1/2-x) hδ0 hδ1 (by linarith) (by linarith)
  rw [baseline_identity δ x (ne_of_gt hj)] at hc
  have hh : 0 ≤ -E (1/6) δ x-1/5000 :=
    nonneg_of_mul_nonneg_left (by simpa [mul_comm] using hc) (by positivity : 0 < 10368*J δ x)
  linarith

lemma derivative_upper (δ x : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    -1/4+δ+δ*x+3*R δ x/2 ≤ 45/32 := by
  have hp := P_lower x hx0 hx1
  have hd := D_ge_P x hx0 hx1
  have hjl := J_lower δ x hδ0 hδ1 hx0 hx1
  have hj : 0 < J δ x := by linarith
  have hjp : (5/6)*P x ≤ J δ x := by
    have hm := mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr hd)
    unfold J at *
    nlinarith
  have hquad : (5/6-δ)*δ ≤ (5/6)^2/4 := by nlinarith [sq_nonneg (δ-5/12)]
  have hm₁ := mul_nonneg (by linarith : 0 ≤ P x) (sub_nonneg.mpr hquad)
  have hm₂ := mul_nonneg (by norm_num : (0 : ℝ) ≤ 5/24) (sub_nonneg.mpr hjp)
  have hn : (5/6-δ)*δ*P x ≤ (5/24)*J δ x := by nlinarith
  have hr : (5/6-δ)*δ*P x/(2*J δ x) ≤ 5/48 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*J δ x)).2
    nlinarith
  have hx := mul_nonneg hδ0 (sub_nonneg.mpr hx1)
  unfold R
  nlinarith

lemma perturbation_identity (δ x : ℝ) :
    E (5003/30000) δ x = E (1/6) δ x+
      (1/10000)*(-1/4+δ+δ*x+3*R δ x/2) := by
  unfold E
  ring

theorem perturbed_endpoint (δ x : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : E (5003/30000) δ x ≤ -19/320000 := by
  have hb := baseline_endpoint δ x hδ0 hδ1 hx0 hx1
  have hd := derivative_upper δ x hδ0 hδ1 hx0 hx1
  rw [perturbation_identity]
  linarith

def lx (ℓ : ℝ) : ℝ := (1-1/8-ℓ)/2
def ly (ℓ : ℝ) : ℝ := (1+1/8-ℓ)/2
def h (ℓ : ℝ) : ℝ := (1+1/8+3*ℓ)/2
def signal (ℓ s : ℝ) : ℝ := lx ℓ/2+s-1+h ℓ/6

theorem signal_identity (ℓ s : ℝ) : signal ℓ s = s-11/16 := by
  unfold signal lx h
  ring

theorem exact_geometry :
    lx (5003/30000) = 21247/60000 ∧
    ly (5003/30000) = 28747/60000 ∧
    h (5003/30000) = 16253/20000 ∧
    signal (5003/30000) (34999/40000) = 7499/40000 := by
  norm_num [lx, ly, h, signal]

#print axioms baseline_endpoint
#print axioms perturbed_endpoint
#print axioms exact_geometry

end
end RHGeometry

end LocalModule5
/- END geometry.Endpoint -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedCentralExponent -/
section LocalModule6

/-! Literal generalized physical high-row exponent arithmetic. This is the
source eight-term exponent with independent scales. Actual arithmetic sum
bounds remain separate; no physical energy bound is assumed or concluded. -/
namespace RHZeroFreeExtension.PerturbedCentralExponent
noncomputable section

def ell : ℝ := 5003/30000
def lx : ℝ := 21247/60000
def ly : ℝ := 28747/60000
def h : ℝ := 16253/20000
def boundary : ℝ := 34999/40000

def physicalExponent (a d rowExponent q s : ℝ) : ℝ :=
  lx*(1/2-s)+a+s-1-a*ly-d*s+d*rowExponent+d*(a-1/2)+ell*(s-1/2+q)

lemma physical_scale_endpoint_identity (δ x R s : ℝ) :
    physicalExponent ((1+δ)/2) h R (δ*x) s - (boundary-11/16) =
      RHGeometry.E ell δ x + h*(R-RHGeometry.R δ x) := by
  unfold physicalExponent lx ly h ell boundary RHGeometry.E
  ring

lemma physical_slope_identity (a d R q s : ℝ) :
    physicalExponent a d R q s = physicalExponent a h R q s+(d-h)*(R+a-1/2-s) := by
  unfold physicalExponent
  ring

/-- Insert the actual count exponent only after it is proved. These are
count/slope hypotheses, not a desired high-energy bound. -/
theorem balanced_physical_margin (δ x R d s loss ζ : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hR : R ≤ RHGeometry.R δ x+loss)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+δ/2-s) (hshi : R+δ/2-s ≤ 2) :
    physicalExponent ((1+δ)/2) d R (δ*x) s-(boundary-11/16) ≤
      -19/320000+h*loss+2*ζ := by
  have hend := RHGeometry.perturbed_endpoint δ x hδ hδ' hx hx'
  have hrow := mul_le_mul_of_nonneg_left hR (by norm_num [h] : 0 ≤ h)
  have hext := mul_le_mul_of_nonneg_right (show d-h ≤ ζ by linarith) hslo
  have hz := mul_le_mul_of_nonneg_left hshi hζ
  have hid := physical_scale_endpoint_identity δ x R s
  have hslope := physical_slope_identity ((1+δ)/2) d R (δ*x) s
  have hs : R+(1+δ)/2-1/2-s = R+δ/2-s := by ring
  rw [hs] at hslope
  change RHGeometry.E ell δ x ≤ -19/320000 at hend
  nlinarith

/-- Common-loss conversion, independent of any analytic sum. -/
theorem balanced_physical_saving (δ x R d s loss ζ overhead saving : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6) (hx : 0 ≤ x) (hx' : x ≤ 1/2)
    (hR : R ≤ RHGeometry.R δ x+loss)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+δ/2-s) (hshi : R+δ/2-s ≤ 2)
    (hbudget : h*loss+2*ζ+overhead+saving ≤ 19/320000) :
    physicalExponent ((1+δ)/2) d R (δ*x) s+overhead ≤ boundary-11/16-saving := by
  have hm := balanced_physical_margin δ x R d s loss ζ
    hδ hδ' hx hx' hR hζ hd hslo hshi
  linarith

lemma physical_extend (a d R q s ζ : ℝ) (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+a-1/2-s) (hshi : R+a-1/2-s ≤ 2) :
    physicalExponent a d R q s ≤ physicalExponent a h R q s+2*ζ := by
  have h1 := mul_le_mul_of_nonneg_right (show d-h ≤ ζ by linarith) hslo
  have h2 := mul_le_mul_of_nonneg_left hshi hζ
  rw [physical_slope_identity]
  linarith

/-- The delta>5/6 branch uses the unmarked high count, not the balanced
certificate outside its parameter rectangle. -/
theorem high_physical_margin (δ R d q s loss ζ : ℝ)
    (hδ : 5/6 ≤ δ) (hq : q ≤ δ/2) (hR : R ≤ 1-δ+loss)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ R+δ/2-s) (hshi : R+δ/2-s ≤ 2) :
    physicalExponent ((1+δ)/2) d R q s-(boundary-11/16) ≤
      -1/20+h*loss+2*ζ := by
  have hs : R+(1+δ)/2-1/2-s = R+δ/2-s := by ring
  have he := physical_extend ((1+δ)/2) d R q s ζ hζ hd
    (by simpa only [hs] using hslo) (by simpa only [hs] using hshi)
  unfold physicalExponent lx ly h ell boundary at *
  nlinarith

/-- No zero witness or marked count is assumed on the actual floor. -/
theorem floor_physical_margin (d s q ζ : ℝ) (hq : q ≤ 1/100)
    (hζ : 0 ≤ ζ) (hd : d ≤ h+ζ)
    (hslo : 0 ≤ 1+(51/100:ℝ)-1/2-s)
    (hshi : 1+(51/100:ℝ)-1/2-s ≤ 2) :
    physicalExponent (51/100) d 1 q s-(boundary-11/16) ≤
      -4279/750000+2*ζ := by
  have he := physical_extend (51/100) d 1 q s ζ hζ hd hslo hshi
  unfold physicalExponent lx ly h ell boundary at *
  linarith

/-- The distinct intermediate row range, using its own source exponent. -/
theorem intermediate_physical_margin (δ d q : ℝ)
    (_hδ : 0 ≤ δ) (hδ' : δ ≤ 5/6) (hq : q ≤ δ/2) (hd : d ≤ 1/2) :
    physicalExponent ((1+δ)/2) d (76/75-(2/3)*δ) q (17/50)-(boundary-11/16) ≤
      -59657/18000000 := by
  have hs : 0 ≤ (76/75-(2/3)*δ)+(1+δ)/2-1/2-(17/50:ℝ) := by linarith
  have he := mul_le_mul_of_nonneg_right hd hs
  unfold physicalExponent lx ly ell boundary
  nlinarith

#print axioms balanced_physical_margin
#print axioms balanced_physical_saving
#print axioms high_physical_margin
#print axioms floor_physical_margin
#print axioms intermediate_physical_margin
end
end RHZeroFreeExtension.PerturbedCentralExponent

end LocalModule6
/- END RHZeroFreeExtension.analytic_high.PerturbedCentralExponent -/

/- BEGIN original module geometry.CountOptimization -/
section LocalModule7
set_option maxHeartbeats 0
namespace RHCount
noncomputable section

def A (x : ℝ) : ℝ := 2-8*x/9
def D (x : ℝ) : ℝ := 3-17*x/9
def P (x : ℝ) : ℝ := A x*(1-x)
def J (δ x : ℝ) : ℝ := (5/6-δ)*D x+δ*P x
def t (δ x : ℝ) : ℝ := 1+δ*P x/(2*J δ x)
def long (δ t : ℝ) : ℝ := 1-δ+(5/6-δ)*(t-1)
def short (δ x t : ℝ) : ℝ := 1-δ+δ*P x/D x*(3/2-t)
def rstar (x t : ℝ) : ℝ := (A x*t-5*x/9)/D x
def inverse (δ x r : ℝ) : ℝ := 1-δ*(x+(1-x)*r)
def plain (δ x t r : ℝ) : ℝ := 1-δ*(4*x/9+A x*(t-r))
def inverseCapacity (r : ℝ) : ℝ := (1-r)/2
def plainCapacity (m : ℝ) : ℝ := 2*(1-2*m)/9

lemma A_lower (x : ℝ) (hx : x ≤ 1/2) : 14/9 ≤ A x := by
  unfold A
  linarith
lemma D_lower (x : ℝ) (hx : x ≤ 1/2) : 37/18 ≤ D x := by
  unfold D
  linarith
lemma P_lower (x : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 7/9 ≤ P x := by
  unfold P A
  nlinarith [mul_nonneg _hx0 _hx0]
lemma difference_identity (x : ℝ) : D x-P x = 1+x-8*x^2/9 := by
  unfold D P A
  ring
lemma D_ge_P (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : P x ≤ D x := by
  rw [← sub_nonneg]
  rw [difference_identity]
  nlinarith [mul_nonneg hx0 (sub_nonneg.mpr hx1)]
lemma J_lower (δ x : ℝ) (_hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 35/54 ≤ J δ x := by
  have hp := P_lower x hx0 hx1
  have hd := D_ge_P x hx0 hx1
  have hm := mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr hd)
  unfold J at *
  nlinarith

theorem t_range (δ x : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : 1 ≤ t δ x ∧ t δ x ≤ 3/2 := by
  have hp := P_lower x hx0 hx1
  have hd := D_lower x hx1
  have hjl := J_lower δ x hδ0 hδ1 hx0 hx1
  have hj : 0 < J δ x := by linarith
  have hn : 0 ≤ δ*P x := mul_nonneg hδ0 (by linarith)
  have hden : δ*P x ≤ J δ x := by
    have hm := mul_nonneg (sub_nonneg.mpr hδ1) (by linarith : 0 ≤ D x)
    unfold J
    linarith
  have hratio0 : 0 ≤ δ*P x/(2*J δ x) := div_nonneg hn (by positivity)
  have hratio1 : δ*P x/(2*J δ x) ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2*J δ x)).2
    linarith
  unfold t
  constructor <;> linarith

theorem balanced_counts (δ x : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) : short δ x (t δ x) = long δ (t δ x) := by
  have hd : D x ≠ 0 := ne_of_gt (by linarith [D_lower x hx1])
  have hj : J δ x ≠ 0 := ne_of_gt (by linarith [J_lower δ x hδ0 hδ1 hx0 hx1])
  unfold short long t
  field_simp [hd, hj]
  unfold J
  ring

theorem weighted_identity (δ x t r : ℝ) (hD : D x ≠ 0) :
    (A x*inverse δ x r+(1-x)*plain δ x t r)/D x = short δ x t := by
  unfold inverse plain short
  field_simp [hD]
  unfold D P A
  ring

theorem crossing_identity (δ x t : ℝ) (hD : D x ≠ 0) :
    inverse δ x (rstar x t) = plain δ x t (rstar x t) := by
  unfold inverse plain rstar
  field_simp [hD]
  unfold D A
  ring

theorem rstar_range (x t : ℝ) (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (ht0 : 1 ≤ t) (ht1 : t ≤ 3/2) : 23/37 ≤ rstar x t ∧ rstar x t ≤ 1 := by
  have ha := A_lower x hx1
  have hd : 0 < D x := by linarith [D_lower x hx1]
  have hm0 := mul_nonneg (by linarith : 0 ≤ A x) (sub_nonneg.mpr ht0)
  have hm1 := mul_nonneg (by linarith : 0 ≤ A x) (sub_nonneg.mpr ht1)
  unfold rstar
  constructor
  · apply (le_div_iff₀ hd).2
    unfold A D at *
    nlinarith
  · apply (div_le_iff₀ hd).2
    unfold A D at *
    nlinarith

theorem complementary_range (x t : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2)
    (ht0 : 1 ≤ t) (ht1 : t ≤ 3/2) :
    1/3 ≤ t-rstar x t ∧ t-rstar x t ≤ 1/2 := by
  have hd : 0 < D x := by linarith [D_lower x hx1]
  have hden : D x ≠ 0 := ne_of_gt hd
  have hid : t-rstar x t = ((1-x)*t+5*x/9)/D x := by
    unfold rstar
    field_simp [hden]
    unfold D A
    ring
  have hm0 := mul_nonneg (by linarith : 0 ≤ 1-x) (sub_nonneg.mpr ht0)
  have hm1 := mul_nonneg (by linarith : 0 ≤ 1-x) (sub_nonneg.mpr ht1)
  rw [hid]
  constructor
  · apply (le_div_iff₀ hd).2
    unfold D at *
    nlinarith
  · apply (div_le_iff₀ hd).2
    unfold D at *
    nlinarith

theorem inverse_capacity_bound (r : ℝ) (hr0 : 23/37 ≤ r) (hr1 : r ≤ 1) :
    0 ≤ inverseCapacity r ∧ inverseCapacity r ≤ 7/37 := by
  unfold inverseCapacity
  constructor <;> linarith

theorem plain_capacity_bound (m : ℝ) (hm0 : 1/3 ≤ m) (hm1 : m ≤ 1/2) :
    0 ≤ plainCapacity m ∧ plainCapacity m ≤ 2/27 := by
  unfold plainCapacity
  constructor <;> linarith

theorem strict_inverse_margins (r ν z : ℝ) (hr : 23/37 ≤ r) (hν : 0 < ν)
    (hz : z ≤ inverseCapacity r-ν) :
    2*ν ≤ 1-r-2*z ∧ 9/37 ≤ 3-2*r-8*z := by
  unfold inverseCapacity at hz
  constructor <;> linarith


theorem crossing_value (δ x t : ℝ) (hD : D x ≠ 0) :
    inverse δ x (rstar x t) = short δ x t := by
  unfold inverse rstar short
  field_simp [hD]
  unfold D P A
  ring

/-- An affine optimization statement only; no analytic row count is assumed. -/
theorem affine_choice_bound (δ x t r : ℝ) (hδ : 0 ≤ δ)
    (_hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    min (inverse δ x r) (plain δ x t r) ≤ short δ x t := by
  have hd : D x ≠ 0 := ne_of_gt (by linarith [D_lower x hx1])
  have hv := crossing_value δ x t hd
  have hc := crossing_identity δ x t hd
  rcases le_total r (rstar x t) with hr | hr
  · have hm := mul_nonneg hδ (mul_nonneg (by linarith [A_lower x hx1] : 0 ≤ A x)
        (sub_nonneg.mpr hr))
    have hs : plain δ x t r ≤ plain δ x t (rstar x t) := by
      unfold plain
      nlinarith
    calc
      min (inverse δ x r) (plain δ x t r) ≤ plain δ x t r := min_le_right _ _
      _ ≤ plain δ x t (rstar x t) := hs
      _ = short δ x t := by rw [← hc, hv]
  · have hm := mul_nonneg hδ (mul_nonneg (by linarith : 0 ≤ 1-x)
        (sub_nonneg.mpr hr))
    have hs : inverse δ x r ≤ inverse δ x (rstar x t) := by
      unfold inverse
      nlinarith
    calc
      min (inverse δ x r) (plain δ x t r) ≤ inverse δ x r := min_le_left _ _
      _ ≤ inverse δ x (rstar x t) := hs
      _ = short δ x t := hv

/-- The chosen t balances a decreasing and an increasing affine bound. -/
theorem balance_is_minimax (δ x t' : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 5/6)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1/2) :
    long δ (t δ x) ≤ max (short δ x t') (long δ t') := by
  have hb := balanced_counts δ x hδ0 hδ1 hx0 hx1
  have hp := P_lower x hx0 hx1
  have hd : 0 < D x := by linarith [D_lower x hx1]
  have hs : 0 ≤ δ*P x/D x := div_nonneg
    (mul_nonneg hδ0 (by linarith)) (le_of_lt hd)
  rcases le_total t' (t δ x) with ht | ht
  · have hm := mul_nonneg hs (sub_nonneg.mpr ht)
    have hh : short δ x (t δ x) ≤ short δ x t' := by
      unfold short
      nlinarith
    calc
      long δ (t δ x) = short δ x (t δ x) := hb.symm
      _ ≤ short δ x t' := hh
      _ ≤ max (short δ x t') (long δ t') := le_max_left _ _
  · have hm := mul_nonneg (sub_nonneg.mpr hδ1) (sub_nonneg.mpr ht)
    have hh : long δ (t δ x) ≤ long δ t' := by
      unfold long
      nlinarith
    exact hh.trans (le_max_right _ _)

#print axioms balanced_counts
#print axioms weighted_identity
#print axioms rstar_range
#print axioms complementary_range
#print axioms strict_inverse_margins
#print axioms affine_choice_bound
#print axioms balance_is_minimax
end
end RHCount

end LocalModule7
/- END geometry.CountOptimization -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedNonfloorExponent -/
section LocalModule8

/-! Fixed-Delta actual source adaptive count exponents and the new physical
mixed exponent. No row energy or improved count conclusion is a premise. -/
namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI.SevenEighths
open PerturbedCentralExponent

lemma source_balanced_count_eq (δ x : ℝ) :
    Endpoint.balancedRowCount δ (1/2-x) = RHGeometry.R δ x := by
  have hD : Endpoint.denominator (1/2-x)=RHGeometry.D x := by
    rw [← HeckeDetectorRowCount.denominator_endpoint]
    rfl
  have hP : Endpoint.primeWeight (1/2-x)=RHGeometry.P x := by
    rw [← HeckeDetectorRowCount.primeWeight_endpoint]
    rfl
  have hJ : Endpoint.balanceDenominator δ (1/2-x)=RHGeometry.J δ x := by
    unfold Endpoint.balanceDenominator RHGeometry.J
    rw [hD,hP]
  unfold Endpoint.balancedRowCount Endpoint.balancedCutoff RHGeometry.R
  rw [hP,hJ]
  ring

lemma adaptive_zero_loss (δ q ε εm slotMesh ν : ℝ) :
    ProbeHighRowFamily.adaptiveRowExponent δ q 0 ε εm slotMesh ν =
      if δ≤5/6 then RHGeometry.R δ (q/δ)+159*ε+εm+slotMesh+7*ν
      else 1-δ+78*ε+εm := by
  unfold ProbeHighRowFamily.adaptiveRowExponent
  rw [source_balanced_count_eq]
  simp only [zero_div,add_zero]

lemma count_range (δ x loss : ℝ) (hδ : 0≤δ) (hδ' : δ≤5/6)
    (hx : 0≤ x) (hx' : x≤1/2) (hl : 0≤ loss) (hl' : loss≤1/32) :
    1-δ≤ RHGeometry.R δ x+loss ∧ RHGeometry.R δ x+loss≤139/96 := by
  have ht := RHCount.t_range δ x hδ hδ' hx hx'
  have he : RHGeometry.R δ x=1-δ+(5/6-δ)*(RHCount.t δ x-1) := by
    unfold RHGeometry.R RHCount.t
    change 1-δ+(5/6-δ)*δ*RHCount.P x/(2*RHCount.J δ x) =
      1-δ+(5/6-δ)*(1+δ*RHCount.P x/(2*RHCount.J δ x)-1)
    ring
  have hp := mul_nonneg (show 0≤5/6-δ by linarith) (show 0≤ RHCount.t δ x-1 by linarith)
  have hu := mul_le_mul_of_nonneg_left ht.2 (show 0≤5/6-δ by linarith)
  rw [he]
  constructor <;> nlinarith

def mixedPhysicalExponent (a v d R q s : ℝ) : ℝ :=
  physicalExponent a v R q s+(d-v)*R

lemma mixed_physical_slack (a v d R q s μ Rmax : ℝ)
    (hR : 0≤ R) (hRmax : R≤ Rmax) (hμ : 0≤μ) (hd : d-v≤μ) :
    mixedPhysicalExponent a v d R q s≤ physicalExponent a v R q s+μ*Rmax := by
  have h1 := mul_le_mul_of_nonneg_right hd hR
  have h2 := mul_le_mul_of_nonneg_left hRmax hμ
  unfold mixedPhysicalExponent
  linarith

lemma balanced_mixed_physical_saving (δ x loss ζ μ v d overhead saving : ℝ)
    (hδ : 0≤δ) (hδ' : δ≤5/6) (hx : 0≤ x) (hx' : x≤1/2)
    (hl : 0≤ loss) (hl' : loss≤1/32) (hζ : 0≤ζ) (hv : v≤ h+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : h*loss+2*ζ+(3/2)*μ+overhead+saving≤19/320000) :
    mixedPhysicalExponent ((1+δ)/2) v d (RHGeometry.R δ x+loss) (δ*x) (17/50)+overhead ≤
      boundary-11/16-saving := by
  have hr := count_range δ x loss hδ hδ' hx hx' hl hl'
  have hslo : 0≤ RHGeometry.R δ x+loss+δ/2-(17/50:ℝ) := by linarith [hr.1]
  have hshi : RHGeometry.R δ x+loss+δ/2-(17/50:ℝ)≤2 := by linarith [hr.2]
  have hm := balanced_physical_margin δ x (RHGeometry.R δ x+loss) v (17/50) loss ζ
    hδ hδ' hx hx' le_rfl hζ hv hslo hshi
  have hs := mixed_physical_slack ((1+δ)/2) v d (RHGeometry.R δ x+loss) (δ*x) (17/50) μ (3/2)
    (by linarith [hr.1]) (by linarith [hr.2]) hμ hdv
  linarith

lemma high_mixed_physical_saving (δ q loss ζ μ v d overhead saving : ℝ)
    (hδ : 5/6≤δ) (hδ' : δ≤1) (hq : q≤δ/2)
    (hl : 0≤ loss) (hl' : loss≤1/32) (hζ : 0≤ζ) (hv : v≤ h+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ)
    (hbudget : h*loss+2*ζ+μ+overhead+saving≤1/20) :
    mixedPhysicalExponent ((1+δ)/2) v d (1-δ+loss) q (17/50)+overhead≤
      boundary-11/16-saving := by
  have hslo : 0≤(1-δ+loss)+δ/2-(17/50:ℝ) := by linarith
  have hshi : (1-δ+loss)+δ/2-(17/50:ℝ)≤2 := by linarith
  have hm := high_physical_margin δ (1-δ+loss) v q (17/50) loss ζ
    hδ hq le_rfl hζ hv hslo hshi
  have hs := mixed_physical_slack ((1+δ)/2) v d (1-δ+loss) q (17/50) μ 1
    (by linarith) (by linarith) hμ hdv
  linarith

def perturbedRealLoss (N : ℕ) (v e eps loss mesh : ℝ) : ℝ :=
  (131253/10000)*e+12*v*e+v*eps*(N+8)+loss+ell*mesh

lemma perturbed_realLoss_bound (N : ℕ) (v e eps loss mesh : ℝ)
    (hv : v≤1) (he : 0≤ e) (heps : 0≤ eps) :
    perturbedRealLoss N v e eps loss mesh≤26*e+(N+8)*eps+loss+ell*mesh := by
  have h1 := mul_le_mul_of_nonneg_right hv he
  have h2 := mul_le_mul_of_nonneg_right hv (show 0≤ eps*(N+8) by positivity)
  unfold perturbedRealLoss
  nlinarith

lemma perturbed_central_class_exponent_identity (N : ℕ)
    (a v d R q e eps loss mesh overhead : ℝ) :
    ((31253/60000)*a-226253/375000+(131253/10000)*e)+
      (overhead+d*R+v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-
        5003/187500+ell*q+ell*mesh) =
      mixedPhysicalExponent a v d R q (17/50)+perturbedRealLoss N v e eps loss mesh+overhead := by
  unfold mixedPhysicalExponent physicalExponent perturbedRealLoss lx ly ell
  ring

/-- Actual adaptive source exponent at Delta=0; the actual Moments
premises still have to be established for the physical batch. -/
theorem perturbed_adaptive_mixed_saving (N : ℕ)
    (a q ε εm slotMesh ν ζ μ v d e eps loss mesh overhead saving : ℝ)
    (ha : 1/2< a) (ha' : a≤1) (hq : 0≤ q) (hq' : q≤(2*a-1)/2)
    (hε : 0≤ε) (hεm : 0≤εm) (hslot : 0≤ slotMesh) (hν : 0≤ν)
    (hcount : 159*ε+εm+slotMesh+7*ν≤1/32)
    (hζ : 0≤ζ) (hζ' : ζ≤1/48) (hv : v≤ h+ζ)
    (hμ : 0≤μ) (hdv : d-v≤μ) (he : 0≤ e) (heps : 0≤ eps)
    (hbudget : h*(159*ε+εm+slotMesh+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+ell*mesh)+overhead+saving≤19/320000) :
    mixedPhysicalExponent a v d
      (ProbeHighRowFamily.adaptiveRowExponent (2*a-1) q 0 ε εm slotMesh ν) q (17/50)+
      perturbedRealLoss N v e eps loss mesh+overhead≤ boundary-11/16-saving := by
  have hδ : 0<2*a-1 := by linarith
  have hx : 0≤ q/(2*a-1) := div_nonneg hq hδ.le
  have hx' : q/(2*a-1)≤1/2 := (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0≤159*ε+εm+slotMesh+7*ν := by positivity
  have haeq : (1+(2*a-1))/2=a := by ring
  have hqeq : (2*a-1)*(q/(2*a-1))=q := mul_div_cancel₀ q hδ.ne'
  have hr := perturbed_realLoss_bound N v e eps loss mesh
    (by unfold h at hv; linarith) he heps
  by_cases hd : 2*a-1≤5/6
  · have hb := balanced_mixed_physical_saving (2*a-1) (q/(2*a-1))
      (159*ε+εm+slotMesh+7*ν) ζ μ v d
      (perturbedRealLoss N v e eps loss mesh+overhead) saving
      hδ.le hd hx hx' hl hcount hζ hv hμ hdv (by linarith)
    rw [haeq,hqeq] at hb
    rw [adaptive_zero_loss]
    simp only [ite_eq_left hd]
    simpa only [add_assoc] using hb
  · have hhl : 0≤78*ε+εm := by positivity
    have hhl' : 78*ε+εm≤1/32 := by linarith
    have hdiff := mul_nonneg (by norm_num [h] : 0≤ h)
      (show 0≤(159*ε+εm+slotMesh+7*ν)-(78*ε+εm) by linarith)
    have hh := high_mixed_physical_saving (2*a-1) q (78*ε+εm) ζ μ v d
      (perturbedRealLoss N v e eps loss mesh+overhead) saving
      (le_of_lt (lt_of_not_ge hd)) (by linarith) hq' hhl hhl' hζ hv hμ hdv (by nlinarith)
    rw [haeq] at hh
    rw [adaptive_zero_loss]
    simpa only [ite_eq_right hd,add_assoc] using hh

#print axioms balanced_mixed_physical_saving
#print axioms high_mixed_physical_saving
#print axioms perturbed_adaptive_mixed_saving
end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule8
/- END RHZeroFreeExtension.analytic_high.PerturbedNonfloorExponent -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedCubeProfileScale -/
section LocalModule9

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI OAI.SevenEighths
open PerturbedCentralExponent

lemma perturbed_physical_scale_identity (Z a e : ℝ) (hZ : 0< Z) :
    (Z^(21247/60000:ℝ))^(4/25:ℝ)*Z^(a+16*e-33/50)*(Z^(28747/60000:ℝ))^(-a-6*e)=
      Z^((31253/60000)*a-226253/375000+(131253/10000)*e) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul hZ.le,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma perturbed_class_profile_exponent_identity (a v d R q e eps loss mesh cost : ℝ) (N : ℕ) :
    ((31253/60000)*a-226253/375000+(131253/10000)*e)+cost+d*R+
      v*(a-1/2+12*e+eps*(N+8)-17/50)+loss-5003/187500+
      (5003/30000)*q+(5003/30000)*mesh =
    mixedPhysicalExponent a v d R q (17/50)+(131253/10000)*e+
      v*(12*e+eps*(N+8))+loss+(5003/30000)*mesh+cost := by
  unfold mixedPhysicalExponent physicalExponent lx ly ell
  ring

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule9
/- END RHZeroFreeExtension.analytic_high.PerturbedCubeProfileScale -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorArithmetic -/
section LocalModule10
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily PerturbedCentralExponent
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem perturbed_fixed_actual_nonfloor_cube_arithmetic (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=5003/30000)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (16253/20000)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(5003/30000)*mesh)+(logCost+heightCost+momentCost)+saving≤19/320000) (counts : ProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤16253/20000+ζ → d-v≤μ →
      51/100< a → a≤1 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      ∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm →
      ‖cubeArithmeticSum S hS hmax η rows T (fixed_nonfloorPoolOutside M H S N c b Y) W Y a e t‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
          Z^(7499/40000-saving-((31253/60000)*a-226253/375000+(131253/10000)*e)) := by
  obtain ⟨C,hC,hclass⟩ :=
    perturbed_fixed_actual_nonfloor_class_from_raw_moments M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hν hlog hMomentHeight counts
  let cardCost : ℝ := (HeckeDetectorClassBudget.alphabetBound mesh:ℝ)^N
  have hcardCost : 0≤ cardCost := by dsimp [cardCost];positivity
  refine ⟨(cardCost+1)*C,by positivity,?_⟩
  intro η
  filter_upwards [hclass η,eventually_gt_atTop (1:ℝ)] with Z hclass hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro t ht hmom
  let z : ℂ := (17/50:ℂ)+t.1.2*Complex.I
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let Q := physical M H (fun u : FreeRow=> u.val) W (fun _=> b) (fun j=> ell j/d) (fun _=> z) (Z^d)
  let bound : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(7499/40000-saving-((31253/60000)*a-226253/375000+(131253/10000)*e))
  have hb : 0≤ bound := by dsimp [bound];positivity
  have hpart := cubeArithmeticSum_class_uniform S hS hmax η rows T
    (fixed_nonfloorPoolOutside M H S N c b Y) W Y a e t Finset.univ (Z^d) ((2*a-1)/2) mesh hmesh
    (by linarith) (fun j=> ell j/d) Q bound hb (by
      intro bin hne
      have hp := hclass d hd hd' v a C0 hv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent t ht hmom bin hne
      dsimp only at hp
      rw [hΔzero] at hp
      let q := classMean Finset.univ ((2*a-1)/2) mesh (fun j=> ell j/d) bin
      have hs := perturbed_adaptive_mixed_saving N a q ε εm R ν ζ μ v d e eps loss mesh
        (logCost+heightCost+momentCost) saving (by linarith) ha' hp.1 hp.2.1 hε.le hεm.le
        hR hν.le hcount hζ hζ1 hv' hμ hdv he.le heps.le hfinal
      have hid := perturbed_central_class_exponent_identity N a v d
        (adaptiveRowExponent (2*a-1) q Δ ε εm R ν) q e eps loss mesh (logCost+heightCost+momentCost)
      rw [hΔzero] at hid
      unfold boundary at hs
      unfold RHZeroFreeExtension.PerturbedCentralExponent.ell at hid
      apply hp.2.2.trans
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.rpow_le_rpow_of_exponent_le hZ.le
      linarith)
  simp only [Finset.card_univ,Fintype.card_fin] at hpart
  calc
    _ ≤ cardCost*bound := hpart
    _ ≤ (cardCost+1)*bound := mul_le_mul_of_nonneg_right (by linarith) hb
    _ = _ := by dsimp [bound];ring


end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule10
/- END RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorArithmetic -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorIntegral -/
section LocalModule11
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem perturbed_fixed_actual_nonfloor_cube_norm (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℂ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,‖W j t‖≤ A)
    (hellsum : ∑j,ell j=5003/30000)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (16253/20000)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(5003/30000)*mesh)+(logCost+heightCost+momentCost)+saving≤19/320000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) (counts : ProbeFinalAssembly.CountParameters M H εm) :
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤16253/20000+ζ → d-v≤μ →
      51/100< a → a≤1 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell W Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      ‖finiteCentralCubeRows S hS hmax η rows T (fixed_nonfloorPoolOutside M H S N c b Y) W Y
        W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z e (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(7499/40000-saving) := by
  obtain ⟨C,hC,harith⟩ :=
    perturbed_fixed_actual_nonfloor_cube_arithmetic M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hΔzero hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal counts
  obtain ⟨D,hD,hprofile⟩ := actual_common_cube_aggregate_norm W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨D*C,mul_pos hD hC,?_⟩
  intro η
  filter_upwards [harith η,(tendsto_rpow_atTop hτ).eventually (eventually_gt_atTop (2:ℝ)),
    eventually_gt_atTop (1:ℝ)] with Z harith hT hZ
  intro d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
  dsimp only
  intro hmom
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let A : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
    Z^(7499/40000-saving-((31253/60000)*a-226253/375000+(131253/10000)*e))
  have hA : 0≤ A := by dsimp [A];positivity
  have hp := hprofile e a (Z^τ) ((3*i+1:ℕ)*Z^τ) i he he1 ha.le ha' hT
    (by gcongr;omega) S hS hmax hfirst η rows (fun u hu=>(hrows u hu).1)
    T (fixed_nonfloorPoolOutside M H S N c b Y) (rayCubeFamily M H hH) hnext W Y
    (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z (by positivity) (by positivity) hZp A hA
    (fun t ht=> harith d hd hd' v a C0 hv hv' hdv ha ha' hC0 rows hrows hnorm i hi hnext hcurrent
      t ht (hmom t ht))
  apply hp.trans_eq
  rw [perturbed_physical_scale_identity Z a e hZp]
  dsimp only [A]
  calc
    _ = (D*C)*C0*(η.modulus.absNorm:ℝ)^(2*eps)*
        (Z^((31253/60000)*a-226253/375000+(131253/10000)*e)*Z^(7499/40000-saving-((31253/60000)*a-226253/375000+(131253/10000)*e))) := by ring
    _ = _ := by rw [←Real.rpow_add hZp];congr 2;ring


end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule11
/- END RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorIntegral -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedCubeNormalizer -/
section LocalModule12
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

theorem perturbed_actual_ray_normalizer_inverse {K : ℕ}
    (M : Ideal O) [NeZero M] [Finite (O ⧸ M)]
    (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (c b : ℝ) (hc : 0< c) (hcb : c≤ b)
    (ell : Fin K→ℝ) (hell : ∀j,0< ell j) (hellsum : ∑j,ell j=5003/30000)
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
        (Probe.principalScalar Finset.univ Z (5003/30000)
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
    (residueWeights W (fun j=> Z^(ell j))) Z (5003/30000) hZ (fun j _=> hmass.1 j),?_⟩
  have hb : ‖(sourceResidueConstant W0 W1 (∏P∈S,P)*
      (Probe.principalScalar Finset.univ Z (5003/30000)
        (slotMass (fun j=> pool (RayQuotient.identityClass M H) S c b (Z^(ell j)))
          (residueWeights W (fun j=> Z^(ell j)))) : ℂ))⁻¹‖≤‖cs⁻¹‖*Z^nu := by
    rw [mul_inv_rev,norm_mul,←Complex.ofReal_inv,Complex.norm_real]
    simpa only [hellsum,Real.norm_eq_abs,mul_comm] using
      mul_le_mul_of_nonneg_left hmass.2 (norm_nonneg cs⁻¹)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hZ.le _))

end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule12
/- END RHZeroFreeExtension.analytic_high.PerturbedCubeNormalizer -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorNormalized -/
section LocalModule13
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem perturbed_fixed_actual_normalized_nonfloor_cube (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=5003/30000)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (16253/20000)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(5003/30000)*mesh)+(logCost+heightCost+momentCost)+saving≤19/320000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu) (counts : ProbeFinalAssembly.CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,
      ∀d : ℝ,dmin≤ d → d≤ dmax → ∀(v a C0 : ℝ),0≤ v → v≤16253/20000+ζ → d-v≤μ →
      51/100< a → a≤1 → 0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(d-margin)) →
      (∀u∈rows,Z^v≤ rowNorm u ∧ rowNorm u≤2*Z^v) →
      ∀i : ℕ,i≤ n →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(i+1:ℕ)*Z^τ)< a+2*e) →
      (∀u∈rows,a≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*i:ℕ)*Z^τ)) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      (∀t : HeightSpace,((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
      SourceMomentsAt M H hH S hS.prime η rows ell (fun j y=>(W j y:ℂ)) Z d a ε τ dmax b R mesh i
        ((17/50:ℂ)+t.1.2*Complex.I) Δ
        (if 2*a-1≤5/6 then counts.cB else counts.cH) (if 2*a-1≤5/6 then counts.kB else counts.kH)
        (C0*Z^momentCost) (Z^heightCost) εm) →
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (5003/30000)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (fixed_nonfloorPoolOutside M H S N c b Y) (fun j y=>(W j y:ℂ)) Y
        W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z e (fun _=> a) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(7499/40000-saving+nu) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  have hWC (j : Fin N) : ContDiff ℝ ∞ (WC j) := Complex.ofRealCLM.contDiff.comp (hW j)
  have hWCs (j : Fin N) : Function.support (WC j)⊆Ioo c b := by
    intro y hy
    apply hWs j
    intro hh
    exact hy (by dsimp [WC];rw [hh];simp)
  have hWCB (j : Fin N) (y : ℝ) : ‖WC j y‖≤ A := by
    simpa only [WC,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hWB j y).1] using (hWB j y).2
  obtain ⟨C,hC,hbound⟩ :=
    perturbed_fixed_actual_nonfloor_cube_norm M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi WC hWCs hWC hWCB hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hΔzero hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 counts
  have hellpos (j : Fin N) : 0< ell j :=
    (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := perturbed_actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
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
  rw [Real.rpow_add hZ (7499/40000-saving) nu]
  ring


end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule13
/- END RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorNormalized -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorCollected -/
section LocalModule14
set_option linter.unusedVariables false

namespace RHZeroFreeExtension.AnalyticHigh

noncomputable section
open scoped Classical BigOperators Topology ContDiff
open Filter Set
open OAI OAI.SevenEighths
open ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
open ProbeRaySlots HeckeDetectorPhysicalSelection HeckeDetectorAmplitudeFirst HeckeDetectorFiberPartition
local notation "O" => HeckeFamily.O
variable (M : Ideal O) [NeZero M]
local instance : Finite (O ⧸ M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H : Subgroup (O ⧸ M)ˣ) (hH : RayOrthogonality.globalUnits M≤ H)

theorem perturbed_fixed_actual_nonfloor_rows_saving (N n : ℕ) (e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss : ℝ)
    (he : 0< e) (he1 : e<1/1000) (heps : 0< eps) (hc : 0< c) (hcb : c≤ b) (hA : 0≤ A)
    (hR : 0≤ R) (hdmin : 0< dmin) (hdmax : 0≤ dmax) (hdRange : dmin≤ dmax) (hrmin : 0< rmin)
    (hτ : 0<τ) (hε : 0<ε) (hκ : 0<κ) (hcost : 0≤ cost) (hmesh : 0< mesh)
    (hbudget : 8*e*R+κ≤ε) (hgap : ε< rmin*mesh) (hmargin : 0< margin)
    (hheight : 2*τ< dmin*cost) (hloss : τ*(2+4*eps)< loss)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal)
    (ell : Fin N→ℝ) (hell : Function.Injective ell)
    (hello : ∀j,dmax*rmin≤ ell j) (hellhi : ∀j,ell j≤ dmin*R)
    (W : Fin N→ℝ→ℝ)
    (hWs : ∀j,Function.support (W j)⊆Ioo c b) (hW : ∀j,ContDiff ℝ ∞ (W j)) (hWB : ∀j t,0≤ W j t ∧ W j t≤ A)
    (hcompact : ∀j,HasCompactSupport (W j)) (hne : ∀j,W j≠0)
    (hellsum : ∑j,ell j=5003/30000)
    (hdtop : dmax≤37/42) (hε1 : ε≤1/1000) (hκ1 : κ≤1)
    (hτzero : τ< dmin/2) (hτheight : 4*τ< dmin*cost)
    (hwbudget : 12*e*((22:ℝ)+2)+8*κ+2*cost≤ε/2)
    (φ : ℝ→ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ)
    (hφp : tsupport φ⊆Ioi 0) (hφ0 : ∀y,0≤φ y) (hφne : φ≠0)
    (a₀ b₀ B₀ : ℝ) (ha₀ : 0< a₀) (hab₀ : a₀≤ b₀) (hB₀ : 0< B₀)
    (hφs : Function.support φ⊆Ioo a₀ b₀) (hφB : ∀y,φ y≤ B₀)
    (εm Δ ν logCost heightCost momentCost : ℝ)
    (hεm : 0<εm) (hΔ : 0≤Δ) (hΔ1 : Δ≤1/8) (hΔzero : Δ=0) (hν : 0<ν)
    (hlog : 0< logCost) (hMomentHeight : τ< heightCost)
    (ζ μ saving : ℝ) (hζ : 0≤ζ) (hζ1 : ζ≤1/48) (hμ : 0≤μ)
    (hcount : 159*ε+εm+R+7*ν≤1/32)
    (hfinal : (16253/20000)*(159*ε+εm+R+7*ν)+2*ζ+(3/2)*μ+
      (26*e+(N+8)*eps+loss+(5003/30000)*mesh)+(logCost+heightCost+momentCost)+saving≤19/320000)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (hr0 : ∀y,(W0 y).im=0) (hr1 : ∀y,(W1 y).im=0)
    (hp0 : ∀y,0≤(W0 y).re) (hp1 : ∀y,0≤(W1 y).re) (hn0 : W0≠0) (hn1 : W1≠0)
    (nu : ℝ) (hnu : 0< nu)
    (m : ℕ) (dyadCost : ℝ) (hdyadCost : 0< dyadCost)
    (hdmin1 : dmin<1/100) (hconductor : 16253/20000+ζ+2*margin≤ dmax)
    (hmuMargin : 2*margin≤μ) (counts : ProbeFinalAssembly.CountParameters M H εm) :
    letI : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0< C ∧
    ∀η : Character,∀ᶠZ : ℝ in atTop,∀C0 : ℝ,0≤ C0 → ∀rows : Finset FreeRow,
      (∀u∈rows,u.val≠1 ∧ Z^(1/100:ℝ)≤ rowNorm u ∧
        (calibrationForSet S hmax).residueMonoid u.val≠0 ∧ rowNorm u≤ Z^(16253/20000+ζ)) →
      ∀idx grid : FreeRow→ℕ,
      (∀u∈rows,idx u≤ n ∧ grid u≤ m ∧ grid u≠0 ∧ 51/100+e*grid u≤1) →
      (∀u∈rows,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        (3*(idx u+1:ℕ)*Z^τ)<51/100+e*grid u+2*e) →
      (∀u∈rows,51/100+e*grid u≤ detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
        ((3*idx u:ℕ)*Z^τ)) →
      (∀k∈smallDyadicIndices (Z^(16253/20000+ζ)),∀i∈Finset.range (n+1),∀j∈Finset.range (m+1),
        let rows' := cubeBinRows (rows∩dyadicRows 1 k) idx grid i j
        rows'.Nonempty → ∀t : HeightSpace,
        ((|t.1.1|≤(3*i+1:ℕ)*Z^τ ∧ |t.2|≤(3*i+1:ℕ)*Z^τ) ∧ |t.1.2|≤(3*i+1:ℕ)*Z^τ) →
        SourceMomentsAt M H hH S hS.prime η rows' ell (fun j y=>(W j y:ℂ)) Z
          (sourceDyadConductor Z margin k) (51/100+e*j) ε τ dmax b R mesh i
          ((17/50:ℂ)+t.1.2*Complex.I) Δ
          (if 2*(51/100+e*j)-1≤5/6 then counts.cB else counts.cH)
          (if 2*(51/100+e*j)-1≤5/6 then counts.kB else counts.kH)
          (C0*Z^momentCost) (Z^heightCost) εm) →
      let Y : Fin N→ℝ := fun j=> Z^(ell j)
      let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
      let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
        (Probe.principalScalar Finset.univ Z (5003/30000)
          (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
      normer≠0 ∧ ‖finiteCentralCubeRows S hS hmax η rows T (fixed_nonfloorPoolOutside M H S N c b Y)
        (fun j y=>(W j y:ℂ)) Y W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z e
        (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤
        C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(7499/40000-saving+nu+dyadCost) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ :=
    perturbed_fixed_actual_normalized_nonfloor_cube M H hH N n e eps c b A R dmin dmax rmin τ ε κ cost mesh margin loss
      he he1 heps hc hcb hA hR hdmin hdmax hdRange hrmin hτ hε hκ hcost hmesh
      hbudget hgap hmargin hheight hloss S hS hfirst hmax ell hell hello hellhi W hWs hW hWB hcompact hne hellsum
      hdtop hε1 hκ1 hτzero hτheight hwbudget
      φ hφ hφc hφp hφ0 hφne a₀ b₀ B₀ ha₀ hab₀ hB₀ hφs hφB
      εm Δ ν logCost heightCost momentCost hεm hΔ hΔ1 hΔzero hν hlog hMomentHeight
      ζ μ saving hζ hζ1 hμ hcount hfinal W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      hr0 hr1 hp0 hp1 hn0 hn1 nu hnu counts
  have hellpos (j : Fin N) : 0< ell j := (mul_pos (hdmin.trans_le hdRange) hrmin).trans_le (hello j)
  obtain ⟨Cn,hCn,hnormer⟩ := perturbed_actual_ray_normalizer_inverse M H hH S hS c b hc hcb ell hellpos hellsum
    W hW hcompact hWs (fun j y=>(hWB j y).1) hne W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    hr0 hr1 hp0 hp1 hn0 hn1 nu hnu
  obtain ⟨Cd,hCd,hdyad⟩ := canonical_dyad_cost dyadCost hdyadCost
  refine ⟨Cd*(n+1:ℕ)*(m+1:ℕ)*C,by positivity,?_⟩
  intro η
  filter_upwards [hbound η,hnormer,
    sourceDyad_geometry_eventually dmin dmax margin (16253/20000+ζ) hdmin hdmin1 hmargin hconductor,
    eventually_gt_atTop (1:ℝ)] with Z hb hn hg hZ
  intro C0 hC0 rows hrows idx grid hlabels hnext hcurrent hmom
  dsimp only at hn ⊢
  refine ⟨hn.1,?_⟩
  have hZp : 0< Z := zero_lt_one.trans hZ
  let Y : Fin N→ℝ := fun j=> Z^(ell j)
  let T : Fin N→Finset ProbePhysical.PrimeIdeal := fun j=> pool (RayQuotient.identityClass M H) S c b (Y j)
  let hT := fixed_nonfloorPoolOutside M H S N c b Y
  let WC : Fin N→ℝ→ℂ := fun j y=>(W j y:ℂ)
  let normer := PrincipalMellinResidues.sourceResidueConstant W0 W1 (∏P∈S,P)*
    (Probe.principalScalar Finset.univ Z (5003/30000)
      (PrincipalSignalComparison.slotMass T (ProbePrincipalResidueActual.residueWeights W Y)) : ℂ)
  let D : ℝ := C*C0*(η.modulus.absNorm:ℝ)^(2*eps)*Z^(7499/40000-saving+nu)
  have hD : 0≤ D := by dsimp [D];positivity
  let F : Finset FreeRow→(FreeRow→ℝ)→(FreeRow→ℝ)→ℂ := fun R a H=>
    finiteCentralCubeRows S hS hmax η R T hT WC Y W0 W1
      (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z e a H
  have hcell (k : ℕ) (hk : k∈smallDyadicIndices (Z^(16253/20000+ζ)))
      (i : ℕ) (hi : i∈Finset.range (n+1)) (j : ℕ) (hj : j∈Finset.range (m+1)) :
      ‖F (cubeBinRows (rows∩dyadicRows 1 k) idx grid i j)
        (fun _=>51/100+e*j) (fun _=>(3*i+1:ℕ)*Z^τ)/normer‖≤ D := by
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
        have hjp : (0:ℝ)< j := by exact_mod_cast Nat.pos_of_ne_zero hju
        nlinarith
      have ha' : 51/100+e*j≤1 := by simpa only [huj] using (hlabels u (hsub hu)).2.2.2
      have hnext' : ∀u∈Rij,detectorMaximum (sourceDetectorFamily S hS.prime η u (rayCubeFamily M H hH u))
          (3*(i+1:ℕ)*Z^τ)<51/100+e*j+2*e := by
        intro u hu
        have hh := hnext u (hsub hu)
        have hm := (mem_cubeBinRows Rk idx grid i j u).mp hu
        rwa [hm.2.1,hm.2.2] at hh
      have hcurrent' : ∀u∈Rij,51/100+e*j≤ detectorMaximum
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
        (fun u hu=> hgeo.2.2.2.2.1 u (hsubk hu)) i (by simpa using Nat.le_of_lt_succ (Finset.mem_range.mp hi))
        hnext' hcurrent' (fun t ht=> hmom k hk i hi j hj ⟨u,hu⟩ t ht)
      exact hbounded.2
    · have he : Rij=∅ := Finset.not_nonempty_iff_eq_empty.mp hne'
      simpa only [F,show cubeBinRows (rows∩dyadicRows 1 k) idx grid i j=∅ from he,
        finiteCentralCubeRows,Finset.sum_empty,zero_div,norm_zero] using hD
  have hpartition : F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)=
      ∑k∈smallDyadicIndices (Z^(16253/20000+ζ)),
        F (rows∩dyadicRows 1 k) (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ) := by
    unfold F finiteCentralCubeRows
    exact retained_dyadic_sum rows _ (fun u hu=>⟨(hrows u hu).1,(hrows u hu).2.2.2⟩) _
  change ‖F rows (fun u=>51/100+e*grid u) (fun u=>(3*idx u+1:ℕ)*Z^τ)/normer‖≤_
  rw [hpartition,Finset.sum_div]
  calc
    _ ≤ ∑k∈smallDyadicIndices (Z^(16253/20000+ζ)),(n+1:ℕ)*(m+1:ℕ)*D := by
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k hk
      have hpart := finiteCentralCubeRows_bin_partition S hS hmax η (rows∩dyadicRows 1 k) T hT WC Y
        W0 W1 (Z^(21247/60000:ℝ)) (Z^(28747/60000:ℝ)) Z e (Z^τ) idx grid n m
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
          exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun j hj=> hcell k hk i hi j hj))
        _ = _ := by simp;ring
    _ = ((smallDyadicIndices (Z^(16253/20000+ζ))).card:ℝ)*((n+1:ℕ)*(m+1:ℕ)*D) := by simp
    _ ≤ (Cd*Z^dyadCost)*((n+1:ℕ)*(m+1:ℕ)*D) :=
      mul_le_mul_of_nonneg_right (hdyad Z (16253/20000+ζ) hZ.le (by linarith)) (by positivity)
    _ = _ := by dsimp [D];rw [Real.rpow_add hZp (7499/40000-saving+nu) dyadCost];ring


end

end RHZeroFreeExtension.AnalyticHigh

end LocalModule14
/- END RHZeroFreeExtension.analytic_high.PerturbedFixedNonfloorCollected -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedEulerRegion -/
section LocalModule15

set_option linter.unusedVariables false

/-! Actual local Euler formulas on the perturbed x-half-plane.
The proofs use upstream coordinate norm estimates and rational denominator
bounds; no perturbed local bound is assumed. The broad summable17/10 bound
is retained, and the narrower second rectangle has exact decay72599/40000.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler

theorem perturbed_unramifiedClosed_open_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (34999/40000:ℝ) ≤ x.re) (hw : (9/10:ℝ) ≤ w.re) (hz : (4/25:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(17/10:ℝ)) := by
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


theorem perturbed_unramifiedClosed_second_region_bound (Q : ℝ) (A eta v x w z : ℂ)
    (hQ : 4 ≤ Q) (hA : ‖A‖ ≤ 1) (heta : ‖eta‖ ≤ 1) (hv : ‖v‖ ≤ 1)
    (hx : (34999/40000:ℝ) ≤ x.re) (hw : (19/20:ℝ) ≤ w.re) (hz : (33/200:ℝ) ≤ z.re) :
    ‖unramifiedClosed Q A eta v x w z - 1‖ ≤ 240 * Q ^ (-(72599/40000:ℝ)) := by
  have hQ0 : 0 < Q := by linarith
  have hQ1 : 1 ≤ Q := by linarith
  let V := coordV Q z
  let R := coordR Q A x z
  let W := coordW Q v w
  let D := coordD Q eta v x
  let K := coordK Q eta x w
  have hV : ‖V‖ ≤ Q ^ (-(99/100:ℝ)) := by
    rw [show V = coordV Q z from rfl, coordV_norm Q hQ0]
    exact Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith)
  have hR : ‖R‖ ≤ Q ^ (-(44797/20000:ℝ)) :=
    (coordR_norm_le Q hQ0 A x z hA).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hW : ‖W‖ ≤ Q ^ (-(19/20:ℝ)) :=
    (coordW_norm_le Q hQ0 v w hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hD : ‖D‖ ≤ Q ^ (-(34999/40000:ℝ)) :=
    (coordD_norm_le Q hQ0 eta v x heta hv).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hK : ‖K‖ ≤ Q ^ (-(32999/40000:ℝ)) :=
    (coordK_norm_le Q hQ1 eta x w heta).trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by linarith))
  have hVh : ‖V‖ ≤ 1/2 := hV.trans (rpow_le_half Q _ hQ (by norm_num))
  have hRh : ‖R‖ ≤ 1/2 := hR.trans (rpow_le_half Q _ hQ (by norm_num))
  have hDh : ‖D‖ ≤ 1/2 := hD.trans (rpow_le_half Q _ hQ (by norm_num))
  have hWh : ‖W‖ ≤ 1 := by
    exact hW.trans ((Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num : -(19/20:ℝ) ≤ 0)).trans_eq (Real.rpow_zero Q))
  have hqi : ‖(Q:ℂ)⁻¹‖ ≤ 1 := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hQ0, ← one_div]
    exact (div_le_one hQ0).mpr hQ1
  let T := Q ^ (-(72599/40000:ℝ))
  have hT : 0 ≤ T := Real.rpow_nonneg hQ0.le _
  have hRT : ‖R‖ ≤ T := hR.trans (Real.rpow_le_rpow_of_exponent_le hQ1 (by norm_num))
  have hprod (a b a' b' : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
      (haa : a ≤ Q^a') (hbb : b ≤ Q^b') (he : a'+b' ≤ -(72599/40000:ℝ)) : a*b ≤ T := by
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


lemma perturbed_open_region_denominators (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 34999/40000≤ x.re) (hz : 4/25≤ z.re) :
    1-coordR Q A x z≠0 ∧ 1-coordV Q z≠0 ∧ 1-coordD Q eta v x≠0 := by
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

theorem perturbed_unramifiedClosed_analytic_x (Q : ℝ) (A eta v w z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> unramifiedClosed Q A eta v x w z) {x : ℂ|34999/40000< x.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := perturbed_open_region_denominators Q A eta v x z hQ hA he hv hx.le hz
  exact (unramifiedClosed_differentiableAt Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem perturbed_unramifiedClosed_analytic_w (Q : ℝ) (A eta v x z : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1)
    (hx : 34999/40000≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> unramifiedClosed Q A eta v x w z) {w : ℂ|9/10< w.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hd := perturbed_open_region_denominators Q A eta v x z hQ hA he hv hx hz
  exact (unramifiedClosed_differentiableAt_w Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt

theorem perturbed_unramifiedClosed_analytic_z (Q : ℝ) (A eta v x w : ℂ)
    (hQ : 4≤ Q) (hA : ‖A‖≤1) (he : ‖eta‖≤1) (hv : ‖v‖≤1) (hx : 34999/40000≤ x.re) :
    AnalyticOnNhd ℂ (fun z=> unramifiedClosed Q A eta v x w z) {z : ℂ|4/25< z.re} := by
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := perturbed_open_region_denominators Q A eta v x z hQ hA he hv hx hz.le
  exact (unramifiedClosed_differentiableAt_z Q (by linarith) A eta v x w z hd.1 hd.2.1 hd.2.2).differentiableWithinAt


end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule15
/- END RHZeroFreeExtension.analytic_high.PerturbedEulerRegion -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedGlobalCorrection -/
section LocalModule16

set_option linter.unusedVariables false

/-! The genuine upstream idealClosedCorrection and globalClosedCorrection
on the new half-plane. The original summable prime majorant and original
cutoff are reused because the new local theorem retains the same17/10 decay.
No product bound, analyticity, or perturbed contraction is assumed.
-/

namespace RHZeroFreeExtension.AnalyticHigh
noncomputable section
open scoped Classical BigOperators
open OAI.SevenEighths OAI.SevenEighths.ProbeEuler
open OAI.SevenEighths.ProbePhysical OAI.ActualEisensteinCubic
local notation "Id" => Ideal OAI.ActualEisensteinCubic.O

lemma perturbed_idealClosedCorrection_bound (η : HeckeFamily.Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (hP : 4≤ Ideal.absNorm P.val) (x w z : ℂ)
    (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖idealClosedCorrection η P x w z-1‖≤ globalPrimeDefectBound P := by
  apply perturbed_unramifiedClosed_open_region_bound
  · exact_mod_cast hP
  · exact actualAPhase_norm_le_one η _
  · exact HeckeFamily.idealCoeff_norm_le_one η P.val
  · simp
  · exact hx
  · exact hw
  · exact hz

theorem perturbed_globalClosedCorrection_bound (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    ‖globalClosedCorrection η S x w z-1‖≤1/2 :=
  product_defect_le _ _ hS.summable
    (fun P=> perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz)
    hS.half hS.small

lemma perturbed_globalClosedCorrection_multipliable (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w z : ℂ)
    (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    Multipliable (fun P : {P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z) := by
  let F := fun P : {P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal // P.val∉S}=> idealClosedCorrection η P.val x w z
  let B := fun P : {P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal // P.val∉S}=> globalPrimeDefectBound P.val
  have hB (P) : ‖F P-1‖≤ B P :=
    perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz
  refine ⟨Complex.exp (∑' P,Complex.log (F P)),?_⟩
  apply ((log_summable_of_defect F B hS.summable hB hS.half).of_norm.hasSum.cexp).congr
  intro T
  apply Finset.prod_congr rfl
  intro P hP
  exact Complex.exp_log (factor_ne_zero_of_defect _ ((hB P).trans (hS.half P)))

theorem perturbed_globalClosedCorrection_analytic_x (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (w z : ℂ) (hw : 9/10≤ w.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun x=> globalClosedCorrection η S x w z) {x : ℂ|34999/40000< x.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply perturbed_unramifiedClosed_analytic_x
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hz
  · intro P x hx
    exact perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx.le hw hz
  · exact hS.half

theorem perturbed_globalClosedCorrection_analytic_w (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x z : ℂ) (hx : 34999/40000≤ x.re) (hz : 4/25≤ z.re) :
    AnalyticOnNhd ℂ (fun w=> globalClosedCorrection η S x w z) {w : ℂ|9/10< w.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply perturbed_unramifiedClosed_analytic_w
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
    · exact hz
  · intro P w hw
    exact perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw.le hz
  · exact hS.half

theorem perturbed_globalClosedCorrection_analytic_z (η : HeckeFamily.Character) (S : Finset Id)
    (hS : CorrectionTail S) (x w : ℂ) (hx : 34999/40000≤ x.re) (hw : 9/10≤ w.re) :
    AnalyticOnNhd ℂ (fun z=> globalClosedCorrection η S x w z) {z : ℂ|4/25< z.re} := by
  apply normalProduct_analytic _ _ _ (Complex.isOpen_re_gt _) hS.summable
  · intro P
    apply perturbed_unramifiedClosed_analytic_z
    · exact_mod_cast hS.norm_four P.val P.property
    · exact actualAPhase_norm_le_one η _
    · exact HeckeFamily.idealCoeff_norm_le_one η _
    · simp
    · exact hx
  · intro P z hz
    exact perturbed_idealClosedCorrection_bound η P.val (hS.norm_four P.val P.property) x w z hx hw hz.le
  · exact hS.half


end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule16
/- END RHZeroFreeExtension.analytic_high.PerturbedGlobalCorrection -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFiniteProduct -/
section LocalModule17

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

theorem perturbed_correction_lower_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    1/2 ≤ ‖idealClosedCorrection η P x w z‖ := by
  have hb := (perturbed_idealClosedCorrection_bound η P (hS.norm_four P hP) x w z hx hw hz).trans
    (hS.half ⟨P,hP⟩)
  have hn := norm_sub_norm_le (1 : ℂ) (idealClosedCorrection η P x w z)
  rw [norm_one, norm_sub_rev] at hn
  linarith

theorem perturbed_correction_ne_zero (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    idealClosedCorrection η P x w z ≠ 0 :=
  norm_pos_iff.mp ((by norm_num : (0 : ℝ)<1/2).trans_le
    (perturbed_correction_lower_bound η S hS P hP x w z hx hw hz))

theorem perturbed_correction_inverse_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ)
    (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖(idealClosedCorrection η P x w z)⁻¹‖ ≤ 2 := by
  have hh := perturbed_correction_lower_bound η S hS P hP x w z hx hw hz
  rw [norm_inv, inv_eq_one_div]
  exact (div_le_iff₀ (by linarith : 0 < ‖idealClosedCorrection η P x w z‖)).mpr (by linarith)

lemma perturbed_marked_differentiableAt_w (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 34999/40000 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun w => idealMarkedClosed η P x w z) w := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := perturbed_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  have hk := coordK_w_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

lemma perturbed_marked_differentiableAt_z (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 34999/40000 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun z => idealMarkedClosed η P x w z) z := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := perturbed_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  have hr := coordR_z_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) x
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem perturbed_local_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x z : ℂ)
    (hx : 34999/40000 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => localMultiplier η P x w z) {w : ℂ | 9/10 < w.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hd := perturbed_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hc := perturbed_unramifiedClosed_analytic_w (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro w hw
  have hmc := perturbed_marked_differentiableAt_w η P x w z hQ hx hz
  have hcc : DifferentiableAt ℂ (fun w => idealClosedCorrection η P x w z) w :=
    (hc w hw).differentiableAt
  have hh := perturbed_correction_ne_zero η S hS P hP x w z hx hw.le hz
  have hcw := coordW_differentiable (Ideal.absNorm P.val) hQ0 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem perturbed_local_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x w : ℂ)
    (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => localMultiplier η P x w z) {z : ℂ | 4/25 < z.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := perturbed_unramifiedClosed_analytic_z (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x w hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro z hz
  have hd := perturbed_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz.le
  have hmc := perturbed_marked_differentiableAt_z η P x w z hQ hx hz.le
  have hcc : DifferentiableAt ℂ (fun z => idealClosedCorrection η P x w z) z :=
    (hc z hz).differentiableAt
  have hh := perturbed_correction_ne_zero η S hS P hP x w z hx hw hz.le
  have hcv := coordV_differentiable (Ideal.absNorm P.val) hQ0
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

lemma perturbed_marked_bound (Q : ℝ) (A η x w z : ℂ) (hQ : 4 ≤ Q)
    (hA : ‖A‖ ≤ 1) (hη : ‖η‖ ≤ 1) (hx : 34999/40000 ≤ x.re)
    (hw : 19/20 ≤ w.re) (hz : 33/200 ≤ z.re) :
    ‖PrincipalSlotEstimate.regionMarked Q A η x w z‖ ≤ 16 := by
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

lemma perturbed_replacement_bound (V W D P B q : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hV : ‖V‖ ≤ 1/2) (hW : ‖W‖ ≤ 1) (hD : ‖D‖ ≤ 1/2)
    (hP : ‖P‖ ≤ 16) (hB : ‖B‖ ≤ R) (hq : ‖q‖ ≤ 1) :
    ‖compensatedReplacement V W D P B q‖ ≤ 200*(1+R) := by
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

lemma perturbed_localBound_nonneg (Bx Bz : ℝ) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) : 0 ≤ localBound Bx Bz P := by
  unfold localBound
  positivity

theorem perturbed_local_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (34999/40000) Bx) (hw : 19/20 ≤ w.re)
    (hz : z.re ∈ Icc (33/200) Bz) :
    ‖localMultiplier η P x w z‖ ≤ localBound Bx Bz P := by
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
    perturbed_marked_bound Q (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) x w z hQ
      (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) hx.1 hw hz.1
  have hr := perturbed_replacement_bound _ _ _ _ _ _ (Q^Bx) (Real.rpow_nonneg hQ0.le _) hV hW hD hm hB hq
  have hi := perturbed_correction_inverse_bound η S hS P hP x w z hx.1 (by linarith) (by linarith [hz.1])
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

lemma perturbed_selectedBound_nonneg (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (Bx Bz : ℝ) :
    0 ≤ selectedBound T Bx Bz := Finset.prod_nonneg (fun P _ => perturbed_localBound_nonneg Bx Bz P)

lemma perturbed_slotBound_nonneg {ι : Type*} (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (Bx Bz : ℝ) : 0 ≤ slotBound J T b Bx Bz := by
  apply Finset.prod_nonneg
  intro j hj
  exact Finset.sum_nonneg (fun P _ => mul_nonneg (norm_nonneg _) (perturbed_localBound_nonneg Bx Bz P))

theorem perturbed_selected_analytic_w (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x z : ℂ)
    (hx : 34999/40000 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => selectedMultiplier η T x w z) {w : ℂ | 9/10 < w.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => perturbed_local_analytic_w η S hS P (hT P hp) x z hx hz)

theorem perturbed_selected_analytic_z (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w : ℂ)
    (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => selectedMultiplier η T x w z) {z : ℂ | 4/25 < z.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => perturbed_local_analytic_z η S hS P (hT P hp) x w hx hw)

theorem perturbed_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 34999/40000 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => slotMultiplier η J T b x w z) {w : ℂ | 9/10 < w.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (perturbed_local_analytic_w η S hS P (hT j hj P hp) x z hx hz)

theorem perturbed_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => slotMultiplier η J T b x w z) {z : ℂ | 4/25 < z.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (perturbed_local_analytic_z η S hS P (hT j hj P hp) x w hx hw)

theorem perturbed_selected_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (34999/40000) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖selectedMultiplier η T x w z‖ ≤ selectedBound T Bx Bz := by
  simp only [selectedMultiplier,selectedBound,norm_prod]
  exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    (fun P hp => perturbed_local_norm_bound η S hS P (hT P hp) x w z Bx Bz hx hw hz)

theorem perturbed_slot_norm_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (34999/40000) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖slotMultiplier η J T b x w z‖ ≤ slotBound J T b Bx Bz := by
  simp only [slotMultiplier,slotBound,norm_prod]
  apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
  intro j hj
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro P hp
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (perturbed_local_norm_bound η S hS P (hT j hj P hp) x w z Bx Bz hx hw hz) (norm_nonneg _)

lemma perturbed_global_norm_bound (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (x w z : ℂ) (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    ‖globalClosedCorrection η S x w z‖ ≤ 3/2 := by
  have hb := perturbed_globalClosedCorrection_bound η S hS x w z hx hw hz
  have hn := norm_add_le (globalClosedCorrection η S x w z-1) (1 : ℂ)
  rw [sub_add_cancel,norm_one] at hn
  linarith

theorem perturbed_combined_slot_analytic_w {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x z : ℂ)
    (hx : 34999/40000 ≤ x.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun w => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {w : ℂ | 9/10 < w.re} :=
  (perturbed_globalClosedCorrection_analytic_w η S hS x z hx hz).mul (perturbed_slot_analytic_w η S hS J T b hT x z hx hz)

theorem perturbed_combined_slot_analytic_z {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w : ℂ)
    (hx : 34999/40000 ≤ x.re) (hw : 9/10 ≤ w.re) :
    AnalyticOnNhd ℂ (fun z => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {z : ℂ | 4/25 < z.re} :=
  (perturbed_globalClosedCorrection_analytic_z η S hS x w hx hw).mul (perturbed_slot_analytic_z η S hS J T b hT x w hx hw)

theorem perturbed_combined_slot_bound {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (x w z : ℂ) (Bx Bz : ℝ)
    (hx : x.re ∈ Icc (34999/40000) Bx) (hw : 19/20 ≤ w.re) (hz : z.re ∈ Icc (33/200) Bz) :
    ‖globalClosedCorrection η S x w z * slotMultiplier η J T b x w z‖ ≤
      (3/2)*slotBound J T b Bx Bz := by
  rw [norm_mul]
  exact mul_le_mul (perturbed_global_norm_bound η S hS x w z hx.1 (by linarith) (by linarith [hz.1]))
    (perturbed_slot_norm_bound η S hS J T b hT x w z Bx Bz hx hw hz) (norm_nonneg _) (by norm_num)

theorem perturbed_selected_initial_identity (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (x w z : ℂ)
    (hx : 3/2 < x.re) (hw : 2 < w.re) (hz : 1/6 < z.re) :
    (∏ P ∈ T, (Ideal.absNorm P.val : ℂ)^(z-1)) *
      spectralCompensatedHigh S T η x w z
        (fun P => star (idealCoeff η P.val)*(Ideal.absNorm P.val : ℂ)^x)
        (fun P => (Ideal.absNorm P.val : ℂ)^(-w)) =
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w /
        LFunction (η.excludePrimes S hS.prime) x) *
        (globalClosedCorrection η S x w z * selectedMultiplier η T x w z) := by
  rw [spectralCompensatedHigh_continued S hS T hT η x w z _ _ hx hw hz]
  simp only [selectedMultiplier,localMultiplier,Finset.prod_mul_distrib,Complex.ofReal_natCast]
  ring_nf

theorem perturbed_source_w_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : 34999/40000 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw : ℝ} (hcw : 1< cw) :
    BoundaryControl (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z *
        LFunction (fixedPrincipal M) w) (19/20) cw := by
  apply PrincipalMellinGrowth.source_w_boundary W0 W1 a1 b1 ha1 hW1 M X Y Z hY
    (η.excludePrimes S hS.prime) s z hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re z.re) hcw
    (mul_nonneg (by norm_num) (perturbed_slotBound_nonneg J T b _ _)) 0
  · exact (perturbed_combined_slot_analytic_w η S hS.tail J T b hT s z hs (by linarith)).continuousOn.mono
      (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using perturbed_combined_slot_bound η S hS.tail J T b hT s
      ((x : ℂ)+t*I) z s.re z.re ⟨hs,le_rfl⟩ (by simpa using hx.1) ⟨hz,le_rfl⟩

theorem perturbed_source_z_boundary {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : 34999/40000 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
        LFunction (fixedPrincipal M) (6*z)) (33/200) (1/6+e) := by
  apply PrincipalMellinGrowth.source_z_boundary W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ
    (η.excludePrimes S hS.prime) s hEta (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) he he'
    (mul_nonneg (by norm_num) (perturbed_slotBound_nonneg J T b _ _)) 0
  · exact (perturbed_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using perturbed_combined_slot_bound η S hS.tail J T b hT s
      1 ((x : ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)

theorem perturbed_source_multiplier_differentiable_w {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1) (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : 34999/40000 ≤ s.re) (hz : 4/25 ≤ z.re) :
    DifferentiableOn ℂ (fun w => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {w : ℂ | 9/10 < w.re} := by
  have hM := CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)
  have hH := (perturbed_combined_slot_analytic_w η S hS.tail J T b hT s z hs hz).differentiableOn
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

theorem perturbed_source_multiplier_differentiable_z {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s w : ℂ) (hs : 34999/40000 ≤ s.re) (hw : 9/10 ≤ w.re) :
    DifferentiableOn ℂ (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) w z) {z : ℂ | 4/25 < z.re} := by
  have hM : DifferentiableOn ℂ (mellin (EisensteinSchwartzPoisson.paperRadialFourier W0))
      {z : ℂ | 4/25 < z.re} :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).mono (by intro z hz; change 0 < z.re; change (4/25:ℝ)< z.re at hz; linarith)
  have hH := (perturbed_combined_slot_analytic_z η S hS.tail J T b hT s w hs hw).differentiableOn
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

theorem perturbed_source_w_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0< a1)
    (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hY : 0< Y)
    (s z : ℂ) (hs : 34999/40000 ≤ s.re) (hz : 33/200 ≤ z.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0) {cw : ℝ} (hcw : 1< cw) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral cw (fun w => K w z * LFunction (fixedPrincipal M) w) =
      verticalIntegral (19/20) (fun w => K w z * LFunction (fixedPrincipal M) w) +
        K 1 z * fixedPrincipalResidue M := by
  dsimp only
  apply PrincipalMellinResidues.source_w_shift (fixedPrincipal M) _ z hcw
  · exact (perturbed_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY s z hs (by linarith)).mono (by intro w hw; change (9/10:ℝ)< w.re; linarith [hw.1])
  · exact perturbed_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1 M X Y Z hY s z hs hz hEta hcw

theorem perturbed_source_residue_z_shift {ι : Type*} (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0 ⊆ Icc a0 b0)
    (M : Ideal HeckeFamily.O) [NeZero M] (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : 34999/40000 ≤ s.re) (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {e : ℝ} (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    verticalIntegral (1/6+e) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) =
      verticalIntegral (33/200) (fun z => K 1 z * LFunction (fixedPrincipal M) (6*z)) +
        K 1 (1/6) * fixedPrincipalResidue M / 6 := by
  dsimp only
  apply PrincipalMellinResidues.source_residue_z_shift (fixedPrincipal M) _ he
  · exact (perturbed_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ s 1 hs
      (by norm_num)).mono (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · exact perturbed_source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0 M X Y Z hX hZ s hs hEta he he'


theorem perturbed_fixed_source_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : 34999/40000 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  dsimp only
  let : NeZero (∏ P ∈ S, P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  constructor
  · intro z hz
    exact perturbed_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏ P ∈ S, P) X Y Z hY s z hs (by rw [hz]; linarith) hEta hcw
  · exact perturbed_source_z_boundary η S hS J T b hT W0 W1 a0 b0 ha0 hW0
      (∏ P ∈ S, P) X Y Z hX hZ s hs hEta he he'

lemma perturbed_boundary_mul_const (F : ℂ → ℂ) (a b : ℝ) (h : BoundaryControl F a b) (c : ℂ) :
    BoundaryControl (fun z => F z*c) a b := by
  refine ⟨h.left.mul_const c,h.right.mul_const c,?_,?_⟩
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.lower.mul_const c
  · simpa only [intervalIntegral.integral_mul_const,zero_mul] using h.upper.mul_const c

theorem perturbed_fixed_source_ordered_boundaries {ι : Type*} (S : Finset Id) (hS : SourceExclusions S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0 ⊆ Icc a0 b0) (hW1 : Function.support W1 ⊆ Icc a1 b1)
    (X Y Z : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (η : Character) (s : ℂ) (hs : 34999/40000 ≤ s.re)
    (hEta : LFunction (η.excludePrimes S hS.prime) s ≠ 0)
    {cw e : ℝ} (hcw : 1< cw) (he : 0< e) (he' : e≤2/3) :
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (∀ z : ℂ, z.re=1/6+e → BoundaryControl
      (fun w => K w z * LFunction (fixedSourcePrincipal S hS.prime) (6*z) *
        LFunction (fixedSourcePrincipal S hS.prime) w) (19/20) cw) ∧
      BoundaryControl (fun z => K 1 z * LFunction (fixedSourcePrincipal S hS.prime) (6*z))
        (33/200) (1/6+e) := by
  have hh := perturbed_fixed_source_boundaries S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ η s hs hEta hcw he he'
  dsimp only at hh ⊢
  refine ⟨?_,hh.2⟩
  intro z hz
  convert perturbed_boundary_mul_const _ _ _ (hh.1 z hz) (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
  funext w
  ring

theorem perturbed_uniform_closed_box_bound {ι : Type*} (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (Bx Bw Bz : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (η : Character) (s w z : ℂ),
      s.re ∈ Icc (34999/40000) Bx → w.re ∈ Icc (19/20) Bw → z.re ∈ Icc (33/200) Bz →
      ‖globalClosedCorrection η S s w z * slotMultiplier η J T b s w z‖ ≤ C :=
  ⟨(3/2)*slotBound J T b Bx Bz,
    mul_nonneg (by norm_num) (perturbed_slotBound_nonneg J T b Bx Bz),
    fun η s w z hs hw hz => perturbed_combined_slot_bound η S hS J T b hT s w z Bx Bz hs hw.1 hz⟩

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule17
/- END RHZeroFreeExtension.analytic_high.PerturbedFiniteProduct -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedFiniteProductX -/
section LocalModule18

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

lemma perturbed_marked_differentiableAt_x (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : ℂ)
    (hQ : 4 ≤ (Ideal.absNorm P.val : ℝ)) (hx : 34999/40000 ≤ x.re) (hz : 4/25 ≤ z.re) :
    DifferentiableAt ℂ (fun x => idealMarkedClosed η P x w z) x := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hd := perturbed_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx hz
  have hr := coordR_differentiable (Ideal.absNorm P.val) hQ0
    (actualAPhase η (primaryGenerator P.val)) z
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  have hk := coordK_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) w
  unfold idealMarkedClosed markedFactor
  dsimp only
  fun_prop (disch := aesop)

theorem perturbed_local_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hP : P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => localMultiplier η P x w z) {x : ℂ | 34999/40000 < x.re} := by
  have hQ : 4 ≤ (Ideal.absNorm P.val : ℝ) := by exact_mod_cast hS.norm_four P hP
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by linarith
  have hn : (Ideal.absNorm P.val : ℂ) ≠ 0 := by exact_mod_cast hQ0.ne'
  have hc := perturbed_unramifiedClosed_analytic_x (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 w z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hz
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hd := perturbed_open_region_denominators (Ideal.absNorm P.val)
    (actualAPhase η (primaryGenerator P.val)) (idealCoeff η P.val) 1 x z hQ
    (actualAPhase_norm_le_one η _) (idealCoeff_norm_le_one η _) (by simp) hx.le hz
  have hm := perturbed_marked_differentiableAt_x η P x w z hQ hx.le hz
  have hcc : DifferentiableAt ℂ (fun x => idealClosedCorrection η P x w z) x :=
    (hc x hx).differentiableAt
  have hh := perturbed_correction_ne_zero η S hS P hP x w z hx.le hw hz
  have hd' := coordD_differentiable (Ideal.absNorm P.val) hQ0 (idealCoeff η P.val) 1
  apply DifferentiableAt.differentiableWithinAt
  unfold localMultiplier compensatedReplacement
  dsimp only
  fun_prop (disch := first | assumption | exact hd.2.2 | exact Or.inl hn)

theorem perturbed_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => selectedMultiplier η T x w z) {x : ℂ | 34999/40000 < x.re} :=
  T.analyticOnNhd_fun_prod (fun P hp => perturbed_local_analytic_x η S hS P (hT P hp) w z hw hz)

theorem perturbed_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => slotMultiplier η J T b x w z) {x : ℂ | 34999/40000 < x.re} := by
  apply J.analyticOnNhd_fun_prod
  intro j hj
  apply (T j).analyticOnNhd_fun_sum
  intro P hp
  exact analyticOnNhd_const.mul (perturbed_local_analytic_x η S hS P (hT j hj P hp) w z hw hz)

theorem perturbed_window_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (W : ι → ℝ → ℂ) (scale : ι → ℝ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => windowMultiplier η J T W scale x w z) {x : ℂ | 34999/40000 < x.re} :=
  perturbed_slot_analytic_x η S hS J T _ hT w z hw hz

theorem perturbed_combined_selected_analytic_x (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (T : Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (hT : ∀ P ∈ T, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * selectedMultiplier η T x w z)
      {x : ℂ | 34999/40000 < x.re} :=
  (perturbed_globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (perturbed_selected_analytic_x η S hS T hT w z hw hz)

theorem perturbed_combined_slot_analytic_x {ι : Type*} (η : Character) (S : Finset Id) (hS : CorrectionTail S)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => globalClosedCorrection η S x w z * slotMultiplier η J T b x w z)
      {x : ℂ | 34999/40000 < x.re} :=
  (perturbed_globalClosedCorrection_analytic_x η S hS w z hw hz).mul
    (perturbed_slot_analytic_x η S hS J T b hT w z hw hz)

theorem perturbed_continued_source_analytic_x {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | max (34999/40000 : ℝ) HeckeZeroSupremum.beta < x.re} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _ (Complex.isOpen_re_gt _)
  intro x hx
  have hx' : (34999/40000 : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx
  have hH := (perturbed_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (perturbed_slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  have hR := HeckeReciprocal.reciprocal_differentiableAt (η.excludePrimes S hS.prime) hβ
  apply DifferentiableAt.differentiableWithinAt
  unfold continuedSourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem perturbed_continued_source_eq_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ)
    (hx0 : x≠0) (hx1 : x≠1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z x w z =
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS) x
        (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z := by
  simp only [continuedSourceMultiplier,sourceMultiplier,
    HeckeReciprocal.reciprocal_eq_inv _ hx0 hx1,div_eq_mul_inv]

theorem perturbed_continued_source_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a : ℝ) (w z : ℂ) :
    (fun t : ℝ => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z ((a:ℂ)+t*I) w z)
      =ᵐ[volume] (fun t : ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
        ((a:ℂ)+t*I) (globalClosedCorrection η S ((a:ℂ)+t*I))
          (slotMultiplier η J T b ((a:ℂ)+t*I)) w z) := by
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply perturbed_continued_source_eq_raw
  · intro h
    exact ht (by simpa using congrArg Complex.im h)
  · intro h
    exact ht (by simpa using congrArg Complex.im h)

theorem perturbed_source_analytic_x_off_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) :
    AnalyticOnNhd ℂ (fun x => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) x
      (globalClosedCorrection η S x) (slotMultiplier η J T b x) w z)
      {x : ℂ | max (34999/40000 : ℝ) HeckeZeroSupremum.beta < x.re ∧ x≠1} := by
  have hn : (Z:ℂ) ≠ 0 := by exact_mod_cast hZ.ne'
  apply DifferentiableOn.analyticOnNhd _
    ((Complex.isOpen_re_gt _).inter (isClosed_singleton.isOpen_compl))
  intro x hx
  have hx' : (34999/40000 : ℝ)< x.re := lt_of_le_of_lt (le_max_left _ _) hx.1
  have hβ : HeckeZeroSupremum.beta< x.re := lt_of_le_of_lt (le_max_right _ _) hx.1
  have hx0 : x≠0 := by intro h; simp only [h,zero_re] at hx'; norm_num at hx'
  have hL := LFunction_differentiableAt (η.excludePrimes S hS.prime) hx0 (Or.inl hx.2)
  have hLn := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime) hβ (Or.inl hx.2)
  have hH := (perturbed_globalClosedCorrection_analytic_x η S hS.tail w z hw hz x hx').differentiableAt
  have hB := (perturbed_slot_analytic_x η S hS.tail J T b hT w z hw hz x hx').differentiableAt
  apply DifferentiableAt.differentiableWithinAt
  unfold sourceMultiplier
  fun_prop (disch := first | assumption | exact Or.inl hn)

theorem perturbed_continued_source_differentiable_strip {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀ j ∈ J, ∀ P ∈ T j, P.val ∉ S)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hZ : 0< Z) (w z : ℂ)
    (hw : 9/10 ≤ w.re) (hz : 4/25 ≤ z.re) {a c : ℝ}
    (ha : 34999/40000< a) (hβ : HeckeZeroSupremum.beta< a) :
    DifferentiableOn ℂ (fun x => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z x w z)
      {x : ℂ | a≤ x.re ∧ x.re≤ c} := by
  apply (perturbed_continued_source_analytic_x η S hS J T b hT W0 W1 X Y Z hZ w z hw hz).differentiableOn.mono
  intro x hx
  exact lt_of_lt_of_le (max_lt ha hβ) hx.1

theorem perturbed_continued_source_principal_one {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀ P ∈ S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (w z : ℂ)
    (hχ : (η.excludePrimes S hS).residue=1) :
    continuedSourceMultiplier η S hS J T b W0 W1 X Y Z 1 w z=0 := by
  simp only [continuedSourceMultiplier,HeckeReciprocal.reciprocal_principal_one _ hχ,mul_zero,zero_mul]

end
end RHZeroFreeExtension.AnalyticHigh

end LocalModule18
/- END RHZeroFreeExtension.analytic_high.PerturbedFiniteProductX -/

/- BEGIN original module RHZeroFreeExtension.analytic_high.PerturbedPrincipalContours -/
section LocalModule19

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

@[fun_prop] lemma perturbed_measurable_const_cpow {α : Type*} [MeasurableSpace α] (Q : ℝ) (hQ : 0< Q)
    (f : α → ℂ) (hf : Measurable f) : Measurable (fun x => (Q:ℂ)^f x) := by
  have hn : (Q:ℂ)≠0 := by exact_mod_cast hQ.ne'
  exact ((differentiable_id.const_cpow (Or.inl hn)).continuous.measurable).comp hf

lemma perturbed_ideal_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => idealClosedCorrection η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  unfold idealClosedCorrection unramifiedClosed continuedCorrection markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma perturbed_global_correction_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (S : Finset Id) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => globalClosedCorrection η S (x t) (w t) (z t)) := by
  unfold globalClosedCorrection
  exact Measurable.tprod (fun P => perturbed_ideal_correction_measurable η P.val x w z hx hw hz)

lemma perturbed_local_multiplier_measurable {α : Type*} [MeasurableSpace α]
    (η : Character) (P : OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (x w z : α → ℂ)
    (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => localMultiplier η P (x t) (w t) (z t)) := by
  have hQ : 0<(Ideal.absNorm P.val : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero)
  have hc := perturbed_ideal_correction_measurable η P x w z hx hw hz
  unfold localMultiplier compensatedReplacement idealMarkedClosed markedFactor
    coordR coordV coordW coordD coordK
  dsimp only
  fun_prop (disch := aesop)

lemma perturbed_slot_multiplier_measurable {α ι : Type*} [MeasurableSpace α]
    (η : Character) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (x w z : α → ℂ) (hx : Measurable x) (hw : Measurable w) (hz : Measurable z) :
    Measurable (fun t => slotMultiplier η J T b (x t) (w t) (z t)) := by
  unfold slotMultiplier
  apply Finset.measurable_prod
  intro j hj
  apply Finset.measurable_sum
  intro P hP
  exact measurable_const.mul (perturbed_local_multiplier_measurable η P x w z hx hw hz)

lemma perturbed_zBoxAmplitude_nonneg (M : Id) [NeZero M] (Bz : ℝ) : 0≤ zBoxAmplitude M Bz := by
  unfold zBoxAmplitude
  exact mul_nonneg (mul_nonneg (by norm_num) (le_trans (by norm_num) (le_max_left _ _)))
    (principalConstant_pos M).le

lemma perturbed_fixed_principal_z_box_growth (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) :
    ‖HeckeOrigin.poleRemoved (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤ zBoxAmplitude M Bz*height t^3 := by
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

lemma perturbed_LFunction_eq_pole_quotient (χ : Character) {s : ℂ} (h0 : s≠0) (h1 : s≠1) :
    LFunction χ s=HeckeOrigin.poleRemoved χ s/(s-1) := by
  rw [HeckeOrigin.poleRemoved_eq χ h0 h1]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr h1)).symm

lemma perturbed_LFunction_vertical_continuous (χ : Character) (a : ℝ) (ha0 : a≠0) (ha1 : a≠1) :
    Continuous (fun t : ℝ => LFunction χ ((a:ℂ)+t*I)) := by
  have h0 (t : ℝ) : (a:ℂ)+t*I≠0 := by intro h; exact ha0 (by simpa using congrArg Complex.re h)
  have h1 (t : ℝ) : (a:ℂ)+t*I≠1 := by intro h; exact ha1 (by simpa using congrArg Complex.re h)
  have hc := ((HeckeOrigin.poleRemoved_entire χ).continuous.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I))).div
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I-1)) (fun t => sub_ne_zero.mpr (h1 t))
  exact hc.congr (fun t => (perturbed_LFunction_eq_pole_quotient χ (h0 t) (h1 t)).symm)

lemma perturbed_reciprocal_vertical_continuous (χ : Character) (a : ℝ) (ha : HeckeZeroSupremum.beta< a) :
    Continuous (fun t : ℝ => HeckeReciprocal.reciprocal χ ((a:ℂ)+t*I)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (HeckeReciprocal.reciprocal_differentiableAt χ (by simpa using ha)).continuousAt.comp
    (by fun_prop : Continuous (fun t : ℝ => (a:ℂ)+t*I)).continuousAt

lemma perturbed_LFunction_norm_le_of_poleRemoved (χ : Character) (s : ℂ) (h0 : s≠0) (h1 : s≠1)
    (A δ : ℝ) (hδ : 0<δ) (hd : δ≤‖s-1‖) (hA : ‖HeckeOrigin.poleRemoved χ s‖≤ A) :
    ‖LFunction χ s‖≤ A/δ := by
  apply (le_div_iff₀ hδ).mpr
  calc
    _ ≤ ‖LFunction χ s‖*‖s-1‖ := mul_le_mul_of_nonneg_left hd (norm_nonneg _)
    _ = ‖HeckeOrigin.poleRemoved χ s‖ := by rw [HeckeOrigin.poleRemoved_eq χ h0 h1,norm_mul]; ring
    _ ≤ A := hA

lemma perturbed_fixed_principal_w_bound (M : Id) [NeZero M] {cw υ : ℝ} (hcw : 1< cw)
    (hυ : υ∈Icc (19/20 : ℝ) cw) (hυ1 : υ≠1) (t : ℝ) :
    ‖LFunction (fixedPrincipal M) ((υ:ℂ)+t*I)‖≤
      (wAmplitude M cw/|υ-1|)*height t^3 := by
  have h0 : (υ:ℂ)+t*I≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hυ.1]
  have h1 : (υ:ℂ)+t*I≠1 := by intro h; exact hυ1 (by simpa using congrArg Complex.re h)
  have hδ : 0 < |υ-1| := abs_pos.mpr (sub_ne_zero.mpr hυ1)
  have h := perturbed_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ
    (pole_distance_vertical 1 υ t) (fixed_principal_w_growth M hcw hυ t)
  convert h using 1
  ring

lemma perturbed_fixed_principal_z_bound (M : Id) [NeZero M] (Bz ξ t : ℝ)
    (hξ : ξ∈Icc (33/200 : ℝ) Bz) (hξ1 : 6*ξ≠1) :
    ‖LFunction (fixedPrincipal M) (6*((ξ:ℂ)+t*I))‖≤
      (zBoxAmplitude M Bz/|6*ξ-1|)*height t^3 := by
  have h0 : (6*((ξ:ℂ)+t*I) : ℂ)≠0 := by
    intro h; have he := congrArg Complex.re h; simp at he; linarith [hξ.1]
  have h1 : (6*((ξ:ℂ)+t*I) : ℂ)≠1 := by intro h; exact hξ1 (by simpa using congrArg Complex.re h)
  have hd : |6*ξ-1|≤‖6*((ξ:ℂ)+t*I)-1‖ := by
    simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+t*I)-1)
  have hδ : 0 < |6*ξ-1| := abs_pos.mpr (sub_ne_zero.mpr hξ1)
  have h := perturbed_LFunction_norm_le_of_poleRemoved (fixedPrincipal M) _ h0 h1 _ _ hδ hd
    (perturbed_fixed_principal_z_box_growth M Bz ξ t hξ)
  convert h using 1
  ring

lemma perturbed_arithmetic_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s w z : ℂ) :
    arithmeticMultiplier η S hS J T b X Y Z s w z*profile W0 W1 s w z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s w z *
        LFunction (fixedSourcePrincipal S hS) (6*z)*LFunction (fixedSourcePrincipal S hS) w := by
  unfold arithmeticMultiplier profile continuedSourceMultiplier
  ring

lemma perturbed_arithmetic_onLines_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Y Z a ξ υ : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) (hυ0 : υ≠0) (hυ1 : υ≠1) :
    Measurable (fun p : HeightSpace => arithmeticMultiplier η S hS J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  have hH := perturbed_global_correction_measurable η S
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := perturbed_slot_multiplier_measurable η J T b
    (fun p : HeightSpace => (a:ℂ)+p.1.1*I) (fun p : HeightSpace => (υ:ℂ)+p.2*I)
    (fun p : HeightSpace => (ξ:ℂ)+p.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (perturbed_reciprocal_vertical_continuous (η.excludePrimes S hS) a ha).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.1.1))
  have hW := (perturbed_LFunction_vertical_continuous (fixedSourcePrincipal S hS) υ hυ0 hυ1).measurable.comp
    (by fun_prop : Measurable (fun p : HeightSpace => p.2))
  have hZL := (perturbed_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
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

lemma perturbed_boxScale_pos (X Y Z a Bs Bz cw : ℝ) : 0< boxScale X Y Z a Bs Bz cw := by
  unfold boxScale
  exact mul_pos (mul_pos (scaleBound_pos _ _ _) (scaleBound_pos _ _ _)) (scaleBound_pos _ _ _)

lemma perturbed_height_le_joint_s (t v u : ℝ) : height t≤ jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg v,abs_nonneg u]
lemma perturbed_height_le_joint_z (t v u : ℝ) : height v≤ jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg u]
lemma perturbed_height_le_joint_w (t v u : ℝ) : height u≤ jointHeight t v u := by
  unfold height jointHeight; linarith [abs_nonneg t,abs_nonneg v]

lemma perturbed_arithmetic_onLines_bound_of_gaps {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (δw δz : ℝ) (hdw : 0<δw) (hdz : 0<δz)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace)
    (hwgap : δw≤‖((υ:ℂ)+p.2*I)-1‖) (hzgap : δz≤‖6*((ξ:ℂ)+p.1.2*I)-1‖) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz *
        jointHeight p.1.1 p.1.2 p.2^8 := by
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
  have hh := perturbed_combined_slot_bound η S hS.tail J T b hT ((σ:ℂ)+p.1.1*I)
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
  have hlz0 := perturbed_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hz0 hz1 _ _ hdz hzgap
    (perturbed_fixed_principal_z_box_growth (∏P∈S,P) Bz ξ p.1.2 hξ)
  have hlw0 := perturbed_LFunction_norm_le_of_poleRemoved (fixedPrincipal (∏P∈S,P)) _ hw0 hw1 _ _ hdw hwgap
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
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (perturbed_slotBound_nonneg J T b Bs Bz)
  have hAZ := div_nonneg (perturbed_zBoxAmplitude_nonneg (∏P∈S,P) Bz) hdz.le
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
      gcongr <;> first | positivity | exact perturbed_height_le_joint_s _ _ _ | exact perturbed_height_le_joint_z _ _ _ | exact perturbed_height_le_joint_w _ _ _
    _ = _ := by unfold arithmeticAmplitude boxScale; ring

lemma perturbed_arithmetic_onLines_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Y Z a Bs Bz cw σ ξ υ C : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hσ : σ∈Icc a Bs) (hξ : ξ∈Icc (33/200 : ℝ) Bz)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ, a≤ s.re → ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (p : HeightSpace) :
    ‖arithmeticMultiplier η S hS.prime J T b X Y Z ((σ:ℂ)+p.1.1*I)
      ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)‖≤
      arithmeticAmplitude S J T b X Y Z a Bs Bz cw C |υ-1| |6*ξ-1| *
        jointHeight p.1.1 p.1.2 p.2^8 := by
  apply perturbed_arithmetic_onLines_bound_of_gaps η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ |υ-1| |6*ξ-1| (abs_pos.mpr (sub_ne_zero.mpr hυ1))
    (abs_pos.mpr (sub_ne_zero.mpr hξ1)) hC hR p
  · exact pole_distance_vertical 1 υ p.2
  · simpa using Complex.abs_re_le_norm (6*((ξ:ℂ)+p.1.2*I)-1)

theorem perturbed_continued_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+p.1.1*I)
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  have hi := profile_arithmetic_integrable W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 a ξ υ
    (by linarith) (fun p : HeightSpace => arithmeticMultiplier η S hS.prime J T b X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I))
    (perturbed_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
      (by linarith) hξ1 (by linarith [hυ.1]) hυ1).aestronglyMeasurable
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|) 8
    (perturbed_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
      ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR)
  apply hi.congr
  exact Eventually.of_forall (fun p => perturbed_arithmetic_profile_eq_source η S hS.prime J T b W0 W1 X Y Z _ _ _)

lemma perturbed_outer_height_ne_zero_ae : ∀ᵐp : HeightSpace ∂heightMeasure, p.1.1≠0 := by
  have hh : ∀ᵐp : ℝ×ℝ ∂volume.prod volume, p.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  exact Measure.quasiMeasurePreserving_fst.ae hh

lemma perturbed_continued_joint_ae_raw {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S, Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z a ξ υ : ℝ) :
    (fun p : HeightSpace => continuedSourceMultiplier η S hS J T b W0 W1 X Y Z
      ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) =ᵐ[heightMeasure]
    (fun p : HeightSpace => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS)
      ((a:ℂ)+p.1.1*I) (globalClosedCorrection η S ((a:ℂ)+p.1.1*I))
      (slotMultiplier η J T b ((a:ℂ)+p.1.1*I)) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)) := by
  filter_upwards [perturbed_outer_height_ne_zero_ae] with p hp
  apply perturbed_continued_source_eq_raw
  · intro h; exact hp (by simpa using congrArg Complex.im h)
  · intro h; exact hp (by simpa using congrArg Complex.im h)

theorem perturbed_source_joint_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)) heightMeasure := by
  apply (perturbed_continued_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1).congr
  filter_upwards [perturbed_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z a ξ υ] with p hp
  rw [hp]

theorem perturbed_source_joint_fubini {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    let F := fun p : HeightSpace =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((a:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((a:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
      LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
      LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)
    ((∫p, F p ∂heightMeasure)=∫t : ℝ,∫v : ℝ,∫u : ℝ,F ((t,v),u)) ∧
    ((∫p, F p ∂heightMeasure)=∫u : ℝ,∫v : ℝ,∫t : ℝ,F ((t,v),u)) := by
  dsimp only
  have hi := perturbed_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  constructor
  · rw [integral_prod _ hi]
    exact integral_prod _ hi.integral_prod_left
  · rw [integral_prod_symm _ hi]
    apply integral_congr_ae
    filter_upwards [hi.prod_left_ae] with u hu
    exact integral_prod_symm _ hu

lemma perturbed_arithmeticAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ)
    (X Y Z a Bs Bz cw C δw δz : ℝ) (hcw : 1< cw) (hC : 0≤ C) (hw : 0≤δw) (hz : 0≤δz) :
    0≤ arithmeticAmplitude S J T b X Y Z a Bs Bz cw C δw δz := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hbox := (perturbed_boxScale_pos X Y Z a Bs Bz cw).le
  have hb := perturbed_slotBound_nonneg J T b Bs Bz
  have hza := perturbed_zBoxAmplitude_nonneg (∏P∈S,P) Bz
  have hwa := (wAmplitude_pos (∏P∈S,P) hcw).le
  unfold arithmeticAmplitude
  positivity

theorem perturbed_continued_source_slices {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
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
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ υ υ (by linarith) 8 N
  refine ⟨C,K,hC,hK,?_⟩
  intro axis R
  let G : HeightSpace → ℂ := fun p => arithmeticMultiplier η S hS.prime J T b X Y Z
    ((a:ℂ)+p.1.1*I) ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I)
  have hm := perturbed_arithmetic_onLines_measurable η S hS.prime J T b X Y Z a ξ υ hX hY hZ hβ
    (by linarith) hξ1 (by linarith [hυ.1]) hυ1
  have hbound := perturbed_arithmetic_onLines_bound η S hS J T b hT X Y Z a a ξ cw a ξ υ C hX hY hZ ha
    ⟨le_rfl,le_rfl⟩ ⟨hξ,le_rfl⟩ hcw hυ hξ1 hυ1 hC hR
  have hh := hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩ axis R
    (arithmeticAmplitude S J T b X Y Z a a ξ cw C |υ-1| |6*ξ-1|)
    (perturbed_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a a ξ cw C _ _ hcw hC (abs_nonneg _) (abs_nonneg _))
    (fun q => G (sliceMap axis R q)) ((hm.comp (sliceMap_continuous axis R).measurable).aestronglyMeasurable)
    (fun q => hbound (sliceMap axis R q))
  simpa only [G,onLines,perturbed_arithmetic_profile_eq_source] using hh

theorem perturbed_source_w_leftover_outer_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (he : 0< e)
    (hs1 : (a:ℂ)+t*I≠1) :
    let s : ℂ := (a:ℂ)+t*I
    let K := sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    Integrable (fun v : ℝ => verticalIntegral (19/20) (fun w =>
      K w ((1/6+e:ℝ)+v*I)*LFunction (fixedSourcePrincipal S hS.prime)
        (6*((1/6+e:ℝ)+v*I))*LFunction (fixedSourcePrincipal S hS.prime) w)) := by
  obtain ⟨C,K,hC,hK,hslice⟩ := perturbed_continued_source_slices η S hS J T b hT W0 W1 a0 b0 a1 b1
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
    simpa only [sliceMap,perturbed_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ hs0 hs1] using hi
  simpa only [verticalIntegral] using hpair.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem perturbed_source_z_boundary_any {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 : ℝ) (ha0 : 0< a0)
    (hW0 : Function.support W0⊆Icc a0 b0) (X Y Z : ℝ) (hX : 0< X) (hZ : 0< Z)
    (s : ℂ) (hs : 34999/40000≤ s.re) (hη : LFunction (η.excludePrimes S hS.prime) s≠0)
    {e : ℝ} (he : 0< e) :
    BoundaryControl (fun z => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) s
      (globalClosedCorrection η S s) (slotMultiplier η J T b s) 1 z *
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)) (33/200) (1/6+e) := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  apply ProbeMellinBoundary.source_z_boundary W0 W1 a0 b0 ha0 hW0 (∏P∈S,P)
    X Y Z hX hZ (η.excludePrimes S hS.prime) s hη
    (globalClosedCorrection η S s) (slotMultiplier η J T b s)
    (AH := (3/2)*slotBound J T b s.re (1/6+e)) (AL := zBoxAmplitude (∏P∈S,P) (1/6+e))
    he (mul_nonneg (by norm_num) (perturbed_slotBound_nonneg J T b _ _))
    (perturbed_zBoxAmplitude_nonneg _ _) 0 3
  · exact (perturbed_combined_slot_analytic_z η S hS.tail J T b hT s 1 hs (by norm_num)).continuousOn.mono
      (by intro z hz; change (4/25:ℝ)< z.re; linarith [hz.1])
  · intro x hx t _
    simpa only [pow_zero,mul_one] using perturbed_combined_slot_bound η S hS.tail J T b hT s
      1 ((x:ℂ)+t*I) s.re (1/6+e) ⟨hs,le_rfl⟩ (by norm_num) (by simpa using hx)
  · intro x hx t _
    exact perturbed_fixed_principal_z_box_growth (∏P∈S,P) (1/6+e) x t hx

theorem perturbed_source_ordered_at_height {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e t cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e)
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
  dsimp only
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hs : (34999/40000 : ℝ)≤(((a:ℂ)+t*I) : ℂ).re := by simpa using ha
  have hη := HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt (η.excludePrimes S hS.prime)
    (show HeckeZeroSupremum.beta<(((a:ℂ)+t*I) : ℂ).re by simpa using hβ) (Or.inl hs1)
  have hzb := perturbed_source_z_boundary_any η S hS J T b hT W0 W1 a0 b0 ha0 hW0 X Y Z hX hZ
    ((a:ℂ)+t*I) hs hη he
  apply source_ordered_double_shift (fixedSourcePrincipal S hS.prime) _ hcw he
  · intro z hz
    apply (perturbed_source_multiplier_differentiable_w η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith)).mono
    intro w hw
    change (9/10 : ℝ)< w.re
    linarith [hw.1]
  · intro z hz
    have hh := perturbed_source_w_boundary η S hS J T b hT W0 W1 a1 b1 ha1 hW1
      (∏P∈S,P) X Y Z hY ((a:ℂ)+t*I) z hs (by rw [hz]; linarith) hη hcw
    convert perturbed_boundary_mul_const _ _ _ hh (LFunction (fixedSourcePrincipal S hS.prime) (6*z)) using 1
    funext w
    dsimp only [fixedSourcePrincipal,fixedPrincipal]
    ring
  · apply (perturbed_source_multiplier_differentiable_z η S hS J T b hT W0 W1 X Y Z hX hZ
      ((a:ℂ)+t*I) 1 hs (by norm_num)).mono
    intro z hz
    change (4/25 : ℝ)< z.re
    linarith [hz.1]
  · exact hzb
  · exact perturbed_source_w_leftover_outer_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a e t hX hY hZ ha hβ he hs1

theorem perturbed_source_ordered_ae {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
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
  filter_upwards [Measure.ae_ne volume (0:ℝ)] with t ht
  apply perturbed_source_ordered_at_height η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a e t cw hX hY hZ ha hβ hcw he
  intro h
  exact ht (by simpa using congrArg Complex.im h)

lemma perturbed_residue_profile_eq_source {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (s z : ℂ) :
    residueArithmetic η S hS J T b X Z s z*profile W0 W1 s 1 z =
      continuedSourceMultiplier η S hS J T b W0 W1 X Y Z s 1 z *
        LFunction (fixedSourcePrincipal S hS) (6*z) := by
  unfold residueArithmetic profile continuedSourceMultiplier
  simp only [sub_self,Complex.cpow_zero,mul_one]
  ring

lemma perturbed_residue_arithmetic_measurable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : ∀P∈S,Prime P) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (hβ : HeckeZeroSupremum.beta< a) (hξ0 : ξ≠0) (hξ1 : 6*ξ≠1) :
    Measurable (fun q : ℝ×ℝ => residueArithmetic η S hS J T b X Z
      ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)) := by
  have hH := perturbed_global_correction_measurable η S (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hB := perturbed_slot_multiplier_measurable η J T b (fun q : ℝ×ℝ => (a:ℂ)+q.1*I)
    (fun _ : ℝ×ℝ => (1:ℂ)) (fun q : ℝ×ℝ => (ξ:ℂ)+q.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  have hR := (perturbed_reciprocal_vertical_continuous (η.excludePrimes S hS) a hβ).measurable.comp
    (by fun_prop : Measurable (fun q : ℝ×ℝ => q.1))
  have hL := (perturbed_LFunction_vertical_continuous (fixedSourcePrincipal S hS) (6*ξ)
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

lemma perturbed_residue_arithmetic_bound {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (X Z a ξ C : ℝ) (hX : 0< X) (hZ : 0< Z) (ha : 34999/40000≤ a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1)
    (hC : 0≤ C) (hR : ∀s : ℂ,a≤ s.re→‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) s‖≤ C*(1+|s.im|^2))
    (q : ℝ×ℝ) :
    ‖residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)‖≤
      residueAmplitude S J T b X Z a ξ C*jointHeight q.1 q.2 0^5 := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  have hr : ‖HeckeReciprocal.reciprocal (η.excludePrimes S hS.prime) ((a:ℂ)+q.1*I)‖≤ C*height q.1^2 := by
    apply (hR _ (by simp)).trans
    simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add]
    apply mul_le_mul_of_nonneg_left _ hC
    unfold height
    nlinarith [abs_nonneg q.1]
  have hh := perturbed_combined_slot_bound η S hS.tail J T b hT ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I) a ξ
    (by simpa using ha) (by norm_num) (by simpa using hξ)
  have hL := perturbed_fixed_principal_z_bound (∏P∈S,P) ξ ξ q.2 ⟨hξ,le_rfl⟩ hξ1
  have hX0 := (Real.rpow_pos_of_pos hX (1/2-ξ)).le
  have hZ0 := (Real.rpow_pos_of_pos hZ (a+ξ-1)).le
  have hHB := mul_nonneg (by norm_num : (0:ℝ)≤3/2) (perturbed_slotBound_nonneg J T b a ξ)
  have hA := div_nonneg (perturbed_zBoxAmplitude_nonneg (∏P∈S,P) ξ) (abs_nonneg (6*ξ-1))
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
      gcongr <;> first | positivity | exact perturbed_height_le_joint_s _ _ _ | exact perturbed_height_le_joint_z _ _ _
    _ = _ := by unfold residueAmplitude; ring

lemma perturbed_residueAmplitude_nonneg {ι : Type*} (S : Finset Id) (hS : ∀P∈S,Prime P)
    (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal) (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (X Z a ξ C : ℝ)
    (hX : 0≤ X) (hZ : 0≤ Z) (hC : 0≤ C) : 0≤ residueAmplitude S J T b X Z a ξ C := by
  let : NeZero (∏P∈S,P) := ⟨fixedPrimeProduct_ne_zero S hS⟩
  have hb := perturbed_slotBound_nonneg J T b a ξ
  have hza := perturbed_zBoxAmplitude_nonneg (∏P∈S,P) ξ
  unfold residueAmplitude
  positivity

theorem perturbed_continued_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => continuedSourceMultiplier η S hS.prime J T b W0 W1 X Y Z
      ((a:ℂ)+q.1*I) 1 ((ξ:ℂ)+q.2*I)*
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  obtain ⟨C,hC,hR⟩ := HeckeReciprocalGrowth.polynomial_reciprocal_bound (η.excludePrimes S hS.prime) a hβ
  obtain ⟨K,hK,hk⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    a a ξ ξ 1 1 (by linarith) 5 0
  have hm := perturbed_residue_arithmetic_measurable η S hS.prime J T b X Z a ξ hX hZ hβ (by linarith) hξ1
  have hb := perturbed_residue_arithmetic_bound η S hS J T b hT X Z a ξ C hX hZ ha hξ hξ1 hC hR
  have hh := (hk a ⟨le_rfl,le_rfl⟩ ξ ⟨le_rfl,le_rfl⟩ 1 ⟨le_rfl,le_rfl⟩ .w 0
    (residueAmplitude S J T b X Z a ξ C)
    (perturbed_residueAmplitude_nonneg S hS.prime J T b X Z a ξ C hX.le hZ.le hC)
    (fun q : ℝ×ℝ => residueArithmetic η S hS.prime J T b X Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I))
    hm.aestronglyMeasurable hb).1
  apply hh.congr
  apply Eventually.of_forall
  intro q
  simpa only [sliceMap,onLines,ofReal_one,ofReal_zero,zero_mul,add_zero] using
    perturbed_residue_profile_eq_source η S hS.prime J T b W0 W1 X Y Z ((a:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I)

theorem perturbed_residue_pair_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun q : ℝ×ℝ => sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime)
      ((a:ℂ)+q.1*I) (globalClosedCorrection η S ((a:ℂ)+q.1*I)) (slotMultiplier η J T b ((a:ℂ)+q.1*I))
      1 ((ξ:ℂ)+q.2*I)*LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+q.2*I))) (volume.prod volume) := by
  apply (perturbed_continued_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1).congr
  have hh : ∀ᵐq : ℝ×ℝ ∂volume.prod volume,q.1≠0 :=
    Measure.quasiMeasurePreserving_fst.ae (Measure.ae_ne volume (0:ℝ))
  filter_upwards [hh] with q hq
  have h0 : (a:ℂ)+q.1*I≠0 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  have h1 : (a:ℂ)+q.1*I≠1 := by intro h; exact hq (by simpa using congrArg Complex.im h)
  rw [perturbed_continued_source_eq_raw η S hS.prime J T b W0 W1 X Y Z _ _ _ h0 h1]

theorem perturbed_source_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ υ cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ)
    (hcw : 1< cw) (hυ : υ∈Icc (19/20 : ℝ) cw) (hξ1 : 6*ξ≠1) (hυ1 : υ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z => verticalIntegral υ (fun w =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) w z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z)*LFunction (fixedSourcePrincipal S hS.prime) w))) := by
  have hi := perturbed_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ υ cw hX hY hZ ha hβ hξ hcw hυ hξ1 hυ1
  simpa only [verticalIntegral,integral_const_mul,mul_assoc] using
    (hi.integral_prod_left.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))).const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem perturbed_residue_iterated_integrable {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a ξ : ℝ) (hX : 0< X) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hξ : 33/200≤ξ) (hξ1 : 6*ξ≠1) :
    Integrable (fun t : ℝ => verticalIntegral ξ (fun z =>
      sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((a:ℂ)+t*I)
        (globalClosedCorrection η S ((a:ℂ)+t*I)) (slotMultiplier η J T b ((a:ℂ)+t*I)) 1 z *
        LFunction (fixedSourcePrincipal S hS.prime) (6*z))) := by
  have hi := perturbed_residue_pair_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z a ξ hX hZ ha hβ hξ hξ1
  simpa only [verticalIntegral] using hi.integral_prod_left.const_mul (((1/(2*Real.pi):ℝ):ℂ))

theorem perturbed_source_ordered_outer {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z a e cw : ℝ) (hX : 0< X) (hY : 0< Y) (hZ : 0< Z)
    (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (he : 0< e) :
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
    perturbed_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) cw cw hX hY hZ ha hβ (by linarith) hcw ⟨by linarith,le_rfl⟩
      (by linarith) (ne_of_gt hcw)
  have hB : Integrable (fun t : ℝ => B ((a:ℂ)+t*I)) :=
    perturbed_source_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (1/6+e) (19/20) cw hX hY hZ ha hβ (by linarith) hcw ⟨le_rfl,by linarith⟩
      (by linarith) (by norm_num)
  have hD : Integrable (fun t : ℝ => D ((a:ℂ)+t*I)) :=
    (perturbed_residue_iterated_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z a (33/200) hX hZ ha hβ le_rfl (by norm_num)).const_mul R
  have hp : ∀ᵐt : ℝ,A ((a:ℂ)+t*I)=B ((a:ℂ)+t*I)+D ((a:ℂ)+t*I)+E ((a:ℂ)+t*I) :=
    perturbed_source_ordered_ae η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
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

theorem perturbed_source_initial_ordered {ι : Type*} (η : Character) (S : Finset Id)
    (hS : SourceExclusions S) (J : Finset ι) (T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)
    (b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ) (hT : ∀j∈J,∀P∈T j,P.val∉S)
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
  simpa only [show (1/6+11/6:ℝ)=2 by norm_num] using
    perturbed_source_ordered_outer η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
      X Y Z 3 (11/6) 3 hX hY hZ (by norm_num)
      (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num) (by norm_num)

theorem perturbed_source_uniform_joint_tails {ι : Type*}
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (a Bs Bz cw : ℝ) (ha : 34999/40000≤ a) (hβ : HeckeZeroSupremum.beta< a) (hcw : 1< cw) (N : ℕ) :
    ∃ K : ℝ,0< K ∧ ∀(η : Character)(S : Finset Id)(hS : SourceExclusions S)
      (J : Finset ι)(T : ι → Finset OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal)(b : ι → OAI.SevenEighths.HeckeInverseAmplification.PrimeIdeal → ℂ),
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
  have hA : 0≤ A := perturbed_arithmeticAmplitude_nonneg S hS.prime J T b X Y Z a Bs Bz cw C _ _ hcw hC
    (abs_nonneg _) (abs_nonneg _)
  have hi := perturbed_source_joint_integrable η S hS J T b hT W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z σ ξ υ cw hX hY hZ (ha.trans hσ.1) (hβ.trans_le hσ.1) hξ.1 hcw hυ hξ1 hυ1
  have hmi := (hm σ hσ ξ hξ υ hυ).1
  have hbound := perturbed_arithmetic_onLines_bound η S hS J T b hT X Y Z a Bs Bz cw σ ξ υ C hX hY hZ
    ha hσ hξ hcw hυ hξ1 hυ1 hC hR
  have hdom : ∀ᵐp : HeightSpace ∂heightMeasure,
      ‖sourceMultiplier W0 W1 X Y Z (η.excludePrimes S hS.prime) ((σ:ℂ)+p.1.1*I)
        (globalClosedCorrection η S ((σ:ℂ)+p.1.1*I)) (slotMultiplier η J T b ((σ:ℂ)+p.1.1*I))
        ((υ:ℂ)+p.2*I) ((ξ:ℂ)+p.1.2*I) *
        LFunction (fixedSourcePrincipal S hS.prime) (6*((ξ:ℂ)+p.1.2*I)) *
        LFunction (fixedSourcePrincipal S hS.prime) ((υ:ℂ)+p.2*I)‖ ≤
      A*(jointHeight p.1.1 p.1.2 p.2^8*‖onLines W0 W1 σ ξ υ p‖) := by
    filter_upwards [perturbed_continued_joint_ae_raw η S hS.prime J T b W0 W1 X Y Z σ ξ υ] with p hp
    rw [←hp,←perturbed_arithmetic_profile_eq_source]
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

lemma perturbed_LFunction_measurable (χ : Character) : Measurable (LFunction χ) := by
  classical
  have hm := ((HeckeOrigin.poleRemoved_entire χ).continuous.measurable).div
    (measurable_id.sub_const (1:ℂ))
  have h1 : Measurable (fun s : ℂ => if s=1 then LFunction χ 1 else HeckeOrigin.poleRemoved χ s/(s-1)) :=
    Measurable.ite (measurableSet_singleton (1:ℂ))
