end SevenEighths.CenteredMomentOriginalReflectionErrorMass

end

end OAI
end OAIOriginalModule2195

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RetainedWeightedSource
Source SHA256: a3096f19636f78b7eafecd3288c7def52a9f3c360ccdb6cc81e1ecb001132105
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2196




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentRetainedWeightedSource
open HeckeFamily CenteredMomentNaturalPrimitive CenteredMomentReflectionDeletion
open CenteredMomentReflectionMass CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentReflectedNormalization
open CenteredMomentReflectedAnnuli CenteredMomentReflectedTruncation
open CenteredMomentReflectedUniformPair CenteredMomentSectorLocalization
open EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

abbrev sourcePrimes (χ ψ : Character) := redundantSet χ.modulus ψ.modulus

def dualScale (χ ψ : Character) (X : ℝ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) : ℝ :=
  (ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D.val,P):ℝ)/(X*norm H.val)

lemma dualScale_pos (χ ψ : Character) (X : ℝ) (hX : 0<X)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    0<dualScale χ ψ X D H := by
  have hD : (∏P∈D.val,P : Ideal O)≠0 := Finset.prod_ne_zero_iff.mpr (fun P hP=>
    (redundantSet_prime χ.modulus ψ.modulus P ((Finset.mem_powerset.mp D.property) hP)).ne_zero)
  have hQ : 0<(ψ.modulus.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr ψ.modulus_ne_bot)
  have hd : 0<(Ideal.absNorm (∏P∈D.val,P):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD)
  exact div_pos (mul_pos hQ hd) (mul_pos hX (CenteredMomentReflectionDeletion.norm_pos H.val))

def retainedColumn (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ)) : ℂ :=
  if a.2∈retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2) then
    HeckeDyadic.polynomial χ.inverse false
      (normalizedReflected CenteredMomentReflectedAnnuli.logWindow W B n (dyadicScale a.2) t)
      (dyadicScale a.2*dualScale χ ψ X a.1.1 a.1.2) 0 0 * P
  else 0

lemma retainedColumn_zero (χ ψ : Character) (W : ℝ→ℂ) (X R t : ℝ) (hX : 0<X)
    (B n : ℕ) (P : ℂ) (a : Index (sourcePrimes χ ψ))
    (ha : a.2∉retainedAnnuli R (dualScale χ ψ X a.1.1 a.1.2)
      (dualScale_pos χ ψ X hX a.1.1 a.1.2)) :
    retainedColumn χ ψ W X R t hX B n P a=0 := by
  simp only [retainedColumn,ite_eq_right ha]

theorem finiteAnnularColumn_normalized (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (D : (sourcePrimes χ ψ).powerset) (H : SmoothIdeal (sourcePrimes χ ψ)) :
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H)*P =
    (((1+‖t‖)^n:ℝ):ℂ)*∑'k : ℤ,(annularMass B k:ℂ)*
      retainedColumn χ ψ W X R t hX B n P ((D,H),k) := by
  rw [finiteAnnularColumn,dite_eq_left (dualScale_pos χ ψ X hX D H),
    tsum_eq_sum (s:=retainedAnnuli R (dualScale χ ψ X D H) (dualScale_pos χ ψ X hX D H))
      (fun k hk=>by simp only [retainedColumn,ite_eq_right hk,mul_zero]),
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [retainedColumn,ite_eq_left hk,actual_annular_normalization]
  ring

theorem retainedOriginal_eq_weighted (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖)) :
    retainedOriginal χ ψ W X R t*P =
      (((1+‖t‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes χ ψ),
        signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
          retainedColumn χ ψ W X R t hX B n P a := by
  rw [signed_series_reindex ψ ψ.inverse (sourcePrimes χ ψ) B _ hs]
  change (∑D∈(sourcePrimes χ ψ).powerset,∑'H : SmoothIdeal (sourcePrimes χ ψ),
    coefficient ψ ψ.inverse (sourcePrimes χ ψ) D H*
      finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
        R ((ψ.modulus.absNorm:ℝ)*(Ideal.absNorm (∏P∈D,P):ℝ)/(X*norm H.val)))*P = _
  rw [←Finset.sum_coe_sort (sourcePrimes χ ψ).powerset,
    Finset.sum_mul,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro D _
  rw [←tsum_mul_right,←tsum_mul_left]
  apply tsum_congr
  intro H
  change (coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
    finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
      R (dualScale χ ψ X D H))*P = _
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [mul_assoc,tsum_mul_left]
  ring

theorem retainedOriginal_fiber_summable (χ ψ : Character) (W : ℝ→ℂ)
    (X R t : ℝ) (hX : 0<X) (B n : ℕ) (P : ℂ)
    (hs : Summable (fun a : Index (sourcePrimes χ ψ)=>
      ‖signedWeight ψ ψ.inverse (sourcePrimes χ ψ) B a*
        retainedColumn χ ψ W X R t hX B n P a‖))
    (D : (sourcePrimes χ ψ).powerset) :
    Summable (fun H : SmoothIdeal (sourcePrimes χ ψ)=>
      ‖(coefficient ψ ψ.inverse (sourcePrimes χ ψ) D.val H*
        finiteAnnularColumn χ.inverse (paperRadialFourier (CompletedHeight.normTwistedSource W t))
          R (dualScale χ ψ X D H))*P‖) := by
  have hh := ((hs.of_norm.prod.prod_factor D).mul_left (((1+‖t‖)^n:ℝ):ℂ)).norm
  apply hh.congr
  intro H
  congr 1
  rw [mul_assoc,finiteAnnularColumn_normalized χ ψ W X R t hX B n P D H]
  simp only [signedWeight,mul_assoc,tsum_mul_left]
  ring

theorem actual_retained_weighted_energy (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*} [Fintype ι],
      ∀(χ ψ : ι→Character)(W : ι→ℝ→ℂ)(X R t : ι→ℝ)
        (hX : ∀i,0<X i)(B : ι→ℕ)(n : ℕ)(P : ι→ℂ),
      (∀i,2≤B i) → ∀(T Rcap E : ℝ),0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀a : ∀i,Index (sourcePrimes (χ i) (ψ i)),
        (∑i,‖retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) (a i)‖^2)≤E) →
      (∀i,Summable (fun a : Index (sourcePrimes (χ i) (ψ i))=>
        ‖signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
          retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a‖)) ∧
      (∀i,retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i =
        (((1+‖t i‖)^n:ℝ):ℂ)*∑'a : Index (sourcePrimes (χ i) (ψ i)),
          signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*
            retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i) a) ∧
      (∀i,∀D : (sourcePrimes (χ i) (ψ i)).powerset,
        Summable (fun H : SmoothIdeal (sourcePrimes (χ i) (ψ i))=>
          ‖(coefficient (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) D.val H*
            finiteAnnularColumn (χ i).inverse
              (paperRadialFourier (CompletedHeight.normTwistedSource (W i) (t i)))
              (R i) (dualScale (χ i) (ψ i) (X i) D H))*P i‖)) ∧
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2) ≤
        C*Rcap^ε*(1+T)^(2*n)*E := by
  obtain ⟨C,hC,hbound⟩ := actual_reflection_energy ε hε
  refine ⟨C,hC,?_⟩
  intro ι _ χ ψ W X R t hX B n P hB T Rcap E hT ht hRcap hcap hselection
  let f (i : ι) := retainedColumn (χ i) (ψ i) (W i) (X i) (R i) (t i) (hX i) (B i) n (P i)
  have he := hbound (fun i=>sourcePrimes (χ i) (ψ i))
    (fun i=>redundantSet_prime (χ i).modulus (ψ i).modulus) ψ (fun i=>(ψ i).inverse)
    B hB Rcap E hRcap hcap f hselection
  have hid (i : ι) := retainedOriginal_eq_weighted (χ i) (ψ i) (W i) (X i) (R i) (t i)
    (hX i) (B i) n (P i) (he.1 i)
  refine ⟨he.1,hid,?_,?_⟩
  · intro i D
    exact retainedOriginal_fiber_summable (χ i) (ψ i) (W i) (X i) (R i) (t i)
      (hX i) (B i) n (P i) (he.1 i) D
  · let z (i : ι) := ∑'a : Index (sourcePrimes (χ i) (ψ i)),
        signedWeight (ψ i) (ψ i).inverse (sourcePrimes (χ i) (ψ i)) (B i) a*f i a
    have hn (i : ι) :
        ‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖=(1+‖t i‖)^n*‖z i‖ := by
      rw [hid i,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
    have hp (i : ι) : (1+‖t i‖)^n≤(1+T)^n :=
      pow_le_pow_left₀ (by positivity) (by linarith [ht i]) n
    calc
      (∑i,‖retainedOriginal (χ i) (ψ i) (W i) (X i) (R i) (t i)*P i‖^2)
          = ∑i,((1+‖t i‖)^n*‖z i‖)^2 := by simp_rw [hn]
      _ ≤ ∑i,((1+T)^n*‖z i‖)^2 := by
        apply Finset.sum_le_sum
        intro i _
        exact pow_le_pow_left₀ (by positivity)
          (mul_le_mul_of_nonneg_right (hp i) (norm_nonneg _)) 2
      _ = ((1+T)^n)^2*∑i,‖z i‖^2 := by simp only [mul_pow,Finset.mul_sum]
      _ ≤ ((1+T)^n)^2*(C*Rcap^ε*E) := mul_le_mul_of_nonneg_left he.2 (sq_nonneg _)
      _ = C*Rcap^ε*(1+T)^(2*n)*E := by rw [←pow_mul,Nat.mul_comm n 2];ring

end SevenEighths.CenteredMomentRetainedWeightedSource

end

end OAI
end OAIOriginalModule2196

/-! Original module: OAI.NumberTheory.DirichletL.Moments.RetainedComparisonEnergy
Source SHA256: 7a24ae6bae9c710916e5d648f58c26091daf3b202cba534ab7a1c9853d5b2f06
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2197



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentRetainedComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentReflectedChoiceEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectionWeightedEnergy CenteredMomentReflectedTruncation
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_retained_fixed_profile_energy (a b epsilon : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (B J : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀{ι : Type}[Fintype ι],
      ∀(χ ψ : ι→Character)(P : ι→ℂ)(X R t ly omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d lo hi low high E T Rcap : ℝ),
      (∀i,0<X i) → 0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      lo≤hi → low≤high → (∀i,ly i∈Set.Icc low high) →
      (∀i (u : Index (sourcePrimes (χ i) (ψ i))),
        ∀hY : 0<dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2,
        u.2∈retainedAnnuli (R i) (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) hY →
        Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2)∈Set.Icc lo hi) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,(Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc lo hi,∀y∈Set.Icc low high,
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Real.exp y) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (X i) (R i) (t i)*
        polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(hi-lo))*(1+2*(high-low))*E := by
  obtain ⟨n,hn⟩ := actual_independent_profile_choices a b ha B J
  obtain ⟨Cw,hCw,hw⟩ := actual_retained_weighted_energy epsilon hepsilon
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨Cp,hCp,hp⟩ := hn Wlong hs hW
  refine ⟨Cw*Cp,mul_pos hCw hCp,?_⟩
  intro ι _ χ ψ P X R t ly omega Wshort c d lo hi low high E T Rcap
    hX hd hshort hshortsmooth hlh hlw hly hgeom hE hT ht hRcap hcap henergy
  let α (i : ι) := Index (sourcePrimes (χ i) (ψ i))
  let s (i : ι) (u : α i) := dyadicScale u.2
  let Y (i : ι) (u : α i) := s i u*dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2
  let keep (i : ι) (u : α i) := u.2∈retainedAnnuli (R i)
    (dualScale (χ i) (ψ i) (X i) u.1.1 u.1.2) (dualScale_pos _ _ _ (hX i) _ _)
  have hchoice := hp χ P s Y keep t ly omega Wshort c d lo hi low high E
    hd hshort hshortsmooth hlh hlw hly
    (fun i u=>dyadicScale_pos u.2)
    (fun i u hu=>⟨mul_pos (dyadicScale_pos u.2) (dualScale_pos _ _ _ (hX i) _ _),
      hgeom i u _ hu⟩) hE henergy
  let P' (i : ι) := polynomial (χ i) false Wshort (Real.exp (ly i)) 0 (omega i)*P i
  have hselected (u : ∀i,α i) :
      (∑i,‖retainedColumn (χ i) (ψ i) Wlong (X i) (R i) (t i) (hX i) B n (P' i) (u i)‖^2)≤
        Cp*(1+2*(hi-lo))*(1+2*(high-low))*E := by
    simpa only [retainedColumn,P',Y,s,keep,mul_assoc] using hchoice u
  have hh := hw χ ψ (fun _=>Wlong) X R t hX (fun _=>B) n P' (fun _=>hB)
    T Rcap _ hT ht hRcap hcap hselected
  have hfinal := hh.2.2.2
  simp only [P',←mul_assoc] at hfinal
  convert hfinal using 1 ; ring

end SevenEighths.CenteredMomentRetainedComparisonEnergy

end

end OAI
end OAIOriginalModule2197

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalRetainedEnergy
Source SHA256: 883a4a0c0c86d80b5648f811a8d727d2b71b5bc836d4376fdfa711a55dd4d123
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2198


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentNaturalRetainedEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum CenteredMomentNaturalPrimitive
open CenteredMomentRetainedComparisonEnergy CenteredMomentRetainedWeightedSource
open CenteredMomentReflectedChoiceEnergy CenteredMomentReflectionWeightedEnergy
open CenteredMomentOriginalReflectionApproximation CenteredMomentSectorLocalization

theorem actual_natural_retained_energy (a b epsilon Cscale xi : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C : ℝ,0<C ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ ψ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      (∀i,(ψ i).modulus.absNorm*(redundantIdeal (χ i).modulus (ψ i).modulus).absNorm≤(χ i).modulus.absNorm) →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖retainedOriginal (χ i) (ψ i) Wlong (Z^along) (Z^(xi/4)) (t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E := by
  obtain ⟨n,hn⟩ := actual_retained_fixed_profile_energy a b epsilon ha hepsilon B J hB
  refine ⟨n,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hb⟩ := hn Wlong hs hW
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_natural_choice_geometry Cscale xi hscale hxi] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ ψ P t omega Wshort c d M along bshort E T Rcap hd hshort hshortsmooth
    hnatural hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  have hlog : 0≤Real.log Z := (Real.log_pos hZ.1).le
  have hexp : Real.exp (bshort*Real.log Z)=Z^bshort := by
    rw [Real.rpow_def_of_pos hz,mul_comm]
  have hgeom (i : ι) (u : Index (sourcePrimes (χ i) (ψ i)))
      (hY : 0<dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)
      (hu : u.2∈CenteredMomentReflectedTruncation.retainedAnnuli (Z^(xi/4))
        (dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2) hY) :
      Real.log (dyadicScale u.2*dualScale (χ i) (ψ i) (Z^along) u.1.1 u.1.2)∈
        Set.Icc 0 (max 0 (M-along+xi)*Real.log Z) := by
    have hh := hZ.2 (χ i) (ψ i) M along (hnatural i) (hmod i) u hY hu
    exact ⟨hh.2.1,hh.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hlog)⟩
  have hrad (i : ι) : (Ideal.absNorm (∏Q∈sourcePrimes (χ i) (ψ i),Q):ℝ)≤Rcap :=
    (radical_le_original (χ i) (ψ i) (hnatural i)).trans (hcap i)
  have hh := hb χ ψ P (fun _=>Z^along) (fun _=>Z^(xi/4)) t (fun _=>bshort*Real.log Z) omega
    Wshort c d 0 (max 0 (M-along+xi)*Real.log Z) (bshort*Real.log Z) (bshort*Real.log Z)
    E T Rcap (fun _=>Real.rpow_pos_of_pos hz _) hd hshort hshortsmooth
    (mul_nonneg (le_max_left _ _) hlog) le_rfl (fun _=>⟨le_rfl,le_rfl⟩) hgeom
    hE hT ht hRcap hrad (by
      intro v j k x hx y hy
      have hey : y=bshort*Real.log Z := le_antisymm hy.2 hy.1
      simpa only [hey,hexp] using henergy v j k x hx)
  simpa only [hexp,sub_zero,sub_self,mul_zero,add_zero,mul_one] using hh

end SevenEighths.CenteredMomentNaturalRetainedEnergy

end

end OAI
end OAIOriginalModule2198

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OriginalComparisonEnergy
Source SHA256: 809f12da392f4461638971c7873a5458205f6120df2db56be930184a088c7dbf
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2199



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalComparisonEnergy
open HeckeFamily HeckeDyadic CenteredMomentScaleSupremum
open CenteredMomentNaturalRetainedEnergy CenteredMomentOriginalReflectionEnergy
open CenteredMomentSectorLocalization

theorem actual_original_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0<a) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀{ι : Type}[Fintype ι],∀(χ : ι→Character)(P : ι→ℂ)(t omega : ι→ℝ)
        (Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      (∀i,(χ i).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀i,((χ i).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀i,‖t i‖≤T) → 1≤Rcap →
      (∀i,((χ i).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        (∑i,‖polynomial (χ i) false (scaleTest (fun z : ℝ=>(annulus z:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ i) false (scaleTest Wshort k) (Z^bshort) 0 (omega i)*P i‖^2)
          ≤E*(1+‖v‖)^(2*J)) →
      (∑i,‖polynomial (χ i) false Wlong (Z^along) 0 (2*Real.pi*t i)*
        polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2)≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          (∑i,‖polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i‖^2) := by
  obtain ⟨n,hn⟩ := actual_natural_retained_energy a b epsilon Cscale xi ha hepsilon hscale hxi B J hB
  obtain ⟨ne,hne⟩ := actual_original_energy_to_retained a b (xi/2) saving L Cscale epsilon
    ha (by positivity) hscale hepsilon
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,hC,hr⟩ := hn Wlong hs hW
  obtain ⟨D,hD,ho⟩ := hne Wlong hs hW
  refine ⟨2*C,D,by positivity,hD,?_⟩
  filter_upwards [hr] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro ι _ χ P t omega Wshort c d M along bshort E T Rcap hχ hd hshort hshortsmooth
    hML hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z := by linarith [hZ.1]
  obtain ⟨ψ,hψ,horiginal⟩ := ho χ hχ
  let Q (i : ι) := polynomial (χ i) false Wshort (Z^bshort) 0 (omega i)*P i
  have hsource (i : ι) : ((χ i).modulus.absNorm:ℝ)≤Cscale*Z^L*Z^along := by
    have hh := (hmod i).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hZ.1.le hML) hscale.le)
    rw [Real.rpow_add hz] at hh
    simpa only [mul_assoc] using hh
  have he := horiginal (fun _=>Z^along) t Q T Z Rcap hT hZ.1.le hRcap
    (fun _=>Real.rpow_pos_of_pos hz _) ht hcap hsource
  have hcut : (xi/2)/2=xi/4 := by ring
  rw [hcut] at he
  have hretained := hZ.2 χ ψ P t omega Wshort c d M along bshort E T Rcap
    hd hshort hshortsmooth (fun i=>(hψ i).2.2) hmod hE hT ht hRcap hcap henergy
  dsimp only [Q] at he
  simp only [←mul_assoc] at he
  have hh := he.trans (add_le_add (mul_le_mul_of_nonneg_left hretained (by norm_num : (0:ℝ)≤2)) le_rfl)
  convert hh using 1 ; ring

end SevenEighths.CenteredMomentOriginalComparisonEnergy

end

end OAI
end OAIOriginalModule2199

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OriginalRadialComparison
Source SHA256: 73cf7ccff4079321e94cdc40cbffb8371f532936445c85c8e3cfc483b8b5eda8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2200



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
open Filter
namespace SevenEighths.CenteredMomentOriginalRadialComparison
open HeckeFamily HeckeDyadic ConcreteTraceCRT
open CenteredMomentScaleSupremum CenteredMomentSectorLocalization
open CenteredMomentOriginalComparisonEnergy CenteredMomentRadialPolynomialEnergy
local notation "O" => HeckeFamily.O

def radialEnergy (F : O→ℂ) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0

lemma sqrt_weight (a p : ℂ) (u : ℝ) (hu : 0≤u) :
    ‖a*(p*(Real.sqrt u:ℂ))‖^2=‖a*p‖^2*u := by
  rw [←mul_assoc,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt hu]

lemma finite_weighted (rows : Finset O) (keep : O→Prop) (F : O→ℂ)
    (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hΦ : ∀z:O,0≤(Φ (‖eisEmbedding z‖^2/K)).re) :
    (∑z : ↥(rows.filter keep),‖F z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)‖^2)=
    ∑z∈rows,if keep z then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0 := by
  simp_rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _),Real.sq_sqrt (hΦ _)]
  rw [Finset.sum_coe_sort (rows.filter keep) (fun z:O=>‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re),Finset.sum_filter]

theorem actual_original_radial_comparison (a b epsilon Cscale xi saving L : ℝ)
    (ha : 0<a) (_hb : 0≤b) (hepsilon : 0<epsilon) (hscale : 0<Cscale) (hxi : 0<xi)
    (B J : ℕ) (hB : 2≤B) :
    ∃n ne : ℕ,∀Wlong : ℝ→ℂ,Function.support Wlong⊆Set.Icc a b → ContDiff ℝ ∞ Wlong →
      ∃C D : ℝ,0<C ∧ 0<D ∧ ∀ᶠ Z : ℝ in atTop,1<Z ∧
      ∀(χ : O→Character)(P : O→ℂ)(t omega : O→ℝ)(keep : O→Prop)
        (Φ : 𝓢(ℝ,ℂ))(K Pbound : ℝ)(Wshort : ℝ→ℂ)(c d M along bshort E T Rcap : ℝ),
      0<K → (∀z,0≤(Φ (‖eisEmbedding z‖^2/K)).re) → (∀z,‖P z‖≤Pbound) →
      (∀z,keep z → (χ z).residue≠1) →
      0≤d → Function.support Wshort⊆Set.Icc c d → ContDiff ℝ ∞ Wshort →
      M≤L+along → (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Cscale*Z^M) →
      0≤E → 0≤T → (∀z,keep z → ‖t z‖≤T) → 1≤Rcap →
      (∀z,keep z → ((χ z).modulus.absNorm:ℝ)≤Rcap) →
      (∀v : ℝ,∀j k : Fin 2,∀x∈Set.Icc 0 (max 0 (M-along+xi)*Real.log Z),
        radialEnergy (fun z=>polynomial (χ z) false (scaleTest (fun y : ℝ=>(annulus y:ℂ)) j)
          (Real.exp x) 0 (-2*Real.pi*v)*
          polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) keep Φ K
          ≤E*(1+‖v‖)^(2*J)) →
      radialEnergy (fun z=>polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*
        polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K≤
        C*Rcap^epsilon*(1+T)^(2*n)*(1+2*(max 0 (M-along+xi)*Real.log Z))*E+
        D*Rcap^(2*epsilon)*(1+T)^(2*ne)*Z^(-2*saving)*
          radialEnergy (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) keep Φ K := by
  obtain ⟨n,ne,h⟩:=actual_original_comparison a b epsilon Cscale xi saving L ha hepsilon hscale hxi B J hB
  refine ⟨n,ne,?_⟩
  intro Wlong hs hW
  obtain ⟨C,D,hC,hD,h⟩:=h Wlong hs hW
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [h] with Z hZ
  refine ⟨hZ.1,?_⟩
  intro χ P t omega keep Φ K Pbound Wshort c d M along bshort E T Rcap hK hΦ hP hχ
    hd hshort hshortsmooth hML hmod hE hT ht hRcap hcap henergy
  have hz : 0<Z:=by linarith [hZ.1]
  have hshortsum:=single_radial_summable χ P omega Wshort c d (Z^bshort) Pbound hd
    (Real.rpow_pos_of_pos hz _) hshort hP keep Φ K hK
  unfold radialEnergy
  apply Real.tsum_le_of_sum_le (fun z=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  intro rows
  let S:=rows.filter keep
  let weightedP (z : ↥S) : ℂ:=P z*(Real.sqrt ((Φ (‖eisEmbedding z‖^2/K)).re):ℂ)
  have hmem (z : ↥S) : keep (z:O):=(Finset.mem_filter.mp z.property).2
  have hh:=hZ.2 (fun z:↥S=>χ z) weightedP (fun z=>t z) (fun z=>omega z)
    Wshort c d M along bshort E T Rcap (fun z=>hχ z (hmem z)) hd hshort hshortsmooth
    hML (fun z=>hmod z (hmem z)) hE hT (fun z=>ht z (hmem z)) hRcap
    (fun z=>hcap z (hmem z)) ?_
  · simp only [weightedP,←mul_assoc] at hh
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false Wlong (Z^along) 0 (2*Real.pi*t z)*polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ,
      finite_weighted rows keep (fun z=>polynomial (χ z) false Wshort (Z^bshort) 0 (omega z)*P z) Φ K hΦ] at hh
    apply hh.trans
    apply add_le_add
    · apply le_of_eq;ring
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hshortsum.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)
  · intro v j k x hx
    have hschild:=pair_radial_summable χ P (fun _=>-2*Real.pi*v) omega
      (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (scaleTest Wshort k)
      (1/4) 1 c d (Real.exp x) (Z^bshort) Pbound (by norm_num) hd
      (Real.exp_pos _) (Real.rpow_pos_of_pos hz _)
      (scaleTest_support _ _ _ CenteredMomentOneReflectionScaleEnergy.annulus_complex_support j)
      (scaleTest_support _ _ _ hshort k) hP keep Φ K hK
    simp only [weightedP,←mul_assoc]
    rw [finite_weighted rows keep (fun z=>polynomial (χ z) false (scaleTest (fun y:ℝ=>(annulus y:ℂ)) j) (Real.exp x) 0 (-2*Real.pi*v)*polynomial (χ z) false (scaleTest Wshort k) (Z^bshort) 0 (omega z)*P z) Φ K hΦ]
    exact (hschild.sum_le_tsum rows (fun z _=>by split_ifs;exact mul_nonneg (sq_nonneg _) (hΦ z);exact le_rfl)).trans
      (henergy v j k x hx)

end SevenEighths.CenteredMomentOriginalRadialComparison

end

end OAI
end OAIOriginalModule2200

/-! Original module: OAI.NumberTheory.DirichletL.Moments.OriginalRadialTail
Source SHA256: 851b11d1e74816a8ac27cf0da92e9303e90f02a2d1563c4a557889615a3cc54d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2201



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentOriginalRadialTail
open HeckeFamily ConcreteTraceCRT CenteredMomentAbsoluteEnergy
open CenteredMomentPositiveSummability CenteredMomentOriginalRadialComparison
open QuadraticInitialBound EisensteinSchwartzPoisson
local notation "O" => HeckeFamily.O

def tailControl (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) : ℝ :=
  (2:ℝ)^(A+2)*(Finset.Iic (A+2,0)).sup (schwartzSeminormFamily ℝ ℝ ℂ) Φ

lemma cauchy_all (K : ℝ) (hK : 0<K) :
    (∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤4*(1+Real.pi)^2*max 1 K := by
  by_cases hk : 1≤K
  · have hh:=scaled_eisenstein_cauchy_small K⁻¹ (inv_pos.mpr hK) (inv_le_one_of_one_le₀ hk)
    rw [max_eq_right hk]
    have he : K*(K⁻¹*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹))=
        ∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by rw [←mul_assoc,mul_inv_cancel₀ hK.ne',one_mul]
    have hb:=mul_le_mul_of_nonneg_left hh hK.le
    rw [he] at hb
    simpa only [mul_comm K] using hb
  · have hk' : K≤1:=(not_le.mp hk).le
    have hi : 1≤K⁻¹:=(one_le_inv₀ hK).mpr hk'
    have hs:=scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)
    have hh:=hs.tsum_le_tsum (g:=fun z:O=>((1+1*‖eisEmbedding z‖^2)^2)⁻¹) (fun z=>by
      apply inv_anti₀ (by positivity)
      gcongr)
      (scaled_eisenstein_cauchy_summable 1 (by norm_num))
    have hb:=scaled_eisenstein_cauchy_small 1 (by norm_num) (by norm_num)
    rw [max_eq_left hk',mul_one]
    exact hh.trans (by simpa only [one_mul] using hb)

lemma tail_pointwise (A : ℕ) (Φ : 𝓢(ℝ,ℂ)) (x r : ℝ) (hr : 0≤r) (hx : r≤x) :
    ‖Φ x‖≤tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹ := by
  have hxp : 0≤x:=hr.trans hx
  have hh:=SchwartzMap.one_add_le_sup_seminorm_apply (𝕜:=ℝ)
    (m:=(A+2,0)) (k:=A+2) (n:=0) le_rfl le_rfl Φ x
  simp only [norm_iteratedFDeriv_zero,Real.norm_of_nonneg hxp] at hh
  change (1+x)^(A+2)*‖Φ x‖≤tailControl A Φ at hh
  have hp : (1+r)^A≤(1+x)^A:=pow_le_pow_left₀ (by positivity) (by linarith) A
  have hb : (1+r)^A*((1+x)^2*‖Φ x‖)≤tailControl A Φ := by
    apply (mul_le_mul_of_nonneg_right hp (by positivity)).trans
    simpa only [pow_add,mul_assoc] using hh
  have hd : 0<(1+r)^A*(1+x)^2:=by positivity
  rw [show tailControl A Φ*((1+r)^A)⁻¹*((1+x)^2)⁻¹=
    tailControl A Φ/((1+r)^A*(1+x)^2) by field_simp]
  exact (le_div_iff₀ hd).mpr (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hb)

theorem actual_radial_tail (A : ℕ) (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) (hR : 0≤R) :
    radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
  let C:=tailControl A Φ*B^2*((1+R/K)^A)⁻¹
  have hC : 0≤C:=by dsimp [C,tailControl];positivity
  have hs:=bounded_radial_summable F B hF (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K hK
  have hp (z:O) :
      (if keep z ∧ R<‖eisEmbedding z‖^2 then ‖F z‖^2*(Φ (‖eisEmbedding z‖^2/K)).re else 0)
      ≤C*((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹ := by
    split_ifs with hz
    · have ht:=tail_pointwise A Φ (‖eisEmbedding z‖^2/K) (R/K)
        (div_nonneg hR hK.le) (div_le_div_of_nonneg_right hz.2.le hK.le)
      have hf:=pow_le_pow_left₀ (norm_nonneg _) (hF z) 2
      have hh:=(mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul hf ht (norm_nonneg _) (sq_nonneg B))
      convert hh using 1 ; dsimp [C] ; simp only [div_eq_mul_inv] ; ring
    · exact mul_nonneg hC (by positivity)
  have hb:=Summable.tsum_le_tsum hp (hs.congr (fun z=>by by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz])) ((scaled_eisenstein_cauchy_summable K⁻¹ (inv_pos.mpr hK)).mul_left C)
  rw [tsum_mul_left] at hb
  have hh:=mul_le_mul_of_nonneg_left (cauchy_all K hK) hC
  have hh' : C*(∑'z:O,((1+K⁻¹*‖eisEmbedding z‖^2)^2)⁻¹)≤
      4*(1+Real.pi)^2*tailControl A Φ*B^2*max 1 K*((1+R/K)^A)⁻¹ := by
    convert hh using 1 ; dsimp [C] ; ring
  convert hb.trans hh' using 1
  unfold radialEnergy
  apply tsum_congr
  intro z
  by_cases hz:keep z ∧ R<‖eisEmbedding z‖^2 <;> simp [hz]

lemma actual_radial_split (F : O→ℂ) (B : ℝ) (hF : ∀z,‖F z‖≤B)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K R : ℝ) (hK : 0<K) :
    radialEnergy F keep Φ K=
      radialEnergy F (fun z=>keep z ∧ ‖eisEmbedding z‖^2≤R) Φ K+
      radialEnergy F (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K := by
  unfold radialEnergy
  rw [←Summable.tsum_add (bounded_radial_summable F B hF _ Φ K hK)
    (bounded_radial_summable F B hF _ Φ K hK)]
  apply tsum_congr
  intro z
  by_cases hk:keep z
  · by_cases hr:‖eisEmbedding z‖^2≤R
    · simp [hk,hr,not_lt.mpr hr]
    · simp [hk,hr,not_le.mp hr]
  · simp [hk]

theorem actual_positive_row_tail {ι:Type*} [Fintype ι] [DecidableEq ι]
    (order:ℕ) (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤b₁) (hb₂:0≤b₂) (hB₁:0≤B₁) (hB₂:0≤B₂)
    (hX₁:0<X₁) (hX₂:0<X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤B₁) (hW₂:∀x,‖W₂ x‖≤B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0<P i) (hb:∀i,0≤b i) (hB:∀i,0≤B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K R:ℝ) (hK:0<K) (hR:0≤R) :
    radialEnergy (fun z=>CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
      (fun z=>keep z ∧ R<‖eisEmbedding z‖^2) Φ K≤
      4*(1+Real.pi)^2*tailControl order Φ*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i))*
        max 1 K*((1+R/K)^order)⁻¹ := by
  let E:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖CenteredMomentRetainedEnergy.positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤E:=
    CenteredMomentInductionEnergy.positive_squared_absolute η m A z t W₁ W₂
      b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
      S β P b B hP hb hB hβ hN
  have hh:=actual_radial_tail order _ (Real.sqrt E)
    (fun z=>Real.le_sqrt_of_sq_le (hp z)) keep Φ K R hK hR
  simpa only [Real.sq_sqrt hE] using hh

end SevenEighths.CenteredMomentOriginalRadialTail

end

end OAI
end OAIOriginalModule2201

/-! Original module: OAI.NumberTheory.DirichletL.Moments.NaturalRadialCutoff
Source SHA256: 230a06100e9b4b782da7e81d5e5a07b07f63244e66f76c21b15919e99f327217
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2202



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace SevenEighths.CenteredMomentNaturalRadialCutoff
open HeckeFamily ConcreteTraceCRT CenteredMomentNaturalRowSource
open CenteredMomentOriginalRadialTail CenteredMomentOriginalRadialComparison
local notation "O" => HeckeFamily.O

lemma retained_conductor (η:Character) (Z m q xi Ck K:ℝ) (hZ:0<Z) (hCk:0≤Ck)
    (hη:(η.modulus.absNorm:ℝ)≤Z^m) (hK:K≤Ck*Z^q)
    (z:O) (hz:z≠0) (hrow:‖eisEmbedding z‖^2≤K*Z^xi) :
    ((naturalRow η z hz).character.modulus.absNorm:ℝ)≤
      (fixedConductorFactor:ℝ)*Ck*Z^(m+q+xi) := by
  have hn:((Ideal.span {z}).absNorm:ℝ)≤Ck*Z^(q+xi) := by
    rw [←ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
    apply hrow.trans
    have hh:=mul_le_mul_of_nonneg_right hK (Real.rpow_nonneg hZ.le xi)
    simpa only [Real.rpow_add hZ,mul_assoc] using hh
  have hh:=(naturalRow η z hz).modulus_power_bound Z m (q+xi) Ck hZ hCk hη hn
  simpa only [add_assoc] using hh

lemma reciprocal_cutoff_bound (Z xi:ℝ) (order:ℕ) (hZ:0<Z) :
    ((1+Z^xi)^order)⁻¹≤Z^(-xi*(order:ℝ)) := by
  have hp : (Z^xi)^order≤(1+Z^xi)^order:=
    pow_le_pow_left₀ (Real.rpow_nonneg hZ.le _) (by linarith) order
  have hh:=inv_anti₀ (pow_pos (Real.rpow_pos_of_pos hZ _) _) hp
  have he : (Z^xi)^order=Z^(xi*(order:ℝ)) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hZ.le]
  apply hh.trans_eq
  rw [he,←Real.rpow_neg hZ.le]
  congr 1
  ring

theorem actual_tail_arbitrary_saving (xi saving mass : ℝ) (hxi:0<xi) :
    ∃order:ℕ,∀(F:O→ℂ)(B:ℝ)(keep:O→Prop)(Φ:𝓢(ℝ,ℂ))(K Z:ℝ),
      (∀z,‖F z‖≤B) → 0<K → 1≤Z → B^2*max 1 K≤Z^mass →
      radialEnergy F (fun z=>keep z ∧ K*Z^xi<‖eisEmbedding z‖^2) Φ K≤
        (4*(1+Real.pi)^2*tailControl order Φ)*Z^(-saving) := by
  obtain ⟨order,horder⟩:=exists_nat_ge ((mass+saving)/xi)
  have ho:mass-xi*(order:ℝ)≤-saving := by
    have hh:mass+saving≤(order:ℝ)*xi:=(div_le_iff₀ hxi).mp horder
    linarith
  refine ⟨order,?_⟩
  intro F B keep Φ K Z hF hK hZ hmass
  have hz:0<Z:=by linarith
  have hh:=actual_radial_tail order F B hF keep Φ K (K*Z^xi) hK (by positivity)
  have hdiv:K*Z^xi/K=Z^xi:=by field_simp
  rw [hdiv] at hh
  have hc:0≤4*(1+Real.pi)^2*tailControl order Φ:=by unfold tailControl;positivity
  have hb:(B^2*max 1 K)*((1+Z^xi)^order)⁻¹≤Z^(-saving) := by
    calc
      _≤Z^mass*Z^(-xi*(order:ℝ)) :=
        mul_le_mul hmass (reciprocal_cutoff_bound Z xi order hz) (by positivity) (Real.rpow_nonneg hz.le _)
      _=Z^(mass-xi*(order:ℝ)) := by rw [←Real.rpow_add hz];congr 1;ring
      _≤Z^(-saving):=Real.rpow_le_rpow_of_exponent_le hZ ho
  apply hh.trans
  convert mul_le_mul_of_nonneg_left hb hc using 1 ; ring

end SevenEighths.CenteredMomentNaturalRadialCutoff

end

end OAI
end OAIOriginalModule2202

/-! Original module: OAI.NumberTheory.DirichletL.Moments.WholeSlotDeletion
Source SHA256: ec2989a9ebb4a4575e08abfa036dfea5ed00a7e82284223bf38875154d022285
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2203



namespace OAI

noncomputable section
open scoped BigOperators Classical

namespace SevenEighths.CenteredMomentWholeSlotDeletion
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeHeight
local notation "O" => ActualEisensteinCubic.O

theorem whole_removal {α:Type*} (S:Finset α) (w:α→ℝ) (F κ mesh:ℝ)
    (hF:0≤F) (hκ:0<κ) (hm:0≤mesh)
    (hw:∀i∈S,0≤w i) (hwm:∀i∈S,w i≤mesh) :
    ∃R:Finset α,R⊆S ∧
      (∑i∈R,w i)≤min (∑i∈S,w i) (F/(6*κ)+mesh) ∧
      (R=S ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤F/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay⟩:=CenteredMomentSlotRemoval.whole_slot_removal S w mesh κ F hm hκ hF hw hwm
  refine ⟨R,hR,hbound,hpay,?_⟩
  have hh:=mul_le_mul_of_nonneg_left (hbound.trans (min_le_right _ _)) hκ.le
  have he:κ*(F/(6*κ)+mesh)=F/6+κ*mesh:=by field_simp
  rwa [he] at hh

def normalizedSlot (η:Character) (m A z:O) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (t P:ℝ) : ℂ := (Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S β t

def selectedProduct {α:Type*} (J:Finset α) (η:Character) (m A z:O)
    (W₁ W₂:ℝ→ℂ) (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ)
    (t X₁ X₂:ℝ) : ℂ :=
  ((Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂))*
    ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i)

theorem selectedProduct_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂:ℝ) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      (∏i∈R,normalizedSlot η m A z (S i) (β i) t (P i))*
        selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct
  rw [←Finset.prod_sdiff hR]
  ring

theorem selectedProduct_energy_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂ Z κ:ℝ)
    (hZ:0<Z) (w B:α→ℝ) (_hB:∀i∈R,0≤B i)
    (hslot:∀i∈R,‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2≤B i*Z^(κ*w i)) :
    ‖selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((∏i∈R,B i)*Z^(κ*∑i∈R,w i))*
        ‖selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  rw [selectedProduct_remove J R hR,norm_mul,mul_pow,norm_prod,←Finset.prod_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _≤∏i∈R,B i*Z^(κ*w i):=Finset.prod_le_prod₀ (fun i _=>sq_nonneg _) hslot
    _=_:=by rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,Finset.mul_sum]

end SevenEighths.CenteredMomentWholeSlotDeletion

end

end OAI
end OAIOriginalModule2203

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeSlot
Source SHA256: e94a635d9180764a79bc5969c4ea75a0afc673494388add1d25dd99de2ea21b4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2204



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlot
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
local notation "O" => HeckeFamily.O

def primePool (M:Ideal O) (H:Subgroup (O⧸M)ˣ) (b D:ℝ) : Finset (Ideal O) :=
  (annulusSet b D).filter (fun I=>Prime I ∧ I∈RayQuotient.identityClass M H)

def slotProfile (W:ℝ→ℂ) (D σ:ℝ) (I:Ideal O) : ℂ := annularWeight W D σ 0 I

lemma norm_height_split (N D σ t:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ 0))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ t) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_zero,zero_mul,sub_zero]
  ring

lemma sqrt_inverse_cpow (D:ℝ) (hD:0<D) :
    (Real.sqrt D:ℂ)⁻¹=(D:ℂ)^(-(1/2:ℂ)) := by
  rw [Complex.cpow_neg,Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hD.le (1/2:ℝ))

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ t := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ 0)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t:ℝ) (hD:0<D) :
    ‖normalizedSlot η m A z (primePool M H b D) (slotProfile W D σ) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ t‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end SevenEighths.CenteredMomentPrimeSlot

end

end OAI
end OAIOriginalModule2204

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeSlotBound
Source SHA256: 482a51e166c39caeb3b22c1e1b3004220b73f1a5a85ea4c52d2322b26c94817b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2205



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff
namespace SevenEighths.CenteredMomentPrimeSlotBound
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentWholeSlotDeletion CenteredMomentRayNonprincipal
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)

include hH
theorem actual_slot_all_height_squared (W:ℝ→ℂ) (a b:ℝ) (ha:0<a)
    (hWs:Function.support W⊆Set.Icc a b) (hW:ContDiff ℝ ∞ W)
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧ ∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η m A z (primePool M H b P) (slotProfile W P σ) t P‖^2≤
        C*(1+|t|)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=CenteredMomentPrimeHeight.ray_prime_all_height_squared
    M H hH W a b ha hWs hW Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  obtain ⟨χ,hχ,hrow⟩:=exists_row_character_with_conductor η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  have hχreal:(χ.modulus.absNorm:ℝ)≤Z^Lmod:=
    (show (χ.modulus.absNorm:ℝ)≤rowConductorBound η m 1 (A*z) by exact_mod_cast hχ).trans hcond
  rw [normalizedSlot_norm_sq M H η χ m A z hrow W b P σ t (zero_lt_one.trans_le hP)]
  exact hbound Z P hZ hP hPcap χ hχreal
    (all_ray_twists_nonprincipal M H hH η χ Q m A z hrow hQ hex) σ t hσ hσhi

end SevenEighths.CenteredMomentPrimeSlotBound

end

end OAI
end OAIOriginalModule2205

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeSlotShift
Source SHA256: 4e01124feb01caec738881fff5b60338ecc998267cff570f6c984fe0555b130c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2206


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentPrimeSlotShift
open HeckeFamily HeckeRowClosure HeckePrimeRay HeckePrimeAnnular HeckeDyadic
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentTwist
open CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma norm_height_split (N D σ t v:ℝ) (hN:0<N) (hD:0<D) :
    (((N/D:ℝ):ℂ)^(-shift σ v))*(N:ℂ)^(Complex.I*t)=
      (D:ℂ)^(Complex.I*t)*((N/D:ℝ):ℂ)^(-shift σ (t+v)) := by
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hN.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hD.ne'),
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (div_pos hN hD).ne'),
    ←Complex.ofReal_log (div_pos hN hD).le,←Complex.ofReal_log hN.le,
    ←Complex.ofReal_log hD.le,Real.log_div hN.ne' hD.ne',←Complex.exp_add,←Complex.exp_add]
  congr 1
  simp only [HeckeDyadic.shift,Complex.ofReal_sub,Complex.ofReal_add]
  ring

theorem normalizedSlot_eq_ray (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    normalizedSlot η m A z (primePool M H b D) (annularWeight W D σ v) t D=
      (D:ℂ)^(Complex.I*t)*rayPrimePolynomial M H χ W b D σ (t+v) := by
  unfold normalizedSlot rowSlot rayPrimePolynomial primePool
  rw [sqrt_inverse_cpow D hD]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  have hp:Prime I := (Finset.mem_filter.mp hI).2.1
  have hN:0<(I.absNorm:ℝ) := norm_pos ⟨I,hp.ne_zero⟩
  have hc:=idealCoeff_eq_row η χ m 1 (A*z) hrow I
  simp only [one_pow,mul_one] at hc
  rw [←hc]
  change (D:ℂ)^(-(1/2:ℂ))*
    ((W ((I.absNorm:ℝ)/D)*(((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v))*idealCoeff χ I*
      (I.absNorm:ℂ)^(Complex.I*t))=_
  have hn:=norm_height_split (I.absNorm:ℝ) D σ t v hN hD
  simp only [Complex.ofReal_natCast] at hn
  calc
    _=(D:ℂ)^(-(1/2:ℂ))*(W ((I.absNorm:ℝ)/D)*idealCoeff χ I)*
      ((((I.absNorm:ℝ)/D:ℝ):ℂ)^(-shift σ v)*(I.absNorm:ℂ)^(Complex.I*t)) := by ring
    _=_ := by rw [hn]; unfold annularWeight; ring

theorem normalizedSlot_norm_sq (M:Ideal O) (H:Subgroup (O⧸M)ˣ)
    (η χ:Character) (m A z:O)
    (hrow:∀n:O,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W:ℝ→ℂ) (b D σ t v:ℝ) (hD:0<D) :
    ‖normalizedSlot η m A z (primePool M H b D) (annularWeight W D σ v) t D‖^2=
      ‖rayPrimePolynomial M H χ W b D σ (t+v)‖^2 := by
  rw [normalizedSlot_eq_ray M H η χ m A z hrow W b D σ t v hD,norm_mul,
    norm_real_imaginary_power D t hD,one_mul]

end SevenEighths.CenteredMomentPrimeSlotShift

end

end OAI
end OAIOriginalModule2206

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeSlotUniform
Source SHA256: 1d6a687d39cddcbbdb726b5f6f783c1cec8174f724fd44b7a6359f7455a4cf2e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2207


namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotUniform
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotBound CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_slots_uniform {ι:Type*} [Fintype ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,1≤C ∧ 1<Z₀ ∧ ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t:ℝ,lo≤σ → σ≤hi →
      ‖normalizedSlot η m A z (primePool M H (b i) P) (slotProfile (W i) P σ) t P‖^2≤
        C*(1+|t|)^degree*Z^loss*P^κ := by
  have hall:=fun i=>actual_slot_all_height_squared M H hH (W i) (a i) (b i) (ha i)
    (hWs i) (hW i) Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  choose degree C Z₀ hC hZ₀ hbound using hall
  let D:ℕ:=∑i,degree i
  let Csum:ℝ:=1+∑i,C i
  let Zsum:ℝ:=2+∑i,Z₀ i
  have hCs:1≤Csum:=by dsimp [Csum]; exact le_add_of_nonneg_right (Finset.sum_nonneg (fun i _=>(hC i).le))
  have hZs:1<Zsum:=by
    have hh:0≤∑i,Z₀ i:=Finset.sum_nonneg (fun i _=>le_trans zero_le_one (hZ₀ i).le)
    dsimp [Zsum]; linarith
  refine ⟨D,Csum,Zsum,hCs,hZs,?_⟩
  intro i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  have hz0:Z₀ i≤Zsum:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>le_trans zero_le_one (hZ₀ j).le) (Finset.mem_univ i)
    dsimp [Zsum]; linarith
  have hci:C i≤Csum:=by
    have hh:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>(hC j).le) (Finset.mem_univ i)
    dsimp [Csum]; linarith
  have hdi:degree i≤D:=Finset.single_le_sum (fun j (_:j∈Finset.univ)=>Nat.zero_le _) (Finset.mem_univ i)
  have hh:=hbound i Z P (hz0.trans hZ) hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t hσ hσhi
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) κ)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (hZs.le.trans hZ |>.trans' zero_le_one) loss)
  exact mul_le_mul hci (pow_le_pow_right₀ (by linarith [abs_nonneg t]) hdi)
    (by positivity) (zero_le_one.trans hCs)

end SevenEighths.CenteredMomentPrimeSlotUniform

end

end OAI
end OAIOriginalModule2207

/-! Original module: OAI.NumberTheory.DirichletL.Moments.PrimeSlotExternal
Source SHA256: d5979313fd96270483a856e896e4b9489be7ff3d2deff985bce13137d9d89513
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2208



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentPrimeSlotExternal
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile HeckePrimeAnnular
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotUniform CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_slots_external_uniform {ι:Type*} [Fintype ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot loss lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hloss:0<loss)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,1≤C ∧ 1<Z₀ ∧ ∀i:ι,∀Z P:ℝ,Z₀≤Z → 1≤P → P≤Z^Lslot →
    ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M → m≠0 → A≠0 → z≠0 →
      goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod →
      ¬FixedInducingRow η Q m A z →
      ∀σ t v V:ℝ,lo≤σ → σ≤hi → |v|≤V →
      ‖normalizedSlot η m A z (primePool M H (b i) P) (annularWeight (W i) P σ v) t P‖^2≤
        C*(1+|t|+V)^degree*Z^loss*P^κ := by
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=actual_slots_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  refine ⟨degree,C,Z₀,hC,hZ₀,?_⟩
  intro i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ t v V hσ hσhi hv
  obtain ⟨χ,hχ,hrow⟩:=exists_row_character_with_conductor η m 1 (A*z) hm one_ne_zero
    (mul_ne_zero hA hz) hmLam hm2
  rw [CenteredMomentPrimeSlotShift.normalizedSlot_norm_sq M H η χ m A z hrow (W i) (b i) P σ t v
    (zero_lt_one.trans_le hP),←CenteredMomentPrimeSlot.normalizedSlot_norm_sq M H η χ m A z hrow
      (W i) (b i) P σ (t+v) (zero_lt_one.trans_le hP)]
  apply (hbound i Z P hZ hP hPcap η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ (t+v) hσ hσhi).trans
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans hP) _)
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (zero_le_one.trans (hZ₀.le.trans hZ)) _)
  apply mul_le_mul_of_nonneg_left _ (zero_le_one.trans hC)
  exact pow_le_pow_left₀ (by positivity) (by linarith [abs_add_le t v]) _

end SevenEighths.CenteredMomentPrimeSlotExternal

end

end OAI
end OAIOriginalModule2208

/-! Original module: OAI.NumberTheory.DirichletL.Moments.SlotNormalization
Source SHA256: 07c63682bf1244e45e04c796292c9774c43e5409f8b530c67ab0f8361fc1ac6f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2209


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
local notation "O" => HeckeFamily.O

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤X) (hP:∀i,0≤P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (fun i _=>hP i),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤X₁*X₂) (hP:∀i,0≤P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  calc
    _=((Real.sqrt (X₁*X₂):ℂ)⁻¹*(∏i,(Real.sqrt (P i):ℂ)⁻¹))*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏i,rowSlot η m A z (S i) (β i) t) := by ring
    _=_ := by rw [he]

end SevenEighths.CenteredMomentSlotNormalization

end

end OAI
end OAIOriginalModule2209

/-! Original module: OAI.NumberTheory.DirichletL.Moments.ActualLiveSlotRemoval
Source SHA256: b98857d480a582688353517a3cdcc106289a2f40867591de19f15dcbcfacf02e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2210



namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff

namespace SevenEighths.CenteredMomentActualLiveSlotRemoval
open HeckeFamily HeckeRowClosure HeckeZeroSupremum CenteredExceptionalProfile
open CenteredMomentPrimeSlot CenteredMomentPrimeSlotExternal CenteredMomentWholeSlotDeletion
open ConcretePrimeRowBridge HeckePrimeAnnular
local notation "O" => HeckeFamily.O
variable (M:Ideal O) [NeZero M]
local instance : Finite (O⧸M) := Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne M)
variable (H:Subgroup (O⧸M)ˣ) (hH:RayOrthogonality.globalUnits M≤H)
include hH

theorem actual_live_slot_removal {ι:Type*} [Fintype ι] [DecidableEq ι]
    (W:ι→ℝ→ℂ) (a b:ι→ℝ) (ha:∀i,0<a i)
    (hWs:∀i,Function.support (W i)⊆Set.Icc (a i) (b i)) (hW:∀i,ContDiff ℝ ∞ (W i))
    (Lmod Lslot ε lo hi κ:ℝ) (hLm:0≤Lmod) (hLs:0≤Lslot) (hε:0<ε)
    (hbeta:(51/100:ℝ)≤beta) (hκ:2*beta-1≤κ) :
    ∃degree:ℕ,∃C Z₀:ℝ,0<C ∧ 1<Z₀ ∧
    ∀(J:Finset ι) (w:ι→ℝ) (F mesh:ℝ),0≤F → 0≤mesh →
      (∀i,0≤w i) → (∀i,w i≤mesh) → (∀i,w i≤Lslot) →
      ∃R:Finset ι,R⊆J ∧ (R=J ∨ F≤6*κ*(∑i∈R,w i)) ∧
      κ*(∑i∈R,w i)≤F/6+κ*mesh ∧
      ∀Z:ℝ,Z₀≤Z → ∀(η:Character) (Q:Ideal O) (m A z:O),Q≤M →
      m≠0 → A≠0 → z≠0 → goodLambda∣m → (2:O)∣m →
      (rowConductorBound η m 1 (A*z):ℝ)≤Z^Lmod → ¬FixedInducingRow η Q m A z →
      ∀(σ ν:ι→ℝ) (t V:ℝ), (∀i,lo≤σ i) → (∀i,σ i≤hi) → 0≤V → (∀i,|ν i|≤V) →
      ∀(W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ),
      let P:=fun i=>Z^(w i)
      let S:=fun i=>primePool M H (b i) (P i)
      let coeff:=fun i=>annularWeight (W i) (P i) (σ i) (ν i)
      ‖selectedProduct J η m A z W₁ W₂ S coeff P t X₁ X₂‖^2≤
        C*(1+|t|+V)^degree*Z^(ε+F/6+κ*mesh)*
          ‖selectedProduct (J\R) η m A z W₁ W₂ S coeff P t X₁ X₂‖^2 := by
  let N:=Fintype.card ι
  let loss:=ε/((N:ℝ)+1)
  have hloss:0<loss:=div_pos hε (by positivity)
  obtain ⟨degree,C,Z₀,hC,hZ₀,hbound⟩:=actual_slots_external_uniform M H hH W a b ha hWs hW
    Lmod Lslot loss lo hi κ hLm hLs hloss hbeta hκ
  have hκpos:0<κ:=by linarith
  refine ⟨degree*N,C^N,Z₀,pow_pos (zero_lt_one.trans_le hC) _,hZ₀,?_⟩
  intro J w F mesh hF hmesh hw hwm hwcap
  obtain ⟨R,hR,hRsum,hpay,hcost⟩:=whole_removal J w F κ mesh hF hκpos hmesh
    (fun i _=>hw i) (fun i _=>hwm i)
  refine ⟨R,hR,hpay,hcost,?_⟩
  intro Z hZ η Q m A z hQ hm hA hz hmLam hm2 hcond hex σ ν t V hσ hσhi hV hν W₁ W₂ X₁ X₂
  dsimp only
  have hz1:1≤Z:=hZ₀.le.trans hZ
  have hz0:0<Z:=zero_lt_one.trans_le hz1
  let B:=C*(1+|t|+V)^degree*Z^loss
  have hB:1≤B:=by
    have ht:1≤(1+|t|+V)^degree:=one_le_pow₀ (by linarith [abs_nonneg t])
    have hz:1≤Z^loss:=Real.one_le_rpow hz1 hloss.le
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hC ht) hz
  have hs:∀i∈R,‖normalizedSlot η m A z (primePool M H (b i) (Z^(w i)))
      (annularWeight (W i) (Z^(w i)) (σ i) (ν i)) t (Z^(w i))‖^2≤B*Z^(κ*w i) := by
    intro i hi
    have hb:=hbound i Z (Z^(w i)) hZ (Real.one_le_rpow hz1 (hw i))
      (Real.rpow_le_rpow_of_exponent_le hz1 (hwcap i)) η Q m A z hQ hm hA hz hmLam hm2 hcond hex
      (σ i) t (ν i) V (hσ i) (hσhi i) (hν i)
    rw [←Real.rpow_mul hz0.le] at hb
    simpa only [B,mul_comm (w i) κ] using hb
  have he:=selectedProduct_energy_remove J R hR η m A z W₁ W₂
    (fun i=>primePool M H (b i) (Z^(w i))) (fun i=>annularWeight (W i) (Z^(w i)) (σ i) (ν i))
    (fun i=>Z^(w i)) t X₁ X₂ Z κ hz0 w (fun _=>B) (fun i hi=>zero_le_one.trans hB) hs
  apply he.trans
  gcongr 1
  have hcard:R.card≤N:=Finset.card_le_univ R
  have hpow:(∏i∈R,B)≤B^N:=by
    rw [Finset.prod_const]
    exact pow_le_pow_right₀ hB hcard
  have hcostZ:Z^(κ*∑i∈R,w i)≤Z^(F/6+κ*mesh):=
    Real.rpow_le_rpow_of_exponent_le hz1 hcost
  have hsplit:B^N=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)):=by
    dsimp [B]
    rw [mul_pow,mul_pow,←pow_mul,←Real.rpow_natCast (Z^loss) N,←Real.rpow_mul hz0.le]
  have hlossN:loss*(N:ℝ)≤ε:=by
    dsimp [loss]
    have hden:0<(N:ℝ)+1:=by positivity
    have hh:ε/((N:ℝ)+1)*((N:ℝ)+1)=ε:=div_mul_cancel₀ _ hden.ne'
    nlinarith [hloss.le]
  calc
    _≤B^N*Z^(F/6+κ*mesh):=mul_le_mul hpow hcostZ (Real.rpow_nonneg hz0.le _) (by positivity)
    _=C^N*(1+|t|+V)^(degree*N)*Z^(loss*(N:ℝ)+(F/6+κ*mesh)):=by
      rw [hsplit,mul_assoc,←Real.rpow_add hz0]
    _≤_:=mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hz1 (by linarith)) (by positivity)

  apply le_of_eq
  congr 3
  ext i
  simp

end SevenEighths.CenteredMomentActualLiveSlotRemoval

end

end OAI
end OAIOriginalModule2210

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionary
Source SHA256: 1c7232a450d47106ef84bb8e2f7d8e3bd649fdf3328e728d358e200d54d81146
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2211





namespace OAI

noncomputable section
open scoped Classical BigOperators ContDiff ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure HeckeInverseAmplification
open CenteredMomentHeckeHeight CenteredMomentHeckeTwist CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentWholeSlotDeletion
open CenteredMomentPrimeSlot CenteredMomentSlotNormalization
local notation "O" => HeckeFamily.O

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0<X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=>idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,idealCoeff χ I*W ((I.absNorm:ℝ)/X) at he
  simpa only [summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,HeckeDyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    HeckeDyadic.NonzeroIdeal,UnrestrictedIdealReindex.NonzeroIdeal] using he

theorem plain_polynomial_eq_row (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (X σ t : ℝ) (hX : 0<X) :
    polynomial χ false W X σ t = (Real.sqrt X:ℂ)⁻¹*
      rowTwistedSum η m A z (twistProfile W σ t) 0 X := by
  rw [←polynomial_twistProfile,plain_zero_height _ _ X hX,rowTwistedSum_eq η χ m A z hrow]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem positiveSlotRow_eq_product
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (S : ι→Finset (Ideal O)) (β : ι→Ideal O→ℂ) (P : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t) S β P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,normalizedSlot η m A z (S i) (β i) 0 (P i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem positiveSlotRow_eq_polynomials
    (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (elementHom η) m 1 (A*z) n)
    (W₁ W₂ : ℝ→ℂ) (V : ι→ℝ→ℂ) (b P σp tp : ι→ℝ)
    (X₁ X₂ σ t : ℝ) (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hP : ∀i,0<P i) :
    positiveSlotRow η m A z (twistProfile W₁ σ t) (twistProfile W₂ σ t)
      (fun i=>primePool M H (b i) (P i))
      (fun i=>HeckePrimeAnnular.annularWeight (V i) (P i) (σp i) (tp i)) P 0 X₁ X₂ =
      polynomial χ false W₁ X₁ σ t*polynomial χ false W₂ X₂ σ t*
        ∏i,HeckePrimeRay.rayPrimePolynomial M H χ (V i) (b i) (P i) (σp i) (tp i) := by
  rw [←selectedProduct_univ _ _ _ _ _ _ _ _ _ _ _ _ (mul_pos hX₁ hX₂).le (fun i=>(hP i).le)]
  unfold selectedProduct
  have hslot (i : ι) := CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H η χ m A z hrow
    (V i) (b i) (P i) (σp i) 0 (tp i) (hP i)
  simp_rw [hslot]
  simp only [Complex.ofReal_zero,mul_zero,Complex.cpow_zero,one_mul,zero_add]
  rw [plain_polynomial_eq_row η χ m A z hrow W₁ X₁ σ t hX₁,
    plain_polynomial_eq_row η χ m A z hrow W₂ X₂ σ t hX₂,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  ring

theorem oriented_twist_support (reverse : Bool) (W : ℝ→ℂ) (σ t : ℝ) :
    Function.support (twistProfile (HeckeDetectorCoefficientTransfer.orientedProfile reverse W) σ t)
      ⊆Function.support W := by
  apply (twistProfile_support _ _ _).trans
  cases reverse <;> simp only [HeckeDetectorCoefficientTransfer.orientedProfile,ite_true]
  · exact Set.Subset.rfl
  · intro x hx hzero
    exact hx (by simp only [hzero,map_zero])

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2211

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryProfiles
Source SHA256: e0269ea9a9637b66bbf82eae7d776e0cdcccae18fa7413796a2952c128771146
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2212




namespace OAI

noncomputable section
open scoped Classical ContDiff ComplexConjugate
namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeInverseAmplification HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma logTest_eq_iterate (W : ℝ→ℂ) (n : ℕ) : logTest W n=(logProfile^[n]) W := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [logTest,Function.iterate_succ_apply',ih]

lemma oriented_logTest (reverse : Bool) (W : ℝ→ℂ) (n : ℕ) :
    orientedProfile reverse ((logProfile^[n]) W)=logTest (orientedProfile reverse W) n := by
  rw [←logTest_eq_iterate]
  cases reverse
  · rfl
  · induction n with
    | zero => rfl
    | succ n ih =>
      simp only [logTest,orientedProfile,ite_true] at ih ⊢
      funext x
      rw [←logProfile_conjugate]
      exact congrArg (fun f : ℝ→ℂ=>logProfile f x) ih

theorem detector_profile_support (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    Function.support (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t)
      ⊆Set.Icc (1/4) (9/4) := by
  apply (oriented_twist_support reverse _ σ t).trans
  rw [←logTest_eq_iterate]
  exact (logTest_support positiveAnnular n).trans positiveAnnular_support

theorem detector_profile_smooth (reverse : Bool) (n : ℕ) (σ t : ℝ) :
    ContDiff ℝ ∞ (twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ t) := by
  apply twistProfile_smooth _ σ t (1/4) (9/4) (by norm_num)
  · cases reverse <;> simp only [orientedProfile,ite_true]
    · rw [←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
    · rw [conjugate_profile_support,←logTest_eq_iterate]
      exact (logTest_support positiveAnnular n).trans positiveAnnular_support
  · have hw := logTest_smooth positiveAnnular n (1/4) (9/4) (by norm_num)
      positiveAnnular_support positiveAnnular_smooth
    rw [logTest_eq_iterate] at hw
    cases reverse
    · exact hw
    · exact conjugate_profile_smooth _ hw

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2212

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionarySlots
Source SHA256: d263889b617997352d8480a25fabccb3f5e8af814399deda52d563375eee6541
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2213



namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
open HeckeDetectorRelativePrime
local notation "O" => HeckeFamily.O

def physicalSlotCoefficient (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) : ℂ :=
  idealCoeff η.inverse P*conj (W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1))

lemma physicalSlotCoefficient_norm (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ) (P : Ideal O) :
    ‖physicalSlotCoefficient η W D z P‖≤‖W ((P.absNorm:ℝ)/D)*(((P.absNorm:ℝ)/D:ℝ):ℂ)^(z-1)‖ := by
  rw [physicalSlotCoefficient,norm_mul,RCLike.norm_conj]
  exact mul_le_of_le_one_left (norm_nonneg _) (idealCoeff_norm_le_one η.inverse P)

lemma physicalSlotCoefficient_annular (η : Character) (W : ℝ→ℂ) (D : ℝ) (z : ℂ)
    (P : Ideal O) (hP : P≠0) (hD : 0<D) :
    physicalSlotCoefficient η W D z P=idealCoeff η.inverse P*
      HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) P := by
  have hn : 0<(P.absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hP)
  unfold physicalSlotCoefficient HeckePrimeAnnular.annularWeight
  rw [map_mul,HeckeInverseAmplification.conj_positive_cpow _ (div_pos hn hD)]
  have he : conj (z-1)= -HeckeDyadic.shift (1-z.re) (-z.im) := by
    apply Complex.ext <;> simp [HeckeDyadic.shift]
  rw [he]

theorem physical_slot_conj (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η : Character) (m u : O) (hmLam : ConcretePrimeRowBridge.goodLambda∣m)
    (hMm : M≤Ideal.span {m}) (W : ℝ→ℂ) (b D : ℝ) (z : ℂ) (hD : 0<D)
    (hη : ∀P∈primePool M H b D,W ((P.absNorm:ℝ)/D)≠0→IsCoprime P η.modulus) :
    normalizedSlot η m 1 u (primePool M H b D) (physicalSlotCoefficient η W D z) 0 D=
      conj (HeckePrimeRow.canonicalPrimeAmplitude M H u W b D z) := by
  unfold normalizedSlot rowSlot HeckePrimeRow.canonicalPrimeAmplitude
  rw [←sqrt_inverse_cpow D hD,map_mul]
  simp only [map_inv₀,Complex.conj_ofReal,Complex.ofReal_zero,one_mul,mul_zero,Complex.cpow_zero,mul_one,map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  have hP' : P∈primePool M H b D := hP
  obtain ⟨_,hp,hclass⟩ := Finset.mem_filter.mp hP
  let : P.IsMaximal := (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero
  have hg := HeckePrimeRow.identityClass_prime_good M H m hmLam hMm P hclass
  have hcop := HeckePrimeRow.identityClass_coprime_larger M H hclass hMm
  rw [idealRowHom_argument_mul,idealRowHom_prime_sixth_mask m P hg,ite_eq_left hcop,one_mul]
  by_cases hw : W ((P.absNorm:ℝ)/D)=0
  · simp only [physicalSlotCoefficient,hw,zero_mul,map_zero,mul_zero,zero_mul]
  · have hn := idealCoeff_ne_zero_of_coprime η P hp.ne_zero (hη P hP' hw)
    simp only [physicalSlotCoefficient,HeckeDetectorRelativePrime.idealCoeff_inverse,map_mul,starRingEnd_self_apply]
    field_simp

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2213

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryRelativeSlots
Source SHA256: 19d58851315cccffed32a31a8609101e3cf162381c2c0cf2b7122e93ca5040cb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2214


namespace OAI

noncomputable section
open scoped Classical BigOperators ComplexConjugate

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeFamily HeckeRowClosure CanonicalRowCompletion
open CenteredMomentHeckeSlots CenteredMomentWholeSlotDeletion CenteredMomentPrimeSlot
local notation "O" => HeckeFamily.O

lemma normalizedSlot_character (η ν : Character) (m A z : O)
    (S : Finset (Ideal O)) (β : Ideal O→ℂ) (t D : ℝ) :
    normalizedSlot η m A z S (fun P=>idealCoeff ν P*β P) t D=
      normalizedSlot (η.product ν) m A z S β t D := by
  unfold normalizedSlot rowSlot
  congr 1
  apply Finset.sum_congr rfl
  intro P hP
  rw [idealCoeff_product]
  ring

lemma product_row_presentation (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n) :
    ∀n,elementCoeff (χ.product ν) n=rowTwist (elementHom (η.product ν)) m 1 (A*z) n := by
  intro n
  rw [elementCoeff_product,hrow]
  change (elementCoeff η n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n)*elementCoeff ν n=
    elementCoeff (η.product ν) n*((idealRowHom (m^6*1^4*(A*z))).toMonoidHom.comp principalIdealHom.toMonoidHom) n
  rw [elementCoeff_product]
  ring

theorem relative_normalizedSlot_eq_ray (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ ν : Character) (m A z : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*z) n)
    (W : ℝ→ℂ) (b D σ t v : ℝ) (hD : 0<D) :
    normalizedSlot η m A z (primePool M H b D)
      (fun P=>idealCoeff ν P*HeckePrimeAnnular.annularWeight W D σ v P) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product ν) W b D σ (t+v) := by
  rw [normalizedSlot_character]
  exact CenteredMomentPrimeSlotShift.normalizedSlot_eq_ray M H (η.product ν) (χ.product ν)
    m A z (product_row_presentation η χ ν m A z hrow) W b D σ t v hD

theorem physicalSlot_eq_relativeRay (M : Ideal O) (H : Subgroup (O⧸M)ˣ)
    (η χ : Character) (m A u : O)
    (hrow : ∀n,elementCoeff χ n=rowTwist (elementHom η) m 1 (A*u) n)
    (W : ℝ→ℂ) (b D t : ℝ) (z : ℂ) (hD : 0<D) :
    normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      (D:ℂ)^(Complex.I*t)*HeckePrimeRay.rayPrimePolynomial M H (χ.product η.inverse)
        (fun y=>conj (W y)) b D (1-z.re) (t-z.im) := by
  have he : normalizedSlot η m A u (primePool M H b D) (physicalSlotCoefficient η W D z) t D=
      normalizedSlot η m A u (primePool M H b D)
        (fun P=>idealCoeff η.inverse P*HeckePrimeAnnular.annularWeight (fun y=>conj (W y)) D (1-z.re) (-z.im) P) t D := by
    unfold normalizedSlot rowSlot
    congr 1
    apply Finset.sum_congr rfl
    intro P hP
    rw [physicalSlotCoefficient_annular η W D z P (Finset.mem_filter.mp hP).2.1.ne_zero hD]
  rw [he]
  exact relative_normalizedSlot_eq_ray M H η χ η.inverse m A u hrow
    (fun y=>conj (W y)) b D (1-z.re) t (-z.im) hD

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2214

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniform
Source SHA256: 061aabfa0f4a4cbd471b5ed156c1158683a161b16022bc6dc48129642c47f0c5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2215



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeDetectorDyadicProfiles

theorem compact_family_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (k n : ℕ) :
    ∃C : ℝ,0<C ∧ ∀p∈J,SchwartzMap.seminorm ℝ k n (G p)≤C := by
  have hc := (section_iteratedDeriv_smooth F hF n).continuous.norm
  obtain ⟨M,hM⟩ := (hJ.prod isCompact_Icc).bddAbove_image hc.continuousOn
  refine ⟨1+L^k*(|M|+1),by positivity,?_⟩
  intro p hp
  apply SchwartzMap.seminorm_le_bound' ℝ k n _ (by positivity)
  intro x
  have he : (G p : ℝ→ℂ)=F p := funext (hG p)
  rw [he]
  by_cases hx : x∈Icc (-L) L
  · have hnorm : ‖iteratedDeriv n (F p) x‖≤|M|+1 := by
      have hb := hM (Set.mem_image_of_mem _ (show (p,x)∈J×ˢIcc (-L) L from ⟨hp,hx⟩))
      exact hb.trans (by linarith [le_abs_self M])
    have hxp : ‖x‖^k≤L^k := by
      apply pow_le_pow_left₀ (norm_nonneg _)
      simpa only [Real.norm_eq_abs,abs_le,Set.mem_Icc] using hx
    exact (mul_le_mul hxp hnorm (norm_nonneg _) (pow_nonneg hL k)).trans (by linarith)
  · have hout : iteratedDeriv n (F p) x=0 := by
      by_contra hn
      have hx' := (subset_tsupport (iteratedDeriv n (F p))) hn
      have hh := (CubicReflectionKernel.tsupport_iteratedDeriv_subset (F p) n) hx'
      exact hx ((closure_minimal (hs p) isClosed_Icc) hh)
    rw [hout,norm_zero,mul_zero]
    positivity

theorem compact_family_finite_seminorm
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃C : ℝ,0<C ∧ ∀p∈J,S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (G p)≤C := by
  choose C hC hb using fun z : ℕ×ℕ=>compact_family_seminorm F hF L hL hs J hJ G hG z.1 z.2
  have hsum : 0≤∑z∈S,C z := Finset.sum_nonneg (fun z _=>(hC z).le)
  refine ⟨1+∑z∈S,C z,by linarith,?_⟩
  intro p hp
  apply Seminorm.finset_sup_apply_le (by linarith)
  intro z hz
  apply (hb z p hp).trans
  have hh := Finset.single_le_sum (fun z (_ : z∈S)=>(hC z).le) hz
  linarith

theorem compact_family_frequencyTwist
    (F : (ℝ×ℝ)→ℝ→ℂ) (hF : ContDiff ℝ ∞ (Function.uncurry F))
    (L : ℝ) (hL : 0≤L) (hs : ∀p,Function.support (F p)⊆Icc (-L) L)
    (J : Set (ℝ×ℝ)) (hJ : IsCompact J)
    (G : (ℝ×ℝ)→𝓢(ℝ,ℂ)) (hG : ∀p x,G p x=F p x) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀p∈J,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (JointLogSeparation.frequencyTwist (G p) t)≤C*(1+‖t‖)^n := by
  let S' := S.biUnion (fun z=> (Finset.range (z.2+1)).image (fun i=>(z.1,i)))
  obtain ⟨B,hB,hbound⟩ := compact_family_finite_seminorm F hF L hL hs J hJ G hG S'
  let c : ℕ×ℕ→ℝ := fun z=>(2:ℝ)^z.2*(1+2*Real.pi)^z.2*((z.2+1)*B)
  have hc (z : ℕ×ℕ) : 0≤c z := by dsimp [c];positivity
  have hsum : 0≤∑z∈S,c z := Finset.sum_nonneg (fun z _=>hc z)
  refine ⟨S.sup Prod.snd,1+∑z∈S,c z,by linarith,?_⟩
  intro p hp t
  apply Seminorm.finset_sup_apply_le (by positivity)
  intro z hz
  have hd : JointLogSeparation.derivativeSeminormSum (G p) z.1 z.2≤(z.2+1)*B := by
    unfold JointLogSeparation.derivativeSeminormSum
    calc
      _≤∑i∈Finset.range (z.2+1),B := by
        apply Finset.sum_le_sum
        intro i hi
        have hi' : (z.1,i)∈S' := Finset.mem_biUnion.mpr ⟨z,hz,Finset.mem_image.mpr ⟨i,hi,rfl⟩⟩
        exact (Seminorm.le_finset_sup_apply hi').trans (hbound p hp)
      _=_ := by simp
  have hzC : c z≤1+∑z∈S,c z := by
    have hh := Finset.single_le_sum (fun z (_ : z∈S)=>hc z) hz
    linarith
  have he := JointLogSeparation.frequencyTwist_seminorm_polynomial (G p) t z.1 z.2
  have hb : SchwartzMap.seminorm ℝ z.1 z.2 (JointLogSeparation.frequencyTwist (G p) t)≤c z*(1+‖t‖)^z.2 := by
    apply he.trans
    dsimp only [c]
    gcongr
  exact hb.trans (mul_le_mul hzC
    (pow_le_pow_right₀ (by linarith [norm_nonneg t]) (Finset.le_sup hz)) (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2215

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformLog
Source SHA256: a4998cbac5b5001efcc83c86914d5fa26456fddb67c907addc70bb4182b2921a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2216



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic

def realInterpolatedLog (W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • W (Real.exp x)

lemma realInterpolatedLog_smooth (W : ℝ→ℂ) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (realInterpolatedLog W)) := by
  unfold realInterpolatedLog Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>Real.exp (-p.1.1*p.2))).smul
    (hW.comp (by fun_prop))

lemma realInterpolatedLog_support (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (realInterpolatedLog W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  intro x hx
  have hw : W (Real.exp x)≠0 := by intro hw;exact hx (by simp [realInterpolatedLog,hw])
  have hlo : Real.log a≤x := by simpa only [Real.log_exp] using Real.log_le_log ha (hs hw).1
  have hhi : x≤Real.log b := by simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos x) (hs hw).2
  constructor <;> linarith [neg_abs_le (Real.log a),le_abs_self (Real.log b),abs_nonneg (Real.log a),abs_nonneg (Real.log b)]

def realInterpolatedLogSchwartz (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logSchwartz (twistProfile W p.1 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W p.1 0 a b ha hs hW)

lemma realInterpolatedLogSchwartz_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (p : ℝ×ℝ) (x : ℝ) :
    realInterpolatedLogSchwartz W a b ha hs hW p x=realInterpolatedLog W p x := by
  rw [realInterpolatedLogSchwartz,CubicReflectionKernel.logSchwartz_apply]
  unfold twistProfile realInterpolatedLog
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos x).ne'),
    ←Complex.ofReal_log (Real.exp_pos x).le,Real.log_exp]
  simp only [HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,sub_zero]
  change W (Real.exp x)*Complex.exp ((x:ℂ)*-(p.1:ℂ))=
    ((Real.exp (-p.1*x):ℝ):ℂ)*W (Real.exp x)
  rw [Complex.ofReal_exp,Complex.ofReal_mul,Complex.ofReal_neg]
  have he : (x:ℂ)*-(p.1:ℂ)=-(p.1:ℂ)*(x:ℂ) := by ring
  rw [he,mul_comm]

def interpolatedProfile (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CenteredMomentLattice.normPowerProfile (twistProfile W σ 0) a b ha
    ((twistProfile_support _ _ _).trans hs) (twistProfile_smooth W σ 0 a b ha hs hW) t

lemma interpolatedProfile_apply (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (σ t x : ℝ) :
    interpolatedProfile W a b ha hs hW σ t x=twistProfile W σ t x := by
  rw [interpolatedProfile,CenteredMomentLattice.normPowerProfile_apply]
  unfold twistProfile
  by_cases hw : W x=0
  · simp [hw]
  · have hx : 0<x := ha.trans_le (hs hw).1
    calc
      _=W x*((x:ℂ)^(Complex.I*t)*(x:ℂ)^(-HeckeDyadic.shift σ 0)) := by ring
      _=W x*(x:ℂ)^(Complex.I*t-HeckeDyadic.shift σ 0) := by
        rw [←Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hx.ne')];rfl
      _=_ := by congr 2;unfold HeckeDyadic.shift;simp only [Complex.ofReal_zero,zero_mul,sub_zero];ring

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2216

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformHeight
Source SHA256: 02786e3187ade1aa46acbca98e597dd96f1e00cf85f464711fad6b4644a4e27c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2217


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic JointLogSeparation

 theorem interpolatedProfile_uniform (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hs : Function.support W⊆Icc a b) (hW : ContDiff ℝ ∞ W) (S : Finset (ℕ×ℕ)) :
    ∃n : ℕ,∃C : ℝ,0<C ∧ ∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤C*(1+‖t‖)^n := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CompletedHeight.fixedLogReturnCLM a b ha) S
  obtain ⟨n,B,hB,hbound⟩ := compact_family_frequencyTwist
    (realInterpolatedLog W) (realInterpolatedLog_smooth W hW)
    (|Real.log a|+|Real.log b|) (by positivity) (realInterpolatedLog_support W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ)) (isCompact_Icc.prod isCompact_singleton)
    (realInterpolatedLogSchwartz W a b ha hs hW) (realInterpolatedLogSchwartz_apply W a b ha hs hW) T
  refine ⟨n,A*B,mul_pos hA hB,?_⟩
  intro σ hσ t
  have hp : (σ,0)∈Icc (0:ℝ) 1 ×ˢ ({0}:Set ℝ) := ⟨hσ,rfl⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (interpolatedProfile W a b ha hs hW σ t)≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (realInterpolatedLogSchwartz W a b ha hs hW (σ,0)) (t/(2*Real.pi)))≤B*(1+‖t‖)^n :=
    (hbound (σ,0) hp (t/(2*Real.pi))).trans
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) n) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2217

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseUniformLog
Source SHA256: 759d1f8f4234c3071ee76f234dc7384a7bdc37c6765bf85e696a67602131e25b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2218



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDetectorCoefficientTransfer HeckeDetectorDyadicProfiles
open HeckeDetectorRowwisePolynomial CenteredMomentDetectorDictionary

lemma logTest_apply (W : ℝ→ℂ) (n : ℕ) (x : ℝ) :
    logTest W n x=(Real.log x:ℂ)^n*W x := by
  induction n with
  | zero => simp [logTest]
  | succ n ih => simp only [logTest,logProfile,ih,pow_succ];ring

def baseProfile (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) : ℝ→ℂ :=
  logTest (orientedProfile reverse (ratioProfile V W R)) n

lemma baseProfile_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R : ℝ) :
    Function.support (baseProfile reverse n V W R)⊆Function.support W := by
  apply (logTest_support _ _).trans
  cases reverse
  · exact ratioProfile_support V W R
  · rw [orientedProfile,ite_eq_left rfl,conjugate_profile_support]
    exact ratioProfile_support V W R

lemma baseProfile_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (R a b : ℝ)
    (ha : 0<a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) : ContDiff ℝ ∞ (baseProfile reverse n V W R) := by
  apply logTest_smooth _ n a b ha
  · cases reverse
    · exact (ratioProfile_support V W R).trans hs
    · rw [orientedProfile,ite_eq_left rfl,conjugate_profile_support]
      exact (ratioProfile_support V W R).trans hs
  · have hv : ContDiff ℝ ∞ (ratioProfile V W R) :=
      (hV.comp (by fun_prop)).mul hW
    cases reverse
    · exact hv
    · exact conjugate_profile_smooth _ hv

def inverseLogFamily (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) : ℂ :=
  Real.exp (-p.1*x) • ((x:ℂ)^n*
    (orientedProfile reverse V (p.2*Real.exp x)*orientedProfile reverse W (Real.exp x)))

lemma inverseLogFamily_smooth (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (Function.uncurry (inverseLogFamily reverse n V W)) := by
  have hv : ContDiff ℝ ∞ (orientedProfile reverse V) := by
    cases reverse
    · exact hV
    · exact conjugate_profile_smooth _ hV
  have hw : ContDiff ℝ ∞ (orientedProfile reverse W) := by
    cases reverse
    · exact hW
    · exact conjugate_profile_smooth _ hW
  unfold inverseLogFamily Function.uncurry
  exact (by fun_prop : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>Real.exp (-p.1.1*p.2))).smul
    (((Complex.ofRealCLM.contDiff.comp (contDiff_snd : ContDiff ℝ ∞ (fun p : (ℝ×ℝ)×ℝ=>p.2))).pow n).mul
      ((hv.comp (by fun_prop)).mul (hw.comp (by fun_prop))))

lemma inverseLogFamily_eq (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (p : ℝ×ℝ) (x : ℝ) :
    inverseLogFamily reverse n V W p x=realInterpolatedLog (baseProfile reverse n V W p.2) p x := by
  unfold inverseLogFamily realInterpolatedLog baseProfile
  rw [logTest_apply,Real.log_exp]
  cases reverse <;> simp [orientedProfile,ratioProfile,map_mul]

lemma inverseLogFamily_support (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ)
    (ha : 0<a) (hs : Function.support W⊆Icc a b) (p : ℝ×ℝ) :
    Function.support (inverseLogFamily reverse n V W p)⊆Icc (-(|Real.log a|+|Real.log b|)) (|Real.log a|+|Real.log b|) := by
  have he : inverseLogFamily reverse n V W p=realInterpolatedLog (baseProfile reverse n V W p.2) p :=
    funext (inverseLogFamily_eq reverse n V W p)
  rw [he]
  exact realInterpolatedLog_support _ a b ha ((baseProfile_support reverse n V W p.2).trans hs) p

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end OAIOriginalModule2218

/-! Original module: OAI.NumberTheory.DirichletL.Moments.DetectorDictionaryUniformTests
Source SHA256: 2e4a2dfe4c3499924e985ceab3f89f73ff0fba29f2ce844bffec266e0f824043
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2219


namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.CenteredMomentDetectorDictionary
open HeckeInverseAmplification HeckeDyadic HeckeDetectorCoefficientTransfer
open HeckeDetectorRowwisePolynomial HeckeDetectorDyadicProfiles

lemma twistProfile_zero (W : ℝ→ℂ) : twistProfile W 0 0=W := by
  funext x
  simp [twistProfile,HeckeDyadic.shift]

lemma oriented_detector_log_support (reverse : Bool) (n : ℕ) :
    Function.support (orientedProfile reverse ((logProfile^[n]) positiveAnnular))⊆Icc (1/4) (9/4) := by
  simpa only [twistProfile_zero] using detector_profile_support reverse n 0 0

lemma oriented_detector_log_smooth (reverse : Bool) (n : ℕ) :
    ContDiff ℝ ∞ (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) := by
  simpa only [twistProfile_zero] using detector_profile_smooth reverse n 0 0

def detectorSchwartz (reverse : Bool) (n : ℕ) (σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support reverse n) (oriented_detector_log_smooth reverse n) σ
      (orientedFrequency reverse t)

lemma detectorSchwartz_apply (reverse : Bool) (n : ℕ) (σ t x : ℝ) :
    detectorSchwartz reverse n σ t x=
      twistProfile (orientedProfile reverse ((logProfile^[n]) positiveAnnular)) σ (orientedFrequency reverse t) x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem detectorSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀reverse : Bool,∀n : ℕ,n≤2→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Fin 3=>interpolatedProfile_uniform
    (orientedProfile q.1 ((logProfile^[q.2.val]) positiveAnnular)) (1/4) (9/4)
    (by norm_num) (oriented_detector_log_support q.1 q.2.val) (oriented_detector_log_smooth q.1 q.2.val) S
  let J := (Finset.univ : Finset (Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Fin 3,C q,by linarith,?_⟩
  intro reverse n hn σ hσ t
  let q : Bool×Fin 3 := (reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q σ hσ (orientedFrequency reverse t)
  have hnorm : ‖orientedFrequency reverse t‖=‖t‖ := by cases reverse <;> simp [orientedFrequency]
  rw [hnorm] at he
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (detectorSchwartz reverse n σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.CenteredMomentDetectorDictionary

end

end OAI
end OAIOriginalModule2219

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseUniformScale
Source SHA256: 098fc23b098230b54672519ea49eaceb98c4ddd3460c9f33ccfacf1672faa868
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2220


namespace OAI

noncomputable section
open scoped Classical SchwartzMap
namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification

def scaleCLM : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  (-1/2:ℝ) • ContinuousLinearMap.id ℝ (𝓢(ℝ,ℂ))-
    (SchwartzMap.smulLeftCLM ℂ (fun x : ℝ=>x)).comp (SchwartzMap.derivCLM ℝ ℂ)

lemma scaleCLM_apply (W : 𝓢(ℝ,ℂ)) (x : ℝ) : scaleCLM W x=scaleProfile W x := by
  simp only [scaleCLM,sub_apply,smul_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.comp_apply,
    SchwartzMap.smulLeftCLM_apply_apply Function.HasTemperateGrowth.id',
    SchwartzMap.derivCLM_apply,Complex.real_smul,scaleProfile]
  push_cast
  ring

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end OAIOriginalModule2220

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseUniformFamily
Source SHA256: b73d146afebb23a99e212c826e612fd6933f54ecb895a9713f71035c564c2af5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2221



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic JointLogSeparation CenteredMomentDetectorDictionary

def inverseLogSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) : 𝓢(ℝ,ℂ) :=
  realInterpolatedLogSchwartz (baseProfile reverse n V W p.2) a b ha
    ((baseProfile_support reverse n V W p.2).trans hs)
    (baseProfile_smooth reverse n V W p.2 a b ha hV hW hs) p

lemma inverseLogSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (p : ℝ×ℝ) (x : ℝ) :
    inverseLogSchwartz reverse n V W a b ha hV hW hs p x=inverseLogFamily reverse n V W p x := by
  rw [inverseLogSchwartz,realInterpolatedLogSchwartz_apply,inverseLogFamily_eq]

def inverseSchwartz (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  interpolatedProfile (baseProfile reverse n V W R) a b ha
    ((baseProfile_support reverse n V W R).trans hs)
    (baseProfile_smooth reverse n V W R a b ha hV hW hs) σ t

lemma inverseSchwartz_apply (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W) (hs : Function.support W⊆Icc a b)
    (R σ t x : ℝ) :
    inverseSchwartz reverse n V W a b ha hV hW hs R σ t x=
      twistProfile (baseProfile reverse n V W R) σ t x :=
  interpolatedProfile_apply _ _ _ _ _ _ _ _ _

theorem inverseSchwartz_operator_uniform (reverse : Bool) (n : ℕ) (V W : ℝ→ℂ)
    (a b : ℝ) (ha : 0<a) (hV : ContDiff ℝ ∞ V) (hW : ContDiff ℝ ∞ W)
    (hs : Function.support W⊆Icc a b) (Rmax : ℝ)
    (op : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ)) (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀R∈Icc (0:ℝ) Rmax,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤C*(1+‖t‖)^J := by
  obtain ⟨T,A,hA,hcontrol⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (op.comp (CompletedHeight.fixedLogReturnCLM a b ha)) S
  obtain ⟨J,B,hB,hbound⟩ := compact_family_frequencyTwist
    (inverseLogFamily reverse n V W) (inverseLogFamily_smooth reverse n V W hV hW)
    (|Real.log a|+|Real.log b|) (by positivity) (inverseLogFamily_support reverse n V W a b ha hs)
    (Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax) (isCompact_Icc.prod isCompact_Icc)
    (inverseLogSchwartz reverse n V W a b ha hV hW hs)
    (inverseLogSchwartz_apply reverse n V W a b ha hV hW hs) T
  refine ⟨J,A*B,mul_pos hA hB,?_⟩
  intro R hR σ hσ t
  have hp : (σ,R)∈Icc (0:ℝ) 1 ×ˢ Icc (0:ℝ) Rmax := ⟨hσ,hR⟩
  have hheight : ‖t/(2*Real.pi)‖≤‖t‖ := by
    rw [norm_div,Real.norm_of_nonneg (by positivity : 0≤2*Real.pi)]
    exact div_le_self (norm_nonneg _) (by linarith [Real.pi_gt_three])
  have hh := hcontrol (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (op (inverseSchwartz reverse n V W a b ha hV hW hs R σ t))≤_ at hh
  apply hh.trans
  have hb : T.sup (schwartzSeminormFamily ℝ ℝ ℂ)
      (frequencyTwist (inverseLogSchwartz reverse n V W a b ha hV hW hs (σ,R)) (t/(2*Real.pi)))≤B*(1+‖t‖)^J :=
    (hbound (σ,R) hp (t/(2*Real.pi))).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) (by linarith) J) hB.le)
  exact (mul_le_mul_of_nonneg_left hb hA.le).trans_eq (by ring)

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end OAIOriginalModule2221

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseUniformTests
Source SHA256: 196e776c64e0c63cd48a9d818c218974e3f7713adbc623e81c2442f83d03a8f6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2222



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles

def sourceOperator (scaled : Bool) : 𝓢(ℝ,ℂ)→L[ℝ]𝓢(ℝ,ℂ) :=
  if scaled then scaleCLM else ContinuousLinearMap.id ℝ _

def inverseDetectorSchwartz (reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseSchwartz reverse n cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support R σ t

lemma inverseDetectorSchwartz_apply (reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorSchwartz reverse n R σ t x=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x :=
  inverseSchwartz_apply _ _ _ _ _ _ _ _ _ _ _ _ _ _

def inverseDetectorTest (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  sourceOperator scaled (inverseDetectorSchwartz reverse n R σ t)

lemma inverseDetectorTest_apply (scaled reverse : Bool) (n : ℕ) (R σ t x : ℝ) :
    inverseDetectorTest scaled reverse n R σ t x=
      if scaled then scaleProfile (twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t) x
      else twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t x := by
  have he : (inverseDetectorSchwartz reverse n R σ t : ℝ→ℂ)=
      twistProfile (baseProfile reverse n cutoff positiveAnnular R) σ t :=
    funext (inverseDetectorSchwartz_apply reverse n R σ t)
  cases scaled
  · exact inverseDetectorSchwartz_apply _ _ _ _ _ _
  · change scaleCLM (inverseDetectorSchwartz reverse n R σ t) x=_
    rw [scaleCLM_apply,he]
    rfl

theorem inverseDetectorTest_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R∈Icc (0:ℝ) 4,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤C*(1+‖t‖)^J := by
  choose degree C hC hb using fun q : Bool×Bool×Fin 3=>inverseSchwartz_operator_uniform
    q.2.1 q.2.2.val cutoff positiveAnnular (1/4) (9/4) (by norm_num)
    (cutoff.smooth ⊤) positiveAnnular_smooth positiveAnnular_support 4 (sourceOperator q.1) S
  let J := (Finset.univ : Finset (Bool×Bool×Fin 3)).sup degree
  have hsum : 0≤∑q : Bool×Bool×Fin 3,C q := Finset.sum_nonneg (fun q _=>(hC q).le)
  refine ⟨J,1+∑q : Bool×Bool×Fin 3,C q,by linarith,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  let q : Bool×Bool×Fin 3 := (scaled,reverse,⟨n,by omega⟩)
  have hCq : C q≤1+∑q : Bool×Bool×Fin 3,C q := by
    have hh := Finset.single_le_sum (fun q (_ : q∈(Finset.univ : Finset (Bool×Bool×Fin 3)))=>(hC q).le) (Finset.mem_univ q)
    linarith
  have hdegree : degree q≤J := Finset.le_sup (Finset.mem_univ q)
  have he := hb q R hR σ hσ t
  change S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤_ at he
  exact he.trans (mul_le_mul hCq (pow_le_pow_right₀ (by linarith [norm_nonneg t]) hdegree)
    (by positivity) (by linarith))

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end OAIOriginalModule2222

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseUniformSource
Source SHA256: b3fddbbb0ffd420c5dd5ae3f1e6eed6e90452c6e1193ce09153dd90ba0787c3a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2223



namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff Topology
open Set

namespace SevenEighths.DetectorDictionaryInverseUniform
open HeckeInverseAmplification HeckeDyadic HeckeDetectorProfiles HeckeDetectorDyadicProfiles
open HeckeDetectorCoefficientTransfer HeckeDetectorRowwisePolynomial

lemma positiveAnnular_support_sharp : Function.support positiveAnnular⊆Ioo (1/2) 2 := by
  intro x hx
  have hx0 : 0≤x := by have := (positiveAnnular_support hx).1; linarith
  have he : DyadicTransfer.annularCutoff cutoff x≠0 := by
    rwa [←positiveAnnular_eq x hx0]
  simpa using HeckeDetectorPartition.annular_support cutoff cutoff_one cutoff_zero x hx0 0 (by simpa using he)

lemma ratioProfile_zero_of_four_le (R : ℝ) (hR : 4≤R) :
    ratioProfile cutoff positiveAnnular R=0 := by
  funext x
  by_cases hx : positiveAnnular x=0
  · simp [ratioProfile,hx]
  · have hs := positiveAnnular_support_sharp hx
    have hrx : 2≤R*x := by nlinarith [hs.1]
    simp [ratioProfile,cutoff_zero _ hrx]

lemma inverseDetectorTest_zero_of_four_le (scaled reverse : Bool) (n : ℕ) (R σ t : ℝ)
    (hR : 4≤R) : inverseDetectorTest scaled reverse n R σ t=0 := by
  have hz : inverseDetectorSchwartz reverse n R σ t=0 := by
    ext x
    rw [inverseDetectorSchwartz_apply]
    simp only [baseProfile,ratioProfile_zero_of_four_le R hR]
    cases reverse <;> simp [orientedProfile,twistProfile,HeckeDyadic.shift,logTest_apply]
  rw [inverseDetectorTest,hz,map_zero]

theorem inverseDetectorTest_uniform_all_ratios (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀R : ℝ,0≤R→∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseDetectorTest scaled reverse n R σ t)≤C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn R hR σ hσ t
  by_cases hh : R≤4
  · exact hb scaled reverse n hn R ⟨hR,hh⟩ σ hσ t
  · rw [inverseDetectorTest_zero_of_four_le _ _ _ _ _ _ (le_of_not_ge hh),map_zero]
    positivity

def inverseSourceSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  inverseDetectorTest scaled reverse n (U^r/U^tstar) σ t

lemma inverseSourceSchwartz_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    inverseSourceSchwartz scaled reverse n U tstar r σ t x=
      if scaled then scaleProfile (twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t) x
      else twistProfile
        (logTest (orientedProfile reverse (HeckeDetectorInverseFiberCount.inverseTest U tstar r)) n) σ t x := by
  simp only [inverseSourceSchwartz,inverseDetectorTest_apply,baseProfile,
    HeckeDetectorInverseFiberCount.inverseTest,inverseProfile_eq_ratio]

theorem inverseSourceSchwartz_uniform (S : Finset (ℕ×ℕ)) :
    ∃J : ℕ,∃C : ℝ,0<C ∧ ∀scaled reverse : Bool,∀n : ℕ,n≤2→
      ∀U : ℝ,0<U→∀tstar r : ℝ,∀σ∈Icc (0:ℝ) 1,∀t : ℝ,
      S.sup (schwartzSeminormFamily ℝ ℝ ℂ) (inverseSourceSchwartz scaled reverse n U tstar r σ t)≤C*(1+‖t‖)^J := by
  obtain ⟨J,C,hC,hb⟩ := inverseDetectorTest_uniform_all_ratios S
  refine ⟨J,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t
  exact hb scaled reverse n hn (U^r/U^tstar) (by positivity) σ hσ t

end SevenEighths.DetectorDictionaryInverseUniform

end

end OAI
end OAIOriginalModule2223

/-! Original module: OAI.NumberTheory.DirichletL.Dictionary.InverseClippedUniform
Source SHA256: 81ed9ccd76253d82b0e6413a8a597780dd9eab0772e9d31fc98a056fb197729b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2224





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap FourierTransform ContDiff
open MeasureTheory FourierBridge

namespace SevenEighths.DetectorDictionaryInverseClippedUniform
open DetectorDictionaryInverseUniform HeckeInverseAmplification
open InverseMoment InverseInitialClippedColumns InverseInitialOverlapFourier
open ActualEisensteinCubic CompletedGauss
local notation "O" => ActualEisensteinCubic.O

theorem source_support (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    Function.support (inverseSourceSchwartz scaled reverse n U tstar r σ t : ℝ→ℂ) ⊆
      Set.Icc (1/4 : ℝ) (9/4) := by
  let W := inverseDetectorSchwartz reverse n (U^r/U^tstar) σ t
  have hw : Function.support (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) := by
    have he : (W : ℝ→ℂ) = twistProfile
        (baseProfile reverse n HeckeDetectorProfiles.cutoff
          HeckeDetectorDyadicProfiles.positiveAnnular (U^r/U^tstar)) σ t := by
      funext x
      exact inverseDetectorSchwartz_apply _ _ _ _ _ _
    rw [he]
    exact (twistProfile_support _ _ _).trans
      ((baseProfile_support _ _ _ _ _).trans HeckeDetectorDyadicProfiles.positiveAnnular_support)
  have ht : tsupport (W : ℝ→ℂ) ⊆ Set.Icc (1/4 : ℝ) (9/4) :=
    closure_minimal hw isClosed_Icc
  cases scaled
  · exact hw
  · intro x hx
    by_contra hn
    have hz : W x = 0 := by
      by_contra h
      exact hn (hw h)
    have hd : deriv (W : ℝ→ℂ) x = 0 := by
      by_contra h
      exact hn (ht (support_deriv_subset h))
    apply hx
    change scaleCLM W x = 0
    rw [scaleCLM_apply]
    simp [scaleProfile, hz, hd]

theorem source_zero_of_ratio (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ)
    (h : 4 ≤ U^r/U^tstar) : inverseSourceSchwartz scaled reverse n U tstar r σ t = 0 :=
  inverseDetectorTest_zero_of_four_le scaled reverse n _ σ t h

theorem exists_reference_window :
    ∃w : 𝓢(ℝ,ℂ), HasCompactSupport (w : ℝ→ℂ) ∧
      tsupport (w : ℝ→ℂ) ⊆ Set.Icc (1/18 : ℝ) (13/4) ∧
      ∀x∈Set.Icc (1/9 : ℝ) (9/4), w x = 1 := by
  obtain ⟨w,hc,hone,hs⟩ := InverseSecondChildWindows.positive_cutoff
    (1/9 : ℝ) (9/4) (by norm_num) (by norm_num)
  refine ⟨w,hc,?_,hone⟩
  convert hs using 1
  norm_num

def referenceWindow : 𝓢(ℝ,ℂ) := Classical.choose exists_reference_window

theorem referenceWindow_compact : HasCompactSupport (referenceWindow : ℝ→ℂ) :=
  (Classical.choose_spec exists_reference_window).1

theorem referenceWindow_support : tsupport (referenceWindow : ℝ→ℂ) ⊆
    Set.Icc (1/18 : ℝ) (13/4) :=
  (Classical.choose_spec exists_reference_window).2.1

theorem referenceWindow_one (x : ℝ) (hx : x∈Set.Icc (1/9 : ℝ) (9/4)) :
    referenceWindow x = 1 :=
  (Classical.choose_spec exists_reference_window).2.2 x hx

theorem referenceWindow_agrees (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c y : ℝ)
    (hc : 1≤c) (hcb : c≤9/4) (hy : 0<y) :
    referenceWindow y * inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) := by
  by_cases hz : inverseSourceSchwartz scaled reverse n U tstar r σ t (c*y) = 0
  · simp [hz]
  have hs := source_support scaled reverse n U tstar r σ t hz
  have hh : y∈Set.Icc (1/9 : ℝ) (9/4) := by
    constructor <;> nlinarith [hs.1,hs.2]
  rw [referenceWindow_one y hh,one_mul]

def logSource (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) : 𝓢(ℝ,ℂ) :=
  CubicReflectionKernel.logPullbackCLM (1/4) (9/4)
    (inverseSourceSchwartz scaled reverse n U tstar r σ t)

theorem logSource_apply (scaled reverse : Bool) (n : ℕ) (U tstar r σ t x : ℝ) :
    logSource scaled reverse n U tstar r σ t x =
      inverseSourceSchwartz scaled reverse n U tstar r σ t (Real.exp x) :=
  CubicReflectionKernel.logPullbackCLM_eq_actual _ _ (by norm_num) _
    (source_support scaled reverse n U tstar r σ t) x

theorem logSource_eq_logSchwartz (scaled reverse : Bool) (n : ℕ) (U tstar r σ t : ℝ) :
    logSource scaled reverse n U tstar r σ t =
      CubicReflectionKernel.logSchwartz (inverseSourceSchwartz scaled reverse n U tstar r σ t)
        (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
        ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤) := by
  ext x
  rw [logSource_apply,CubicReflectionKernel.logSchwartz_apply]

def familyDensity (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) : ℂ :=
  density (logSource scaled reverse n U tstar r σ t) (Real.log c) v

theorem familyDensity_formula (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    familyDensity scaled reverse n U tstar r σ t c v =
      (𝓕 (logSource scaled reverse n U tstar r σ t)) v * logPhase v (Real.log c) := rfl

theorem familyDensity_norm (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c v : ℝ) :
    ‖familyDensity scaled reverse n U tstar r σ t c v‖ =
      ‖(𝓕 (logSource scaled reverse n U tstar r σ t)) v‖ := density_norm _ _ _

theorem familyDensity_integrable (J : ℕ) (scaled reverse : Bool) (n : ℕ)
    (U tstar r σ t c : ℝ) :
    Integrable (fun v : ℝ => (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) := by
  simp only [familyDensity_norm]
  exact AnalyticBridge.schwartz_fourier_one_plus_integrable _ _

theorem familyDensity_moment (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
      ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t c : ℝ,
      (∫v : ℝ, (1+‖v‖)^J * ‖familyDensity scaled reverse n U tstar r σ t c v‖) ≤
        C*(1+‖t‖)^K := by
  let p := (volume : Measure ℝ).integrablePower
  let S : Finset (ℕ×ℕ) := Finset.Iic (p,J+p)
  obtain ⟨T,A,hA,hop⟩ := EisensteinSchwartzPoisson.schwartzCLM_finite_seminorm_control
    (CubicReflectionKernel.logPullbackCLM (1/4) (9/4)) S
  obtain ⟨K,B,hB,hsource⟩ := inverseSourceSchwartz_uniform T
  let C := 1+(2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B))
  have hC : 0<C := by
    have h₀ := coefficientMomentBound_nonneg 0 (2*A*B) (by positivity)
    have hJ := coefficientMomentBound_nonneg J (2*A*B) (by positivity)
    dsimp [C]
    positivity
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t c
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  let g := logSource scaled reverse n U tstar r σ t
  have hb : S.sup (schwartzSeminormFamily ℝ ℝ ℂ) g ≤ A*B*(1+‖t‖)^K := by
    exact (hop W).trans ((mul_le_mul_of_nonneg_left
      (hsource scaled reverse n hn U hU tstar r σ hσ t) hA.le).trans_eq (by ring))
  have hs (i : ℕ) (hi : i≤J+p) :
      (SchwartzMap.seminorm ℝ 0 i) g + (SchwartzMap.seminorm ℝ p i) g ≤
        2*A*B*(1+‖t‖)^K := by
    have h₀ : schwartzSeminormFamily ℝ ℝ ℂ (0,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have hp : schwartzSeminormFamily ℝ ℝ ℂ (p,i) ≤ S.sup (schwartzSeminormFamily ℝ ℝ ℂ) :=
      Finset.le_sup (f:=schwartzSeminormFamily ℝ ℝ ℂ) (by simp [S,hi])
    have h₁ := (Seminorm.le_def.mp h₀ g).trans hb
    have h₂ := (Seminorm.le_def.mp hp g).trans hb
    change (SchwartzMap.seminorm ℝ 0 i) g ≤ _ at h₁
    change (SchwartzMap.seminorm ℝ p i) g ≤ _ at h₂
    linarith
  have hmoment := uniform_fourier_one_plus_moment g J 1
    (2*A*B*(1+‖t‖)^K) (by norm_num) (by positivity)
    (by intro i hi; simpa only [one_mul] using hs i hi)
  simp only [one_mul] at hmoment
  simp only [familyDensity_norm]
  apply hmoment.trans
  have he : (2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B*(1+‖t‖)^K)+
      coefficientMomentBound J (2*A*B*(1+‖t‖)^K)) =
      ((2 : ℝ)^J*(coefficientMomentBound 0 (2*A*B)+coefficientMomentBound J (2*A*B)))*(1+‖t‖)^K := by
    unfold coefficientMomentBound
    ring
  rw [he]
  dsimp [C]
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)

section Rows
variable {ι ρ : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})

theorem canonical_family_mode_integrable
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m f k : O) (slots : Finset ρ)
    (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c θ X : ℝ) :
    Integrable (fun v : ℝ => familyDensity scaled reverse n U tstar r σ t c v *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
        (childLogTest referenceWindow (θ+v)) X) :=
  canonical_clipped_mode_integrable p hp hcop hg hpr pool Ψ m f k slots lists a
    (logSource scaled reverse n U tstar r σ t) referenceWindow c θ X

theorem canonical_clipped_family_fourier
    (hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m f k : O) (slots : Finset ρ)
    (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (scaled reverse : Bool) (n : ℕ) (U tstar r σ t c θ X : ℝ)
    (hc : 1≤c) (hcb : c≤9/4) (hX : 0<X) :
    finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
      (clippedTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) c θ) X =
    ∫v : ℝ, familyDensity scaled reverse n U tstar r σ t c v *
      finiteCanonicalMarkedRow p hp hcop hg pool Ψ m f k slots lists a
        (childLogTest referenceWindow (θ+v)) X := by
  simp only [familyDensity,logSource_eq_logSchwartz]
  exact canonical_clipped_fourier p hp hcop hg hpr pool Ψ m f k slots lists a
    (inverseSourceSchwartz scaled reverse n U tstar r σ t) (1/4) (9/4) (by norm_num)
    (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow c θ X (zero_lt_one.trans_le hc) hX
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t c y hc hcb hy)
end Rows

theorem canonical_clipped_family_energy (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
    ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t : ℝ,
    ∀{ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (slots : Finset ρ) (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O→ℝ) (_hD : ∀f∈labels,0≤D f)
    (c θ X Z F E : ℝ), 1≤c → c≤9/4 → 0<X → 0≤E →
    (∀s, normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest referenceWindow s) X Z F ≤ E*(1+‖s‖)^(2*J)) →
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (clippedTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) c θ) X Z F ≤
        C*E*(1+‖t‖)^(2*K)*(1+‖θ‖)^(2*J) := by
  obtain ⟨K,C,hC,hmass⟩ := familyDensity_moment J
  refine ⟨K,C^2,by positivity,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t ι ρ _ _ p hp _ hcop hg hpr
    pool Ψ m slots lists a labels rows D hD c θ X Z F E hc hcb hX hE he
  have hb := canonical_clipped_energy p hp hcop hg hpr pool Ψ m slots lists a
    labels rows D hD (inverseSourceSchwartz scaled reverse n U tstar r σ t)
    (1/4) (9/4) (by norm_num) (source_support scaled reverse n U tstar r σ t)
    ((inverseSourceSchwartz scaled reverse n U tstar r σ t).smooth ⊤)
    referenceWindow c θ X Z F E J (zero_lt_one.trans_le hc) hX hE
    (fun y hy=>referenceWindow_agrees scaled reverse n U tstar r σ t c y hc hcb hy) he
  have hm := hmass scaled reverse n hn U hU tstar r σ hσ t c
  simp only [familyDensity_norm,logSource_eq_logSchwartz] at hm
  have hs := pow_le_pow_left₀
    (integral_nonneg (fun v : ℝ => by positivity)) hm 2
  apply hb.trans
  calc
    _ ≤ E*(1+‖θ‖)^(2*J)*(C*(1+‖t‖)^K)^2 :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = _ := by rw [mul_pow,←pow_mul]; ring_nf

theorem initial_raw_family_energy (J : ℕ) :
    ∃K : ℕ, ∃C : ℝ, 0<C ∧ ∀scaled reverse : Bool, ∀n : ℕ, n≤2 →
    ∀U : ℝ, 0<U → ∀tstar r : ℝ, ∀σ∈Set.Icc (0 : ℝ) 1, ∀t : ℝ,
    ∀{ι ρ : Type*} [DecidableEq ι] [DecidableEq ρ]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,ConcretePrimeRowBridge.goodLambda∉Ideal.span {p i})
    (_hpr : ∀i,ConcretePrimeRowBridge.goodLambda^2∣p i-1)
    (pool : Finset ι) (Ψ : O→*ℂ) (m : O) (slots : Finset ρ) (lists : ρ→Finset ι) (a : ρ→ι→ℂ)
    (labels : Finset (Ideal O)) (rows : Finset O) (D : Ideal O→ℝ) (_hD : ∀f∈labels,0≤D f)
    (Z N F E : ℝ) (z : JointLogSeparation.Frequency×(Fin 6→ℝ)) (h : ℝ), 1<Z → 0≤E →
    (h = -InverseInitialClippedColumns.leftHeight z ∨ h = InverseInitialClippedColumns.rightHeight z) →
    (∀s, normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest referenceWindow s) (Z^(max 0 N)) Z F ≤ E*(1+‖s‖)^(2*J)) →
    normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest (inverseSourceSchwartz scaled reverse n U tstar r σ t) h) (Z^N) Z F ≤
        C*E*(1+‖t‖)^(2*K)*
          (InverseMoment.tripleHeight (4*J) z.1 * InverseMoment.coordinateHeight (4*J) z.2) := by
  obtain ⟨K,C,hC,hbound⟩ := canonical_clipped_family_energy J
  refine ⟨K,C,hC,?_⟩
  intro scaled reverse n hn U hU tstar r σ hσ t ι ρ _ _ p hp _ hcop hg hpr
    pool Ψ m slots lists a labels rows D hD Z N F E z h hZ hE hh he
  let W := inverseSourceSchwartz scaled reverse n U tstar r σ t
  by_cases hne : (freshColumns p pool W (Z^N)).Nonempty
  · obtain ⟨hc,hcb⟩ := freshColumns_clipping_range p hp pool W (1/4) (9/4)
      Z N hZ (by norm_num) (source_support scaled reverse n U tstar r σ t) hne
    rw [InverseInitialEnergyCallerClipping.normalized_energy_clipping p hp hcop hg
      pool Ψ m slots lists a labels rows D W (by linarith) N h F]
    apply (hbound scaled reverse n hn U hU tstar r σ hσ t
      p hp hcop hg hpr pool Ψ m slots lists a labels rows D hD
      (Z^(max 0 N-N)) h (Z^(max 0 N)) Z F E hc hcb (by positivity) hE he).trans
    exact mul_le_mul_of_nonneg_left
      (InverseInitialEnergyCallerUniform.initial_height_bound J z h hh) (by positivity)
  · have hz := Finset.not_nonempty_iff_eq_empty.mp hne
    change normalizedColumnEnergy p hp hcop hg pool Ψ m slots lists a labels rows D
      (childLogTest W h) (Z^N) Z F ≤ _
    unfold normalizedColumnEnergy
    simp_rw [canonical_row_zero_of_freshColumns_empty p hp hcop hg pool Ψ m _ _
      slots lists a W (Z^N) h hz,mul_zero,norm_zero,zero_pow (by omega : (2 : ℕ)≠0),
      Finset.sum_const_zero,mul_zero,Finset.sum_const_zero]
    dsimp [InverseMoment.tripleHeight,InverseMoment.coordinateHeight]
    positivity

end SevenEighths.DetectorDictionaryInverseClippedUniform

end

end OAI
end OAIOriginalModule2224

/-! Original module: OAI.NumberTheory.DirichletL.Moments.LiveCapacity
Source SHA256: 830fc6fa183f7da62fbd40121fdca927bca137599475729ce61e8cab38d4fa76
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2225


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentLiveCapacity

 def excess {ι:Type*} (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ:ℝ) : ℝ :=
  max (n₁+n₂+6*κ*(∑i∈J,w i)-M) 0

 theorem remaining_capacity {ι:Type*} [DecidableEq ι]
    (J R:Finset ι) (hR:R⊆J) (w:ι→ℝ) (n₁ n₂ M κ:ℝ)
    (hpay:R=J ∨ excess J w n₁ n₂ M κ≤6*κ*(∑i∈R,w i)) :
    R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤M := by
  rcases hpay with h|h
  · exact Or.inl h
  · right
    have hs:=Finset.sum_sdiff hR (f:=w)
    have hm:=le_max_left (n₁+n₂+6*κ*(∑i∈J,w i)-M) (0:ℝ)
    change max _ _≤_ at h
    have hh:=hm.trans h
    rw [←hs] at hh
    nlinarith

 theorem removal_excess_cost {ι:Type*} [DecidableEq ι]
    (J:Finset ι) (w:ι→ℝ) (n₁ n₂ M κ mesh:ℝ)
    (hκ:0<κ) (hm:0≤mesh) (hw:∀i∈J,0≤w i) (hwm:∀i∈J,w i≤mesh) :
    ∃R:Finset ι,R⊆J ∧ (R=J ∨ n₁+n₂+6*κ*(∑i∈J\R,w i)≤M) ∧
      κ*(∑i∈R,w i)≤excess J w n₁ n₂ M κ/6+κ*mesh := by
  obtain ⟨R,hR,hbound,hpay,hcost⟩:=CenteredMomentWholeSlotDeletion.whole_removal
    J w (excess J w n₁ n₂ M κ) κ mesh (le_max_right _ _) hκ hm hw hwm
  exact ⟨R,hR,remaining_capacity J R hR w n₁ n₂ M κ hpay,hcost⟩

end SevenEighths.CenteredMomentLiveCapacity

end

end OAI
end OAIOriginalModule2225

/-! Original module: OAI.NumberTheory.DirichletL.Energy.ReferenceDeletionBudget
Source SHA256: ecaee06f0788f5172c15d6f6888154a9a7b072a6d36e8fb5ff2480fc4ef64333
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2226




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.CenteredMomentEnergyReferenceDeletionBudget
open HeckeFamily CenteredMomentCommonMaskExpansion CenteredMomentReflectionMass
open CenteredMomentReflectionDeletion UniqueFactorizationMonoid
local notation "O"=>HeckeFamily.O

lemma product_norm_ge_one (D:Finset (Ideal O))(hD:∀I∈D,Prime I):
    (1:ℝ)≤(∏I∈D,I).absNorm:=by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr
    (Ideal.absNorm_eq_zero_iff.not.mpr (subset_product_nonzero D hD))

lemma weighted_inverse_sqrt (I:Ideal O)(hI:I≠0)(t:ℝ)(ht:t≤1/2):
    weight I*(I.absNorm:ℝ)^t≤1:=by
  have hn:(1:ℝ)≤I.absNorm:=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hI)
  have hp:(0:ℝ)<I.absNorm:=zero_lt_one.trans_le hn
  rw [weight,Real.sqrt_eq_rpow,←Real.rpow_neg hp.le,←Real.rpow_add hp]
  exact Real.rpow_le_one_of_one_le_of_nonpos hn (by linarith)

lemma powerset_square_subpower (eps:ℝ)(heps:0<eps):
    ∃C:ℝ,0<C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I),
      (R.powerset.card:ℝ)^2≤C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨C,hC,hb⟩:=HeckeDeletionBounds.constant_pow_primeSupport_bound 4 eps (by norm_num) heps
  refine ⟨C,hC,?_⟩
  intro R hR
  have hf:normalizedFactors (∏I∈R,I)=R.val:=by
    simpa using normalizedFactors_prod_of_prime (m:=R.val) hR
  have hs:IdealMobiusDivisorSum.primeSupport (∏I∈R,I)=R:=by
    simp [IdealMobiusDivisorSum.primeSupport,hf]
  have hh:=hb (∏I∈R,I) (subset_product_nonzero R hR)
  rw [hs] at hh
  convert hh using 1
  rw [Finset.card_powerset,Nat.cast_pow,Nat.cast_ofNat,←pow_mul, mul_comm R.card 2,pow_mul]
  norm_num

variable {α:Type*}

lemma weighted_uniform_term (R D₁ D₂:Finset (Ideal O))
    (hR:∀I∈R,Prime I)(hD₁:D₁⊆R)(hD₂:D₂⊆R)(J:Finset α)
    (b M:α→ℝ)(hM:∀i∈J,0≤M i)(t:ℝ)(ht:t≤1/2):
    uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t≤
      ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
  have hn₂:=subset_product_nonzero D₂ (fun I hi=>hR I (hD₂ hi))
  have hw₁:weight (∏I∈D₁,I)≤1:=by
    simpa using weighted_inverse_sqrt (∏I∈D₁,I)
      (subset_product_nonzero D₁ (fun I hi=>hR I (hD₁ hi))) 0 (by norm_num)
  have hw₂:=weighted_inverse_sqrt (∏I∈D₂,I) hn₂ t ht
  have hprod:0≤∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=
    Finset.prod_nonneg (fun i hi=>mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
      (Finset.sum_nonneg (fun I _=>weight_nonneg I)))
  unfold uniformMajorant
  calc
    _=(weight (∏I∈D₁,I)*(weight (∏I∈D₂,I)*((∏I∈D₂,I).absNorm:ℝ)^t))*
        (∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by ring
    _≤1*(∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul hw₁ hw₂ (mul_nonneg (weight_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) t))
          zero_le_one).trans_eq (one_mul 1)) hprod
    _=_:=one_mul _

lemma signed_weighted_term (χ:Character)(R D₁ D₂:Finset (Ideal O))
    (hR:∀I∈R,Prime I)(hD₁:D₁⊆R)(hD₂:D₂⊆R)(J:Finset α)
    (pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P b M:α→ℝ)
    (hp:∀i∈J,∀I∈pool i,Prime I)(hP:∀i∈J,0<P i)(hM:∀i∈J,0≤M i)
    (hβ:∀i∈J,∀I∈pool i,‖β i I‖≤M i)
    (hs:∀i∈J,∀I∈pool i,β i I≠0→(I.absNorm:ℝ)≤b i*P i)
    (t:ℝ)(ht:t≤1/2):
    ‖signedCoefficient χ R D₁ D₂ J pool β P‖*((∏I∈D₂,I).absNorm:ℝ)^t≤
      ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
  have hn₂:=subset_product_nonzero D₂ (fun I hi=>hR I (hD₂ hi))
  have hw₁:weight (∏I∈D₁,I)≤1:=by
    simpa using weighted_inverse_sqrt (∏I∈D₁,I)
      (subset_product_nonzero D₁ (fun I hi=>hR I (hD₁ hi))) 0 (by norm_num)
  have hw₂:=weighted_inverse_sqrt (∏I∈D₂,I) hn₂ t ht
  have hprod:0≤∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=
    Finset.prod_nonneg (fun i hi=>mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
      (Finset.sum_nonneg (fun I _=>weight_nonneg I)))
  apply (mul_le_mul_of_nonneg_right
    (signedCoefficient_uniform χ R hR D₁ D₂ hD₁ hD₂ J pool β P b M hp hP hM hβ hs)
    (Real.rpow_nonneg (Nat.cast_nonneg _) t)).trans
  unfold uniformMajorant
  calc
    _=(weight (∏I∈D₁,I)*(weight (∏I∈D₂,I)*((∏I∈D₂,I).absNorm:ℝ)^t))*
        (∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by ring
    _≤1*(∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=
      mul_le_mul_of_nonneg_right
        ((mul_le_mul hw₁ hw₂ (mul_nonneg (weight_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) t))
          zero_le_one).trans_eq (one_mul 1)) hprod
    _=_:=one_mul _

lemma slot_majorant_mass (R:Finset (Ideal O))(hR:∀I∈R,Prime I)
    (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤M i):
    (∑J∈F.powerset,∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I))≤
      (∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i))*(∏I∈R,localMass I)^F.card:=by
  rw [←Finset.prod_one_add]
  have he:1+∑I∈R,weight I≤∏I∈R,localMass I:=
    (one_add_sum_weight R).trans (deletion_le_euler R hR)
  have hp (i:α)(hi:i∈F):1+(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)≤
      max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I):=by
    have h1:=le_max_left 1 (Real.sqrt (max 1 (b i))*M i)
    have h2:=le_max_right 1 (Real.sqrt (max 1 (b i))*M i)
    have hs:0≤∑I∈R,weight I:=Finset.sum_nonneg (fun I _=>weight_nonneg I)
    nlinarith
  calc
    _≤∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)*(∏I∈R,localMass I):=
      Finset.prod_le_prod₀ (fun i hi=>add_nonneg zero_le_one
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hM i hi))
          (Finset.sum_nonneg (fun I _=>weight_nonneg I)))) hp
    _=_:=by rw [Finset.prod_mul_distrib,Finset.prod_const]

theorem weighted_uniform_mass_subpower (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤M i)
    (eps:ℝ)(heps:0<eps):
    ∃C:ℝ,0<C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I),
      ∀t:ℝ,t≤1/2→
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t)≤
        C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨Cc,hCc,hcard⟩:=powerset_square_subpower (eps/2) (by linarith)
  let delta:=eps/(2*((F.card:ℝ)+1))
  have hd:0<delta:=div_pos heps (by positivity)
  obtain ⟨Ce,hCe,heuler⟩:=euler_mass_subpower delta hd
  let A:ℝ:=∏i∈F,max 1 (Real.sqrt (max 1 (b i))*M i)
  have hA:0<A:=Finset.prod_pos (fun i _=>lt_of_lt_of_le zero_lt_one (le_max_left _ _))
  refine ⟨Cc*A*Ce^F.card,by positivity,?_⟩
  intro R hR t ht
  have hsum:(∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
      uniformMajorant R D₁ D₂ J b M*((∏I∈D₂,I).absNorm:ℝ)^t)≤
      (R.powerset.card:ℝ)^2*(∑J∈F.powerset,
        ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I)):=by
    calc
      _≤∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
          ∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
        apply Finset.sum_le_sum;intro D₁ hD₁
        apply Finset.sum_le_sum;intro D₂ hD₂
        apply Finset.sum_le_sum;intro J hJ
        have hJF:=Finset.mem_powerset.mp hJ
        exact weighted_uniform_term R D₁ D₂ hR (Finset.mem_powerset.mp hD₁)
          (Finset.mem_powerset.mp hD₂) J b M (fun i hi=>hM i (hJF hi)) t ht
      _=_:=by simp only [Finset.sum_const,nsmul_eq_mul];ring
  let N:ℝ:=(∏I∈R,I).absNorm
  have hN:1≤N:=product_norm_ge_one R hR
  have hN0:0<N:=zero_lt_one.trans_le hN
  have hmass:0≤∑J∈F.powerset,∏i∈J,(Real.sqrt (max 1 (b i))*M i)*(∑I∈R,weight I):=by
    exact Finset.sum_nonneg (fun J hJ=>Finset.prod_nonneg (fun i hi=>mul_nonneg
      (mul_nonneg (Real.sqrt_nonneg _) (hM i ((Finset.mem_powerset.mp hJ) hi)))
      (Finset.sum_nonneg (fun I _=>weight_nonneg I))))
  have hpow:(∏I∈R,localMass I)^F.card≤Ce^F.card*N^(eps/2):=by
    calc
      _≤(Ce*N^delta)^F.card:=pow_le_pow_left₀
        (Finset.prod_nonneg (fun I hi=>localMass_nonneg I (hR I hi))) (heuler R hR) _
      _=Ce^F.card*N^(delta*(F.card:ℝ)):=by rw [mul_pow,←Real.rpow_mul_natCast hN0.le]
      _≤_:=mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN (by
        dsimp [delta]
        rw [div_mul_eq_mul_div]
        apply (div_le_iff₀ (by positivity:0<2*((F.card:ℝ)+1))).mpr
        nlinarith)) (by positivity)
  calc
    _≤(R.powerset.card:ℝ)^2*(A*(∏I∈R,localMass I)^F.card):=
      hsum.trans (mul_le_mul_of_nonneg_left (slot_majorant_mass R hR F b M hM) (sq_nonneg _))
    _≤(Cc*N^(eps/2))*(A*(Ce^F.card*N^(eps/2))):=
      mul_le_mul (hcard R hR) (mul_le_mul_of_nonneg_left hpow hA.le)
        (mul_nonneg hA.le (pow_nonneg (Finset.prod_nonneg (fun I hi=>localMass_nonneg I (hR I hi))) _))
        (by positivity)
    _=(Cc*A*Ce^F.card)*N^eps:=by
      rw [show (Cc*N^(eps/2))*(A*(Ce^F.card*N^(eps/2)))=
        (Cc*A*Ce^F.card)*(N^(eps/2)*N^(eps/2)) by ring,←Real.rpow_add hN0]
      congr 2
      ring

theorem weighted_signed_mass_subpower (F:Finset α)(b M:α→ℝ)(hM:∀i∈F,0≤M i)
    (eps:ℝ)(heps:0<eps):
    ∃C:ℝ,0<C ∧ ∀(R:Finset (Ideal O))(_hR:∀I∈R,Prime I)
      (χ:Character)(pool:α→Finset (Ideal O))(β:α→Ideal O→ℂ)(P:α→ℝ),
      (∀i∈F,∀I∈pool i,Prime I)→(∀i∈F,0<P i)→
      (∀i∈F,∀I∈pool i,‖β i I‖≤M i)→
      (∀i∈F,∀I∈pool i,β i I≠0→(I.absNorm:ℝ)≤b i*P i)→
      ∀t:ℝ,t≤1/2→
      (∑D₁∈R.powerset,∑D₂∈R.powerset,∑J∈F.powerset,
        ‖signedCoefficient χ R D₁ D₂ J pool β P‖*((∏I∈D₂,I).absNorm:ℝ)^t)≤
        C*((∏I∈R,I).absNorm:ℝ)^eps:=by
  obtain ⟨C,hC,hbound⟩:=weighted_uniform_mass_subpower F b M hM eps heps
  refine ⟨C,hC,?_⟩
  intro R hR χ pool β P hp hP hβ hs t ht
  apply le_trans _ (hbound R hR t ht)
  apply Finset.sum_le_sum;intro D₁ hD₁
  apply Finset.sum_le_sum;intro D₂ hD₂
  apply Finset.sum_le_sum;intro J hJ
  have hJF:=Finset.mem_powerset.mp hJ
  exact mul_le_mul_of_nonneg_right
    (signedCoefficient_uniform χ R hR D₁ D₂ (Finset.mem_powerset.mp hD₁)
      (Finset.mem_powerset.mp hD₂) J pool β P b M
      (fun i hi=>hp i (hJF hi)) (fun i hi=>hP i (hJF hi))
      (fun i hi=>hM i (hJF hi)) (fun i hi=>hβ i (hJF hi))
      (fun i hi=>hs i (hJF hi))) (Real.rpow_nonneg (Nat.cast_nonneg _) t)

end SevenEighths.CenteredMomentEnergyReferenceDeletionBudget

end

end OAI
end OAIOriginalModule2226

/-! Original module: OAI.NumberTheory.DirichletL.Moments.AllocatedChildCapacity
Source SHA256: 87899d96509e0e41058b12d1210a1817f95bfa6dc33ec9b6b843e512935dc24b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2227





namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentAllocatedChildCapacity
open HeckeFamily CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRaw CenteredMomentDivisorRetained CenteredMomentEligibleEnergy
open CenteredMomentCommonRadialData
local notation "O" => HeckeFamily.O

def clippingLoss (Z U₁ U₂ : ℝ) : ℝ :=
  max (-Real.logb Z U₁) 0+max (-Real.logb Z U₂) 0

lemma clipped_log (Z U : ℝ) (hZ : 1<Z) (hU : 0<U) :
    Real.logb Z (clippedScale U)=Real.logb Z U+max (-Real.logb Z U) 0 := by
  by_cases h : 1≤U
  · rw [clippedScale,max_eq_right h,max_eq_right (neg_nonpos.mpr (Real.logb_nonneg hZ h))]
    ring
  · have hu : U≤1 := (lt_of_not_ge h).le
    have hl : Real.logb Z U≤0 := Real.logb_nonpos hZ hU.le hu
    rw [clippedScale,max_eq_left hu,max_eq_left (neg_nonneg.mpr hl),Real.logb_one]
    ring

lemma clipped_pair_log (Z U₁ U₂ : ℝ) (hZ : 1<Z) (h₁ : 0<U₁) (h₂ : 0<U₂) :
    Real.logb Z (clippedScale U₁)+Real.logb Z (clippedScale U₂)=
      Real.logb Z U₁+Real.logb Z U₂+clippingLoss Z U₁ U₂ := by
  rw [clipped_log Z U₁ hZ h₁,clipped_log Z U₂ hZ h₂]
  unfold clippingLoss
  ring

lemma clipping_loss_bound (Z U₁ U₂ b₁ b₂ : ℝ) (hZ : 1<Z)
    (h₁ : 0<U₁) (h₂ : 0<U₂) (hs₁ : 1≤U₁*b₁) (hs₂ : 1≤U₂*b₂) :
    0≤clippingLoss Z U₁ U₂ ∧
      clippingLoss Z U₁ U₂≤Real.logb Z (max 1 b₁*max 1 b₂) := by
  have one (U b : ℝ) (hU : 0<U) (hs : 1≤U*b) :
      max (-Real.logb Z U) 0≤Real.logb Z (max 1 b) := by
    have hb : 0<max 1 b := zero_lt_one.trans_le (le_max_left _ _)
    have hc : clippedScale U≤max 1 b*U := by
      apply max_le
      · exact hs.trans (by nlinarith [le_max_right (1:ℝ) b])
      · nlinarith [le_max_left (1:ℝ) b]
    have hl := Real.logb_le_logb_of_le hZ
      (zero_lt_one.trans_le (clippedScale_ge_one U)) hc
    rw [clipped_log Z U hZ hU,Real.logb_mul hb.ne' hU.ne'] at hl
    linarith
  refine ⟨add_nonneg (le_max_right _ _) (le_max_right _ _),?_⟩
  rw [Real.logb_mul (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₁)))
    (ne_of_gt (zero_lt_one.trans_le (le_max_left (1:ℝ) b₂)))]
  exact add_le_add (one U₁ b₁ h₁ hs₁) (one U₂ b₂ h₂ hs₂)

lemma profile_polynomial_survives (χ : Character) (V : Plain) (U : ℝ) (hU : 0<U)
    (t X σ v : ℝ) (hn : HeckeDyadic.polynomial χ false (V.profile U hU t) X σ v≠0) :
    1≤U*V.b := by
  by_contra hs
  rw [V.profile_zero U hU t (lt_of_not_ge hs)] at hn
  exact hn (by simp [HeckeDyadic.polynomial,HeckeDyadic.summand])

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def plainLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) : ℝ :=
  Real.logb Z (clippedScale (rawScale D a X₁ 0))+
    Real.logb Z (clippedScale (rawScale D a X₂ 1))

def remainingLogs (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (P : ι→ℝ) : ℝ := ∑i∈liveIndices D a,Real.logb Z (P i)

def preVolume (s : Data ι) : ℝ := s.X₁*s.X₂*∏i,s.P i

omit [DecidableEq ι] in
lemma preVolume_pos (s : Data ι) : 0<preVolume s :=
  mul_pos (mul_pos s.X₁_pos s.X₂_pos) (Finset.prod_pos (fun i _=>s.P_pos i))

lemma selectedNorm_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) :
    1≤selectedNorm D a := by
  have hn (j : Fin 2) : (1:ℝ)≤Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  exact one_le_mul_of_one_le_of_one_le (hn 0) (hn 1)

lemma formalReduction_ge_one (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (P : ι→ℝ) (hP : ∀i,1≤P i) : 1≤formalReductionFactor D a P :=
  one_le_mul_of_one_le_of_one_le (selectedNorm_ge_one D a)
    (Finset.one_le_prod₀ (fun i _=>hP i))

lemma remainingLogs_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z : ℝ) (hZ : 1<Z) (P : ι→ℝ) (hP : ∀i,1≤P i) :
    remainingLogs D a Z P≤∑i,Real.logb Z (P i) :=
  Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

lemma raw_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (X₁ X₂ : ℝ) (P : ι→ℝ) (hP : ∀i,0<P i) :
    rawScale D a X₁ 0*rawScale D a X₂ 1*(∏i∈liveIndices D a,P i)=
      (X₁*X₂*∏i,P i)/formalReductionFactor D a P := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  apply (eq_div_iff hr.ne').mpr
  simpa only [rawScale,div_mul_div_comm,rawRemaining,selectedNorm] using
    CenteredMomentDivisorRaw.raw_scale_identity D a (X₁*X₂) P

lemma raw_log_volume (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂) (P : ι→ℝ) (hP : ∀i,0<P i) :
    Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+remainingLogs D a Z P=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P) := by
  have hr : 0<formalReductionFactor D a P :=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=>hP i))
  have hh := congrArg (Real.logb Z) (raw_volume D a X₁ X₂ P hP)
  rw [Real.logb_div (mul_pos (mul_pos h₁ h₂) (Finset.prod_pos (fun i _=>hP i))).ne' hr.ne',
    Real.logb_mul (mul_pos (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)).ne'
      (Finset.prod_pos (fun i _=>hP i)).ne',
    Real.logb_mul (rawScale_pos D a X₁ h₁ 0).ne' (rawScale_pos D a X₂ h₂ 1).ne',
    Real.logb_prod _ _ (fun i _=>(hP i).ne')] at hh
  exact hh

theorem affine_exact (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i) :
    plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M=
      Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+
        clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) := by
  have hv := raw_log_volume D a Z X₁ X₂ h₁ h₂ P hP
  rw [plainLogs,clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1)]
  nlinarith

theorem excess_le (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,1≤P i) (hκ : (1/6:ℝ)≤κ)
    (hs₁ : 1≤rawScale D a X₁ 0*b₁) (hs₂ : 1≤rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*(∑i,Real.logb Z (P i))+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P (fun i=>zero_lt_one.trans_le (hP i))]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  have hp := mul_le_mul_of_nonneg_left (remainingLogs_le D a Z hZ P hP)
    (by linarith : 0≤6*κ-1)
  exact max_le_max (by linarith) le_rfl

theorem allocated_survives (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (X₁ X₂ : ℝ) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    1≤rawScale D a X₁ 0*s.b₁ ∧ 1≤rawScale D a X₂ 1*s.b₂ := by
  have hz (hs : rawScale D a X₁ 0*s.b₁<1 ∨ rawScale D a X₂ 1*s.b₂<1) : False := by
    apply hne
    exact CenteredMomentCommonMaskEnergy.original_retained_zero s.η s.m s.A z _ _ _ _
      s.support₁ s.support₂ (fun i : liveIndices D a=>s.slots i)
      (fun i : liveIndices D a=>s.coefficient i) (fun i : liveIndices D a=>s.P i)
      s.t _ _ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs
  constructor
  · exact le_of_not_gt (fun hh=>hz (Or.inl hh))
  · exact le_of_not_gt (fun hh=>hz (Or.inr hh))

theorem paired_capacity (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let bound := max (Real.logb Z (preVolume s)-Real.logb Z (formalReductionFactor D a s.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.X₁ s.X₂≠0 →
      max (plainLogs D a Z s.X₁ s.X₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ s.Y₁ s.Y₂≠0 →
      max (plainLogs D a Z s.Y₁ s.Y₂+6*κ*remainingLogs D a Z s.P-M) 0≤bound) := by
  constructor
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.X₁ s.X₂ s.X₁_pos s.X₂_pos hn
    exact excess_le D a Z _ _ _ _ κ M hZ s.X₁_pos s.X₂_pos s.P hP hκ h₁ h₂
  · intro z hn
    obtain ⟨h₁,h₂⟩ := allocated_survives s D a z s.Y₁ s.Y₂ s.Y₁_pos s.Y₂_pos hn
    have hb := excess_le D a Z _ _ _ _ κ M hZ s.Y₁_pos s.Y₂_pos s.P hP hκ h₁ h₂
    simpa only [s.same_product,preVolume] using hb

omit [DecidableEq ι] in
theorem common_preVolume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) :
    preVolume (commonData s C R B)=preVolume s.toData/
      CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hr := CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos
  apply (eq_div_iff hr.ne').mpr
  simpa only [preVolume,commonData,div_mul_div_comm,
    CenteredMomentCommonRawScale.remainingRaw,CenteredMomentCommonRawScale.plainNorm] using
      CenteredMomentCommonRawScale.raw_scale_identity B.val (alloc_ne s C B) (s.X₁*s.X₂) s.P

omit [DecidableEq ι] in
lemma common_reduction_ge_one (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C) (hP : ∀i,1≤s.P i) :
    1≤CenteredMomentCommonRawScale.rawReduction B.val s.P := by
  have hn (j : ι⊕Fin 2) : (1:ℝ)≤Ideal.absNorm (B.val j) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (alloc_ne s C B j))
  apply one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le (hn (Sum.inr 0)) (hn (Sum.inr 1)))
  apply Finset.one_le_prod₀
  intro i _
  unfold CenteredMomentCommonRawScale.frozenScale
  split_ifs
  · exact le_rfl
  · exact hP i

omit [DecidableEq ι] in
lemma common_slot_logs_le (s : Input ι) (C : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (Z : ℝ) (hZ : 1<Z) (hP : ∀i,1≤s.P i) :
    (∑i : CenteredMomentCommonProfile.liveIndices B.val,Real.logb Z (s.P i))≤
      ∑i,Real.logb Z (s.P i) := by
  rw [Finset.sum_coe_sort (CenteredMomentCommonProfile.liveIndices B.val) (fun i : ι=>Real.logb Z (s.P i))]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun i _ _=>Real.logb_nonneg hZ (hP i))

theorem common_allocated_raw_volume (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2))) :
    let v := commonData s C R B
    let result := preVolume s.toData/(CenteredMomentCommonRawScale.rawReduction B.val s.P*
      formalReductionFactor D a v.P)
    rawScale D a v.X₁ 0*rawScale D a v.X₂ 1*(∏i∈liveIndices D a,v.P i)=result ∧
      rawScale D a v.Y₁ 0*rawScale D a v.Y₂ 1*(∏i∈liveIndices D a,v.P i)=result := by
  dsimp only
  have hx := raw_volume D a (commonData s C R B).X₁ (commonData s C R B).X₂
    (commonData s C R B).P (commonData s C R B).P_pos
  have hy := raw_volume D a (commonData s C R B).Y₁ (commonData s C R B).Y₂
    (commonData s C R B).P (commonData s C R B).P_pos
  change _=preVolume (commonData s C R B)/_ at hx
  rw [common_preVolume s C R B,div_div] at hx
  rw [(commonData s C R B).same_product] at hy
  change _=preVolume (commonData s C R B)/_ at hy
  rw [common_preVolume s C R B,div_div] at hy
  exact ⟨hx,hy⟩

theorem common_paired_capacity (s : Input ι) (C R : Ideal O)
    (B : CenteredMomentCommonAllocationSum.actualAllocations s.pools C)
    (D : Ideal O) (a : Allocation D
      (Finset.univ : Finset ((CenteredMomentCommonProfile.liveIndices B.val)⊕Fin 2)))
    (Z κ M : ℝ) (hZ : 1<Z) (hκ : (1/6:ℝ)≤κ) (hP : ∀i,1≤s.P i) :
    let v := commonData s C R B
    let bound := max (Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a v.P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.X₁ v.X₂≠0 →
      max (plainLogs D a Z v.X₁ v.X₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) ∧
    (∀z,allocatedPositiveRow v.η v.m v.A z v.t v.slots v.coefficient v.P D a
      v.W₁ v.W₂ v.Y₁ v.Y₂≠0 →
      max (plainLogs D a Z v.Y₁ v.Y₂+6*κ*remainingLogs D a Z v.P-M) 0≤bound) := by
  dsimp only
  obtain ⟨hx,hy⟩ := paired_capacity (commonData s C R B) D a Z κ M hZ hκ (fun i=>hP i)
  have hv : Real.logb Z (preVolume (commonData s C R B))=
      Real.logb Z (preVolume s.toData)-Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P) := by
    rw [common_preVolume s C R B,Real.logb_div (preVolume_pos s.toData).ne'
      (CenteredMomentCommonRawScale.rawReduction_pos B.val (alloc_ne s C B) s.P s.P_pos).ne']
  have hl := mul_le_mul_of_nonneg_left (common_slot_logs_le s C B Z hZ hP)
    (by linarith : 0≤6*κ-1)
  have hb : max (Real.logb Z (preVolume (commonData s C R B))-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z ((commonData s C R B).P i))+
      Real.logb Z (max 1 (commonData s C R B).b₁*max 1 (commonData s C R B).b₂)) 0≤
      max (Real.logb Z (preVolume s.toData)-
        Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
        Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
        (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)) 0 := by
    rw [hv]
    apply max_le_max _ le_rfl
    change _≤Real.logb Z (preVolume s.toData)-
      Real.logb Z (CenteredMomentCommonRawScale.rawReduction B.val s.P)-
      Real.logb Z (formalReductionFactor D a (commonData s C R B).P)-M+
      (6*κ-1)*(∑i,Real.logb Z (s.P i))+Real.logb Z (max 1 s.b₁*max 1 s.b₂)
    dsimp only [commonData]
    linarith
  exact ⟨fun z hz=>(hx z hz).trans hb,fun z hz=>(hy z hz).trans hb⟩

theorem excess_le_remaining (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ M : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (P : ι→ℝ) (hP : ∀i,0<P i)
    (hs₁ : 1≤rawScale D a X₁ 0*b₁) (hs₂ : 1≤rawScale D a X₂ 1*b₂) :
    max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0≤
      max (Real.logb Z (X₁*X₂*∏i,P i)-Real.logb Z (formalReductionFactor D a P)-M+
        (6*κ-1)*remainingLogs D a Z P+Real.logb Z (max 1 b₁*max 1 b₂)) 0 := by
  rw [affine_exact D a Z X₁ X₂ κ M hZ h₁ h₂ P hP]
  have hc := (clipping_loss_bound Z _ _ b₁ b₂ hZ
    (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂).2
  exact max_le_max (by linarith) le_rfl

theorem allocated_clipping (s : Data ι) (D : Ideal O)
    (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2))) (z : O)
    (Z X₁ X₂ : ℝ) (hZ : 1<Z) (h₁ : 0<X₁) (h₂ : 0<X₂)
    (hne : allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0) :
    plainLogs D a Z X₁ X₂=Real.logb Z (rawScale D a X₁ 0)+Real.logb Z (rawScale D a X₂ 1)+
      clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    0≤clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1) ∧
    clippingLoss Z (rawScale D a X₁ 0) (rawScale D a X₂ 1)≤Real.logb Z (max 1 s.b₁*max 1 s.b₂) := by
  obtain ⟨hs₁,hs₂⟩ := allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact ⟨clipped_pair_log Z _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1),
    clipping_loss_bound Z _ _ _ _ hZ (rawScale_pos D a X₁ h₁ 0) (rawScale_pos D a X₂ h₂ 1) hs₁ hs₂⟩

lemma native_excess (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ M : ℝ) (P : ι→ℝ) :
    CenteredMomentLiveCapacity.excess (liveIndices D a) (fun i=>Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) M κ=
      max (plainLogs D a Z X₁ X₂+6*κ*remainingLogs D a Z P-M) 0 := rfl

end SevenEighths.CenteredMomentAllocatedChildCapacity

end

end OAI
end OAIOriginalModule2227

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityLedger
Source SHA256: e20373738876fd5c8deb8055779d53ad895ef93a8d59d87c674821934dfad807
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2228


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

theorem formal_reduction_pays_slots (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z:ℝ)(hZ:1<Z)(P:ι→ℝ)(hP:∀i,1≤P i):
    (∑i,Real.logb Z (P i))-remainingLogs D a Z P≤
      Real.logb Z (formalReductionFactor D a P) := by
  have hp:∀i,0<P i:=fun i=>zero_lt_one.trans_le (hP i)
  have hs:=congrArg (Real.logb Z) (split_slot_product D a P)
  rw [Real.logb_mul (Finset.prod_pos (fun i _=>hp i)).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne'),
    Real.logb_prod _ _ (fun i _=>(hp i).ne')] at hs
  rw [formalReductionFactor,Real.logb_mul (selectedNorm_pos D a).ne'
    (Finset.prod_pos (fun i _=>hp i)).ne',
    Real.logb_prod _ _ (fun i _=>(hp i).ne')]
  have hn:=Real.logb_nonneg hZ (selectedNorm_ge_one D a)
  dsimp only [remainingLogs]
  linarith

theorem affine_reduction_le_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z κ:ℝ)(hZ:1<Z)(hκ:0≤κ)(P:ι→ℝ)(hP:∀i,1≤P i):
    -Real.logb Z (formalReductionFactor D a P)+(6*κ-1)*remainingLogs D a Z P≤
      (6*κ-1)*(∑i,Real.logb Z (P i)) := by
  have hred:=formal_reduction_pays_slots D a Z hZ P hP
  have hrem:=remainingLogs_le D a Z hZ P hP
  nlinarith

theorem allocated_excess_from_parent (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ b₁ b₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)
    (P:ι→ℝ)(hP:∀i,1≤P i)
    (hs₁:1≤rawScale D a X₁ 0*b₁)(hs₂:1≤rawScale D a X₂ 1*b₂)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 b₁*max 1 b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ b₁ b₂ κ Mact hZ h₁ h₂ P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le
  · have hr:=affine_reduction_le_parent D a Z κ hZ hκ P hP
    linarith
  · positivity

theorem live_allocated_excess (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        6*(w+ell)+δ+2*θ := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  exact allocated_excess_from_parent D a Z X₁ X₂ s.b₁ s.b₂ κ A M Mnom Mact
    w ell δ θ hZ h₁ h₂ hκ s.P hP hs₁ hs₂ hparent hshift hactual hw hell hδ hθ hclip

theorem live_whole_removal (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hactual:Mnom≤Mact)(hw:0≤w)(hell:0≤ell)(hδ:0≤δ)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      κ*(∑i∈removed,Real.logb Z (s.P i))≤w+ell+δ/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hactual hw hell hδ hθ hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  linarith

theorem paired_edge_cost (shell width₁ width₂ cost₁ cost₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)(hwidth₁:width₁≤δ₂)(hwidth₂:width₂≤δ₂)
    (hc₁:cost₁≤w+ell+δ₁/6+θ/3+κ*mesh)
    (hc₂:cost₂≤w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(width₁+width₂)/2+(cost₁+cost₂)/2-(w+ell)≤
      δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

theorem edge_loss_budget (δ₁ δ₂ θ κ mesh ξ η:ℝ)
    (hδ₁:δ₁≤ξ)(hδ₂:δ₂≤ξ)(hθ:θ≤ξ)(hκ:κ≤1)
    (hm:0≤mesh)(hmesh:mesh≤η):
    δ₂+δ₁/6+κ*mesh+7*θ/3≤7*ξ/2+η := by
  nlinarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
end OAIOriginalModule2228

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityShift
Source SHA256: 968b826c1385f5ca9b465c993ff79052d326fa48f981818c7bafc6759cf1b07d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2229



namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentFirstAmplificationChoice CenteredMomentRowNorm CenteredMomentSectorLocalization
local notation "O"=>ActualEisensteinCubic.O

lemma nominal_capacity_shift_identity (A m q c d R E j g w wo g₂ t₂ c₂ V:ℝ):
    let K₀:=2*A-c-d+R+E-m;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+wo+t₂+V;
    (A-c-w-c₂)-(m'+q')-(A-(m+q))=
      g+w-(d+K₀-j)-wo+g₂-t₂-c₂ := by dsimp;ring

lemma main_capacity_gain (D₀ c σ δ:ℝ)(hc:0≤c)(hδ:0≤δ)(hD: -δ≤D₀):
    mainGain D₀ c σ-D₀≤6*(σ/3)+δ := by
  have hh:max (D₀-c) 0≤D₀+δ:=max_le (by linarith) (by linarith)
  unfold mainGain
  linarith

lemma error_capacity_gain (D₀ c σ δ Z:ℝ)(p:O)(k:ℕ)
    (hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)(hD: -δ≤D₀)
    (hk:k=1 ∨ k=6 ∨ k=7)
    (hl:σ/6≤Real.logb Z (normValue p)):
    errorGain D₀ c σ Z p k+errorRemoval p Z k-D₀-errorMoving p Z k≤
      6*errorRemoval p Z k+δ := by
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hm:0≤errorMoving p Z k ∧ errorMoving p Z k≤errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl
    all_goals norm_num [errorMoving,errorRemoval]
    all_goals first | exact hp | constructor <;> linarith
  have hw:0≤errorRemoval p Z k:=hm.1.trans hm.2
  have he:σ+errorRemoval p Z k-errorMoving p Z k≤6*errorRemoval p Z k:=by
    rcases hk with rfl|rfl|rfl <;> simp only [errorMoving,errorRemoval] <;> norm_num <;> linarith
  have hh:max (D₀-c-2*errorRemoval p Z k+errorMoving p Z k) 0≤D₀+δ:=
    max_le (by linarith) (by linarith)
  unfold errorGain
  linarith

theorem main_nominal_capacity_shift (A m q c d R E j σ δ g₂ t₂ c₂ V:ℝ)
    (hc:0≤c)(hδ:0≤δ)(hD: -δ≤d+(2*A-c-d+R+E-m)-j)
    (hcommon:g₂-t₂≤c₂):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let g:=mainGain D₀ c σ;
    let m':=2*(A-c)-j-g-g₂-V;
    let q':=q+R+E+t₂+V;
    (A-c-c₂)-(m'+q')≤A-(m+q)+6*(σ/3)+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (mainGain (d+(2*A-c-d+R+E-m)-j) c σ) 0 0 g₂ t₂ c₂ V
  have hg:=main_capacity_gain _ c σ δ hc hδ hD
  dsimp only at hi ⊢
  simp only [sub_zero,add_zero] at hi
  linarith

theorem error_nominal_capacity_shift (A m q c d R E j σ δ Z g₂ t₂ c₂ V:ℝ)
    (p:O)(k:ℕ)(hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)
    (hD: -δ≤d+(2*A-c-d+R+E-m)-j)(hcommon:g₂-t₂≤c₂)
    (hk:k=1 ∨ k=6 ∨ k=7)(hl:σ/6≤Real.logb Z (normValue p)):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let w:=errorRemoval p Z k;
    let wo:=errorMoving p Z k;
    let g:=errorGain D₀ c σ Z p k;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+2*wo+t₂+V;
    (A-c-w-c₂)-(m'+q')≤A-(m+q)+6*w+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (errorGain (d+(2*A-c-d+R+E-m)-j) c σ Z p k)
    (errorRemoval p Z k) (errorMoving p Z k) g₂ t₂ c₂ V
  have hg:=error_capacity_gain _ c σ δ Z p k hc hσ hδ hD hk hl
  have hp:0≤Real.logb Z (normValue p):=by linarith
  have hwo:0≤errorMoving p Z k:=by
    unfold errorMoving
    split_ifs <;> linarith
  dsimp only at hi ⊢
  linarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
end OAIOriginalModule2229

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondCapacityDefect
Source SHA256: 1e6a0cebdc553a98c82616b3564b4ef54e9d6a102c531f3f50c3807b1a9942e6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2230


namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondCapacityLedger
open CenteredMomentAllocatedChildCapacity CenteredMomentDivisorRaw
open CenteredMomentDivisorAllocation CenteredMomentDivisorRetained
open CenteredMomentEligibleEnergy CenteredMomentLiveCapacity
open CenteredMomentAllocatedNaturalSource CenteredMomentRetainedProfile
local notation "O"=>ActualEisensteinCubic.O
variable {ι:Type*}[Fintype ι][DecidableEq ι]

lemma width_defect_cost (x B δ:ℝ)(hB:0≤B)(hδ:0≤δ)(hx:x≤δ):
    x+max (B-x) 0/6≤δ+B/6 := by
  by_cases h:0≤B-x
  · rw [max_eq_left h];linarith
  · rw [max_eq_right (le_of_not_ge h)];linarith

theorem live_allocated_excess_defect (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ θ:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0≤κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ):
    excess (liveIndices D a) (fun i=>Real.logb Z (s.P i))
      (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
      (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ≤
        max (6*(w+ell)+δ+2*θ+Mnom-Mact) 0 := by
  obtain ⟨hs₁,hs₂⟩:=allocated_survives s D a z X₁ X₂ h₁ h₂ hne
  rw [native_excess]
  apply (excess_le_remaining D a Z X₁ X₂ s.b₁ s.b₂ κ Mact hZ h₁ h₂ s.P
    (fun i=>zero_lt_one.trans_le (hP i)) hs₁ hs₂).trans
  apply max_le_max _ le_rfl
  have hr:=affine_reduction_le_parent D a Z κ hZ hκ s.P hP
  linarith

theorem live_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))(z:O)
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hne:allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
      s.W₁ s.W₂ X₁ X₂≠0)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤w)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
        δ₂+w+ell+δ₁/6+θ/3+κ*mesh := by
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem source_removal_width_cost (s:Data ι)(D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (Z X₁ X₂ κ A M Mnom Mact w ell δ₁ δ₂ θ mesh:ℝ)
    (hZ:1<Z)(h₁:0<X₁)(h₂:0<X₂)(hκ:0<κ)(hP:∀i,1≤s.P i)
    (hparent:A+(6*κ-1)*(∑i,Real.logb Z (s.P i))≤M)
    (hshift:Real.logb Z (X₁*X₂*∏i,s.P i)-Mnom≤A-M+6*(w+ell)+δ₁)
    (hwidth:Mact-Mnom≤δ₂)(hw:0≤w)(hell:0≤ell)(hδ₁:0≤δ₁)(hδ₂:0≤δ₂)(hθ:0≤θ)
    (hclip:Real.logb Z (max 1 s.b₁*max 1 s.b₂)≤2*θ)
    (hm:0≤mesh)(hmesh:∀i∈liveIndices D a,Real.logb Z (s.P i)≤mesh):
    ∃removed:Finset ι,removed⊆liveIndices D a ∧
      (removed=liveIndices D a ∨
        plainLogs D a Z X₁ X₂+6*κ*(∑i∈liveIndices D a\removed,Real.logb Z (s.P i))≤Mact) ∧
      ((∃z:O,allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a
          s.W₁ s.W₂ X₁ X₂≠0) →
        Mact-Mnom+κ*(∑i∈removed,Real.logb Z (s.P i))≤
          δ₂+w+ell+δ₁/6+θ/3+κ*mesh) := by
  obtain ⟨removed,hr,hcap,hcost⟩:=removal_excess_cost (liveIndices D a)
    (fun i=>Real.logb Z (s.P i))
    (Real.logb Z (clippedScale (rawScale D a X₁ 0)))
    (Real.logb Z (clippedScale (rawScale D a X₂ 1))) Mact κ mesh hκ hm
    (fun i _=>Real.logb_nonneg hZ (hP i)) hmesh
  refine ⟨removed,hr,hcap,?_⟩
  rintro ⟨z,hne⟩
  have he:=live_allocated_excess_defect s D a z Z X₁ X₂ κ A M Mnom Mact w ell δ₁ θ
    hZ h₁ h₂ hκ.le hP hne hparent hshift hclip
  have hh:=width_defect_cost (Mact-Mnom) (6*(w+ell)+δ₁+2*θ) δ₂
    (by positivity) hδ₂ hwidth
  rw [show 6*(w+ell)+δ₁+2*θ-(Mact-Mnom)=6*(w+ell)+δ₁+2*θ+Mnom-Mact by ring] at hh
  linarith

theorem paired_width_defect_cost (shell edge₁ edge₂ w ell δ₁ δ₂ θ κ mesh:ℝ)
    (hs:shell≤2*θ)
    (h₁:edge₁≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh)
    (h₂:edge₂≤δ₂+w+ell+δ₁/6+θ/3+κ*mesh):
    shell+(edge₁+edge₂)/2-(w+ell)≤δ₂+δ₁/6+κ*mesh+7*θ/3 := by linarith

end SevenEighths.CenteredMomentFirstSecondCapacityLedger

end

end OAI
end OAIOriginalModule2230

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondLossParameters
Source SHA256: 71eba77cf26e7ac024e7a64469434ab3f41de88b0af647afbbcd17026e605c14
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2231


namespace OAI

noncomputable section

namespace SevenEighths.CenteredMomentFirstSecondLossParameters
open CenteredMomentFirstSecondCapacityLedger

def depth (Mcap σ:ℝ):ℕ:=⌈2*Mcap/σ⌉₊+1

lemma depth_covers (Mcap σ:ℝ)(hσ:0<σ):Mcap<(depth Mcap σ:ℝ)*σ/2 := by
  have hh:=Nat.le_ceil (2*Mcap/σ)
  have hn:2*Mcap≤(⌈2*Mcap/σ⌉₊:ℝ)*σ:=(div_le_iff₀ hσ).mp hh
  simp only [depth,Nat.cast_add,Nat.cast_one]
  nlinarith

theorem numerical_choices (Mcap ε:ℝ)(hε:0<ε):
    ∃σ ξ mesh:ℝ,0<σ ∧ σ≤1 ∧ σ≤ε/100 ∧ 0<ξ ∧ 0<mesh ∧ mesh≤ξ ∧
      5*ξ≤σ/2 ∧ Mcap<(depth Mcap σ:ℝ)*σ/2 ∧
      (depth Mcap σ:ℝ)*(7*ξ/2+mesh)≤ε/32 ∧
      3*σ+5*ξ/6+7*ξ/2+mesh≤ε/16 := by
  let σ:ℝ:=min 1 (ε/100)
  have hσ:0<σ:=lt_min (by norm_num) (by positivity)
  have hσ₁:σ≤1:=min_le_left _ _
  have hσε:σ≤ε/100:=min_le_right _ _
  let n:=depth Mcap σ
  let ξ:ℝ:=min (σ/100) (ε/(200*((n:ℝ)+1)))
  have hn:0≤(n:ℝ):=Nat.cast_nonneg n
  have hξ:0<ξ:=lt_min (by positivity) (by positivity)
  have hξσ:ξ≤σ/100:=min_le_left _ _
  have hξε:ξ≤ε/(200*((n:ℝ)+1)):=min_le_right _ _
  have he:ξ*(200*((n:ℝ)+1))≤ε:=(le_div_iff₀ (by positivity)).mp hξε
  have hne:(n:ℝ)*ξ≤ε/200:=by nlinarith
  refine ⟨σ,ξ,ξ,hσ,hσ₁,hσε,hξ,hξ,le_rfl,?_,depth_covers Mcap σ hσ,?_,?_⟩
  · linarith
  · change (n:ℝ)*(7*ξ/2+ξ)≤ε/32
    nlinarith
  · linarith

theorem edge_with_choices (δ₁ δ₂ θ κ mesh ξ:ℝ)
    (hδ₁:δ₁≤ξ)(hδ₂:δ₂≤ξ)(hθ:θ≤ξ)(hκ:κ≤1)
    (hm:0≤mesh)(hmesh:mesh≤ξ):
    δ₂+δ₁/6+κ*mesh+7*θ/3≤9*ξ/2 := by
  have hh:=edge_loss_budget δ₁ δ₂ θ κ mesh ξ ξ hδ₁ hδ₂ hθ hκ hm hmesh
  linarith

end SevenEighths.CenteredMomentFirstSecondLossParameters

end

end OAI
end OAIOriginalModule2231

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstSecondPaidLedger
Source SHA256: 3d6fddab64ad4ac4feddc9b85a2a4d56961695408f4d5614760b48517431df11
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2232





namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstSecondPaidLedger
open CenteredMomentFirstSecondCapacityLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale
open CenteredMomentSectorLocalization CenteredMomentDescentLedger
open CenteredMomentSecondCanonical CenteredMomentSecondLedger CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentSupportedCorrelation
open CenteredMomentSupport CenteredMomentRankinRadical
open CenteredMomentFinalStageLedger CanonicalQuadraticSieve
local notation "O"=>ActualEisensteinCubic.O

theorem repaired_error_capacity_shift (A m q c d R E j σ δ Z g₂ t₂ c₂ V:ℝ)
    (p:O)(k:ℕ)(hc:0≤c)(hσ:0≤σ)(hδ:0≤δ)
    (hD: -δ≤d+(2*A-c-d+R+E-m)-j)(hcommon:g₂-t₂≤c₂)
    (hk:k=1 ∨ k=6 ∨ k=7)(hl:σ/6≤Real.logb Z (CenteredMomentSectorLocalization.normValue p)):
    let D₀:=d+(2*A-c-d+R+E-m)-j;
    let w:=errorRemoval p Z k;
    let wo:=errorMoving p Z k;
    let g:=errorGain D₀ c σ Z p k;
    let m':=2*(A-c-w)-j-g-g₂-V;
    let q':=q+R+E+wo+t₂+V;
    (A-c-w-c₂)-(m'+q')≤A-(m+q)+6*w+δ := by
  have hi:=nominal_capacity_shift_identity A m q c d R E j
    (errorGain (d+(2*A-c-d+R+E-m)-j) c σ Z p k)
    (errorRemoval p Z k) (errorMoving p Z k) g₂ t₂ c₂ V
  have hg:=error_capacity_gain _ c σ δ Z p k hc hσ hδ hD hk hl
  dsimp only at hi ⊢
  linarith

lemma paired_first_saving (c D₀ q B wL wR woL woR gL gR ellL ellR:ℝ):
    (firstSaving c D₀ wL q woL B gL ellL+
      firstSaving c D₀ wR q woR B gR ellR)/2=
      firstSaving c D₀ ((wL+wR)/2) q ((woL+woR)/2) B
        ((gL+gR)/2) ((ellL+ellR)/2) := by
  unfold firstSaving
  ring

theorem actual_stage_saving
    (I J E:Ideal O)(hI:Supported I)(hJ:Supported J)(hE:E≠0)
    (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)
    (u:O)(hne:idealCorrelation C D hC hD (commonFrequencyGenerator C D*u)≠0)
    (A M Z H X Tsec Csec ξ q w wo ell σ branch:ℝ)
    (hZ:1<Z)(hH:0<H)(hX:0<X)(hCsec:1≤Csec)(hξ:0≤ξ)
    (hsec:Tsec≤Csec*firstNominalScale I J E H X)
    (n:ℤ)(hn:Retained (frequencyRadius Tsec Z ξ) n)
    (hq:0≤q)(hw:0≤w)(hwo:0≤wo)(hell:0≤ell)(hσ:0≤σ)
    (hbranch:branch≤2)(hwσ:w≤7*σ/3):
    let c:=Real.logb Z ((commonPart I J).absNorm:ℝ);
    let d:=Real.logb Z ((commonPart J I).absNorm:ℝ);
    let p:=Real.logb Z ((commonRadical I J).absNorm:ℝ);
    let R:=Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ);
    let e:=Real.logb Z (E.absNorm:ℝ);
    let D₀:=d+Real.logb Z (firstNominalScale I J E H X)-Real.logb Z (dyadicScale n);
    let F₁:=firstSaving c D₀ w (q+R+e) wo (c+d-2*p-R)
      (max (D₀-c-2*w+wo) 0+branch*σ) ell;
    let F₂:=secondSaving (commonPrime C D) (leftExponent C D) (rightExponent C D) u Z;
    let v:=c+w+min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ));
    A-5*M/6-F₁-F₂-max (M/4-v) 0≤
      max (A-M) 0+3*σ+5*frequencyLoss Z Csec ξ/6 := by
  have hfirst:=actual_first_saving I J E hI hJ hE Z H X Tsec Csec ξ q w wo ell σ branch
    hZ hH hX hCsec hξ hsec n hn hq hw hwo hell hσ hbranch hwσ
  have hsecond:=actual_ideal_secondSaving_lower C D hC hD hCD u Z hZ hne
  have hm₁:=min_le_left (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))
  have hm₂:=min_le_right (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ))
  have hf:=final_exponent A M
    (Real.logb Z ((commonPart I J).absNorm:ℝ)+w+
      min (Real.logb Z (C.absNorm:ℝ)) (Real.logb Z (D.absNorm:ℝ)))
    (3*σ+5*frequencyLoss Z Csec ξ/6) 0
  dsimp only at hfirst ⊢
  linarith

end SevenEighths.CenteredMomentFirstSecondPaidLedger

end

end OAI
end OAIOriginalModule2232

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstExceptionalPaidScales
Source SHA256: 519f416c9c5fc2fd1f19c106ff9b50102a7f2164d6eb3fb0158fda5abdcfb1a6
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2233



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstExceptionalPaidScales
open CanonicalQuadraticSieve CenteredMomentFirstScale CenteredMomentCanonicalFirst
open CenteredMomentCompleteCommon CenteredMomentRankinRadical CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstPhysicalLedger
local notation "O"=>ActualEisensteinCubic.O

structure Branch (Z:ℝ) where
  I:Ideal O
  J:Ideal O
  E:Ideal O
  hI:Supported I
  hJ:Supported J
  hE:E≠0
  H:ℝ
  X:ℝ
  Tsec:ℝ
  Csec:ℝ
  ξ:ℝ
  q:ℝ
  w:ℝ
  wo:ℝ
  ell:ℝ
  σ:ℝ
  kind:ℝ
  hH:0<H
  hX:0<X
  hCsec:1≤Csec
  hξ:0≤ξ
  hsec:Tsec≤Csec*firstNominalScale I J E H X
  n:ℤ
  hn:Retained (frequencyRadius Tsec Z ξ) n
  hq:0≤q
  hw:0≤w
  hwo:0≤wo
  hell:0≤ell
  hσ:0≤σ
  hkind:kind≤2
  hwσ:w≤7*σ/3

def removedWidth {Z:ℝ}(s:Branch Z):ℝ:=
  Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+s.w

def saving {Z:ℝ}(s:Branch Z):ℝ:=
  let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
  let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
  let p:=Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)
  let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
  let e:=Real.logb Z (s.E.absNorm:ℝ)
  let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
    Real.logb Z (dyadicScale s.n)
  firstSaving c D₀ s.w (s.q+R+e) s.wo (c+d-2*p-R)
    (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell

def loss {Z:ℝ}(s:Branch Z):ℝ:=3*s.σ+5*frequencyLoss Z s.Csec s.ξ/6

def rawCap (Z:ℝ)(X red:Fin 2→ℝ):ℝ:=
  min (Real.logb Z (X 0/red 0)) (Real.logb Z (X 1/red 1))

lemma actual_saving {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤saving s:=by
  have hh:=actual_first_saving s.I s.J s.E s.hI s.hJ s.hE Z s.H s.X s.Tsec s.Csec
    s.ξ s.q s.w s.wo s.ell s.σ s.kind hZ s.hH s.hX s.hCsec s.hξ s.hsec
    s.n s.hn s.hq s.hw s.hwo s.hell s.hσ s.hkind s.hwσ
  simpa only [removedWidth,loss,saving,sub_add_eq_sub_sub] using hh

lemma raw_cap_lower (Z L d:ℝ)(hZ:1<Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^L≤X i)(hred:∀i,0<red i)(hupper:∀i,red i≤Z^d):
    L-d≤rawCap Z X red:=by
  have h (i:Fin 2):L-d≤Real.logb Z (X i/red i):=by
    have hz:0<Z:=zero_lt_one.trans hZ
    have hx:0<X i:=(Real.rpow_pos_of_pos hz L).trans_le (hX i)
    have hl:=Real.logb_le_logb_of_le hZ (Real.rpow_pos_of_pos hz L) (hX i)
    have hr:=Real.logb_le_logb_of_le hZ (hred i) (hupper i)
    rw [Real.logb_rpow hz hZ.ne'] at hl hr
    rw [Real.logb_div hx.ne' (hred i).ne']
    linarith
  exact le_min (h 0) (h 1)

theorem actual_branch_stage (Z A M:ℝ)(hZ:1<Z)(s:Branch Z)(X red:Fin 2→ℝ)
    (hX:∀i,Z^(M/4)≤X i)(hred:∀i,0<red i)
    (hupper:∀i,red i≤Z^(removedWidth s)):
    A-5*M/6-saving s-2*max (rawCap Z X red) 0/3≤A-M+loss s:=by
  have hs:=actual_saving hZ s
  have hr:=raw_cap_lower Z (M/4) (removedWidth s) hZ X red hX hred hupper
  have hm:=le_max_left (rawCap Z X red) (0:ℝ)
  linarith

theorem actual_paired_stage (Z A M:ℝ)(hZ:1<Z)(s:Fin 2→Branch Z)
    (X red:Fin 2→Fin 2→ℝ)
    (hX:∀j i,Z^(M/4)≤X j i)(hred:∀j i,0<red j i)
    (hupper:∀j i,red j i≤Z^(removedWidth (s j))):
    A-5*M/6-(saving (s 0)+saving (s 1))/2-
      (max (rawCap Z (X 0) (red 0)) 0+max (rawCap Z (X 1) (red 1)) 0)/3≤
      max (A-M) 0+(loss (s 0)+loss (s 1))/2:=by
  have h₀:=actual_branch_stage Z A M hZ (s 0) (X 0) (red 0) (hX 0) (hred 0) (hupper 0)
  have h₁:=actual_branch_stage Z A M hZ (s 1) (X 1) (red 1) (hX 1) (hred 1) (hupper 1)
  have hm:=le_max_left (A-M) (0:ℝ)
  linarith

end SevenEighths.CenteredMomentFirstExceptionalPaidScales

end

end OAI
end OAIOriginalModule2233

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedAllowance
Source SHA256: d70f3f72b6f06f5ff014a37fe5a9ed7ae0376d6ff826c5493336d949334dd448
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2234



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedAllowance
open CanonicalQuadraticSieve CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentRankinRadical CenteredMomentFirstCanonicalAllowance
open CenteredMomentFirstPhysicalLedger CenteredMomentFirstScale CenteredMomentSectorLocalization
open CenteredMomentDescentLedger CenteredMomentFirstExceptionalPaidScales
local notation "O"=>ActualEisensteinCubic.O

def allowance (C D:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z (C.absNorm:ℝ)-5*Real.logb Z (D.absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6

def extractedAllowance (I J:Ideal O)(Z:ℝ):ℝ:=
  max (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) 0/6

lemma allowance_nonneg (C D:Ideal O)(Z:ℝ):0≤allowance C D Z:=by
  unfold allowance;positivity

lemma actual_allowance_sum (C D:Ideal O)(hC:Supported C)(hD:Supported D)
    (hCD:CompletedGauss.primeSupport C=CompletedGauss.primeSupport D)(Z:ℝ)(hZ:1<Z):
    allowance C D Z+
      max (3*Real.logb Z (D.absNorm:ℝ)-5*Real.logb Z (C.absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ)) 0/6≤
      Real.logb Z (C.absNorm:ℝ)+Real.logb Z (D.absNorm:ℝ)-
        2*Real.logb Z ((commonRadical C D).absNorm:ℝ)-
        Real.logb Z ((Ideal.span {activeConductor C D}).absNorm:ℝ):=
  actual_canonical_common_support_allowance C D hC hD hCD Z hZ

theorem first_saving_with_allowance {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    let c:=Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)
    let d:=Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)
    let R:=Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)
    let e:=Real.logb Z (s.E.absNorm:ℝ)
    let D₀:=d+Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-
      Real.logb Z (dyadicScale s.n)
    2*(c+s.w)/3-loss s≤
      firstSaving c D₀ s.w (s.q+R+e) s.wo (extractedAllowance s.I s.J Z)
        (max (D₀-c-2*s.w+s.wo) 0+s.kind*s.σ) s.ell:=by
  have hC:(1:ℝ)≤((commonPart s.I s.J).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero s.I s.J))
  have hR:(1:ℝ)≤((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr
        (ActualEisensteinCubic.finitePrimeModulus_ne_zero _)))
  have hE:(1:ℝ)≤(s.E.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr s.hE)
  have hc:=Real.logb_nonneg hZ hC
  have hr:=Real.logb_nonneg hZ hR
  have he:=Real.logb_nonneg hZ hE
  have hd:=retained_deficit s.I s.J s.E s.hE Z s.H s.X s.Tsec s.Csec s.ξ
    hZ s.hH s.hX (zero_lt_one.trans_le s.hCsec) s.hsec s.n s.hn
  have hh:=firstSaving_lower _ _ _ s.w
    (s.q+Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ)+Real.logb Z (s.E.absNorm:ℝ))
    _ s.wo (extractedAllowance s.I s.J Z)
    (max (Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)+
      Real.logb Z (firstNominalScale s.I s.J s.E s.H s.X)-Real.logb Z (dyadicScale s.n)-
      Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)-2*s.w+s.wo) 0+s.kind*s.σ)
    s.ell s.σ (frequencyLoss Z s.Csec s.ξ)
    hc s.hw (by linarith [s.hq]) s.hwo (by unfold extractedAllowance;positivity)
    s.hσ (frequencyLoss_nonneg Z s.Csec s.ξ hZ s.hCsec s.hξ)
    (by linarith [s.hq]) (le_refl _) hd (by nlinarith [s.hkind,s.hσ]) s.hell s.hwσ
  dsimp only at hh ⊢
  simpa only [loss,sub_add_eq_sub_sub] using hh

def columnSaving {Z:ℝ}(s:Branch Z):ℝ:=
  saving s-(Real.logb Z ((commonPart s.I s.J).absNorm:ℝ)+
    Real.logb Z ((commonPart s.J s.I).absNorm:ℝ)-
    2*Real.logb Z ((commonRadical s.I s.J).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor s.I s.J}).absNorm:ℝ))+
    extractedAllowance s.I s.J Z

lemma column_saving {Z:ℝ}(hZ:1<Z)(s:Branch Z):
    2*removedWidth s/3-loss s≤columnSaving s:=by
  have hh:=first_saving_with_allowance hZ s
  dsimp only [columnSaving,saving,removedWidth] at hh ⊢
  unfold firstSaving at hh ⊢
  linarith

end SevenEighths.CenteredMomentFirstMixedAllowance

end

end OAI
end OAIOriginalModule2234

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedCommonRadius
Source SHA256: d60f10c75b6dfe71f43a3ea9335bbb507b677ff080d51122a76cfcff97759ae9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2235



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedCommonRadius
open HeckeFamily CanonicalQuadraticSieve CompletedGauss
open CenteredMomentDescentLedger CenteredMomentFirstAmplificationChoice
open CenteredMomentAmplifiedRetainedRadius CenteredMomentSectorLocalization
open CenteredMomentCompleteCommon CenteredMomentCanonicalFirst
open CenteredMomentFirstCanonicalAllowance CenteredMomentFirstCanonicalFamily
open CenteredMomentRankinRadical ConcreteTraceCRT ActualEisensteinCubic
open CenteredMomentFirstMixedAllowance CenteredMomentCommonRadiusSaving
local notation "O" => ActualEisensteinCubic.O

theorem column_saving_gates (η τ : Character) (m : O)
    (I J : Ideal O) (A : Finset (CommonIndex I J)) (Z : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let q := Real.logb Z (τ.modulus.absNorm:ℝ)
    0≤c ∧ 0≤q ∧ 0≤extractedAllowance I J Z ∧
      3*c-5*d≤6*extractedAllowance I J Z+q := by
  dsimp only
  have hq := canonical_active_log_le η τ m I J A Z hZ hmod
  have hc : 0≤Real.logb Z ((commonPart I J).absNorm:ℝ) := by
    apply Real.logb_nonneg hZ
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (commonPart_ne_zero I J))
  have hm := le_max_left (3*Real.logb Z ((commonPart I J).absNorm:ℝ)-
    5*Real.logb Z ((commonPart J I).absNorm:ℝ)-
    Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)) (0:ℝ)
  refine ⟨hc,hq.1,?_,?_⟩
  · unfold extractedAllowance; positivity
  · unfold extractedAllowance; linarith [hq.2]

theorem actual_main_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J}) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*c/3-4*sigma/3-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) 0 (Real.logb Z (τ.modulus.absNorm:ℝ)) 0
        (extractedAllowance I J Z)
        (Real.logb Z (mainCommonRadius Z d K0 c sigma delta reserve)-j) (sigma/3) := by
  dsimp only
  rw [main_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  convert main_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    hc hq hB hallow using 1
  congr 1
  ring

theorem actual_error_column_saving (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-3*sigma/2-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_lower _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

theorem actual_error_column_saving_refined (η τ : Character) (m : O)
    (I J E : Ideal O) (_hI : Supported I) (_hJ : Supported J)
    (A : Finset (CommonIndex I J)) (K X Z j sigma delta reserve : ℝ) (hZ : 1<Z)
    (hmod : τ.modulus=η.modulus*Ideal.span {m}*Ideal.span {(72:O)}*
      Ideal.span {primeSubsetGenerator (fun P : CommonIndex I J => P.val) A*activeConductor I J})
    (M : Ideal O) [NeZero M] (H : Subgroup (O ⧸ M)ˣ)
    (Sbad : Finset (Ideal O)) (hbad : fixedBadPrimes⊆Sbad)
    (p0 : O) (hp0 : p0∈CenteredMomentPrimeElements.elementPool
      (CenteredMomentPrimePool.primePool M H Sbad (1/2) 1 (Z^(sigma/3))))
    (k : ℕ) (hk : k=1 ∨ k=6 ∨ k=7) :
    let c := Real.logb Z ((commonPart I J).absNorm:ℝ)
    let d := Real.logb Z ((commonPart J I).absNorm:ℝ)
    let _p := Real.logb Z ((commonRadical I J).absNorm:ℝ)
    let _R := Real.logb Z ((Ideal.span {activeConductor I J}).absNorm:ℝ)
    let K0 := nominalLog I J E K X Z
    2*(c+errorRemoval p0 Z k)/3-errorLoss sigma k-5*(delta+reserve)/6≤
      firstSaving c (d+K0-j) (errorRemoval p0 Z k)
        (Real.logb Z (τ.modulus.absNorm:ℝ)) (errorMoving p0 Z k) (extractedAllowance I J Z)
        (Real.logb Z (errorCommonRadius Z d K0 c sigma delta reserve p0 k)-j) 0 := by
  dsimp only
  rw [error_radius_gain _ _ _ _ _ _ _ _ hZ]
  obtain ⟨hc,hq,hB,hallow⟩ := column_saving_gates η τ m I J A Z hZ hmod
  obtain ⟨hl,hu⟩ := pool_prime_log_range M H Sbad hbad Z sigma hZ p0 hp0
  unfold errorRemoval errorMoving
  convert error_saving_refined _ _ (nominalLog I J E K X Z-j) _ _ sigma delta reserve
    (Real.logb Z (normValue p0)) hc hq hB hallow hl hu k hk using 1
  congr 1
  ring

end SevenEighths.CenteredMomentFirstMixedCommonRadius

end

end OAI
end OAIOriginalModule2235

/-! Original module: OAI.NumberTheory.DirichletL.Moments.FirstMixedNormalization
Source SHA256: 31e84cd4fd1bf6fcf5e1a3acf9dc9fd1038d4a291fef72f1662d53a3675d22cb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2236



namespace OAI

noncomputable section
open scoped Classical BigOperators

namespace SevenEighths.CenteredMomentFirstMixedNormalization
open CenteredMomentDescentLedger CenteredMomentSectorLocalization
open CenteredMomentAmplificationErrorEnergy CenteredMomentFirstAmplificationChoice
local notation "O" => ActualEisensteinCubic.O

theorem exceptional_reference_identity (Z V C D NE NR K Q w wo B j g ell:ℝ)
    (hZ:1<Z)(hV:0<V)(hC:0<C)(hD:0<D)(hE:0<NE)(hR:0<NR)(hK:0<K)(hQ:0<Q):
    let c:=Real.logb Z C;
    let d:=Real.logb Z D;
    let q:=Real.logb Z Q;
    let K0:=Real.logb Z (NE*NR*V^2/(K*C*D));
    let M:=Real.logb Z K+q-Real.logb Z NE-Real.logb Z NR;
    (V/C)*Z^(-wo)*(V/C/Z^w)^((1:ℝ)/3)*(Z^(j+g))^((5:ℝ)/6)*Z^(-ell)/
      (Q*(V/C)^2*Z^B)=
      Z^(Real.logb Z V-5*M/6-firstSaving c (d+K0-j) w q wo B g ell):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hzlog:Real.log Z≠0:=ne_of_gt (Real.log_pos hZ)
  dsimp only
  apply Real.log_injOn_pos
  · simp only [Set.mem_Ioi];positivity
  · simp only [Set.mem_Ioi];positivity
  · simp (disch := positivity) only [Real.log_div,Real.log_mul,Real.log_rpow,Real.log_pow]
    unfold firstSaving Real.logb
    rw [Real.log_div,Real.log_mul,Real.log_mul,Real.log_pow,
      Real.log_mul,Real.log_mul] <;> try positivity
    field_simp
    ; ring

