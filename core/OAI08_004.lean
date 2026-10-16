
namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSum
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedChoices
open ProbeSelectedPrimeSums
local notation "O" => HeckeFamily.O

theorem actual_repeated_sum (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(k : ℕ),k≤N → ∀(T : Fin k→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
      (hs : ∀j P,P∈T j→Supported P.val),
      (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin k→ℝ→ℂ) (Y : Fin k→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j,∑P:T j,‖W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j,(Y j)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hprod⟩ := selected_repeated_product e eps he he1 heps
  obtain ⟨D,hD,hcount⟩ := active_card_subpower N eps heps
  let A := annularPower c d (-(4/25:ℝ))
  let E := (max 1 (812*B*A))^N
  have hA : 0≤A := annularPower_nonneg c d _ hc
  have hE : 0<E := by dsimp [E];positivity
  refine ⟨D*C*E,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin k hk T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi
  let R := rowCost S hS u a e eps ((3*i+2:ℕ)*T0)
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  have hR : 0≤R := rowCost_nonneg _ _ _ _ _ _ _
  have hY0 (j : Fin k) : 0<Y j := zero_lt_one.trans_le (hY j)
  have hYY : 0≤∏j,(Y j)^(-(4/25:ℝ)) := Finset.prod_nonneg (fun j _=>Real.rpow_nonneg (hY0 j).le _)
  have hterm (P : ∀j,T j) (hP : P∈activeChoices u T W Y) :
      L*(∏j,‖W j (((P j).val.val.absNorm:ℝ)/Y j)*((P j).val.val.absNorm:ℂ)^(z-1)*
        centralRepeatedTerm η u (P j).val (hs j (P j).val (P j).property) x w z‖)≤
      C*E*R*∏j,(Y j)^(-(4/25:ℝ)) := by
    have hp := (Finset.mem_filter.mp hP).2
    have hb := hprod S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k
      (fun j=>(P j).val) (fun j=>hs j (P j).val (P j).property) (hdis P)
      (fun j=>hη j (P j).val (P j).property) (fun j=>hQ j (P j).val (P j).property)
      (fun j=>hsmall j (P j).val (P j).property) (fun j=>(hp j).1)
      B W Y hB hW x w z hx hw hz hwi
    have hpow : (∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2))≤A^k*∏j,(Y j)^(-(4/25:ℝ)) := by
      have hh := Finset.prod_le_prod₀ (s:=Finset.univ) (fun j _=>Real.rpow_nonneg (show (0:ℝ)≤(P j).val.val.absNorm by positivity) (-(4/25:ℝ)))
        (fun j (_:j∈Finset.univ)=>annular_rpow c d (Y j) ((P j).val.val.absNorm:ℝ) (-(4/25:ℝ)) hc hd (hY0 j)
          ((le_div_iff₀ (hY0 j)).mp (hWS j (hp j).2).1)
          ((div_le_iff₀ (hY0 j)).mp (hWS j (hp j).2).2))
      norm_num only [hz,show (17/50:ℝ)-1/2=-(4/25:ℝ) by norm_num] at ⊢
      simpa only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] using hh
    have hEbound : (812*B)^k*A^k≤E := by
      rw [←mul_pow]
      exact (pow_le_pow_left₀ (by positivity) (le_max_right 1 (812*B*A)) k).trans
        (pow_le_pow_right₀ (le_max_left 1 _) hk)
    calc
      _ ≤ C*(812*B)^k*R*∏j,((P j).val.val.absNorm:ℝ)^(z.re-1/2) := hb
      _ ≤ C*(812*B)^k*R*(A^k*∏j,(Y j)^(-(4/25:ℝ))) :=
        mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = C*((812*B)^k*A^k)*R*∏j,(Y j)^(-(4/25:ℝ)) := by ring
      _ ≤ _ := by gcongr
  rw [sum_products_restrict η u T hs W Y x w z,Finset.mul_sum]
  have hh := Finset.sum_le_sum hterm
  simp only [Finset.sum_const,nsmul_eq_mul] at hh
  apply hh.trans
  calc
    _ ≤ (D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps)*(C*E*R*∏j,(Y j)^(-(4/25:ℝ))) :=
      mul_le_mul_of_nonneg_right (hcount k hk u T W Y) (by positivity)
    _ = _ := by dsimp [R];ring
end SevenEighths.ProbeCentralRepeatedSum

end

end OAI
end OAIOriginalModule2562

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralRepeatedSubset
Source SHA256: 3c09b8f47efe4422099c9ae6beb0d032c8b3624a49f5e79008d70cabaaa7219c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2563


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralRepeatedSubset
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve ProbeCentralRepeatedProduct ProbeCentralRepeatedSum
local notation "O" => HeckeFamily.O

theorem actual_repeated_subset (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀J : Finset (Fin N),
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        (∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖) ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*∏j:J,(Y j.val)^(-(4/25:ℝ)) := by
  obtain ⟨C,hC,hmain⟩ := actual_repeated_sum N e eps c d B he he1 heps hc hd hB
  refine ⟨C,hC,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi J
  let k := Fintype.card J
  let E : J≃Fin k := Fintype.equivFin J
  let idx : Fin k→Fin N := fun j=>(E.symm j).val
  have hi : Function.Injective idx := fun j l h=>E.symm.injective (Subtype.ext h)
  have hk : k≤N := by
    dsimp [k]
    simpa only [Fintype.card_coe,Finset.card_univ,Fintype.card_fin] using J.card_le_univ
  have hd' (P : ∀j,T (idx j)) : Function.Injective (fun j=>(P j).val) := by
    intro j l heq
    change (P j).val=(P l).val at heq
    by_contra hne
    have hdiff : idx j≠idx l := fun h=>hne (hi h)
    exact Finset.disjoint_left.mp (hdis _ _ hdiff) (P j).property (by rw [heq];exact (P l).property)
  have hb := hmain S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin k hk
    (fun j=>T (idx j)) (fun j P hP=>hs (idx j) P hP) hd'
    (fun j P hP=>hη (idx j) P hP) (fun j P hP=>hQ (idx j) P hP)
    (fun j P hP=>hsmall (idx j) P hP) (fun j=>W (idx j)) (fun j=>Y (idx j))
    (fun j=>hY (idx j)) (fun j=>hWS (idx j)) (fun j=>hW (idx j)) x w z hx hw hz hwi
  have hleft : (∏j:Fin k,∑P:T (idx j),‖W (idx j) ((P.val.val.absNorm:ℝ)/Y (idx j))*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs (idx j) P.val P.property) x w z‖)=
      ∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  have hright : (∏j:Fin k,(Y (idx j))^(-(4/25:ℝ)))=∏j:J,(Y j.val)^(-(4/25:ℝ)) :=
    Fintype.prod_equiv E.symm _ _ (fun _=>rfl)
  rw [hleft,hright] at hb
  exact hb
end SevenEighths.ProbeCentralRepeatedSubset

end

end OAI
end OAIOriginalModule2563

/-! Original module: OAI.NumberTheory.DirichletL.Detector.CentralAllSlots
Source SHA256: 44baeae06238618256fefe9973d1c120102a5451845dcbfcf3167570fd963231
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2564




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralAllSlots
open HeckeFamily HeckeInverseAmplification ProbeHighRowFamily ProbePhysical
open CanonicalQuadraticSieve CanonicalRowCompletion ProbeCentralRepeatedProduct
open ProbeCentralRepeatedSubset ProbeCentralBranchProduct
local notation "O" => HeckeFamily.O

def phaseSlot (u : FreeRow) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (W : ℝ→ℂ) (Y : ℝ) (z : ℂ) : ℂ :=
  ∑P:T,W ((P.val.val.absNorm:ℝ)/Y)*(P.val.val.absNorm:ℂ)^(z-1)*(-star (idealRowHom u.val P.val.val))

theorem actual_three_branch_slots (N : ℕ) (e eps c d B : ℝ)
    (he : 0<e) (he1 : e<1/1000) (heps : 0<eps)
    (hc : 0<c) (hd : 0<d) (hB : 0≤B) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : ∀P∈S,Prime P)
      (hmax : ∀P∈S,P.IsMaximal),fixedBadPrimes⊆S →
    ∀(u : FreeRow),u.val≠1 → ∀{ι : Type*} [Fintype ι] (η : Character) (twists : ι→Character)
      (T0 a : ℝ) (i : ℕ),2<T0 → 51/100≤a → a≤1 →
      detectorMaximum (sourceDetectorFamily S hS η u twists) (3*(i+1:ℕ)*T0)<a+2*e →
    ∀(T : Fin N→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hs : ∀j P,P∈T j→Supported P.val),
      (∀j l,j≠l → Disjoint (T j) (T l)) →
      (∀j P,P∈T j→IsCoprime P.val η.modulus) →
      (∀j P,P∈T j→(480:ℝ)≤P.val.absNorm) →
      (∀j P,P∈T j→198*(P.val.absNorm:ℝ)^(-10*e)≤1/2) →
    ∀(W : Fin N→ℝ→ℂ) (Y : Fin N→ℝ),
      (∀j,1≤Y j) → (∀j,Function.support (W j)⊆Set.Icc c d) → (∀j t,‖W j t‖≤B) →
    ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |w.im|≤(3*i+2:ℕ)*T0 →
    ∀p : Fin N→ℝ,(∀j,1≤p j) → (∀j,‖phaseSlot u (T j) (W j) (Y j) z‖≤(Y j)^(-(4/25:ℝ))*p j) →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖*
        ‖∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
          centralNormalizedSlot η u P.val (hs j P.val P.property) x w z‖ ≤
        C*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*
          ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(eps*(N+1))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by
  obtain ⟨Cr,hCr,hregular⟩ := central_regular_slot_sum eps c d B heps hc hd hB
  obtain ⟨Ct,hCt,hrepeated⟩ := actual_repeated_subset N e eps c d B he he1 heps hc hd hB
  refine ⟨Ct*(Cr+2)^N,by positivity,?_⟩
  intro S hS hmax hbad u hu ι _ η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall W Y hY hWS hW x w z hx hw hz hwi p hp hphase
  let L := ‖star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS u) w‖
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  let R := Ct*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*U^eps
  let A : Fin N→ℂ := fun j=>phaseSlot u (T j) (W j) (Y j) z
  let E : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRegularError η u P.val (hs j P.val P.property) x w z
  let F : Fin N→ℂ := fun j=>∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
    centralRepeatedTerm η u P.val (hs j P.val P.property) x w z
  let yy : Fin N→ℝ := fun j=>(Y j)^(-(4/25:ℝ))
  have hU : 1≤U := by dsimp [U];exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hUp : 1≤U^eps := Real.one_le_rpow hU heps.le
  have hR : 0≤R := by dsimp [R];exact mul_nonneg (mul_nonneg hCt.le (rowCost_nonneg _ _ _ _ _ _ _)) (Real.rpow_nonneg (zero_le_one.trans hU) _)
  have hyy (j : Fin N) : 0≤yy j := Real.rpow_nonneg (zero_le_one.trans (hY j)) _
  have hE (j : Fin N) : ‖E j‖≤yy j*(Cr*U^eps) := by
    have hb := hregular η u (T j) (fun P hP=>⟨hs j P hP,hQ j P hP,hη j P hP⟩)
      (Y j) (hY j) (W j) (hWS j) (hW j) a e x w z ha ha1 he he1.le hx hw hz (hsmall j)
    exact (norm_sum_le _ _).trans (hb.trans_eq (by dsimp [yy,U];ring))
  have hF (J : Finset (Fin N)) : L*(∏j∈J,‖F j‖)≤R*(∏j∈J,yy j) := by
    have hb := hrepeated S hS hmax hbad u hu η twists T0 a i hT0 ha ha1 hbin T hs hdis hη hQ hsmall
      W Y hY hWS hW x w z hx hw hz hwi J
    have hp' : (∏j:J,‖F j.val‖)≤∏j:J,∑P:T j.val,‖W j.val ((P.val.val.absNorm:ℝ)/Y j.val)*
        (P.val.val.absNorm:ℂ)^(z-1)*centralRepeatedTerm η u P.val (hs j.val P.val P.property) x w z‖ := by
      apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
      intro j _
      exact norm_sum_le _ _
    have hh := (mul_le_mul_of_nonneg_left hp' (show 0≤L from norm_nonneg _)).trans hb
    rw [Finset.prod_coe_sort J (fun j=>‖F j‖),
      Finset.prod_coe_sort J (fun j=>(Y j)^(-(4/25:ℝ)))] at hh
    exact hh
  have hb := three_branch_bound L R (Cr*U^eps) A E F yy p (norm_nonneg _) hR (by positivity) hyy hp hphase hE hF
  have heq : (∏j,∑P:T j,W j ((P.val.val.absNorm:ℝ)/Y j)*(P.val.val.absNorm:ℂ)^(z-1)*
      centralNormalizedSlot η u P.val (hs j P.val P.property) x w z)=∏j,(A j+E j+F j) := by
    apply Finset.prod_congr rfl
    intro j _
    simp only [A,E,F,phaseSlot,centralNormalizedSlot_split,mul_add,Finset.sum_add_distrib]
  rw [heq]
  apply hb.trans
  have hcoef : (Cr*U^eps+2)^N≤(Cr+2)^N*U^(eps*N) := by
    have hh : Cr*U^eps+2≤(Cr+2)*U^eps := by nlinarith
    have hp' := pow_le_pow_left₀ (show 0≤Cr*U^eps+2 by positivity) hh N
    rw [mul_pow] at hp'
    have heq : (U^eps)^N=U^(eps*N) := by
      rw [←Real.rpow_natCast,←Real.rpow_mul (zero_le_one.trans hU)]
    rwa [heq] at hp'
  have hyprod : 0≤∏j,yy j := Finset.prod_nonneg (fun j _=>hyy j)
  have hpprod : 0≤∏j,p j := Finset.prod_nonneg (fun j _=>zero_le_one.trans (hp j))
  calc
    _ ≤ R*((Cr+2)^N*U^(eps*N))*(∏j,yy j)*(∏j,p j) := by gcongr
    _ = _ := by
      dsimp [R,yy]
      have hh : U^eps*U^(eps*N)=U^(eps*(N+1)) := by rw [←Real.rpow_add (zero_lt_one.trans_le hU)];congr 1;ring
      calc
        _ = Ct*(Cr+2)^N*rowCost S hS u a e eps ((3*i+2:ℕ)*T0)*(U^eps*U^(eps*N))*(∏j,(Y j)^(-(4/25:ℝ)))*(∏j,p j) := by ring
        _ = _ := by rw [hh]
end SevenEighths.ProbeCentralAllSlots

end

end OAI
end OAIOriginalModule2564

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedGrowth
Source SHA256: 08d2cc2f52e265fb04a97bbf0a84b8f361b92c131ec2f0c153932450a206e40f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2565





namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_joint_growth
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e) :
    ∃C : ℝ,0≤C ∧ ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)
  have hR : 0≤R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R :=
    hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*R)*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hR)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2565

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedHeightGrowth
Source SHA256: d0e6128d19fad228d750c57f9b3641009aab0f57281fdacddc63f8331a17fbc3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2566





namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

variable {ι : Type*} [Fintype ι]

theorem calibrated_physicalRow_buffered_height_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    : ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_growth S hS hmax u hu
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let R : ℝ := Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) 0)/9
  have hR : 0≤R := by
    dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
    positivity
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm 2
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*R*Cn*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz
      (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤R*(3+|H|)^2 := by
    have hr := hreciprocal (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
      (Sum.inl false) x hxl hxr hxi
    have hscale : Cr*(HeckeReciprocalGrowth.presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^(1:ℝ)=R*(3+|H|)^2 := by
      dsimp [R,HeckeReciprocalGrowth.presentationComplexity,HeckeLogarithmic.complexity]
      rw [Real.rpow_one]
      ring
    simpa only [sourceDetectorFamily_denominator,hscale] using hr
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(R*(3+|H|)^2))*(Cn*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2566

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CentralCosts
Source SHA256: 68864bda2cd363a8068ead715120d3ac2b02ff789fd8c1e183083d2535afaa1f
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2567





namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical HeckeReciprocalGrowth
local notation "O" => HeckeFamily.O

def centralRemainingScalar (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (η : Character) (u : FreeRow) (x w z : ℂ) : ℂ :=
  LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
    HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x*
    continuedCorrection S hS η u x w z

lemma centralRowScalar_split (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (u : FreeRow) (x w z : ℂ) :
    centralRowScalar S hS hmax η u x w z=
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      centralRemainingScalar S hS η u x w z := by
  unfold centralRowScalar centralRemainingScalar
  ring

theorem centralRemainingScalar_bound (e eps : ℝ)
    (he : 0<e) (he' : e<1/1000) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀(S : Finset (Ideal O)) (hS : SourceExclusions S),FirstTail (4*e) S →
      ∀(η : Character) (u : FreeRow) {ι : Type*} [Fintype ι] (ψ : ι→Character)
      (B a H : ℝ) (i : ℕ),2<B → 51/100≤a → a≤1 → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,x.re=a+16*e → w.re=1-a-6*e → z.re=17/50 → |x.im|≤H →
      ‖centralRemainingScalar S hS η u x w z‖≤C*
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^eps*
        (presentationComplexity ((targetRow η u).excludePrimes S hS.prime) H)^eps := by
  obtain ⟨Ch,hCh,hh⟩ := continuedCorrection_first_subpower eps heps
  obtain ⟨Cr,hCr,hr⟩ := buffered_rectangle_reciprocal_bound e eps he he' heps
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨(L+1)*Cr*Ch,by positivity,?_⟩
  intro S hS hfirst η u ι _ ψ B a H i hB ha ha1 hH hbin x w z hx hw hz hxi
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L+1 :=
    (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2)
      (by simp only [Complex.mul_re];rw [hz];norm_num)).trans (by linarith)
  have hc := hh (4*e) S hS hfirst η u x w z
    (by rw [hx];linarith) (by rw [hw];linarith) (by rw [hz]) (by rw [hx,hw];linarith)
  have hrec := hr (sourceDetectorFamily S hS.prime η u ψ) B a H i hB ha ha1 hH hbin
    (Sum.inl false) x (by rw [hx]) (by rw [hx];linarith) hxi
  simp only [sourceDetectorFamily_denominator] at hrec
  unfold centralRemainingScalar
  rw [norm_mul,norm_mul]
  apply (mul_le_mul (mul_le_mul hl hrec (norm_nonneg _) (by linarith)) hc (norm_nonneg _)
    (mul_nonneg (by linarith) (mul_nonneg hCr.le (Real.rpow_nonneg (by
      unfold presentationComplexity HeckeLogarithmic.complexity;positivity) _)))).trans
  exact le_of_eq (by ring)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2567

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CoarsePhysical
Source SHA256: cbe08174ed57bb737e20fece0870aeda228fcb76ef8aa1fcfde8034ec82f2feb
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2568



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem buffered_denominator_polynomial_growth (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : ∀P∈S,Prime P) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow) (ψ : ι→Character)
      (a B H : ℝ) (i : ℕ),(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H →
      ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS) x‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^2*(3+|H|)^2 := by
  obtain ⟨C,hC,hbound⟩ := buffered_rectangle_reciprocal_bound e 1 he he' (by norm_num)
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨2*C*(1+A^2),by positivity,?_⟩
  intro η u ψ a B H i ha haTop hB hH hbin x hxl hxr hxi
  let χ := (targetRow η u).excludePrimes S hS
  have hb := hbound (sourceDetectorFamily S hS η u ψ) B a H i hB ha haTop hH hbin (Sum.inl false) x hxl hxr hxi
  simp only [sourceDetectorFamily_denominator,Real.rpow_one] at hb
  have hQ : (χ.modulus.absNorm:ℝ)≤(η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    have hh := targetRow_excluded_conductor S hS η u
    dsimp [χ,A]
    exact_mod_cast (by simpa only [mul_assoc,mul_comm,mul_left_comm] using hh)
  apply hb.trans
  unfold HeckeReciprocalGrowth.presentationComplexity HeckeLogarithmic.complexity
  have hrad := HeckeDyadic.radical_norm_le_modulus χ
  calc
    _ ≤ C*((χ.modulus.absNorm:ℝ)*(2*(χ.modulus.absNorm:ℝ)*(3+|H|)^2)) := by gcongr
    _ ≤ C*(((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*
        (2*((η.modulus.absNorm:ℝ)*A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))*(3+|H|)^2)) := by gcongr
    _ ≤ _ := by nlinarith [sq_nonneg ((η.modulus.absNorm:ℝ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)*(3+|H|))]

def coarsePrimeCost (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ := ∏P∈T,(8192:ℝ)*(P.val.absNorm:ℝ)^3

lemma coarsePrimeCost_nonneg (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : 0≤coarsePrimeCost T := by
  unfold coarsePrimeCost
  positivity

theorem calibrated_physicalRow_buffered_polynomial_growth
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (ψ : ι→Character),
      ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀x w z : ℂ,a+16*e≤x.re → x.re≤2 → |x.im|≤H → w.re=1-a-6*e → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z‖≤
        C*(η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*
          coarsePrimeCost T*(3+|H|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  obtain ⟨Cr,hCr,hreciprocal⟩ := buffered_denominator_polynomial_growth (ι:=ι) e he he' S hS.prime
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*Cr*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT ψ a B H i ha ha1 hB hH hbin x w z hxl hxr hxi hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hwlow : -(1/100:ℝ)≤w.re := by rw [hw];linarith
  have hn' := hn u hu w hwlow
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (4*e) S hS hfirst T η u x w z (by linarith) hwlow hz (by rw [hw];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec := hreciprocal η u ψ a B H i ha ha1 hB hH hbin x hxl hxr hxi
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    have hQ : (4:ℝ)≤P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    exact (continuedCompensatedLocal_first_bound η u P.val _ hQ 2 x w z
      (by linarith) hxr hwlow hz (by rw [hw];linarith)).trans (selectedFirstBound_polynomial (by linarith))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*(Cr*(η.modulus.absNorm:ℝ)^2*N^2*(3+|H|)^2))*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (by positivity)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring

theorem calibrated_physicalRow_first_joint_polynomial_growth
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S),∀x w z : ℂ,x.re=2 → -(1/100:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*coarsePrimeCost T*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_first_uniform_growth S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let L : ℝ := HeckeReciprocalBound.bound 2
  have hL : 0≤L := by dsimp [L,HeckeReciprocalBound.bound];positivity
  refine ⟨L*L*Cn*Ch,by positivity,?_⟩
  intro η u hu T hT x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hn' := hn u hu w hw
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh (1/4) S hS hfirst T η u x w z (by rw [hx];norm_num) hw hz
      (by rw [hx];linarith)
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤L :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤L :=
    HeckeReciprocalBound.reciprocal_norm_le _ (by norm_num) (by rw [hx])
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤coarsePrimeCost T := by
    rw [norm_prod]
    unfold coarsePrimeCost
    conv_rhs => rw [←Finset.prod_attach]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    apply (continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) 2 x w z
      (by rw [hx];norm_num) hx.le hw hz (by rw [hx];linarith)).trans
    exact selectedFirstBound_polynomial (by have hn:=hS.tail.norm_four P.val (hT P.val P.property);exact_mod_cast (by omega : 1≤P.val.val.absNorm))
  have heq : star ((calibrationForSet S hmax).residueMonoid u.val)*physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x) ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [heq,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (L*L)*(Cn*N^3*(3+|w.im|)^2)*(Ch*N)*coarsePrimeCost T := by
      apply mul_le_mul _ hg (norm_nonneg _) (by have hc:=coarsePrimeCost_nonneg T;dsimp [N];positivity)
      apply mul_le_mul _ hh' (norm_nonneg _) (by positivity)
      apply mul_le_mul _ hn' (norm_nonneg _) (mul_nonneg hL hL)
      rw [norm_mul]
      exact mul_le_mul hl hrec (norm_nonneg _) hL
    _ = _ := by dsimp [N];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2568

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalBoundary
Source SHA256: 39674d93897a66177d0618736bfc78123516ade7f22649543dcf632c06d04f34
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2569


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def rowKernelScalar {K : ℕ} (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (u : FreeRow)
    (W0 : SchwartzMap ℝ ℂ) (X Z : ℝ) (x z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_w_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      rowKernelScalar P u W0 X Z x z*(Y:ℂ)^(w-1)*mellin W1 w*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel rowKernelScalar sourceMellinWeight
  ring

theorem continuedPhysicalRowKernel_cauchy {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤C)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((v:ℂ)+t*I) z‖≤B*cauchy t := by
  obtain ⟨D,hD,hm⟩ := CubicReflectionKernel.compact_source_mellin_strip_decay W1 a b ha hW
    (W1.smooth ⊤) l r (N+2)
  have hscale := (scaleBound_pos Y (l-1) (r-1)).le
  let A := ‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*C
  refine ⟨A*D,by dsimp [A]; positivity,?_⟩
  intro v hv t
  have hYbd := cpow_le_scaleBound hY (((v:ℂ)+t*I)-1)
    (show (((v:ℂ)+t*I)-1).re∈Icc (l-1) (r-1) by simpa using hv)
  have hm' : height t^2*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖)≤D := by
    simpa [height,pow_add,mul_assoc,mul_comm,mul_left_comm] using hm v hv t
  have hmc : height t^N*‖mellin W1 ((v:ℂ)+t*I)‖≤D*cauchy t :=
    CubicReflectionKernel.weighted_two_to_cauchy
      (mul_nonneg (pow_nonneg (height_pos t).le N) (norm_nonneg _)) t hm'
  rw [continuedPhysicalRowKernel_w_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖rowKernelScalar P u W0 X Z x z‖*scaleBound Y (l-1) (r-1)*
        ‖mellin W1 ((v:ℂ)+t*I)‖)*(C*height t^N) := by
      apply mul_le_mul _ (hpoly v hv t) (norm_nonneg _) (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hYbd (norm_nonneg _)) (norm_nonneg _)
    _ = A*(height t^N*‖mellin W1 ((v:ℂ)+t*I)‖) := by dsimp [A]; ring
    _ ≤ A*(D*cauchy t) := mul_le_mul_of_nonneg_left hmc (by dsimp [A]; positivity)
    _ = _ := by ring

theorem nonprincipal_w_integral_eq_of_polynomial {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r C : ℝ) (N : ℕ) (hC : 0≤C)
    (hlr : l≤r) (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l)
    (hz : (17/50:ℝ)≤z.re) (hxl : 1+eps≤x.re+l)
    (hpoly : ∀v∈Icc l r,∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^N) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW
    X Y Z hY x z l r C N hC hpoly
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun w=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro w hw
  exact (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x w z hx (hl.trans hw.1) hz (by linarith [hw.1])).differentiableWithinAt

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2569

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstWShift
Source SHA256: 705c2f91d3dc5114acb4183a79b52d8523fe5fa753e1e9519c73d8a5792f2ddc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2570



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma physicalRow_first_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,l≤v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z l hx hl hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by unfold height;nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_first_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr hx hl hz hxw
    (fun v hv t=>hbound v hv.1 t)

lemma nonprincipal_first_w_vertical_integrable {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    Integrable (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_first_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z l hx hl hz hxw
  obtain ⟨B,hB,hb⟩ := continuedPhysicalRowKernel_cauchy S hS hmax P hPS η u W0 W1 a b ha hW X Y Z hY x z l l C 2 hC.le
    (fun v hv t=>hbound v hv.1 t)
  have hc : Continuous (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuedPhysicalRowKernel_differentiableAt_w eps heps S hS hfirst hmax P hPS η u hu
      W0 W1 a b ha hW X Y Z hY x ((l:ℂ)+t*I) z hx (by simpa using hl) hz
      (by simpa using hxw)).continuousAt.comp (f:=fun t : ℝ=>(l:ℂ)+t*I)
    fun_prop
  exact (cauchy_integrable.const_mul B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>hb l ⟨le_rfl,le_rfl⟩ t))

theorem finite_rows_first_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character)
    (F : Finset FreeRow) (hF : ∀u∈F,u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hl : -(1/100:ℝ)≤l) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+l) :
    (∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  rw [integral_finsetSum F (fun u hu=>nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l hx hl hz hxw),
    integral_finsetSum F (fun u hu=>nonprincipal_first_w_vertical_integrable eps heps S hS hfirst hmax P hPS η u (hF u hu)
      W0 W1 a b ha hW X Y Z hY x z r hx (hl.trans hlr) hz (by linarith))]
  exact Finset.sum_congr rfl (fun u hu=>nonprincipal_first_w_integral_eq eps heps S hS hfirst hmax P hPS η u (hF u hu)
    W0 W1 a b ha hW X Y Z hY x z l r hlr hx hl hz hxw)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2570

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.TupleGrowth
Source SHA256: 8795aed1b2b14a5320c9e85b39c5e31f203f36ba160e7604cb24e2ca3bea4972
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2571





namespace OAI

noncomputable section
open scoped Classical
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem nonprincipal_positive_growth (σ δ : ℝ) (hσ : 0<σ) (hδ : 0<δ) :
    ∃C : ℝ,0<C ∧ ∀χ : Character,χ.residue≠1 → ∀s : ℂ,σ≤s.re →
      ‖HeckeOrigin.continued χ s‖≤C*(χ.modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  obtain ⟨Cd,hCd,hdel⟩ := HeckeDeletionBounds.factors_subpower_bound σ δ hσ hδ
  refine ⟨(1+HeckeLogarithmicInput.uniformConstant)*Cd,
    mul_pos (by linarith [HeckeLogarithmicInput.uniformConstant_nonneg]) hCd,?_⟩
  intro χ hχ s hs
  obtain ⟨ψ,_,hp,hQ,hmask⟩ := exists_primitive_character χ
  have hψ : ψ.residue≠1 := fun h=>hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr h)
  have hg := HeckeLogarithmicInput.regular_right_growth ψ hp (by linarith : -(1/10:ℝ)≤s.re)
  rw [HeckeLogarithmicInput.regular_eq_nonprincipal ψ hψ] at hg
  have hd : ‖HeckeFiniteDeletion.factors χ.modulus ψ s‖≤Cd*(χ.modulus.absNorm:ℝ)^δ :=
    (le_add_of_nonneg_right (norm_nonneg _)).trans (hdel χ.modulus χ.modulus_ne_bot ψ s hs)
  have hQ' : (ψ.modulus.absNorm:ℝ)^(3/5:ℝ)≤(χ.modulus.absNorm:ℝ)^(3/5:ℝ) :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hQ) (by norm_num)
  have hU := HeckeLogarithmicInput.uniformConstant_nonneg
  have hN : (0:ℝ)<χ.modulus.absNorm := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  rw [HeckeOrigin.continued,ite_eq_right hχ,
    HeckeFiniteDeletion.LFunction_eq_of_mask_nonprincipal χ ψ hmask hχ (by linarith),norm_mul]
  calc
    _ ≤ (HeckeLogarithmicInput.uniformConstant*(ψ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := mul_le_mul hg hd (norm_nonneg _) (by positivity)
    _ ≤ ((1+HeckeLogarithmicInput.uniformConstant)*(χ.modulus.absNorm:ℝ)^(3/5:ℝ)*(3+|s.im|)^2)*
        (Cd*(χ.modulus.absNorm:ℝ)^δ) := by gcongr;linarith
    _ = _ := by rw [Real.rpow_add hN];ring

theorem calibrated_numerator_positive_growth (σ δ : ℝ) (hσ : 0<σ) (hδ : 0<δ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(u : FreeRow),u.val≠1 → ∀s : ℂ,σ≤s.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) s‖≤
        C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := nonprincipal_positive_growth σ δ hσ hδ
  let A : ℝ := (conductorConstant:ℝ)*((∏P∈S,P).absNorm:ℝ)
  have hA : 0≤A := by dsimp [A];positivity
  refine ⟨C*(1+A^(3/5+δ)),mul_pos hC (by positivity),?_⟩
  intro u hu s hs
  by_cases hc : (calibrationForSet S hmax).residueMonoid u.val=0
  · simp only [hc,star_zero,zero_mul,norm_zero]
    positivity
  · have hnp := calibrated_row_nonprincipal S hS.prime hmax hS.bad u hu hc
    have hg := hmain (rowCharacter S hS.prime u) hnp s hs
    have hcal : ‖star ((calibrationForSet S hmax).residueMonoid u.val)‖≤1 := by
      rw [norm_star]
      exact (calibrationForSet S hmax).residueMonoid_norm_le_one _
    have hQ : ((rowCharacter S hS.prime u).modulus.absNorm:ℝ)≤
        A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
      have h := rowCharacter_conductor S hS.prime u
      dsimp [A]
      exact_mod_cast (by simpa only [mul_right_comm] using h)
    rw [norm_mul]
    calc
      _ ≤ ‖HeckeOrigin.continued (rowCharacter S hS.prime u) s‖ :=
        mul_le_of_le_one_left (norm_nonneg _) hcal
      _ ≤ C*((rowCharacter S hS.prime u).modulus.absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := hg
      _ ≤ C*(A*((Ideal.span {u.val}:Ideal O).absNorm:ℝ))^(3/5+δ)*(3+|s.im|)^2 := by
        gcongr
      _ ≤ C*(1+A^(3/5+δ))*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by
        rw [Real.mul_rpow hA (by positivity)]
        calc
          _ = C*A^(3/5+δ)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*(3+|s.im|)^2 := by ring
          _ ≤ _ := by gcongr;linarith

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2571

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ScalarGrowth
Source SHA256: 11a2756996f705d54d74abf122f4a0ca2998e8fedd6539f58db0ac34a784d93b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2572



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_scalar_growth (e δ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hδ : 0<δ) (hδ' : δ≤1) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 → ∀(x w z : ℂ),
      HeckeZeroSupremum.beta+8*e≤x.re → (1/2:ℝ)≤w.re → (17/50:ℝ)≤z.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
          HeckeOrigin.continued (rowCharacter S hS.prime u) w*
          HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)‖≤
        C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
          (3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) (δ/2) (by norm_num) (by linarith) S hS hmax
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e (δ/2) he he' (by linarith) (by linarith) S hS.prime
  let B : ℝ := HeckeReciprocalBound.bound 2
  have hB : 0≤B := tsum_nonneg (fun _=>norm_nonneg _)
  refine ⟨(1+B)*Cn*Cr,by positivity,?_⟩
  intro η u hu x w z hx hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have hn' := hn u hu w hw
  have hr' := hr η u x hx
  have hz' : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤1+B := by
    apply (HeckeStripActual.LFunction_norm_le _ (by norm_num : (1:ℝ)<2) (s:=6*z) ?_).trans
    · dsimp [B];linarith
    · norm_num [Complex.mul_re];linarith
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (HeckeLogarithmicInput.modulus_norm_ge_one η) (by linarith)
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)=
      LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x := by ring
  rw [he,norm_mul,norm_mul]
  calc
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^(δ/2)*N^(δ/2)*(3+|x.im|)^2) := by
      apply mul_le_mul _ hr' (norm_nonneg _) (by positivity)
      exact mul_le_mul hz' hn' (norm_nonneg _) (by positivity)
    _ ≤ (1+B)*(Cn*N^(3/5+δ/2)*(3+|w.im|)^2)*
        (Cr*(η.modulus.absNorm:ℝ)^δ*N^(δ/2)*(3+|x.im|)^2) := by gcongr
    _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = ((1+B)*Cn*Cr)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2572

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.PhysicalBound
Source SHA256: ced32dc9f54bc17044542df030e9623ea350bdcffe3d30bc1b40bc72529fabb0
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2573




namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physical_tuple_sum (K : ℕ) (e δ a b r B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → HeckeZeroSupremum.beta+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r →
      (∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
        (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨CL,hCL,hL⟩ := calibrated_scalar_growth e (δ/2) he he' (by linarith) (by linarith) S hS hmax
  obtain ⟨CG,hCG,hG⟩ := continued_selected_tuple_with_correction K (δ/2) a b r B (by linarith) ha hb hr hB
  refine ⟨CL*CG,mul_pos hCL hCG,?_⟩
  intro η u hu T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  have hN : 0<N := by
    dsimp [N]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  have ht : ∀i P,P∈T i→CanonicalQuadraticSieve.Supported P.val ∧ (4:ℝ)≤P.val.absNorm := by
    intro i P hP
    exact ⟨outside_prime_supported S hS.bad P (hT i P hP),by exact_mod_cast hS.tail.norm_four P (hT i P hP)⟩
  let L : ℂ := star ((calibrationForSet S hmax).residueMonoid u.val)*
    (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*HeckeOrigin.continued (rowCharacter S hS.prime u) w*
      HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)
  let G : (∀i,T i)→ℂ := fun P=>continuedCorrection
    (markExclusions S (Finset.univ.image (fun i=>(P i).val)))
    (markedSourceExclusions S hS (Finset.univ.image (fun i=>(P i).val))) η u x w z*
    ∏i,W i (((P i).val.val.absNorm:ℝ)/Y i)*((P i).val.val.absNorm:ℂ)^(z-1)*
      continuedCompensatedLocal η u (P i).val (ht i (P i).val (P i).property).1 x w z
        (star (idealCoeff η (P i).val.val)*((P i).val.val.absNorm:ℂ)^x)
        (((P i).val.val.absNorm:ℂ)^(-w))
  have heq (P:∀i,T i) : calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i (P i).val (P i).property) W Y x w z=L*G P :=
    calibratedTupleValue_factor S hS hmax η u _ (hdis P) _ W Y x w z
  have hLb : ‖L‖≤CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2 :=
    hL η u hu x w z hxβ hw (by rw [hz];exact hr)
  have hGb : (∑P:(∀i,T i),‖G P‖)≤CG*N^(δ/2)*∏i,(Y i)^r :=
    hG (1/4) S hS hfirst η u T ht Y hY W hWS hWB x w z hx hw hz (by linarith)
  have hη : (η.modulus.absNorm:ℝ)^(δ/2)≤(η.modulus.absNorm:ℝ)^δ :=
    Real.rpow_le_rpow_of_exponent_le (HeckeLogarithmicInput.modulus_norm_ge_one η) (by linarith)
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  simp_rw [heq,norm_mul]
  rw [←Finset.mul_sum]
  calc
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^(δ/2)*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) :=
      mul_le_mul hLb hGb (Finset.sum_nonneg fun _ _=>norm_nonneg _) (by positivity)
    _ ≤ (CL*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ/2)*(3+|x.im|)^2*(3+|w.im|)^2)*
        (CG*N^(δ/2)*∏i,(Y i)^r) := by gcongr
    _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*N^(3/5+δ)*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
      have hp : N^(3/5+δ/2)*N^(δ/2)=N^(3/5+δ) := by
        rw [←Real.rpow_add hN]
        congr 1
        ring
      calc
        _ = (CL*CG)*(η.modulus.absNorm:ℝ)^δ*(N^(3/5+δ/2)*N^(δ/2))*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2573

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.RowCount
Source SHA256: 95b8a28970f6adb58798487eeb689494aa45461f7a1d3451328b493c0ee2a535
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2574



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ConcreteTraceCRT ActualEisensteinCubic
local notation "O" => HeckeFamily.O

lemma freeRow_count (R : Finset FreeRow) (H : ℝ) (hH : 1≤H)
    (hR : ∀u∈R,((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤H) :
    (R.card:ℝ)≤128*H := by
  have hc := DescentFiberCost.finite_element_count_real (R.image Subtype.val) H hH (by
    intro a ha
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp ha
    rw [eisEmbedding_norm_sq_eq_absNorm_span]
    exact hR u hu)
  rw [Finset.card_image_of_injective R Subtype.val_injective] at hc
  exact hc

lemma frequencyWeight_ideal_norm (z : ℂ) (u : FreeRow) :
    ‖frequencyWeight z ⟨u.val,u.property.1⟩‖=
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-z.re) := by
  have hN : (0:ℝ)<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  unfold frequencyWeight elementNorm
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hN,Complex.neg_re]

lemma dyadic_weighted_rows (a r C U : ℝ) (hC : 0≤C) (hU : 1≤U)
    (R : Finset FreeRow)
    (hR : ∀u∈R,U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U)
    (F : FreeRow→ℝ) (hF : ∀u∈R,F u≤C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a)
    (z : ℂ) (hz : z.re=r) :
    (∑u∈R,‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u)≤
      256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(1+a-r) := by
  have hU0 : 0<U := by linarith
  have hcard : (R.card:ℝ)≤256*U := by
    have hc := freeRow_count R (2*U) (by linarith) (fun u hu=>(hR u hu).2)
    linarith
  have hA := ProbeSelectedPrimeSums.annularPower_nonneg 1 2 (a-r) (by norm_num)
  calc
    _ ≤ ∑u∈R,C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r) := by
      apply Finset.sum_le_sum
      intro u hu
      have hN : 0<((Ideal.span {u.val}:Ideal O).absNorm:ℝ) := hU0.trans_le (hR u hu).1
      rw [frequencyWeight_ideal_norm,hz]
      calc
        _ ≤ ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)*
            (C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^a) :=
          mul_le_mul_of_nonneg_left (hF u hu) (Real.rpow_nonneg hN.le _)
        _ = C*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(a-r) := by
          rw [show a-r=(-r)+a by ring,Real.rpow_add hN]
          ring
        _ ≤ _ := by
          have hb := ProbeSelectedPrimeSums.annular_rpow 1 2 U
            ((Ideal.span {u.val}:Ideal O).absNorm:ℝ) (a-r) (by norm_num) (by norm_num) hU0
            (by simpa only [one_mul] using (hR u hu).1) (hR u hu).2
          simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC
    _ = (R.card:ℝ)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) := by simp
    _ ≤ (256*U)*(C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r)*U^(a-r)) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      have hp : U*U^(a-r)=U^(1+a-r) := by
        rw [show 1+a-r=1+(a-r) by ring,Real.rpow_add hU0,Real.rpow_one]
      calc
        _ = (256*C*ProbeSelectedPrimeSums.annularPower 1 2 (a-r))*(U*U^(a-r)) := by ring
        _ = _ := by rw [hp]

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2574

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.DyadBound
Source SHA256: 81b842b0d0093f234df611c3eb99b306abeda9284631469a3d9f1fdc7f308cf9
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2575


namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physical_row_dyad (K : ℕ) (e δ a b r B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (U : ℝ),1≤U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Set.Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀(x w z : ℂ),(7/8:ℝ)≤x.re → HeckeZeroSupremum.beta+8*e≤x.re →
      (1/2:ℝ)≤w.re → z.re=r →
      (∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)≤
      C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*
        (∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2 := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_tuple_sum K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  let A : ℝ := ProbeSelectedPrimeSums.annularPower 1 2 (3/5+δ-r)
  have hA : 0<A := by
    have hh := le_max_left ((1:ℝ)^(3/5+δ-r)) ((2:ℝ)^(3/5+δ-r))
    rw [Real.one_rpow] at hh
    simpa only [A,ProbeSelectedPrimeSums.annularPower,Real.one_rpow] using (lt_of_lt_of_le zero_lt_one hh)
  refine ⟨256*C*A,by positivity,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
  let F : FreeRow→ℝ := fun u=>∑P:(∀i,T i),‖calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
    (fun i=>hT i (P i).val (P i).property) W Y x w z‖
  let D : ℝ := C*(η.modulus.absNorm:ℝ)^δ*(∏i,(Y i)^r)*(3+|x.im|)^2*(3+|w.im|)^2
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  have hD : 0≤D := by dsimp [D];positivity
  have hF (u : FreeRow) (hu : u∈R) : F u≤D*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(3/5+δ) := by
    have hh := hmain η u (hR u hu).1 T hT hdis Y hY W hWS hWB x w z hx hxβ hw hz
    apply hh.trans_eq
    dsimp [D]
    ring
  have heq (u : FreeRow) :
      (∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
          (fun i=>hT i (P i).val (P i).property) W Y x w z‖)=
      ‖frequencyWeight z ⟨u.val,u.property.1⟩‖*F u := by
    simp only [norm_mul,Finset.mul_sum,F]
  simp_rw [heq]
  apply (dyadic_weighted_rows (3/5+δ) r D U hD hU R (fun u hu=>(hR u hu).2) F hF z hz).trans_eq
  change 256*D*A*U^(1+(3/5+δ)-r)=_
  rw [show (1:ℝ)+(3/5+δ)-r=8/5+δ-r by ring]
  dsimp [D]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2575

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.DyadIntegral
Source SHA256: 813f970ca57208cfcfb20ce5c4a2ff5db8da3b96b719bcea3741976cf3796be4
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2576




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def physicalDyadNorm {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) : ℝ :=
  ∑u∈R,∑P:(∀i,T i),‖frequencyWeight z ⟨u.val,u.property.1⟩*
    calibratedTupleValue S hS hmax η u (fun i=>(P i).val)
      (fun i=>hT i (P i).val (P i).property) W Y x w z‖

lemma physicalDyadNorm_nonneg {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (η : Character) (R : Finset FreeRow)
    (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S)
    (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ) (x w z : ℂ) :
    0≤physicalDyadNorm S hS hmax η R T hT W Y x w z := by
  exact Finset.sum_nonneg fun u hu=>Finset.sum_nonneg fun P hP=>norm_nonneg _

lemma physicalDyadNorm_onLines_aestronglyMeasurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (σ υ r : ℝ) : AEStronglyMeasurable (fun p : HeightSpace=>physicalDyadNorm S hS hmax η R T hT W Y
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  unfold physicalDyadNorm
  simp_rw [norm_mul,frequencyWeight_ideal_norm]
  simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,Complex.I_im,
    Complex.ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
  convert Finset.aestronglyMeasurable_sum R (fun u hu=>
    Finset.aestronglyMeasurable_sum (Finset.univ : Finset (∀i,T i)) (fun P hP=>
      (calibratedTupleValue_onLines_aestronglyMeasurable S hS hmax η u
        (fun i=>(P i).val) (fun i=>hT i (P i).val (P i).property) W Y σ υ r heightMeasure).norm.const_mul
          (((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^(-r)))) using 1
  ext p
  simp only [Finset.sum_apply]

theorem calibrated_physical_dyad_integral (K : ℕ) (e δ a b r B σ υ : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1)
    (ha : 0<a) (hb : 0<b) (hr : (17/50:ℝ)≤r) (hB : 0≤B)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hυ : (1/2:ℝ)≤υ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (U : ℝ),1≤U → ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀(Y : Fin K→ℝ), (∀i,1≤Y i) → ∀(W : Fin K→ℝ→ℂ),
      (∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      ∀X Y0 Z : ℝ,0<X → 0<Y0 → 0<Z →
      Integrable (fun p : HeightSpace=>‖sourceMellinWeight W0 W1 X Y0 Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
          physicalDyadNorm S hS hmax η R T hT W Y
            ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure ∧
      (∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y0 Z
        ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
          physicalDyadNorm S hS hmax η R T hT W Y
            ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure)
      ≤C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*(∏i,(Y i)^r)*
        (X^(1/2-r)*Z^(σ+r-1)*Y0^(υ-1)) := by
  obtain ⟨C,hC,hD⟩ := calibrated_physical_row_dyad K e δ a b r B he he' hδ hδ' ha hb hr hB S hS hmax hfirst
  obtain ⟨D,hDp,hP⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r υ υ (by linarith)
  refine ⟨D*C,mul_pos hDp hC,?_⟩
  intro η U hU R hR T hT hdis Y hY W hWS hWB X Y0 Z hX hY0 hZ
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-r)*(∏i,(Y i)^r)
  have hYP : 0≤∏i,(Y i)^r := Finset.prod_nonneg fun i _=>Real.rpow_nonneg (by linarith [hY i]) _
  have hA : 0≤A := by dsimp [A];positivity
  have hbnd (p : HeightSpace) : physicalDyadNorm S hS hmax η R T hT W Y
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)
      ≤A*(3+|p.1.1|)^2*(3+|p.2|)^2 := by
    have hh := hD η U hU R hR T hT hdis Y hY W hWS hWB
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)
      (by simpa using hσ) (by simpa using hσβ) (by simpa using hυ) (by simp)
    simpa only [A,physicalDyadNorm,Complex.add_im,Complex.ofReal_im,Complex.mul_im,Complex.I_re,
      Complex.I_im,Complex.ofReal_re,mul_one,mul_zero,add_zero,zero_add] using hh
  obtain ⟨hi,hb⟩ := hP σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y0 Z hX hY0 hZ A hA _
    (physicalDyadNorm_onLines_aestronglyMeasurable S hS hmax η R T hT W Y σ υ r)
    (fun p=>physicalDyadNorm_nonneg S hS hmax η R T hT W Y _ _ _) hbnd
  refine ⟨hi,hb.trans_eq ?_⟩
  dsimp [A]
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2576

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FixedIntegral
Source SHA256: 345ec3d3284527e39d090318c926a3f80962dae953b4cc1fb7da0d198a7f3565
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2577



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma continuedPhysicalRowKernel_eq_calibratedTuple {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (hW : ∀i,W i (((P i).val.absNorm:ℝ)/Yp i)=1) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      sourceMellinWeight W0 W1 X Y Z x w z*frequencyWeight z ⟨u.val,u.property.1⟩*
        calibratedTupleValue S hS hmax η u P hPS W Yp x w z := by
  have hnorm (i : Fin K) : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)=
      (Ideal.absNorm (P i).val:ℂ) := by
    rw [primaryTuple_norm (P i) (outside_prime_supported S hS.bad (P i) (hPS i))]
    norm_cast
  unfold continuedPhysicalRowKernel calibratedTupleValue
  simp only [hW,one_mul,hnorm]
  ring

theorem continuedPhysicalRowKernel_integrable {K : ℕ}
    (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (fun p : HeightSpace=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
  let W : Fin K→ℝ→ℂ := fun _ y=>if y=1 then 1 else 0
  let Yp : Fin K→ℝ := fun i=>(P i).val.absNorm
  let T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal := fun i=>{P i}
  have hT (i : Fin K) (Q : _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hQ : Q∈T i) : Q.val∉S := by
    have heq : Q=P i := Finset.mem_singleton.mp hQ
    simpa only [heq] using hPS i
  let P0 : ∀i,T i := fun i=>⟨P i,Finset.mem_singleton_self _⟩
  have hTP (Q : ∀i,T i) : (fun i=>(Q i).val)=P := by
    funext i
    exact Finset.mem_singleton.mp (Q i).property
  have hdis (Q : ∀i,T i) : Function.Injective (fun i=>(Q i).val) := by rw [hTP Q];exact hP
  have hYp (i : Fin K) : 1≤Yp i := by
    dsimp [Yp]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr (P i).property.ne_zero)
  have hWS (i : Fin K) : Function.support (W i)⊆Icc (1:ℝ) 1 := by
    intro y hy
    by_cases h : y=1
    · simpa only [h] using (show (1:ℝ)∈Icc 1 1 from ⟨le_rfl,le_rfl⟩)
    · simp [W,h,Function.mem_support] at hy
  have hWB (i : Fin K) (y : ℝ) : ‖W i y‖≤1 := by dsimp [W];split_ifs <;> simp
  have hWeq (i : Fin K) : W i (((P i).val.absNorm:ℝ)/Yp i)=1 := by
    have hn : Yp i≠0 := by linarith [hYp i]
    simp [W,Yp,div_self hn]
  let U : ℝ := (Ideal.span {u.val}:Ideal O).absNorm
  have hU : 1≤U := by
    dsimp [U]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr u.property.1))
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e (1/2) 1 1 r 1 σ υ he he'
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hr (by norm_num) hσ hσβ hυ
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hR (v : FreeRow) (hv : v∈({u}:Finset FreeRow)) :
      v.val≠1 ∧ U≤((Ideal.span {v.val}:Ideal O).absNorm:ℝ) ∧
      ((Ideal.span {v.val}:Ideal O).absNorm:ℝ)≤2*U := by
    have hvu := Finset.mem_singleton.mp hv
    subst v
    exact ⟨hu,le_rfl,by change U≤2*U;linarith⟩
  have hi := (hmain η U hU {u} hR T hT hdis Yp hYp W hWS hWB X Y Z hX hY hZ).1
  have hm := calibratedTupleValue_onLines_aestronglyMeasurable S hS hmax η u P hPS W Yp σ υ r heightMeasure
  have hfn : (elementNorm u.val:ℂ)≠0 := by
    exact_mod_cast (elementNorm_pos u.val u.property.1).ne'
  have hf : Continuous (fun p : HeightSpace=>frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩) := by
    unfold frequencyWeight
    exact (by fun_prop : Continuous (fun p : HeightSpace=>-((r:ℂ)+p.1.2*Complex.I))).const_cpow (Or.inl hfn)
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r υ (by linarith)
  have hme : AEStronglyMeasurable (fun p : HeightSpace=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
      ((σ:ℂ)+p.1.1*Complex.I) ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)) heightMeasure := by
    simp_rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
    exact (hs.mul hf).aestronglyMeasurable.mul hm
  apply hi.mono' hme
  apply Filter.Eventually.of_forall
  intro p
  rw [continuedPhysicalRowKernel_eq_calibratedTuple S hS hmax P hPS η u W0 W1 X Y Z W Yp hWeq]
  rw [mul_assoc,norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  dsimp only [physicalDyadNorm]
  rw [Finset.sum_singleton]
  have hh := Finset.single_le_sum (fun Q (_ : Q∈(Finset.univ:Finset (∀i,T i)))=>norm_nonneg
    (frequencyWeight ((r:ℂ)+p.1.2*Complex.I) ⟨u.val,u.property.1⟩*
      calibratedTupleValue S hS hmax η u (fun i=>(Q i).val)
        (fun i=>hT i (Q i).val (Q i).property) W Yp ((σ:ℂ)+p.1.1*Complex.I)
          ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I))) (Finset.mem_univ P0)
  exact hh

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2577

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.TailScales
Source SHA256: e258f07cfcb71b950e26731c0bb01047d538f069a29dc51ffff5b9ddd41c9a77
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2578


namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma selected_scale_power {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ) (r : ℝ) :
    (∏i,(Z^(length i))^r)=Z^((∑i,length i)*r) := by
  simp_rw [←Real.rpow_mul hZ.le]
  rw [Finset.sum_mul,Real.rpow_sum_of_pos hZ]

lemma physical_scale_power {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (lx ly σ υ r : ℝ) :
    (∏i,(Z^(length i))^r)*((Z^lx)^(1/2-r)*Z^(σ+r-1)*(Z^ly)^(υ-1))=
      Z^(σ-1+lx/2+ly*(υ-1)+(1-lx+∑i,length i)*r) := by
  rw [selected_scale_power Z hZ]
  simp_rw [←Real.rpow_mul hZ.le]
  rw [←Real.rpow_add hZ,←Real.rpow_add hZ,←Real.rpow_add hZ]
  congr 1
  ring

lemma small_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(1/6:ℝ)) (β e : ℝ) :
    (∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(23/48:ℝ))^((1/2:ℝ)-1))=Z^(β-11/16-79/800+8*e) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

lemma small_row_scale_bound {K : ℕ} (Z U δ : ℝ) (hZ : 1≤Z) (hU : 1≤U)
    (hUsmall : U≤Z^(1/100:ℝ)) (_hδ : 0≤δ) (hδ' : δ≤1/2)
    (length : Fin K→ℝ) (hlength : ∑i,length i=(1/6:ℝ)) (β e : ℝ) :
    U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
      ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(β+8*e+(17/50:ℝ)-1)*
        (Z^(23/48:ℝ))^((1/2:ℝ)-1))≤Z^(β-11/16-63/800+8*e) := by
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hrow : U^(8/5+δ-(17/50:ℝ))≤Z^(1/50:ℝ) := by
    calc
      _ ≤ U^(2:ℝ) := Real.rpow_le_rpow_of_exponent_le hU (by linarith)
      _ ≤ (Z^(1/100:ℝ))^(2:ℝ) := Real.rpow_le_rpow (by linarith) hUsmall (by norm_num)
      _ = _ := by rw [←Real.rpow_mul hZ0.le];norm_num
  rw [mul_assoc,small_source_scale Z hZ0 length hlength β e]
  calc
    _ ≤ Z^(1/50:ℝ)*Z^(β-11/16-79/800+8*e) :=
      mul_le_mul_of_nonneg_right hrow (Real.rpow_nonneg hZ0.le _)
    _ = _ := by rw [←Real.rpow_add hZ0];congr 1;ring

lemma large_source_scale {K : ℕ} (Z : ℝ) (hZ : 0<Z) (length : Fin K→ℝ)
    (hlength : ∑i,length i=(1/6:ℝ)) (b : ℝ) :
    (∏i,(Z^(length i))^b)*
      ((Z^(17/48:ℝ))^(1/2-b)*Z^(2+b-1)*(Z^(23/48:ℝ))^((2:ℝ)-1))=
      Z^((53/32:ℝ)+(13/16:ℝ)*b) := by
  rw [physical_scale_power Z hZ,hlength]
  congr 1
  ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2578

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SmallDyad
Source SHA256: f6ef3f77b2965fa1ae431a55f1d83cafd05741de50a5deb90602a4de859e9774
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2579


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def absolutePhysicalDyadIntegral {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) : ℝ :=
  ∫p : HeightSpace,‖sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+p.1.1*Complex.I)
    ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I)‖*
      physicalDyadNorm S hS hmax η R T hT W Yp ((σ:ℂ)+p.1.1*Complex.I)
        ((υ:ℂ)+p.2*Complex.I) ((r:ℂ)+p.1.2*Complex.I) ∂heightMeasure

theorem small_physical_dyad_bound (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z U : ℝ),1≤Z → 1≤U → U≤Z^(1/100:ℝ) →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) le_rfl le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU hUsmall R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=>Z^(length i)) hYp W hWS hWB
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  have hscale := small_row_scale_bound Z U δ hZ hU hUsmall hδ.le hδ' length hl HeckeZeroSupremum.beta e
  calc
    _ ≤ C*(η.modulus.absNorm:ℝ)^δ*U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(23/48:ℝ))^((1/2:ℝ)-1)) := hh
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*(U^(8/5+δ-(17/50:ℝ))*(∏i,(Z^(length i))^(17/50:ℝ))*
        ((Z^(17/48:ℝ))^(1/2-(17/50:ℝ))*Z^(HeckeZeroSupremum.beta+8*e+(17/50:ℝ)-1)*
          (Z^(23/48:ℝ))^((1/2:ℝ)-1))) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hscale (by positivity)

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2579

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.LargeDyad
Source SHA256: 8a753acac47d841f8a4384700c235975d345127e9db652699b7dddd8db06ecc8
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2580


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_dyad_bound (K : ℕ) (δ a b B r : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z U : ℝ),1≤Z → 1≤U →
      ∀R : Finset FreeRow,
      (∀u∈R,u.val≠1 ∧ U≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*U) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      absolutePhysicalDyadIntegral S hS hmax η R T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((53/32:ℝ)+(13/16:ℝ)*r)*U^(8/5+δ-r) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K (1/2000) δ a b r B
    2 2 (by norm_num) (by norm_num) hδ hδ' ha hb hr hB
    (by norm_num) (by linarith [HeckeZeroSupremum.beta_le_one]) (by norm_num)
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨C,hC,?_⟩
  intro η Z U hZ hU R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  have hh := (hmain η U hU R hR T hT hdis (fun i=>Z^(length i)) hYp W hWS hWB
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
  apply hh.trans_eq
  calc
    _ = (C*(η.modulus.absNorm:ℝ)^δ)*U^(8/5+δ-r)*
      ((∏i,(Z^(length i))^r)*((Z^(17/48:ℝ))^(1/2-r)*Z^(2+r-1)*(Z^(23/48:ℝ))^((2:ℝ)-1))) := by ring
    _ = _ := by rw [large_source_scale Z hZ0 length hl r];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2580

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.GeometricTail
Source SHA256: 3caefc28bd867d4bc33df8add72f28925e4ea50eb258d0119c095387baa00431
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2581


namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma large_geometric_scale (Z ζ δ r : ℝ) (hZ : 0<Z) (n : ℕ) :
    Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)=
      Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r)*((2:ℝ)^(8/5+δ-r))^n := by
  rw [Real.mul_rpow (Real.rpow_nonneg hZ.le _) (by positivity),←Real.rpow_mul hZ.le]
  rw [←Real.rpow_natCast_mul (by norm_num : (0:ℝ)≤2),mul_comm (n:ℝ),
    Real.rpow_mul_natCast (by norm_num : (0:ℝ)≤2)]
  rw [←mul_assoc,←Real.rpow_add hZ]
  congr 2
  ring

lemma large_geometric_summable (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    Summable (fun n : ℕ=>Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)) := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  exact (summable_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))).mul_left _

lemma large_geometric_sum (Z ζ δ r : ℝ) (hZ : 0<Z) (hr : 8/5+δ<r) :
    (∑'n : ℕ,Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r))=
      Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹ := by
  simp_rw [large_geometric_scale Z ζ δ r hZ]
  rw [tsum_mul_left,tsum_geometric_of_lt_one (Real.rpow_nonneg (by norm_num : (0:ℝ)≤2) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith))]

lemma exists_large_tail_line (ζ δ saving : ℝ) (hζ : 0<ζ) :
    ∃r : ℝ,(17/50:ℝ)≤r ∧ 8/5+δ<r ∧
      (53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r≤-saving := by
  obtain ⟨r,hr⟩ := exists_gt (max (17/50:ℝ) (max (8/5+δ)
    (((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)+saving)/ζ)))
  have h1 := (le_max_left (17/50:ℝ) _).trans_lt hr
  have h2 := (le_trans (le_max_left (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  have h3 := (le_trans (le_max_right (8/5+δ) _) (le_max_right (17/50:ℝ) _)).trans_lt hr
  refine ⟨r,h1.le,h2,?_⟩
  have hh := (div_lt_iff₀ hζ).mp h3
  nlinarith

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2581

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.LargeTail
Source SHA256: 5fbd7074e634e4ec97f57bc563d01a376b03422f1990fc79c603f1b8ca41ad3b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2582


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma absolutePhysicalDyadIntegral_nonneg {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hT : ∀i P,P∈T i→P.val∉S) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) :
    0≤absolutePhysicalDyadIntegral S hS hmax η R T hT W Yp W0 W1 X Y Z σ υ r := by
  apply integral_nonneg
  intro p
  exact mul_nonneg (norm_nonneg _) (physicalDyadNorm_nonneg S hS hmax η R T hT W Yp _ _ _)

theorem large_physical_dyads_summable (K : ℕ) (δ a b B r ζ : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hr : (17/50:ℝ)≤r) (hr' : 8/5+δ<r) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r) := by
  obtain ⟨C,hC,hmain⟩ := large_physical_dyad_bound K δ a b B r hδ hδ' hr ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  have hq : (2:ℝ)^(8/5+δ-r)<1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  refine ⟨C*(1-(2:ℝ)^(8/5+δ-r))⁻¹,mul_pos hC (inv_pos.mpr (sub_pos.mpr hq)),?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  let f : ℕ→ℝ := fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
    (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r
  let g : ℕ→ℝ := fun n=>Z^((53/32:ℝ)+(13/16:ℝ)*r)*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)^(8/5+δ-r)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ
  have hf0 (n : ℕ) : 0≤f n := absolutePhysicalDyadIntegral_nonneg S hS hmax η (R n) T hT W _ W0 W1 _ _ _ _ _ _
  have hbnd (n : ℕ) : f n≤A*g n := by
    have hUn : 1≤Z^((13/16:ℝ)+ζ)*(2:ℝ)^n :=
      one_le_mul_of_one_le_of_one_le (Real.one_le_rpow hZ (by linarith)) (one_le_pow₀ (by norm_num))
    have hh := hmain η Z (Z^((13/16:ℝ)+ζ)*(2:ℝ)^n) hZ hUn (R n) (hR n) T hT hdis length hl0 hl W hWS hWB
    simpa only [A,g,mul_assoc] using hh
  have hg : Summable g := large_geometric_summable Z ζ δ r hZ0 hr'
  have hf : Summable f := Summable.of_nonneg_of_le hf0 hbnd (hg.mul_left A)
  refine ⟨hf,?_⟩
  calc
    (∑'n,f n) ≤ ∑'n,A*g n := hf.tsum_le_tsum hbnd (hg.mul_left A)
    _ = A*(∑'n,g n) := tsum_mul_left
    _ = A*(Z^((53/32:ℝ)+((13/16:ℝ)+ζ)*(8/5+δ)-ζ*r)*(1-(2:ℝ)^(8/5+δ-r))⁻¹) := by
      rw [show (∑'n,g n)=_ from large_geometric_sum Z ζ δ r hZ0 hr']
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2582

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.LargeSaving
Source SHA256: b0adff82c5486cda19a659a8dacc3f11fb823ce8fddc1c3c963c8b2e56cd4cfc
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2583


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem large_physical_tail_arbitrary_saving (K : ℕ) (δ a b B ζ saving : ℝ)
    (hδ : 0<δ) (hδ' : δ≤1) (hζ : 0<ζ)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃r C : ℝ,(17/50:ℝ)≤r ∧ 0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀R : ℕ→Finset FreeRow,
      (∀n u,u∈R n → u.val≠1 ∧ Z^((13/16:ℝ)+ζ)*(2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(Z^((13/16:ℝ)+ζ)*(2:ℝ)^n)) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      Summable (fun n=>absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r) ∧
      (∑'n,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z 2 2 r)
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(-saving) := by
  obtain ⟨r,hr,hr',hpower⟩ := exists_large_tail_line ζ δ saving hζ
  obtain ⟨C,hC,hmain⟩ := large_physical_dyads_summable K δ a b B r ζ hδ hδ' hr hr' hζ ha hb hB
    S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  refine ⟨r,C,hr,hC,?_⟩
  intro η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  obtain ⟨hs,hb⟩ := hmain η Z hZ R hR T hT hdis length hl0 hl W hWS hWB
  refine ⟨hs,hb.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ hpower) (by positivity)

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2583

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SmallSum
Source SHA256: 3d4e2508b16059f13f430eee8bab2cb20af6dc66defe764c018ecd0994178f2b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2584


namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily

lemma small_dyadic_square_sum : ∃C : ℝ,0<C ∧ ∀H : ℝ,0<H → ∀F : Finset ℕ,
    (∀n∈F,(2:ℝ)^n≤H) → (∑n∈F,((2:ℝ)^n)^(2:ℝ))≤C*H^(2:ℝ) := by
  obtain ⟨C,hC,hmain⟩ := CompletedDyadic.kernel_sum_bound 2 3 (by norm_num) (by norm_num)
  refine ⟨8*C,by positivity,?_⟩
  intro H hH F hF
  obtain ⟨hs,hb⟩ := hmain H⁻¹ (inv_pos.mpr hH)
  have hpoint (n : ℕ) (hn : n∈F) : ((2:ℝ)^n)^(2:ℝ)≤8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := by
    have hd : 0<1+H⁻¹*(2:ℝ)^n := by positivity
    have hu : H⁻¹*(2:ℝ)^n≤1 := by
      rw [mul_comm,←div_eq_mul_inv]
      exact (div_le_one hH).mpr (hF n hn)
    have hh : (1+H⁻¹*(2:ℝ)^n)^3≤(2:ℝ)^3 := pow_le_pow_left₀ hd.le (by linarith) 3
    unfold CompletedDyadic.kernelTerm
    norm_num only [Real.rpow_natCast,Real.rpow_ofNat]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (pow_pos hd 3)).mpr
    have hm := mul_le_mul_of_nonneg_left hh (sq_nonneg ((2:ℝ)^n))
    norm_num at hm
    nlinarith only [hm]
  calc
    _ ≤ ∑n∈F,8*CompletedDyadic.kernelTerm H⁻¹ 2 3 n := Finset.sum_le_sum hpoint
    _ = 8*∑n∈F,CompletedDyadic.kernelTerm H⁻¹ 2 3 n := (Finset.mul_sum _ _ _).symm
    _ ≤ 8*∑'n,CompletedDyadic.kernelTerm H⁻¹ 2 3 n :=
      mul_le_mul_of_nonneg_left (hs.sum_le_tsum F (fun n _=>by unfold CompletedDyadic.kernelTerm;positivity)) (by norm_num)
    _ ≤ 8*(C*(H⁻¹)^(-2:ℝ)) := mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by rw [Real.inv_rpow hH.le,Real.rpow_neg hH.le,inv_inv];ring

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2584

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SmallTail
Source SHA256: 98965e184ea007bfe1a3e36e544a2d783c005e61ba2989d7ea5110c190777c47
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2585


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem small_physical_dyads_sum (K : ℕ) (e δ a b B : ℝ)
    (he : 0<e) (he' : e<1/1000) (hδ : 0<δ) (hδ' : δ≤1/2)
    (ha : 0<a) (hb : 0<b) (hB : 0≤B) (hβ : (7/8:ℝ)≤HeckeZeroSupremum.beta)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1) :
    ∃C : ℝ,0<C ∧ ∀(η : Character) (Z : ℝ),1≤Z → ∀F : Finset ℕ,
      (∀n∈F,(2:ℝ)^n≤Z^(1/100:ℝ)) → ∀R : ℕ→Finset FreeRow,
      (∀n∈F,∀u∈R n,u.val≠1 ∧ (2:ℝ)^n≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ) ∧
        ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)≤2*(2:ℝ)^n) →
      ∀(T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀i P,P∈T i→P.val∉S),
      (∀P:(∀i,T i),Function.Injective (fun i=>(P i).val)) →
      ∀length : Fin K→ℝ,(∀i,0≤length i) → (∑i,length i)=(1/6:ℝ) →
      ∀W : Fin K→ℝ→ℂ,(∀i,Function.support (W i)⊆Icc a b) → (∀i y,‖W i y‖≤B) →
      (∑n∈F,absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50))
      ≤C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
  obtain ⟨C,hC,hmain⟩ := calibrated_physical_dyad_integral K e δ a b (17/50) B
    (HeckeZeroSupremum.beta+8*e) (1/2) he he' hδ (by linarith) ha hb le_rfl hB
    (by linarith) le_rfl le_rfl S hS hmax hfirst W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
  obtain ⟨D,hD,hsmall⟩ := small_dyadic_square_sum
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro η Z hZ F hF R hR T hT hdis length hl0 hl W hWS hWB
  have hZ0 : 0<Z := lt_of_lt_of_le zero_lt_one hZ
  have hYp (i : Fin K) : 1≤Z^(length i) := Real.one_le_rpow hZ (hl0 i)
  let A : ℝ := C*(η.modulus.absNorm:ℝ)^δ*Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)
  have hA : 0≤A := by dsimp [A];positivity
  have hbnd (n : ℕ) (hn : n∈F) :
      absolutePhysicalDyadIntegral S hS hmax η (R n) T hT W (fun i=>Z^(length i)) W0 W1
        (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z (HeckeZeroSupremum.beta+8*e) (1/2) (17/50)
      ≤A*((2:ℝ)^n)^(2:ℝ) := by
    have hUn : 1≤(2:ℝ)^n := one_le_pow₀ (by norm_num)
    have hh := (hmain η ((2:ℝ)^n) hUn (R n) (hR n hn) T hT hdis (fun i=>Z^(length i)) hYp
      W hWS hWB (Z^(17/48:ℝ)) (Z^(23/48:ℝ)) Z
      (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0).2
    have hpow : ((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))≤((2:ℝ)^n)^(2:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hUn (by linarith)
    have hscale := small_source_scale Z hZ0 length hl HeckeZeroSupremum.beta e
    calc
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(8/5+δ-(17/50:ℝ))*
          Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e) := by
        apply hh.trans_eq
        rw [←hscale]
        ring
      _ ≤ (C*(η.modulus.absNorm:ℝ)^δ)*((2:ℝ)^n)^(2:ℝ)*
          Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e) := by gcongr
      _ = _ := by dsimp [A];ring
  calc
    _ ≤ ∑n∈F,A*((2:ℝ)^n)^(2:ℝ) := Finset.sum_le_sum hbnd
    _ = A*∑n∈F,((2:ℝ)^n)^(2:ℝ) := (Finset.mul_sum _ _ _).symm
    _ ≤ A*(D*(Z^(1/100:ℝ))^(2:ℝ)) := mul_le_mul_of_nonneg_left
      (hsmall (Z^(1/100:ℝ)) (Real.rpow_pos_of_pos hZ0 _) F hF) hA
    _ = _ := by
      dsimp [A]
      rw [←Real.rpow_mul hZ0.le]
      have he : Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)*Z^((1/100:ℝ)*2)=
          Z^(HeckeZeroSupremum.beta-11/16-63/800+8*e) := by
        rw [←Real.rpow_add hZ0]
        congr 1
        ring
      calc
        _ = (C*D)*(η.modulus.absNorm:ℝ)^δ*
            (Z^(HeckeZeroSupremum.beta-11/16-79/800+8*e)*Z^((1/100:ℝ)*2)) := by ring
        _ = _ := by rw [he]

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2585

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.WGrowth
Source SHA256: b99a91255d91df65c98c20d0f35405ecae8b94348dc6ee875d91c8007a4fb00b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2586



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem calibrated_physicalRow_w_growth (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+1/2) :
    ∃C : ℝ,0<C ∧ ∀w : ℂ,(1/2:ℝ)≤w.re →
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|w.im|)^2 := by
  obtain ⟨Cn,hCn,hn⟩ := calibrated_numerator_positive_growth (1/2) 1 (by norm_num) (by norm_num) S hS hmax
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>961*((P.val.val.absNorm:ℝ)^(1/2:ℝ)+1)
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  let C : ℝ := L*(Cn*N^(3/5+1:ℝ))*(Ch*N)*∏P:T,A P
  have hC : 0≤C := by dsimp [C,L,A,N];positivity
  refine ⟨1+C,by linarith,?_⟩
  intro w hw
  have hn' := hn u hu w hw
  have hh' := hh eps S hS hfirst T η u x w z (by linarith) (by linarith) hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    change (∏P:T,‖continuedCompensatedLocal η u P.val _ x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖)≤_
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P _
    have hQ : (4:ℝ)≤P.val.val.absNorm := by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)
    apply (continuedCompensatedLocal_bound η u P.val _ hQ x w z hx hw hz).trans
    dsimp [A]
    by_cases hp : P.val.val∣Ideal.span {u.val}
    · rw [ite_eq_left hp]
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply (Real.rpow_le_rpow_of_exponent_le (by linarith : (1:ℝ)≤P.val.val.absNorm)
        (max_le (by linarith) (by norm_num) : max (1-w.re) 0≤(1/2:ℝ))).trans
      linarith
    · rw [ite_eq_right hp]
      have hnq := Real.rpow_nonneg (show (0:ℝ)≤P.val.val.absNorm by positivity) (1/2:ℝ)
      nlinarith
  have he : star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS T hT η u x w z=
      (LFunction (fixedSourcePrincipal S hS.prime) (6*z)*
        HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x)*
      (star ((calibrationForSet S hmax).residueMonoid u.val)*
        HeckeOrigin.continued (rowCharacter S hS.prime u) w)*
      continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z*
      ∏P∈T.attach,continuedCompensatedLocal η u P.val
        (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
        (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
        ((P.val.val.absNorm:ℂ)^(-w)) := by
    unfold physicalCompensatedRow continuedCompensatedRow
    ring
  rw [he,norm_mul,norm_mul,norm_mul]
  have hh'' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh'
  have hn'' : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      HeckeOrigin.continued (rowCharacter S hS.prime u) w‖≤Cn*N^(3/5+1:ℝ)*(3+|w.im|)^2 := hn'
  calc
    _ ≤ L*(Cn*N^(3/5+1:ℝ)*(3+|w.im|)^2)*(Ch*N)*(∏P:T,A P) := by
      rw [norm_mul]
      apply mul_le_mul _ hg (norm_nonneg _) (by dsimp [L,N];positivity)
      apply mul_le_mul _ hh'' (norm_nonneg _) (by dsimp [L,N];positivity)
      exact mul_le_mul_of_nonneg_left hn'' (by positivity)
    _ = C*(3+|w.im|)^2 := by dsimp [C];ring
    _ ≤ (1+C)*(3+|w.im|)^2 := mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

end SevenEighths.ProbeHighRowFamily
end

end OAI
end OAIOriginalModule2586

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.NonprincipalShift
Source SHA256: 8433aa87f7d881aa8c7526ecf384c8efd689c539eb48b5e8571c030292840db5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2587



namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma physicalRow_w_height_bound {K : ℕ} (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (x z : ℂ)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1+eps≤x.re+1/2) :
    ∃C : ℝ,0<C ∧ ∀v : ℝ,(1/2:ℝ)≤v → ∀t : ℝ,
      ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
        physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x ((v:ℂ)+t*I) z‖≤
          C*height t^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_w_growth (eps/2) S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu x z hx hz (by linarith)
  refine ⟨9*C,by positivity,?_⟩
  intro v hv t
  have hb := hbound ((v:ℂ)+t*I) (by simpa using hv)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,mul_one,I_re,mul_zero,add_zero,zero_add] at hb
  apply hb.trans
  have h3 : (3+|t|)^2≤9*(height t)^2 := by
    unfold height
    nlinarith [abs_nonneg t]
  nlinarith

theorem nonprincipal_w_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W1⊆Icc a b)
    (X Y Z : ℝ) (hY : 0<Y) (x z : ℂ) (l r : ℝ) (hlr : l≤r) (hl : (1/2:ℝ)≤l)
    (hx : (7/8:ℝ)≤x.re) (hz : (17/50:ℝ)≤z.re) (hxw : 1+eps≤x.re+1/2) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((l:ℂ)+t*I) z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x ((r:ℂ)+t*I) z := by
  obtain ⟨C,hC,hbound⟩ := physicalRow_w_height_bound eps heps S hS hfirst hmax P hPS η u hu x z hx hz hxw
  exact nonprincipal_w_integral_eq_of_polynomial eps heps S hS hfirst hmax P hPS η u hu
    W0 W1 a b ha hW X Y Z hY x z l r C 2 hC.le hlr (by linarith) (by linarith)
    hz (by linarith) (fun v hv t=>hbound v (hl.trans hv.1) t)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2587

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.IteratedShift
Source SHA256: 371662e87dde8c703bbe52681c23aa30ef1a9683fb43fd4a8010f206fc8faa20
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2588



namespace OAI

noncomputable section
open scoped Classical
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
local instance : Countable O := ActualEisensteinCubic.latticeCoordEquiv.injective.countable
local instance : MeasurableSpace FreeRow := ⊤
local instance : MeasurableSingletonClass FreeRow := ⟨fun _=>trivial⟩

def shiftedRowInner {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z l : ℝ) (q : ℝ×ℝ) : ℂ :=
  ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((3:ℂ)+q.1*I) ((l:ℂ)+t*I) ((2:ℂ)+q.2*I)

theorem rowIntegral_w_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (heps' : eps≤5/2)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (l : ℝ) (hl : (1/2:ℝ)≤l) (hl3 : l≤3) :
    Integrable (shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l) (volume.prod volume) ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q ∂(volume.prod volume) := by
  let p : Fin K→O := fun i=>CompletedGauss.primaryGenerator (P i).val
  have hp : ∀i,p i≠0 := fun i=>(supported_primeGenerator_prime (P i)
    (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  let e : FreeRow→NonzeroFrequency := fun u=>⟨u.val,u.property.1⟩
  have he : Function.Injective e := fun a b h=>Subtype.ext (congrArg (fun v : NonzeroFrequency=>v.val) h)
  have hF := compensatedRows_counting_product_integrable e he η S (calibrationForSet S hmax) p hp
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hi : Integrable (compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u))
      heightMeasure := (Measure.ae_count_iff.mp hF.prod_right_ae) u
  have heq (q : ℝ×ℝ) :
      (∫t : ℝ,compensatedRowOnLines η S (calibrationForSet S hmax) p W0 W1 X Y Z (e u) (q,t))=
        shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z l q := by
    have hs := nonprincipal_w_integral_eq eps heps S hS hfirst hmax P hPS η u hu W0 W1
      a1 b1 ha1 hW1 X Y Z hY ((3:ℂ)+q.1*I) ((2:ℂ)+q.2*I) l 3 hl3 hl
      (by norm_num) (by norm_num) (by norm_num;linarith)
    unfold shiftedRowInner
    rw [hs]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t=>(continuedPhysicalRowKernel_initial S hS hmax P hP hPS
      η u W0 W1 X Y Z (q,t)).symm)
  refine ⟨?_,?_⟩
  · exact hi.integral_prod_left.congr (Filter.Eventually.of_forall heq)
  · unfold rowIntegral
    rw [integral_prod _ hi]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall heq)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2588

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ZContour
Source SHA256: 56a0bcff4293a99e7bb8ebd3892a73600adbc300dee1f9100b34ec6adcc9189a
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2589


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

lemma physicalCompensatedRow_first_z (eps : ℝ) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S) (η : Character) (u : FreeRow)
    (x w z : ℂ) (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>physicalCompensatedRow S hS T hT η u x w z) z := by
  have hz0 : 6*z≠0 := by intro h;have hh:=congrArg Complex.re h;norm_num [Complex.mul_re] at hh;linarith
  have hz1 : 6*z≠1 := by intro h;have hh:=congrArg Complex.re h;norm_num [Complex.mul_re] at hh;linarith
  unfold physicalCompensatedRow continuedCompensatedRow
  apply DifferentiableAt.mul
  · exact (((LFunction_differentiableAt (fixedSourcePrincipal S hS.prime) hz0 (Or.inl hz1)).comp z
      (differentiableAt_id.const_mul 6)).mul_const _).mul_const _
  · apply DifferentiableAt.mul
    · exact (continuedCorrection_first_boundary_z eps heps (markExclusions S T)
        (markedSourceExclusions S hS T) (marked_firstTail (eps/2) S hfirst T) η u x w z
        hx hw hz hxw).differentiableAt
    · apply DifferentiableAt.fun_finsetProd
      intro P hP
      exact continuedCompensatedLocal_first_differentiableAt_z η u P.val _
        (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x w z (by linarith) (by linarith)

lemma sourceMellinWeight_differentiableAt_z (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w z : ℂ) (hz : 0<z.re) :
    DifferentiableAt ℂ (fun z=>sourceMellinWeight W0 W1 X Y Z x w z) z := by
  have hxc : (X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hX.ne'
  have hzc : (Z:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hZ.ne'
  have hm := (ProbeRadialMellin.radial_mellin_analytic W0 z hz).differentiableAt
  unfold sourceMellinWeight
  fun_prop (disch := first | exact Or.inl hxc | exact Or.inl hzc)

theorem continuedPhysicalRowKernel_differentiableAt_z {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w z : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hxw : 1+eps≤x.re+w.re) :
    DifferentiableAt ℂ (fun z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z := by
  have hm := sourceMellinWeight_differentiableAt_z W0 W1 X Y Z hX hZ x w z (by linarith)
  have hp : Differentiable ℂ (fun z : ℂ=>∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1)) := by
    apply Differentiable.fun_finsetProd
    intro i hi
    have hp0 := (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
    have hn : (elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)≠0 :=
      Complex.ofReal_ne_zero.mpr (elementNorm_pos _ hp0).ne'
    exact (differentiable_id.sub_const 1).const_cpow (Or.inl hn)
  have hNu : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hfreq : Differentiable ℂ (fun z=>frequencyWeight z ⟨u.val,u.property.1⟩) :=
    differentiable_id.neg.const_cpow (Or.inl hNu)
  exact ((hm.mul (hp z)).mul (hfreq z)).mul
    ((physicalCompensatedRow_first_z eps heps S hS hfirst _ (contourTupleOutside S P hPS) η u x w z hx hw hz hxw).const_mul _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2589

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ZGrowth
Source SHA256: d25923cc174c7d3cfd899ad2bad1fba2ae9761cff6726fa34c6c5ce375e5ce89
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2590



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_z_bounded (eps : ℝ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (x w : ℂ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) :
    ∃C : ℝ,0≤C ∧ ∀z : ℂ,(17/50:ℝ)≤z.re →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C := by
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm x.re
  let L : ℝ := HeckeReciprocalBound.bound 2*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖*
    ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖
  have hLb : 0≤HeckeReciprocalBound.bound 2 := by unfold HeckeReciprocalBound.bound; positivity
  have hL : 0≤L := by dsimp [L];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro z hz
  have hl : ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖≤HeckeReciprocalBound.bound 2 :=
    HeckeStripActual.LFunction_norm_le _ (by norm_num) (by simp only [Complex.mul_re];norm_num;linarith)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z hx hw hz hxw
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) x.re x w z hx le_rfl
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  rw [mul_assoc L]
  apply mul_le_mul _ (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hL
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hl (norm_nonneg _)) (norm_nonneg _)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2590

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.XGrowth
Source SHA256: 92c18f429c4b5b9b659170731cbb8b283cb1bfa254b6e6adad10423b7aded3e1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2591



namespace OAI

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem physicalRow_first_x_growth (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (T : Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hT : ∀P∈T,P.val∉S)
    (η : Character) (u : FreeRow) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃C : ℝ,0≤C ∧ ∀x : ℂ,l≤x.re → x.re≤r →
      ‖physicalCompensatedRow S hS T hT η u x w z‖≤C*(3+|x.im|)^2 := by
  obtain ⟨Cr,hCr,hr⟩ := targetRow_reciprocal_growth e 1 he he' (by norm_num) (by norm_num) S hS.prime
  obtain ⟨Ch,hCh,hh⟩ := unselectedCorrection_first_subpower 1 (by norm_num)
  let N : ℝ := ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)
  let A : T→ℝ := fun P=>selectedFirstBound P.val.val.absNorm r
  let L : ℝ := ‖LFunction (fixedSourcePrincipal S hS.prime) (6*z)‖*
    ‖HeckeOrigin.continued (rowCharacter S hS.prime u) w‖
  let B : ℝ := Cr*(η.modulus.absNorm:ℝ)*N
  have hL : 0≤L := by dsimp [L];positivity
  have hB : 0≤B := by dsimp [B,N];positivity
  have hA (P : T) : 0≤A P := selectedFirstBound_nonneg _ _ (by positivity)
  have hprod : 0≤∏P:T,A P := Finset.prod_nonneg (fun P _=>hA P)
  refine ⟨L*B*(Ch*N)*(∏P:T,A P),by dsimp [N];positivity,?_⟩
  intro x hxl hxr
  have hrec : ‖HeckeReciprocal.reciprocal ((targetRow η u).excludePrimes S hS.prime) x‖≤B*(3+|x.im|)^2 := by
    simpa only [Real.rpow_one] using hr η u x (hlβ.trans hxl)
  have hh' : ‖continuedCorrection (markExclusions S T) (markedSourceExclusions S hS T) η u x w z‖≤Ch*N := by
    simpa only [Real.rpow_one] using hh eps S hS hfirst T η u x w z (hl.trans hxl) hw hz (by linarith)
  have hg : ‖∏P∈T.attach,continuedCompensatedLocal η u P.val
      (outside_prime_supported S hS.bad P.val (hT P.val P.property)) x w z
      (star (idealCoeff η P.val.val)*(P.val.val.absNorm:ℂ)^x)
      ((P.val.val.absNorm:ℂ)^(-w))‖≤∏P:T,A P := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro P hP
    exact continuedCompensatedLocal_first_bound η u P.val _
      (by exact_mod_cast hS.tail.norm_four P.val (hT P.val P.property)) r x w z (hl.trans hxl) hxr
      hw hz (by linarith [hfirst.positive])
  unfold physicalCompensatedRow continuedCompensatedRow
  simp only [norm_mul]
  calc
    _ ≤ L*(B*(3+|x.im|)^2)*((Ch*N)*(∏P:T,A P)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hrec hL)
        (mul_le_mul hh' hg (norm_nonneg _) (by dsimp [N];positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (by positivity)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2591

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.XBoundary
Source SHA256: 11e4b4eeed42e817f3796efcf19f158b72b27ae2e2ace1272dd7b8d48dca075c
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2592




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def xRowScalar {K : ℕ} (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y : ℝ) (w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Y:ℂ)^(w-1)*
    mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_x_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      xRowScalar P u W0 W1 X Y w z*(Z:ℂ)^(x+z-1)*Complex.exp ((x+z-1)^2)*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel xRowScalar sourceMellinWeight
  ring

lemma coupled_gaussian_bound (z : ℂ) {l r v : ℝ} (hl : 0<l) (hv : v∈Icc l r) (t : ℝ) :
    ‖Complex.exp ((((v:ℂ)+t*I)+z-1)^2)‖≤
      Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)) := by
  rw [Complex.norm_exp,←Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hre : ((((v:ℂ)+t*I)+z-1)^2).re=(v+z.re-1)^2-(t+z.im)^2 := by simp [pow_two]
  rw [hre]
  have hvp : 0<v := hl.trans_le hv.1
  have hA : |v+z.re-1|≤|z.re|+r+1 := by
    rw [abs_le]
    constructor <;> linarith [neg_abs_le z.re,le_abs_self z.re,hv.2]
  have hh := pow_le_pow_left₀ (abs_nonneg (v+z.re-1)) hA 2
  rw [sq_abs] at hh
  linarith

theorem continuedPhysicalRowKernel_x_gaussian {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((v:ℂ)+t*I) w z‖≤
        B*Continuation.polynomialGaussian 2 (t+z.im) := by
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_x_growth e eps he he' S hS hfirst _
    (contourTupleOutside S P hPS) η u w z l r hl hlβ hw hz hlw
  let A := ‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1)*
    Real.exp ((|z.re|+r+1)^2)*C
  have hA : 0≤A := by dsimp [A,scaleBound];positivity
  refine ⟨A*(2*(3+|z.im|)^2),by positivity,?_⟩
  intro v hv t
  have hZb := cpow_le_scaleBound hZ (((v:ℂ)+t*I)+z-1)
    (show (((v:ℂ)+t*I)+z-1).re∈Icc (l+z.re-1) (r+z.re-1) by
      simpa using And.intro (by linarith [hv.1] : l+z.re-1≤v+z.re-1)
        (by linarith [hv.2] : v+z.re-1≤r+z.re-1))
  have hgb := coupled_gaussian_bound z (by linarith : 0<l) hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u ((v:ℂ)+t*I) w z‖≤C*(3+|t|)^2 := by
    rw [norm_mul,norm_star]
    apply (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans
    simpa using hrow ((v:ℂ)+t*I) (by simpa using hv.1) (by simpa using hv.2)
  rw [continuedPhysicalRowKernel_x_factor,norm_mul,norm_mul,norm_mul]
  calc
    _ ≤ (‖xRowScalar P u W0 W1 X Y w z‖*scaleBound Z (l+z.re-1) (r+z.re-1))*
        (Real.exp ((|z.re|+r+1)^2)*Real.exp (-((t+z.im)^2)))*(C*(3+|t|)^2) :=
      mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_left hZb (norm_nonneg _)) hgb
        (norm_nonneg _) (mul_nonneg (norm_nonneg _) (scaleBound_pos _ _ _).le))
        hr (norm_nonneg _) (by unfold scaleBound;positivity)
    _ = A*(3+|t|)^2*Real.exp (-((t+z.im)^2)) := by dsimp [A];ring
    _ ≤ A*(2*(3+|z.im|)^2*(1+|t+z.im|^2))*Real.exp (-((t+z.im)^2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Continuation.shifted_height_two t z.im) hA) (Real.exp_pos _).le
    _ = _ := by unfold Continuation.polynomialGaussian;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2592

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.XShift
Source SHA256: d05a3394d1093f618ccf9df0b1dcbac0b7d789eac8e0aedf4396891f2e10a1de
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2593


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical
local notation "O" => HeckeFamily.O

theorem first_x_integral_eq {K : ℕ}
    (e eps : ℝ) (he : 0<e) (he' : e<1/1000) (heps : 0<eps)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (eps/2) S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z : ℝ) (hZ : 0<Z) (w z : ℂ) (l r : ℝ) (hlr : l≤r)
    (hl : (51/100:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l)
    (hw : -(1/100:ℝ)≤w.re) (hz : (17/50:ℝ)≤z.re)
    (hlw : 1+eps≤l+w.re) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((l:ℂ)+t*I) w z)=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z ((r:ℂ)+t*I) w z := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_x_gaussian e (eps/2) he he' S hS hfirst hmax P hPS
    η u W0 W1 X Y Z hZ w z l r hl hlβ hw hz (by linarith)
  apply Continuation.vertical_integral_eq_of_shifted_polynomial_gaussian_bound
    (fun x=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) z.im 2 hlr _ hbound
  intro x hx
  apply (continuedPhysicalRowKernel_buffered_differentiableAt_x eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hZ x w z (hl.trans hx.1) hw hz (by linarith [hx.1]) ?_).differentiableWithinAt
  intro hpole
  exact HeckeZeroSupremum.LFunction_ne_zero_of_beta_lt _ (by linarith [hx.1]) (by tauto)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2593

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ZBoundary
Source SHA256: 8adc29ab03ad6900efa8241299bb77caccdf06b607ff0613e515303677c8190b
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2594



namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

private lemma norm_mul_seven_le {a b c d e f g : ℂ} {A B C D E F G : ℝ}
    (ha : ‖a‖≤A) (hb : ‖b‖≤B) (hc : ‖c‖≤C) (hd : ‖d‖≤D)
    (he : ‖e‖≤E) (hf : ‖f‖≤F) (hg : ‖g‖≤G) :
    ‖a*b*c*d*e*f*g‖≤A*B*C*D*E*F*G := by
  have hA := (norm_nonneg a).trans ha
  have hB := (norm_nonneg b).trans hb
  have hC := (norm_nonneg c).trans hc
  have hD := (norm_nonneg d).trans hd
  have hE := (norm_nonneg e).trans he
  have hF := (norm_nonneg f).trans hf
  simp only [norm_mul]
  gcongr

def zRowScalar {K : ℕ} (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (u : FreeRow)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) : ℂ :=
  (X:ℂ)^(1/2-z)*(Z:ℂ)^(x+z-1)*(Y:ℂ)^(w-1)*
    Complex.exp ((x+z-1)^2)*mellin W1 w*
    (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(z-1))*
    frequencyWeight z ⟨u.val,u.property.1⟩

lemma continuedPhysicalRowKernel_z_factor {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (x w z : ℂ) :
    continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z=
      zRowScalar P u W1 X Y Z x w z*mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) z*
        (star ((calibrationForSet S hmax).residueMonoid u.val)*
          physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w z) := by
  unfold continuedPhysicalRowKernel zRowScalar sourceMellinWeight
  ring

lemma zRowScalar_bounded {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (u : FreeRow)
    (W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z)
    (x w : ℂ) (l r : ℝ) (hl : 0<l) :
    ∃A : ℝ,0≤A ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖zRowScalar P u W1 X Y Z x w ((v:ℂ)+t*I)‖≤A := by
  let B : Fin K→ℝ := fun i=>scaleBound (elementNorm (CompletedGauss.primaryGenerator (P i).val)) (l-1) (r-1)
  let A := scaleBound X (1/2-r) (1/2-l)*scaleBound Z (x.re+l-1) (x.re+r-1)*
    ‖(Y:ℂ)^(w-1)‖*Real.exp ((|x.re|+r+1)^2)*‖mellin W1 w‖*
    (∏i,B i)*scaleBound (elementNorm u.val) (-r) (-l)
  have hB (i : Fin K) : 0≤B i := (scaleBound_pos _ _ _).le
  have hBP : 0≤∏i,B i := Finset.prod_nonneg (fun i _=>hB i)
  have hscale (a b c : ℝ) : 0≤scaleBound a b c := (scaleBound_pos _ _ _).le
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro v hv t
  have hXb := cpow_le_scaleBound hX (1/2-((v:ℂ)+t*I))
    (show (1/2-((v:ℂ)+t*I)).re∈Icc (1/2-r) (1/2-l) by
      simpa using And.intro (sub_le_sub_left hv.2 (1/2)) (sub_le_sub_left hv.1 (1/2)))
  have hZb := cpow_le_scaleBound hZ (x+((v:ℂ)+t*I)-1)
    (show (x+((v:ℂ)+t*I)-1).re∈Icc (x.re+l-1) (x.re+r-1) by
      simpa using And.intro (by linarith [hv.1] : x.re+l-1≤x.re+v-1)
        (by linarith [hv.2] : x.re+v-1≤x.re+r-1))
  have hGb := gaussian_strip_norm_le x hl hv t
  have hPb : ‖∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((v:ℂ)+t*I)-1)‖≤∏i,B i := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro i hi
    apply cpow_le_scaleBound
      (elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)
    simpa using And.intro (sub_le_sub_right hv.1 1) (sub_le_sub_right hv.2 1)
  have hFb : ‖frequencyWeight (((v:ℂ)+t*I)) ⟨u.val,u.property.1⟩‖≤scaleBound (elementNorm u.val) (-r) (-l) := by
    apply cpow_le_scaleBound (elementNorm_pos _ u.property.1)
    simpa using And.intro (neg_le_neg hv.2) (neg_le_neg hv.1)
  exact (norm_mul_seven_le hXb hZb le_rfl hGb le_rfl hPb hFb).trans (le_max_left A 0)

theorem continuedPhysicalRowKernel_z_cauchy {K : ℕ}
    (eps : ℝ) (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail eps S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    ∃B : ℝ,0≤B ∧ ∀v∈Icc l r,∀t : ℝ,
      ‖continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((v:ℂ)+t*I)‖≤B*cauchy t := by
  obtain ⟨A,hA,hscalar⟩ := zRowScalar_bounded S hS P hPS u W1 X Y Z hX hZ x w l r (by linarith)
  obtain ⟨C,hC,hrow⟩ := physicalRow_first_z_bounded eps S hS hfirst _
    (contourTupleOutside S P hPS) η u x w hx hw hxw
  obtain ⟨D,hD,hm⟩ := ProbeRadialMellin.radial_mellin_strip_decay W0 a b ha hW l r (by linarith) 2
  refine ⟨A*D*C,mul_nonneg (mul_nonneg hA hD.le) hC,?_⟩
  intro v hv t
  have hr : ‖star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u x w ((v:ℂ)+t*I)‖≤C := by
    rw [norm_mul,norm_star]
    exact (mul_le_of_le_one_left (norm_nonneg _)
      ((calibrationForSet S hmax).residueMonoid_norm_le_one _)).trans (hrow _ (by simpa using hl.trans hv.1))
  have hm' : ‖mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) ((v:ℂ)+t*I)‖≤D*cauchy t :=
    CubicReflectionKernel.weighted_two_to_cauchy (norm_nonneg _) t (hm v hv t)
  rw [continuedPhysicalRowKernel_z_factor,norm_mul,norm_mul]
  calc
    _ ≤ A*(D*cauchy t)*C := mul_le_mul (mul_le_mul (hscalar v hv t) hm' (norm_nonneg _) hA)
      hr (norm_nonneg _) (mul_nonneg hA (mul_nonneg hD.le (cauchy_nonneg t)))
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2594

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.ZShift
Source SHA256: a3d42303f4d2131de59d5ca61514c800f138c9e2d61947eb5a0e82d7d24ac71d
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2595


namespace OAI

noncomputable section
open scoped Classical BigOperators Topology
open MeasureTheory Set Complex Filter
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

theorem first_z_integral_eq {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    (∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  obtain ⟨B,hB,hbound⟩ := continuedPhysicalRowKernel_z_cauchy (eps/2) S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l r hx hw (by linarith) hl
  apply Continuation.vertical_integral_eq_of_even_envelope
    (fun z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z) cauchy cauchy_integrable
    (by intro t; simp [cauchy]) cauchy_tendsto hlr _ hbound
  intro z hz
  exact (continuedPhysicalRowKernel_differentiableAt_z eps heps S hS hfirst hmax P hPS η u
    W0 W1 X Y Z hX hZ x w z hx hw (hl.trans hz.1) hxw).differentiableWithinAt

lemma first_z_vertical_integrable {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l : ℝ)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    Integrable (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I)) := by
  obtain ⟨B,hB,hb⟩ := continuedPhysicalRowKernel_z_cauchy (eps/2) S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l l hx hw (by linarith) hl
  have hc : Continuous (fun t : ℝ=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    apply (continuedPhysicalRowKernel_differentiableAt_z eps heps S hS hfirst hmax P hPS η u
      W0 W1 X Y Z hX hZ x w ((l:ℂ)+t*I) hx hw (by simpa using hl) hxw).continuousAt.comp
        (f:=fun t : ℝ=>(l:ℂ)+t*I)
    fun_prop
  exact (cauchy_integrable.const_mul B).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun t=>hb l ⟨le_rfl,le_rfl⟩ t))

theorem finite_rows_first_z_shift {K : ℕ}
    (eps : ℝ) (heps : 0<eps) (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hfirst : FirstTail (eps/2) S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (F : Finset FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a b : ℝ) (ha : 0<a) (hW : Function.support W0⊆Icc a b)
    (X Y Z : ℝ) (hX : 0<X) (hZ : 0<Z) (x w : ℂ) (l r : ℝ) (hlr : l≤r)
    (hx : (51/100:ℝ)≤x.re) (hw : -(1/100:ℝ)≤w.re)
    (hxw : 1+eps≤x.re+w.re) (hl : (17/50:ℝ)≤l) :
    (∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((l:ℂ)+t*I))=
      ∫t : ℝ,∑u∈F,continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w ((r:ℂ)+t*I) := by
  rw [integral_finsetSum F (fun u hu=>first_z_vertical_integrable eps heps S hS hfirst hmax P hPS η u
      W0 W1 a b ha hW X Y Z hX hZ x w l hx hw hxw hl),
    integral_finsetSum F (fun u hu=>first_z_vertical_integrable eps heps S hS hfirst hmax P hPS η u
      W0 W1 a b ha hW X Y Z hX hZ x w r hx hw hxw (hl.trans hlr))]
  exact Finset.sum_congr rfl (fun u hu=>first_z_integral_eq eps heps S hS hfirst hmax P hPS η u
    W0 W1 a b ha hW X Y Z hX hZ x w l r hlr hx hw hxw hl)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2595

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.WZTransport
Source SHA256: cbe562ae5670bcf00fee19463886fac6ade5c226c20ec9c87956841e302f43e3
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2596




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.of_ge_one_fiftieth {S : Finset (Ideal O)} (h : FirstTail (1/4) S)
    {eps : ℝ} (heps : (1/50:ℝ)≤eps) : FirstTail eps S := by
  refine ⟨by linarith,h.norm_four,?_⟩
  simpa only [firstPrimeDefectBound,min_eq_right heps,
    min_eq_right (by norm_num : (1/50:ℝ)≤1/4)] using h.small

private lemma height_integral_wxz (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫x : ℝ,∫z : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod _ hw

def continuedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W0 W1 : SchwartzMap ℝ ℂ)
    (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z
    ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)

theorem continuedRowOnLines_z_transport {K : ℕ}
    (e σ υ l r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ)
    (hυ : (1/2:ℝ)≤υ) (hl : (17/50:ℝ)≤l) (hlr : l≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ l p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi (q : ℝ) (hq : (17/50:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable e σ υ q he he' hσ hσβ hυ hq S hS hmax hfirst P hP hPS η u hu
      W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wxz _ (hi l hl),height_integral_wxz _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tx
  exact first_z_integral_eq (1/4) (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 a0 b0 ha0 hW0
    X Y Z hX hZ ((σ:ℂ)+tx*I) ((υ:ℂ)+tw*I) l r hlr
    (by simp;linarith) (by simp;linarith) (by simp;linarith) hl

theorem rowIntegral_wz_transport {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (υ r : ℝ) (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r) (hr2 : r≤2) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤3 := by linarith [HeckeZeroSupremum.beta_le_one]
  have hi (q : ℝ) (hq : (17/50:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ q) heightMeasure :=
    continuedPhysicalRowKernel_integrable (1/2000) 3 υ q (by norm_num) (by norm_num) (by norm_num) hβ hυ hq
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_w_shift (1/2) (by norm_num) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hP hPS
    η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ hυ hυ3
  have hinner : (∫q : ℝ×ℝ,shiftedRowInner S hS hmax P hPS η u W0 W1 X Y Z υ q ∂(volume.prod volume))=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure :=
    (integral_prod _ (hi 2 (by norm_num))).symm
  have hz := continuedRowOnLines_z_transport (1/2000) 3 υ r 2 (by norm_num) (by norm_num)
    (by norm_num) hβ hυ hr hr2 S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    X Y Z hX hY hZ
  exact ⟨hi r hr,hphysical.trans (by rw [hinner,hz])⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2596

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstIntegral
Source SHA256: 9158acbd0b2bb20acaa11f0150cc43768a2c6ca638d0010e3de4541f9696baa1
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2597



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def rowAmplitudeOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1))*
    frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩*
    (star ((calibrationForSet S hmax).residueMonoid u.val)*
      physicalCompensatedRow S hS (Finset.univ.image P) (contourTupleOutside S P hPS) η u
        ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I))

lemma continuedRowOnLines_eq_amplitude {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) :
    continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r t=
      sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
        rowAmplitudeOnLines S hS hmax P hPS η u σ υ r t := by
  unfold continuedRowOnLines continuedPhysicalRowKernel rowAmplitudeOnLines
  ring

lemma rowAmplitudeOnLines_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (σ υ r : ℝ) : Measurable (rowAmplitudeOnLines S hS hmax P hPS η u σ υ r) := by
  have hp (i : Fin K) : 0<elementNorm (CompletedGauss.primaryGenerator (P i).val) :=
    elementNorm_pos _ (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero
  have hN : (elementNorm u.val:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
  have hphys := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun t : HeightSpace=>(σ:ℂ)+t.1.1*I) (fun t : HeightSpace=>(υ:ℂ)+t.2*I)
    (fun t : HeightSpace=>(r:ℂ)+t.1.2*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold rowAmplitudeOnLines
  apply Measurable.mul
  · apply Measurable.mul
    · apply Finset.measurable_prod
      intro i hi
      exact measurable_const_cpow _ (Complex.ofReal_ne_zero.mpr (hp i).ne') _ (by fun_prop)
    · unfold frequencyWeight
      exact measurable_const_cpow _ hN _ (by fun_prop)
  · exact hphys.const_mul _

lemma rowAmplitudeOnLines_first_bound {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (υ r : ℝ)
    (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_growth S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu
  let B : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hB : 0≤B := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨B*C,mul_nonneg hB hC,?_⟩
  intro t
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hB).trans_eq (by ring)

theorem continuedPhysicalRowKernel_first_integrable {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_first_bound S hS hmax hfirst P hPS η u hu υ r hυ hr
  have hm := rowAmplitudeOnLines_measurable S hS hmax P hPS η u 2 υ r
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    2 2 r r υ υ (by linarith)
  have htwo (t : HeightSpace) : ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hbound t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile 2 ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ υ ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC _ hm.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ 2 r υ (by linarith)
  have hk : AEStronglyMeasurable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure := by
    have heq : continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r=
        (fun t=>sourceMellinWeight W0 W1 X Y Z ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
          rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t) := by funext t;exact continuedRowOnLines_eq_amplitude ..
    rw [heq]
    exact hs.aestronglyMeasurable.mul hm.aestronglyMeasurable
  exact hi.mono' hk (Filter.Eventually.of_forall fun t=>by rw [continuedRowOnLines_eq_amplitude,norm_mul])

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2597

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedIntegral
Source SHA256: 7ee530e8b7a02fd2515d73969d6a3c50e4c29ec247480b90b9357f63b4958756
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2598



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_bound {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_joint_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ) (by simpa using hσ2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continuedPhysicalRowKernel_buffered_integrable {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z)
    (σ r : ℝ) (hσ : a+16*e≤σ) (hσ2 : σ≤2) (hr : (17/50:ℝ)≤r) :
    IntegrableOn (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)
      {t : HeightSpace | |t.1.1|≤H} heightMeasure := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let A := E.indicator (rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r)
  have hA : Measurable A := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).indicator hE
  obtain ⟨C,hC,hbound⟩ := rowAmplitudeOnLines_buffered_bound e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin σ r hσ hσ2 hr
  have hb (t : HeightSpace) : ‖A t‖≤C*(3+|t.2|)^2 := by
    by_cases ht : t∈E
    · simpa only [A,Set.indicator_of_mem ht] using hbound t ht
    · simp only [A,Set.indicator_of_notMem ht,norm_zero]
      positivity
  obtain ⟨D,hD,hprofile⟩ := source_profile_integral_bound W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    σ σ r r (1-a-6*e) (1-a-6*e) (by linarith)
  have htwo (t : HeightSpace) : ‖A t‖≤C*(3+|t.1.1|)^2*(3+|t.2|)^2 := by
    apply (hb t).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hh : 1≤(3+|t.1.1|)^2 := by nlinarith [abs_nonneg t.1.1]
    exact le_mul_of_one_le_right hC hh
  have hi := (hprofile σ ⟨le_rfl,le_rfl⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩
    X Y Z hX hY hZ C hC (fun t=>‖A t‖) hA.norm.aestronglyMeasurable (fun _=>norm_nonneg _) htwo).1
  have hs := sourceMellinWeight_initial_continuous W0 W1 a1 b1 ha1 hW1 X Y Z hX hY hZ σ r (1-a-6*e) (by linarith)
  let F := fun t : HeightSpace => sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I)
      ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*A t
  have hm : AEStronglyMeasurable F heightMeasure := hs.aestronglyMeasurable.mul hA.aestronglyMeasurable
  have hf : Integrable F heightMeasure := hi.mono' hm (Filter.Eventually.of_forall fun t=>by dsimp [F];rw [norm_mul])
  have heq : E.indicator (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ (1-a-6*e) r)=F := by
    funext t
    by_cases ht : t∈E
    · simp only [Set.indicator_of_mem ht,F,A,continuedRowOnLines_eq_amplitude]
    · simp only [Set.indicator_of_notMem ht,F,A,mul_zero]
  exact (integrable_indicator_iff hE).mp (heq ▸ hf)

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2598

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.CoarseAmplitude
Source SHA256: a6ebfc3d7a667bae7f7eb3d090c635672b1faaa20177050b5e23b5a642bc7647
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2599



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma coarsePrimeCost_image {K : ℕ} (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P) :
    coarsePrimeCost (Finset.univ.image P)=(8192:ℝ)^K*(∏i,(P i).val.absNorm:ℝ)^3 := by
  unfold coarsePrimeCost
  rw [Finset.prod_image (by intro a ha b hb hab;exact hP hab)]
  rw [Finset.prod_mul_distrib,←Finset.prod_pow]
  simp

lemma prime_frequency_amplitude_le_one {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (hPS : ∀i,(P i).val∉S) (u : FreeRow) (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (t : ℝ) :
    ‖(∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t*I)-1))*
      frequencyWeight ((r:ℂ)+t*I) ⟨u.val,u.property.1⟩‖≤1 := by
  have hp (i : Fin K) : 1≤elementNorm (CompletedGauss.primaryGenerator (P i).val) := by
    unfold elementNorm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using
        (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero))
  have hu : 1≤elementNorm u.val := by
    unfold elementNorm
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using u.property.1))
  rw [norm_mul,norm_prod]
  refine (mul_le_of_le_one_left (norm_nonneg _) ?_).trans ?_
  · apply Finset.prod_le_one₀ (fun _ _=>norm_nonneg _)
    intro i hi
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith [hp i])]
    simp only [sub_re,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero,one_re]
    simpa using Real.rpow_le_rpow_of_exponent_le (hp i) (by linarith : r-1≤0)
  · unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0<elementNorm u.val)]
    simp only [neg_re,add_re,ofReal_re,mul_re,I_re,I_im,ofReal_im,mul_zero,zero_mul,sub_zero,add_zero]
    simpa using Real.rpow_le_rpow_of_exponent_le hu (by linarith : -r≤0)

def contourArithmeticCost {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) : ℝ :=
  (η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6*(∏i,(P i).val.absNorm:ℝ)^3

lemma contourArithmeticCost_nonneg {K : ℕ} (η : Character) (u : FreeRow) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) :
    0≤contourArithmeticCost η u P := by unfold contourArithmeticCost;positivity

theorem rowAmplitudeOnLines_buffered_polynomial (K : ℕ)
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (4*e) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀ψ : ι→Character,∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,|t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤
        C*contourArithmeticCost η u P*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_polynomial_growth (ι:=ι) e he he' S hS hfirst hmax
  refine ⟨C*(8192:ℝ)^K,by positivity,?_⟩
  intro η u hu P hP hPS ψ a B H i ha haTop hB hH hbin σ hσ r hr t ht
  have hw := prime_frequency_amplitude_le_one S hS P hPS u r (by linarith [hr.1]) hr.2 t.1.2
  have hb := hbound η u hu (Finset.univ.image P) (contourTupleOutside S P hPS) ψ a B H i ha haTop hB hH hbin
    ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr.1)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  unfold rowAmplitudeOnLines
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
  apply hb.trans_eq
  rw [coarsePrimeCost_image P hP]
  unfold contourArithmeticCost
  ring

theorem rowAmplitudeOnLines_first_polynomial (K : ℕ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hfirst : FirstTail (1/4) S)
    (hmax : ∀P∈S,P.IsMaximal) :
    ∃C : ℝ,0≤C ∧ ∀(η : Character) (u : FreeRow),u.val≠1 →
      ∀(P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal),Function.Injective P → ∀hPS : ∀j,(P j).val∉S,
      ∀υ : ℝ,-(1/100:ℝ)≤υ → ∀r∈Icc (17/50:ℝ) 1,∀t : HeightSpace,
      ‖rowAmplitudeOnLines S hS hmax P hPS η u 2 υ r t‖≤
        C*contourArithmeticCost η u P*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_first_joint_polynomial_growth S hS hfirst hmax
  refine ⟨C*(8192:ℝ)^K,by positivity,?_⟩
  intro η u hu P hP hPS υ hυ r hr t
  have hw := prime_frequency_amplitude_le_one S hS P hPS u r (by linarith [hr.1]) hr.2 t.1.2
  have hb := hbound η u hu (Finset.univ.image P) (contourTupleOutside S P hPS)
    ((2:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simp) (by simpa using hυ) (by simpa using hr.1)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hb
  have hN : (1:ℝ)≤(Ideal.span {u.val}:Ideal O).absNorm := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr
      (Ideal.absNorm_eq_zero_iff.not.mpr (by simpa only [Ideal.span_singleton_eq_bot] using u.property.1))
  have hη := HeckeLogarithmicInput.modulus_norm_ge_one η
  have hN46 : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4≤((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6 :=
    pow_le_pow_right₀ hN (by norm_num)
  have hη2 : (1:ℝ)≤(η.modulus.absNorm:ℝ)^2 := by nlinarith
  have hlarge : ((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4≤
      (η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6 :=
    hN46.trans (le_mul_of_one_le_left (by positivity) hη2)
  unfold rowAmplitudeOnLines
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hw).trans
  apply hb.trans
  rw [coarsePrimeCost_image P hP]
  unfold contourArithmeticCost
  calc
    _ = (C*(8192:ℝ)^K)*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^4*(∏i,(P i).val.absNorm:ℝ)^3*(3+|t.2|)^2 := by ring
    _ ≤ (C*(8192:ℝ)^K)*((η.modulus.absNorm:ℝ)^2*((Ideal.span {u.val}:Ideal O).absNorm:ℝ)^6)*
        (∏i,(P i).val.absNorm:ℝ)^3*(3+|t.2|)^2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlarge (mul_nonneg hC (pow_nonneg (by norm_num) _)))
        (pow_nonneg (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (P i).val.absNorm)) _)) (sq_nonneg _)
    _ = _ := by ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2599

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SliceIntegral
Source SHA256: f470226efefa32657d19c46e981f23025059c7b588c321fa36426b4376d1d592
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2600


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open ProbePhysical ProbeMellinBoundary

theorem source_profile_arithmetic_slices (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ)
    (ha0 : 0<a0) (ha1 : 0<a1) (hW0 : Function.support W0⊆Icc a0 b0)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (slo shi zlo zhi wlo whi : ℝ) (hzlo : 0<zlo) (J N : ℕ) :
    ∃K : ℝ,0<K ∧ ∀σ∈Icc slo shi,∀ξ∈Icc zlo zhi,∀υ∈Icc wlo whi,
      ∀axis : SliceAxis,∀T A : ℝ,0≤A → ∀X Y Z : ℝ,0<X → 0<Y → 0<Z →
      ∀G : ℝ×ℝ→ℂ,AEStronglyMeasurable G (volume.prod volume) →
      (∀q,‖G q‖≤A*jointHeight (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J) →
      let F := fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          A*K*(X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1))/height T^N := by
  obtain ⟨K,hK,hbound⟩ := profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    slo shi zlo zhi wlo whi hzlo J N
  refine ⟨K,hK,?_⟩
  intro σ hσ ξ hξ υ hυ axis T A hA X Y Z hX hY hZ G hG hGb
  let E : ℝ := X^(1/2-ξ)*Z^(σ+ξ-1)*Y^(υ-1)
  have hE : 0≤E := by dsimp [E];positivity
  let S := fun q : ℝ×ℝ=>sourceScale X Y Z ((σ:ℂ)+(sliceMap axis T q).1.1*I)
    ((υ:ℂ)+(sliceMap axis T q).2*I) ((ξ:ℂ)+(sliceMap axis T q).1.2*I)
  have hc : Continuous (fun p : HeightSpace => (((σ:ℂ)+p.1.1*I,(υ:ℂ)+p.2*I),(ξ:ℂ)+p.1.2*I)) := by fun_prop
  have hS0 := (sourceScale_continuous X Y Z hX hY hZ).comp (hc.comp (sliceMap_continuous axis T))
  have hS : Continuous S := by simpa only [S,Function.comp_def] using hS0
  have hSn (q : ℝ×ℝ) : ‖S q‖=E := by
    dsimp only [S]
    rw [sourceScale_norm X Y Z hX hY hZ]
    simp [E]
  have hb (q : ℝ×ℝ) : ‖S q*G q‖≤(E*A)*jointHeight
      (sliceMap axis T q).1.1 (sliceMap axis T q).1.2 (sliceMap axis T q).2^J := by
    rw [norm_mul,hSn]
    exact (mul_le_mul_of_nonneg_left (hGb q) hE).trans_eq (by ring)
  obtain ⟨hi,hb⟩ := hbound σ hσ ξ hξ υ hυ axis T (E*A) (mul_nonneg hE hA)
    (fun q=>S q*G q) (hS.aestronglyMeasurable.mul hG) hb
  have heq : (fun q : ℝ×ℝ=>sourceMellinWeight W0 W1 X Y Z
        ((σ:ℂ)+(sliceMap axis T q).1.1*I) ((υ:ℂ)+(sliceMap axis T q).2*I)
        ((ξ:ℂ)+(sliceMap axis T q).1.2*I)*G q)=
      (fun q=>(S q*G q)*onLines W0 W1 σ ξ υ (sliceMap axis T q)) := by
    funext q
    rw [sourceMellinWeight_eq_scale]
    dsimp [S,onLines]
    ring
  dsimp only
  refine ⟨heq.symm ▸ hi,?_⟩
  have hnorm := congrArg (fun f : ℝ×ℝ→ℂ => ∫q : ℝ×ℝ,‖f q‖ ∂volume.prod volume) heq
  rw [hnorm]
  calc
    _ ≤ (E*A)*K/height T^N := hb
    _ = _ := by dsimp [E];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2600

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedSlices
Source SHA256: 0d8e316c5258a86ca5a38a8b30aabe94cdeb0487f670f81f2e1502b6cc59ed6e
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2601


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_uniform {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_joint_growth e a B H i he he' ha haTop hB hH S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ hbin
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro σ hσ t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem continuedPhysicalRowKernel_buffered_slices {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|≤H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_uniform e a B H i he he' ha haTop hB hH
    S hS hmax hfirst P hPS η u hu ψ hbin r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (a+16*e) 2 r r (1-a-6*e) (1-a-6*e) (by linarith) 2 N
  refine ⟨(9*A)*D,by positivity,?_⟩
  intro σ hσ tx htx
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow σ hσ ((tx,q.1),q.2) htx).trans
    calc
      _ ≤ A*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) hA
      _ = _ := by ring
  have ht := hprofile σ hσ r ⟨le_rfl,le_rfl⟩ (1-a-6*e) ⟨le_rfl,le_rfl⟩ .s tx
    (9*A) (by positivity) X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2601

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedJoinDecay
Source SHA256: 5256ce12dd9e33c753b2fb14afe92f80d753d4f761e6fe19d40b236034a04688
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2602



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

lemma rowAmplitudeOnLines_buffered_height_uniform {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀t : HeightSpace, |t.1.1|≤H →
      ‖rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r t‖≤C*(3+|H|)^2*(3+|t.2|)^2 := by
  obtain ⟨C,hC,hbound⟩ := calibrated_physicalRow_buffered_height_growth e he he' S hS hfirst hmax _
    (contourTupleOutside S P hPS) η u hu ψ
  let A : ℝ := (∏i,(elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1))*(elementNorm u.val)^(-r)
  have hA : 0≤A := by
    apply mul_nonneg
    · exact Finset.prod_nonneg (fun i _=>Real.rpow_nonneg (by unfold elementNorm; positivity) _)
    · exact Real.rpow_nonneg (by unfold elementNorm; positivity) _
  refine ⟨A*C,mul_nonneg hA hC,?_⟩
  intro a B H i ha haTop hB hH hbin σ hσ t ht
  have hn (i : Fin K) : ‖(elementNorm (CompletedGauss.primaryGenerator (P i).val):ℂ)^(((r:ℂ)+t.1.2*I)-1)‖=
      (elementNorm (CompletedGauss.primaryGenerator (P i).val))^(r-1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _
      (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero)]
    simp
  have hf : ‖frequencyWeight ((r:ℂ)+t.1.2*I) ⟨u.val,u.property.1⟩‖=(elementNorm u.val)^(-r) := by
    unfold frequencyWeight
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (elementNorm_pos _ u.property.1)]
    simp
  have hh := hbound a B H i ha haTop hB hH hbin ((σ:ℂ)+t.1.1*I) ((((1-a-6*e):ℝ):ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)
    (by simpa using hσ.1) (by simpa using hσ.2) (by simpa using ht) (by simp) (by simpa using hr)
  simp only [add_im,ofReal_im,mul_im,ofReal_re,I_im,I_re,mul_one,mul_zero,add_zero,zero_add] at hh
  unfold rowAmplitudeOnLines
  rw [norm_mul,norm_mul,norm_prod]
  simp_rw [hn,hf]
  exact (mul_le_mul_of_nonneg_left hh hA).trans_eq (by ring)

theorem buffered_x_slice_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ)
    (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,(51/100:ℝ)≤a → a≤1 → 2<B →
      H≤(3*i+2:ℕ)*B → detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀σ∈Icc (a+16*e) 2,∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨A,hA,hrow⟩ := rowAmplitudeOnLines_buffered_height_uniform e he he' S hS hmax hfirst P hPS η u hu ψ r hr
  obtain ⟨D,hD,hprofile⟩ := source_profile_arithmetic_slices W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (51/100) 2 r r (-(1/100)) (1/2) (by linarith) 2 (N+2)
  refine ⟨81*A*D,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin σ hσ tx htx
  let G := fun q : ℝ×ℝ=>rowAmplitudeOnLines S hS hmax P hPS η u σ (1-a-6*e) r ((tx,q.1),q.2)
  have hG : Measurable G := (rowAmplitudeOnLines_measurable S hS hmax P hPS η u σ (1-a-6*e) r).comp (by fun_prop)
  have hb (q : ℝ×ℝ) : ‖G q‖≤(9*A*(3+|H|)^2)*jointHeight tx q.1 q.2^2 := by
    have hh : 3+|q.2|≤3*jointHeight tx q.1 q.2 := by
      unfold jointHeight
      linarith [abs_nonneg tx,abs_nonneg q.1,abs_nonneg q.2]
    apply (hrow a B H i ha haTop hB hH hbin σ hσ ((tx,q.1),q.2) htx.le).trans
    calc
      _ ≤ (A*(3+|H|)^2)*(3*jointHeight tx q.1 q.2)^2 := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hh 2) (by positivity)
      _ = _ := by ring
  have ht := hprofile σ ⟨by linarith [hσ.1],hσ.2⟩ r ⟨le_rfl,le_rfl⟩ (1-a-6*e)
    ⟨by linarith,by linarith⟩ .s tx (9*A*(3+|H|)^2) (by positivity)
    X Y Z hX hY hZ G hG.aestronglyMeasurable hb
  have ht' : Integrable (fun q : ℝ×ℝ=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        σ (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤
        (9*A*(3+|H|)^2)*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height tx^(N+2) := by
    simpa only [sliceMap,G,continuedRowOnLines_eq_amplitude] using ht
  refine ⟨ht'.1,ht'.2.trans ?_⟩
  have hH0 : 0≤H := htx ▸ abs_nonneg tx
  have hheight : height tx=height H := by simp [height,htx,abs_of_nonneg hH0]
  have hpow : (3+|H|)^2≤9*(height H)^2 := by
    have hh : 3+|H|≤3*height H := by unfold height;linarith [abs_nonneg H]
    have hh' := pow_le_pow_left₀ (by positivity) hh 2
    norm_num [mul_pow] at hh'
    exact hh'
  have hden : 0<height H := height_pos H
  rw [hheight]
  calc
    _ ≤ (9*A*(9*(height H)^2))*D*(X^(1/2-r)*Z^(σ+r-1)*Y^((1-a-6*e)-1))/height H^(N+2) := by
      gcongr
    _ = _ := by rw [pow_add];field_simp;ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2602

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.HorizontalIntegral
Source SHA256: 1731faa68cdd5e2d34d9ee9089c75760993a86b8379da53eff46ddc805b13641
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2603


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma continuedRow_horizontal_measurable {K : ℕ}
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow)
    (W0 W1 : SchwartzMap ℝ ℂ) (a1 b1 : ℝ) (ha1 : 0<a1)
    (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) (tx υ r : ℝ) (hr : 0<r) :
    Measurable (fun p : ℝ × (ℝ × ℝ)=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
      p.1 υ r ((tx,p.2.1),p.2.2)) := by
  have hR : Continuous (fun t : ℝ=>mellin (EisensteinSchwartzPoisson.paperRadialFourier W0) ((r:ℂ)+t*I)) :=
    (ProbeRadialMellin.radial_mellin_differentiable W0).continuousOn.comp_continuous
      (by fun_prop) (by intro t;simpa using hr)
  have hW := (CubicReflectionKernel.compact_source_mellin_differentiable W1 a1 b1 ha1 hW1 (W1.smooth ⊤)).continuous
  have hcoords : Continuous (fun p : ℝ × (ℝ × ℝ)=>(((p.1:ℂ)+tx*I,(υ:ℂ)+p.2.2*I),(r:ℂ)+p.2.1*I)) := by fun_prop
  have hscale := (sourceScale_continuous X Y Z hX hY hZ).comp hcoords
  have hprof : Measurable (fun p : ℝ × (ℝ × ℝ)=>profile W0 W1
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    unfold profile
    apply Measurable.mul
    · apply Measurable.mul
      · fun_prop
      · exact hR.measurable.comp (by fun_prop)
    · exact hW.measurable.comp (by fun_prop)
  have hsource : Measurable (fun p : ℝ × (ℝ × ℝ)=>sourceMellinWeight W0 W1 X Y Z
      ((p.1:ℂ)+tx*I) ((υ:ℂ)+p.2.2*I) ((r:ℂ)+p.2.1*I)) := by
    simp_rw [sourceMellinWeight_eq_scale]
    exact hscale.measurable.mul hprof
  have hphysical := physicalCompensatedRow_measurable S hS _ (contourTupleOutside S P hPS) η u
    (fun p : ℝ × (ℝ × ℝ)=>(p.1:ℂ)+tx*I) (fun p : ℝ × (ℝ × ℝ)=>(υ:ℂ)+p.2.2*I)
    (fun p : ℝ × (ℝ × ℝ)=>(r:ℂ)+p.2.1*I) (by fun_prop) (by fun_prop) (by fun_prop)
  unfold continuedRowOnLines continuedPhysicalRowKernel
  apply Measurable.mul
  · apply Measurable.mul
    · apply Measurable.mul hsource
      apply Finset.measurable_prod
      intro i hi
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _
          (supported_primeGenerator_prime (P i) (outside_prime_supported S hS.bad (P i) (hPS i))).ne_zero).ne'
      · fun_prop
    · unfold frequencyWeight
      apply measurable_const_cpow
      · exact Complex.ofReal_ne_zero.mpr (elementNorm_pos _ u.property.1).ne'
      · fun_prop
  · exact hphysical.const_mul _

lemma horizontal_integral_bound (F : ℝ→(ℝ×ℝ)→ℂ) (l r C : ℝ) (hlr : l≤r) (_hC : 0≤C)
    (hm : Measurable (Function.uncurry F))
    (hi : ∀v∈Ioc l r,Integrable (F v) (volume.prod volume))
    (hb : ∀v∈Ioc l r,(∫q : ℝ×ℝ,‖F v q‖ ∂volume.prod volume)≤C) :
    Integrable (fun q : ℝ×ℝ=>∫v : ℝ in l..r,F v q) (volume.prod volume) ∧
      (∫q : ℝ×ℝ,‖∫v : ℝ in l..r,F v q‖ ∂volume.prod volume)≤(r-l)*C := by
  let μ : Measure ℝ := volume.restrict (Ioc l r)
  let ν : Measure (ℝ×ℝ) := volume.prod volume
  have hm' : AEStronglyMeasurable (Function.uncurry F) (μ.prod ν) := hm.aestronglyMeasurable
  have hnorm : Integrable (fun v=>∫q,‖F v q‖ ∂ν) μ := by
    apply (integrable_const C).mono' hm'.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [Real.norm_eq_abs,abs_of_nonneg (integral_nonneg (fun _=>norm_nonneg _))]
    exact hb v hv
  have hprod : Integrable (Function.uncurry F) (μ.prod ν) := by
    apply (integrable_prod_iff hm').mpr
    refine ⟨?_,hnorm⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    exact hi v hv
  have hj : Integrable (fun q=>∫v,F v q ∂μ) ν := hprod.integral_prod_right
  simp only [intervalIntegral.integral_of_le hlr]
  refine ⟨hj,?_⟩
  calc
    _ ≤ ∫q,∫v,‖F v q‖ ∂μ ∂ν := integral_mono hj.norm hprod.integral_norm_prod_right
      (fun q=>norm_integral_le_integral_norm _)
    _ = ∫v,∫q,‖F v q‖ ∂ν ∂μ := integral_integral_swap hprod.norm.swap
    _ ≤ ∫v,C ∂μ := integral_mono_ae hnorm (integrable_const C) (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
      exact hb v hv)
    _ = _ := by
      dsimp [μ]
      rw [setIntegral_const,Real.volume_real_Ioc_of_le hlr,smul_eq_mul]

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2603

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedJoins
Source SHA256: 17a0e9d2ecbf584a957dc4babbf82f18a0aa4a257bd7eab7d599ec30c4e04b54
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2604


namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O
variable {ι : Type*} [Fintype ι]

theorem buffered_horizontal_join_arbitrary_decay {K : ℕ}
    (e : ℝ) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (N : ℕ) (r : ℝ) (hr : (17/50:ℝ)≤r) :
    ∃C : ℝ,0≤C ∧ ∀X Y Z : ℝ,0<X → 0<Y → 0<Z → ∀a B H : ℝ,∀i : ℕ,
      (51/100:ℝ)≤a → a≤1 → 2<B → H≤(3*i+2:ℕ)*B →
      detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e →
      ∀tx : ℝ,|tx|=H →
      let F := fun q : ℝ×ℝ=>∫v : ℝ in (a+16*e)..2,
        continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2)
      Integrable F (volume.prod volume) ∧
        (∫q : ℝ×ℝ,‖F q‖ ∂volume.prod volume)≤
          C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N := by
  obtain ⟨C,hC,hbound⟩ := buffered_x_slice_arbitrary_decay e he he' S hS hmax hfirst P hPS η u hu ψ
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 N r hr
  refine ⟨2*C,by positivity,?_⟩
  intro X Y Z hX hY hZ a B H i ha haTop hB hH hbin tx htx
  let A : ℝ := C*(X^(1/2-r)*scaleBound Z ((51/100)+r-1) (2+r-1)*Y^((1-a-6*e)-1))/height H^N
  have hA : 0≤A := by dsimp [A];exact div_nonneg (mul_nonneg hC (by unfold scaleBound;positivity)) (pow_nonneg (height_pos _).le _)
  have hslice (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :=
    hbound X Y Z hX hY hZ a B H i ha haTop hB hH hbin v ⟨hv.1.le,hv.2⟩ tx htx
  have hnorm (v : ℝ) (hv : v∈Ioc (a+16*e) 2) :
      (∫q : ℝ×ℝ,‖continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z
        v (1-a-6*e) r ((tx,q.1),q.2)‖ ∂volume.prod volume)≤A := by
    apply (hslice v hv).2.trans
    have hz := rpow_le_scaleBound hZ
      (show v+r-1∈Icc ((51/100)+r-1) (2+r-1) by constructor <;> linarith [hv.1,hv.2])
    dsimp [A]
    gcongr
    exact pow_nonneg (height_pos H).le N
  have hm := continuedRow_horizontal_measurable S hS hmax P hPS η u W0 W1 a1 b1 ha1 hW1
    X Y Z hX hY hZ tx (1-a-6*e) r (by linarith)
  obtain ⟨hi,hb⟩ := horizontal_integral_bound
    (fun v q=>continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z v (1-a-6*e) r ((tx,q.1),q.2))
    (a+16*e) 2 A (by linarith) hA hm (fun v hv=>(hslice v hv).1) hnorm
  refine ⟨hi,hb.trans ?_⟩
  calc
    _ ≤ 2*A := mul_le_mul_of_nonneg_right (by linarith : 2-(a+16*e)≤2) hA
    _ = _ := by dsimp [A];ring

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2604

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.SourceTransport
Source SHA256: ddd8d670a8d834de62f39679d8457c0d8a1827f39d51f31a789a71e3ec066523
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2605



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

private lemma height_integral_wzx (f : HeightSpace→ℂ) (hf : Integrable f heightMeasure) :
    (∫p : HeightSpace,f p ∂heightMeasure)=∫w : ℝ,∫z : ℝ,∫x : ℝ,f ((x,z),w) := by
  rw [integral_prod_symm _ hf]
  apply integral_congr_ae
  filter_upwards [hf.prod_left_ae] with w hw
  exact integral_prod_symm _ hw

theorem continuedRowOnLines_x_transport {K : ℕ}
    (e l r υ ξ : ℝ) (he : 0<e) (he' : e<1/1000)
    (hl : (7/8:ℝ)≤l) (hlβ : HeckeZeroSupremum.beta+8*e≤l) (hlr : l≤r)
    (hυ : (1/2:ℝ)≤υ) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z l υ ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z r υ ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : l≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z q υ ξ) heightMeasure :=
    continuedPhysicalRowKernel_integrable e q υ ξ he he' (hl.trans hq) (hlβ.trans hq) hυ hξ
      S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [height_integral_wzx _ (hi l le_rfl),height_integral_wzx _ (hi r hlr)]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  exact first_x_integral_eq e (1/4) he he' (by norm_num) S hS
    (hfirst.of_ge_one_fiftieth (by norm_num)) hmax P hPS η u W0 W1 X Y Z hZ
    ((υ:ℂ)+tw*I) ((ξ:ℂ)+tz*I) l r hlr (by linarith) hlβ
    (by simp;linarith) (by simpa using hξ) (by simp;linarith)

theorem rowIntegral_source_lines {K : ℕ}
    (e σ υ r : ℝ) (he : 0<e) (he' : e<1/1000)
    (hσ : (7/8:ℝ)≤σ) (hσβ : HeckeZeroSupremum.beta+8*e≤σ) (hσ3 : σ≤3)
    (hυ : (1/2:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z σ υ r p ∂heightMeasure := by
  have hi := continuedPhysicalRowKernel_integrable e σ υ r he he' hσ hσβ hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  obtain ⟨_,hphysical⟩ := rowIntegral_wz_transport S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ υ 2 hυ hυ3 (by norm_num) le_rfl
  have hβ3 : HeckeZeroSupremum.beta+8*e≤3 := hσβ.trans hσ3
  have hz : (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ r p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 3 υ 2 p ∂heightMeasure := by
    by_cases hr2 : r≤2
    · exact continuedRowOnLines_z_transport e 3 υ r 2 he he' (by norm_num) hβ3 hυ hr hr2
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
    · exact (continuedRowOnLines_z_transport e 3 υ 2 r he he' (by norm_num) hβ3 hυ (by norm_num) (le_of_not_ge hr2)
        S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ).symm
  have hx := continuedRowOnLines_x_transport e σ 3 υ r he he' hσ hσβ hσ3 hυ hr
    S hS hmax hfirst P hP hPS η u hu W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨hi,hphysical.trans (by rw [hx,hz])⟩

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2605

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.FirstTransport
Source SHA256: 06c5af27754d0faf5f10e3c5e7ed3590bd564f11aed17c715a16438454d3fdca
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2606




namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma FirstTail.mono_parameter {eps eps' : ℝ} {S : Finset (Ideal O)}
    (h : FirstTail eps S) (hle : eps≤eps') : FirstTail eps' S := by
  have hp : 0<eps' := h.positive.trans_le hle
  refine ⟨hp,h.norm_four,?_⟩
  apply le_trans _ h.small
  apply ((firstPrimeDefectBound_summable eps' hp).subtype _).tsum_le_tsum _ h.summable
  intro P
  unfold firstPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le
  · have hn := h.norm_four P.val P.property
    exact_mod_cast (by omega : 1≤P.val.val.absNorm)
  · have hm := min_le_min_right (1/50:ℝ) hle
    linarith

theorem continuedRowOnLines_first_w_transport {K : ℕ}
    (l r ξ : ℝ) (hl : -(1/100:ℝ)≤l) (hlr : l≤r) (hξ : (17/50:ℝ)≤ξ)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    (∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 l ξ p ∂heightMeasure)=
      ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 r ξ p ∂heightMeasure := by
  have hi (q : ℝ) (hq : -(1/100:ℝ)≤q) :
      Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 q ξ) heightMeasure :=
    continuedPhysicalRowKernel_first_integrable q ξ hq hξ S hS hmax hfirst P hPS η u hu W0 W1
      a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  rw [integral_prod _ (hi l hl),integral_prod _ (hi r (hl.trans hlr))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro q
  exact nonprincipal_first_w_integral_eq (1/2) (by norm_num) S hS (by norm_num;exact hfirst) hmax P hPS η u hu
    W0 W1 a1 b1 ha1 hW1 X Y Z hY ((2:ℂ)+q.1*I) ((ξ:ℂ)+q.2*I) l r hlr
    (by norm_num) hl (by simpa using hξ) (by norm_num;linarith)

theorem rowIntegral_first_w_lines {K : ℕ}
    (υ r : ℝ) (hυ : -(1/100:ℝ)≤υ) (hυ3 : υ≤3) (hr : (17/50:ℝ)≤r)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (1/4) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 υ r p ∂heightMeasure := by
  have hβ : HeckeZeroSupremum.beta+8*(1/2000:ℝ)≤2 := by linarith [HeckeZeroSupremum.beta_le_one]
  obtain ⟨_,hphysical⟩ := rowIntegral_source_lines (1/2000) 2 3 r (by norm_num) (by norm_num)
    (by norm_num) hβ (by norm_num) (by norm_num) le_rfl hr S hS hmax hfirst P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  have hw := continuedRowOnLines_first_w_transport υ 3 r hυ hυ3 hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  exact ⟨continuedPhysicalRowKernel_first_integrable υ r hυ hr S hS hmax hfirst P hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ,hphysical.trans (by rw [hw])⟩

theorem rowIntegral_central_start {K : ℕ}
    (a e : ℝ) (ha : (51/100:ℝ)≤a) (ha1 : a≤1) (he : 0<e) (he' : e<1/1000)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀i,(P i).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    Integrable (continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50)) heightMeasure ∧
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3*
        ∫p : HeightSpace,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure :=
  rowIntegral_first_w_lines (1-a-6*e) (17/50) (by linarith) (by linarith) le_rfl
    S hS hmax (hfirst.mono_parameter (by linarith)) P hP hPS η u hu W0 W1
    a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2606

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.BufferedTransport
Source SHA256: f48588d0f8ff619d64c39999d951bd794feb030cde62c3b55e8557acff7d23c5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2607



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

lemma height_slab_integral_wzx (f : HeightSpace→ℂ) (H : ℝ) (hH : 0≤H)
    (hf : IntegrableOn f {t : HeightSpace | |t.1.1|≤H} heightMeasure) :
    (∫p : HeightSpace in {t : HeightSpace | |t.1.1|≤H},f p ∂heightMeasure)=
      ∫w : ℝ,∫z : ℝ,∫x : ℝ in -H..H,f ((x,z),w) := by
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  have hi : Integrable (E.indicator f) heightMeasure := (integrable_indicator_iff hE).mpr hf
  rw [←integral_indicator hE,integral_prod_symm _ hi]
  apply integral_congr_ae
  filter_upwards [hi.prod_left_ae] with w hw
  rw [integral_prod_symm _ hw]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  have heq : (fun x : ℝ=>(E.indicator f) ((x,z),w))=(Icc (-H) H).indicator (fun x=>f ((x,z),w)) := by
    funext x
    simp only [Set.indicator_apply,E,Set.mem_ofPred_eq,Set.mem_Icc,abs_le]
  dsimp only
  rw [heq,integral_indicator measurableSet_Icc,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le (by linarith)]

variable {ι : Type*} [Fintype ι]

theorem rowIntegral_buffered_transport {K : ℕ}
    (e a B H : ℝ) (i : ℕ) (he : 0<e) (he' : e<1/1000)
    (ha : (51/100:ℝ)≤a) (haTop : a≤1) (hB : 2<B) (hH0 : 0≤H) (hH : H≤(3*i+2:ℕ)*B)
    (S : Finset (Ideal O)) (hS : SourceExclusions S) (hmax : ∀P∈S,P.IsMaximal)
    (hfirst : FirstTail (4*e) S) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hP : Function.Injective P)
    (hPS : ∀j,(P j).val∉S) (η : Character) (u : FreeRow) (hu : u.val≠1) (ψ : ι→Character)
    (hbin : detectorMaximum (sourceDetectorFamily S hS.prime η u ψ) (3*(i+1:ℕ)*B)<a+2*e)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Icc a0 b0) (hW1 : Function.support W1⊆Icc a1 b1)
    (X Y Z : ℝ) (hX : 0<X) (hY : 0<Y) (hZ : 0<Z) :
    let F := fun x w z=>continuedPhysicalRowKernel S hS hmax P hPS η u W0 W1 X Y Z x w z
    let E : Set HeightSpace := {t | |t.1.1|≤H}
    rowIntegral η S (calibrationForSet S hmax)
      (fun j=>CompletedGauss.primaryGenerator (P j).val) W0 W1 X Y Z u=
      ((1/(2*Real.pi):ℝ):ℂ)^3 *
        ((∫tw : ℝ,∫tz : ℝ,
          (∫tx : ℝ in -H..H,F ((((a+16*e):ℝ):ℂ)+tx*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))+
          I*((∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+(-H)*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))-
            (∫v : ℝ in (a+16*e)..2,F ((v:ℂ)+H*I) ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I))))+
          ∫p : HeightSpace in Eᶜ,continuedRowOnLines S hS hmax P hPS η u W0 W1 X Y Z 2 (1-a-6*e) (17/50) p ∂heightMeasure) := by
  dsimp only
  obtain ⟨hi,hrow⟩ := rowIntegral_central_start a e ha haTop he he' S hS hmax hfirst P hP hPS η u hu
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 X Y Z hX hY hZ
  let E : Set HeightSpace := {t | |t.1.1|≤H}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  rw [hrow,←integral_add_compl hE hi]
  congr 2
  rw [height_slab_integral_wzx _ H hH0 hi.integrableOn]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tw
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro tz
  have hHT : H≤3*(i+1:ℕ)*B := by
    apply hH.trans
    have hn : (3*i+2:ℕ)≤3*(i+1) := by omega
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast hn) (by linarith)
  simpa only [continuedRowOnLines,Complex.ofReal_div,Complex.ofReal_ofNat] using source_buffered_x_rectangle S hS hmax P hPS η u ψ B a e i he he' ha haTop hfirst hbin W0 W1 X Y Z hZ
    ((((1-a-6*e):ℝ):ℂ)+tw*I) ((17/50:ℂ)+tz*I) (by simp) (by norm_num) 2 H (by linarith) hH0 hHT

end SevenEighths.ProbeHighRowFamily

end

end OAI
end OAIOriginalModule2607

/-! Original module: OAI.NumberTheory.DirichletL.PrimeRows.PhysicalDyad
Source SHA256: e1745d3c5f6464d88e7b408d91dfe01b5395f53a46e2a805313e5addad6427f5
Original private names preserved (no fully qualified collisions in closure). -/
section OAIOriginalModule2608



namespace OAI

noncomputable section
open scoped Classical BigOperators
open MeasureTheory Set Complex
namespace SevenEighths.ProbeHighRowFamily
open HeckeFamily HeckeInverseAmplification ProbePhysical ProbeMellinBoundary
local notation "O" => HeckeFamily.O

def finitePhysicalRows {K : ℕ} (S : Finset (Ideal O)) (hmax : ∀P∈S,P.IsMaximal)
    (η : Character) (R : Finset FreeRow) (T : Fin K→Finset _root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal)
    (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ) (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z : ℝ) : ℂ :=
  ∑u∈R,∑P:(∀i,T i),(∏i,W i (((P i).val.val.absNorm:ℝ)/Yp i))*
    rowIntegral η S (calibrationForSet S hmax)
      (fun i=>CompletedGauss.primaryGenerator (P i).val.val) W0 W1 X Y Z u

def weightedRowOnLines {K : ℕ} (S : Finset (Ideal O)) (hS : SourceExclusions S)
    (hmax : ∀P∈S,P.IsMaximal) (P : Fin K→_root_.OAI.SevenEighths.ProbePhysical.PrimeIdeal) (hPS : ∀i,(P i).val∉S)
    (η : Character) (u : FreeRow) (W : Fin K→ℝ→ℂ) (Yp : Fin K→ℝ)
    (W0 W1 : SchwartzMap ℝ ℂ) (X Y Z σ υ r : ℝ) (t : HeightSpace) : ℂ :=
  sourceMellinWeight W0 W1 X Y Z ((σ:ℂ)+t.1.1*I) ((υ:ℂ)+t.2*I) ((r:ℂ)+t.1.2*I)*
