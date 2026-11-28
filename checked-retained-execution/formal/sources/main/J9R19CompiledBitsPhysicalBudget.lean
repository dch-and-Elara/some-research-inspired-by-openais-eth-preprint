
import J9R19CompiledBitsPhysical
import J9R19CompiledBitsStencil

/-! Uniform input-size word bounds for the actual integer fractions that
feed the compiled Lagrange stage. Coarse polynomial exponents deliberately
avoid the much sharper printed 10M-bit *raw* receiver bound. -/
namespace J9R19CompiledBits
open scoped BigOperators Classical
open J8Physical J8EndToEnd J8J9Grouped LiteralPortCompiler
noncomputable section
set_option linter.unusedSectionVars false

theorem Fits.natOfLe (a w : ℕ) (h : a≤w) : Fits w (a:ℤ) := by
  unfold Fits
  have ex (k : ℕ) : k≤2^k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hp : 0<2^k := by positivity
      rw [pow_succ]
      omega
  simpa only [Int.natAbs_natCast] using h.trans (ex w)

variable {Packet R S V G : Type*} {P : V→Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G] [Fintype Packet]
variable [∀ v, Fintype (P v)]

def massBudget (L v : ℕ) : ℕ := (2*L+10)*v
def momentBudget (L v M b : ℕ) : ℕ := massBudget L v + (2*L+10) + L*b + M + L
def slopeBudget (L v b : ℕ) : ℕ := massBudget L v + 4*L + b + (L+3)*(b+1)
def clearBudget (B M : ℕ) : ℕ := B + (B+1)*M
def acquisitionBudget (L v M groups b : ℕ) : ℕ :=
  clearBudget (slopeBudget L v b) M + massBudget L v * groups + momentBudget L v M b + 1

theorem ordinal_fits (w : Wire R) : Fits L (ordinal d w : ℤ) := by
  apply Fits.natOfLe
  unfold ordinal
  have hh := (d.seat w).2.isLt
  omega

theorem coordinateInt_fits (a : S) (j : Fin (Fintype.card (PinTile d a))) :
    Fits L (coordinateInt d a j) := ordinal_fits d _

theorem oldIntMoment_fits (e : EndpointSeating d) (he : Even L) (hL : 1≤L) (F : OldTables d)
    (g : G) (q : Sigma (LocalPort d (g:=g))) (sparse : ∀ v, Fintype.card (P v)≤3) :
    Fits (2*L+10+massBudget L (Fintype.card V)) (oldIntMoment d e he F g q) := by
  unfold oldIntMoment
  have h1 := fsum_fits (Finset.univ : Finset (LocalPort d q.1→Bool))
    (fun z => actualIntWeight d e he F g none q.1 z * bitZ (z q.2)) (b:=2*L+2)
    (fun z _ => by simpa only [Nat.add_zero] using
      (actualIntWeight_fits d e he hL F g none q.1 z).mul (bitZ_fits (z q.2)))
  have hcard : (Finset.univ : Finset (LocalPort d q.1→Bool)).card ≤8 := by
    simp only [Finset.card_univ,Fintype.card_fun,Fintype.card_bool]
    exact Nat.pow_le_pow_right (by decide) (sparse q.1.val)
  have h2 := fprod_fits (Finset.univ.erase q.1) (actualIntMass d e he F g none)
    (fun v _ => actualIntMass_fits d e he hL F g none v (sparse v.val))
  have hc : (Finset.univ.erase q.1).card≤Fintype.card V := (Finset.card_le_univ _).trans
    (Fintype.card_le_of_injective (f:=Subtype.val) Subtype.val_injective)
  exact (h1.mono (by omega)).mul (h2.mono (Nat.mul_le_mul_left _ hc))

theorem backgroundInt_fits (e : EndpointSeating d) (he : Even L) (hL : 1≤L) (F : OldTables d)
    (a : S) (b : ℕ) (sparse : ∀ v, Fintype.card (P v)≤3) :
    Fits (momentBudget L (Fintype.card V) (Fintype.card (Wire R)) b)
      (backgroundInt d e he F a b) := by
  have hh (q : OldTile d a) :=
    ((ordinal_fits d (ordinaryWire d q.1)).pow b).mul
      (oldIntMoment_fits d e he hL F (d.pinLabel a) (tileOldInSource d q) sparse)
  have h := fsum_fits Finset.univ _ (fun q _ => hh q)
  have hc := J9R18Compiled.oldTile_card_le_wire_card d a
  exact h.mono (by simp only [Finset.card_univ,momentBudget]; omega)

theorem pinMomentZ_fits (he : Even L) (a : S)
    (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool) :
    Fits (L*(b:ℕ)+L) (pinMomentZ d a b sign) := by
  have h := fsum_fits (Finset.univ : Finset (Fin (Fintype.card (PinTile d a)))) _
    (fun j _ => (bitZ_fits (sign (pinEnumeration d a j).1)).mul
      ((coordinateInt_fits d a j).pow (b:ℕ)))
  have hL := pins_per_tile d a he
  exact h.mono (by simp only [Finset.card_univ,Fintype.card_fin,Nat.zero_add]; omega)

theorem integerDenominator_fits (hL : 2<L) (a : S) (j : TargetPorts d a) :
    Fits (L+3) (integerDenominator d a j) := by
  have hs := Fits.natOfLe (d.seat (j.1.1,j.2)).2.val L (d.seat (j.1.1,j.2)).2.isLt.le
  have hp : (d.seat (pinWire d a)).2.val%2≤L := by
    have h := Nat.mod_lt (d.seat (pinWire d a)).2.val (by decide : 0<2)
    omega
  have ht := Fits.natOfLe _ _ hp
  have hv := (Fits.natOfLe L L le_rfl).sub (Fits.one L)
  change Fits (L+3) (((L:ℤ)-1) - (((d.seat (pinWire d a)).2.val % 2 : ℕ) : ℤ) +
    ((d.seat (j.1.1,j.2)).2.val:ℤ))
  exact (hv.sub (ht.mono (by omega))).add (hs.mono (by omega))

theorem targetFraction_fits (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d)
    (a : S) (b : ℕ) (j : TargetPorts d a) (sparse : ∀ v, Fintype.card (P v)≤3) :
    (targetFraction d e he F a b j).fits (slopeBudget L (Fintype.card V) b) := by
  have ht : Fits (2*L) (2*(L:ℤ)) := by
    have h := Fits.natOfLe (2*L) (2*L) le_rfl
    simpa using h
  have htwo : Fits 1 (2:ℤ) := by norm_num [Fits]
  have hpow := htwo.pow b
  have hh := groupIntMass_fits d e he (show 1≤L by omega) F _ (some j) sparse
  have hnum := (((kernel_fits L (by omega)).mul ht).mul hpow).mul hh
  have hden := (integerDenominator_fits d hL a j).pow (b+1)
  exact ⟨hnum.mono (by simp only [massBudget,slopeBudget,Nat.one_mul] at *; omega),
    hden.mono (by simp only [slopeBudget]; omega)⟩

theorem targetClear_width (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d)
    (a : S) (b : ℕ) (sparse : ∀ v, Fintype.card (P v)≤3) :
    let B := clearBudget (slopeBudget L (Fintype.card V) b) (Fintype.card (Wire R))
    (targetClear d e he F a b).result.fits B ∧ (∀ z∈(targetClear d e he F a b).words, Fits B z) := by
  let xs := (groupedTargets d a).toList.map (targetFraction d e he F a b)
  let w := slopeBudget L (Fintype.card V) b
  have h (p : Fraction) (hp : p∈xs) : p.fits w := by
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp hp
    exact targetFraction_fits d e he hL F a b j sparse
  have hn : xs.length≤Fintype.card (Wire R) := by
    simpa [xs] using J9R18Compiled.groupedTargets_card_le_wire_card d a
  have wle : w+(w+1)*xs.length≤clearBudget w (Fintype.card (Wire R)) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ hn) _
  change (clearRun xs).result.fits _ ∧ ∀ z∈(clearRun xs).words, Fits _ z
  have h' := clearRun_result_fits xs h
  exact ⟨⟨h'.1.mono wle,h'.2.mono wle⟩,fun z hz => (clearRun_fits xs h z hz).mono wle⟩

theorem targetClear_work (e : EndpointSeating d) (he : Even L) (F : OldTables d)
    (a : S) (b : ℕ) :
    (targetClear d e he F a b).work ≤ 5*Fintype.card (Wire R) := by
  unfold targetClear
  exact (clearRun_work _).trans (by
    simp only [List.length_map,Finset.length_toList]
    exact Nat.mul_le_mul_left _ (J9R18Compiled.groupedTargets_card_le_wire_card d a))

theorem physicalFractions_width (e : EndpointSeating d) (he : Even L) (hL : 2<L) (F : OldTables d)
    (a : S) (b : Fin (Fintype.card (PinTile d a))) (sign : S→Bool)
    (sparse : ∀ v, Fintype.card (P v)≤3) :
    let B := acquisitionBudget L (Fintype.card V) (Fintype.card (Wire R)) (Fintype.card G) b
    let r := physicalFractions d e he F a b sign
    r.first.fits B ∧ r.scale.fits B ∧ r.background.fits B := by
  dsimp only [physicalFractions]
  let A := massBudget L (Fintype.card V)
  let w := momentBudget L (Fintype.card V) (Fintype.card (Wire R)) b
  let T := clearBudget (slopeBudget L (Fintype.card V) b) (Fintype.card (Wire R))
  let Gp := A*Fintype.card G
  let E := T+Gp+w+1
  have hs : Fits A (groupIntMass d e he F (d.pinLabel a) none) :=
    groupIntMass_fits d e he (by omega) F _ none sparse
  have hb : Fits w (backgroundInt d e he F a b) :=
    backgroundInt_fits d e he (by omega) F a b sparse
  have hp := pinMomentZ_fits d he a b sign
  have hsrc := hb.add ((hs.mul hp).mono (show A+(L*(b:ℕ)+L)≤w by
    dsimp only [A,w,momentBudget]; omega))
  have hsib : Fits Gp (siblingsZ d e he F a) := by
    apply (fprod_fits _ _ (fun g _ => groupIntMass_fits d e he (by omega) F g none sparse)).mono
    exact Nat.mul_le_mul_left _ (Finset.card_le_univ _)
  have ht : (targetClear d e he F a b).result.fits T := (targetClear_width d e he hL F a b sparse).1
  have out := (hsib.mul hsrc).mul ht.1
  have outScale := (hsib.mul hs).mul ht.1
  have hA : A≤w := by dsimp only [A,w,momentBudget]; omega
  have hT : T≤E := by omega
  have hM : w≤E := by omega
  have hG : Gp+A+T≤E := by omega
  refine ⟨⟨out.mono ?_,ht.2.mono hT⟩,⟨outScale.mono hG,ht.2.mono hT⟩,⟨hb.mono hM,hs.mono (hA.trans hM)⟩⟩
  dsimp only [acquisitionBudget]
  change Gp+(w+1)+T ≤ E
  omega

#print axioms coordinateInt_fits
#print axioms oldIntMoment_fits
#print axioms backgroundInt_fits
#print axioms pinMomentZ_fits
#print axioms targetFraction_fits
#print axioms targetClear_width
#print axioms targetClear_work
#print axioms physicalFractions_width

end
end J9R19CompiledBits
