import FirstDigit
import Mathlib.Tactic

/-! Explicit disjoint union of the P10 three-packet literal witnesses.
Exact finite source geometry and the whole-menu cardinal follow from the
verified local digit, without treating an arbitrary per-triple map as free. -/

namespace P10TripleUnion
open scoped BigOperators
noncomputable section

variable {T : Type*} [Fintype T]

abbrev Row (T : Type*) (L : ℕ) := T × Fin L
abbrev Wire (T : Type*) (L : ℕ) := Row T L × Fin 3
abbrev Col (T : Type*) (L : ℕ) := Wire T L

def rowOf {L : ℕ} : Wire T L → Row T L := Prod.fst
def colOf {L : ℕ} : Wire T L → Col T L := id

omit [Fintype T] in
theorem row_degree {L : ℕ} (r : Row T L) :
    Nat.card {w : Wire T L // rowOf w = r} = 3 := by
  let e : {w : Wire T L // rowOf w = r} ≃ Fin 3 :=
    { toFun := fun w => w.val.2
      invFun := fun j => ⟨(r,j),rfl⟩
      left_inv := by rintro ⟨⟨r',j⟩,h⟩; change r'=r at h; subst r'; rfl
      right_inv := by intro j; rfl }
  rw [Nat.card_congr e, Nat.card_fin]

omit [Fintype T] in
theorem col_degree {L : ℕ} (c : Col T L) :
    Nat.card {w : Wire T L // colOf w = c} = 1 := by
  let e : {w : Wire T L // colOf w = c} ≃ Unit :=
    { toFun := fun _ => ()
      invFun := fun _ => ⟨c,rfl⟩
      left_inv := by rintro ⟨w,h⟩; change w=c at h; subst w; rfl
      right_inv := by rintro ⟨⟩; rfl }
  rw [Nat.card_congr e]
  simp

theorem physical_wires (L : ℕ) : Nat.card (Wire T L) = 3*L*Fintype.card T := by
  simp [Wire, Row, Nat.card_eq_fintype_card, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]

variable [DecidableEq T]
variable {F : Type*} [CommSemiring F]

/-- Outer digit of the actual full product of disjoint packet triples:
select the one addressed target and use the original baseline on all
other triples. The supplied baselines are proved equal to one by the
local original-table lemma in the intended P10 packing. -/
def globalMenu (ψ : ZMod 2 →+* F) (z : F) (q B : ℕ)
    {S : Type*} [Fintype S] (toTriple : S → T)
    (base : T → FirstDigit.Address q B → F)
    (w : S → FirstDigit.Address q B → Bool)
    (a : S × FirstDigit.Address q B) : F :=
  FirstDigit.menu ψ z q B (w a.1) a.2 *
    ∏ u ∈ (Finset.univ : Finset T).erase (toTriple a.1), base u a.2

theorem global_reads (ψ : ZMod 2 →+* F) (z : F) (q B : ℕ)
    {S : Type*} [Fintype S] (toTriple : S → T)
    (base : T → FirstDigit.Address q B → F) (hbase : ∀ t a, base t a = 1)
    (w : S → FirstDigit.Address q B → Bool) (a : S × FirstDigit.Address q B) :
    globalMenu ψ z q B toTriple base w a = z * ψ (FirstDigit.bit (ZMod 2) (w a.1 a.2)) := by
  simp [globalMenu, hbase, FirstDigit.menu_reads_exact]

theorem global_injective (ψ : ZMod 2 →+* F) (z : F) (hz : z ≠ 0) (q B : ℕ)
    {S : Type*} [Fintype S] (toTriple : S → T)
    (base : T → FirstDigit.Address q B → F) (hbase : ∀ t a, base t a = 1) :
    Function.Injective (globalMenu ψ z q B toTriple base) := by
  intro w w' e
  funext s a
  have h := congrFun e (s,a)
  rw [global_reads ψ z q B toTriple base hbase, global_reads ψ z q B toTriple base hbase] at h
  exact FirstDigit.probe_reads_bit_injectively ψ z hz h

theorem global_menu_card (ψ : ZMod 2 →+* F) (z : F) (hz : z ≠ 0) (q B : ℕ)
    {S : Type*} [Fintype S] (toTriple : S → T)
    (base : T → FirstDigit.Address q B → F) (hbase : ∀ t a, base t a = 1) :
    Nat.card (Set.range (globalMenu ψ z q B toTriple base)) =
      2^(Fintype.card S * (q*B-2*B)) := by
  classical
  rw [Nat.card_range_of_injective (global_injective ψ z hz q B toTriple base hbase)]
  have hp : (q-2)*B = q*B-2*B := Nat.sub_mul _ _ _
  rw [← hp]
  simp [FirstDigit.Address, Nat.card_eq_fintype_card, ← pow_mul, Nat.mul_comm]

/-- Exact algebraic P10 exponent from the finite physical cardinalities.
The remaining source proof must instantiate the eligible ratio. -/
theorem exponent_matches (r q B M eligible total : ℕ)
    (hr : 0 < r) (hq : 2 ≤ q)
    (hRatio : r*eligible = (r-1)*total)
    (hM : M = 3*(q*B)*total) :
    ((eligible*(q*B-2*B) : ℕ) : ℚ) =
      (1-1/(r:ℚ))/3*(1-4/(2*(q:ℚ)))*M := by
  have hr' : (0:ℚ) < r := by exact_mod_cast hr
  have hq' : (0:ℚ) < q := by exact_mod_cast (by omega : 0<q)
  have hsub : 2*B ≤ q*B := Nat.mul_le_mul_right B hq
  have hrsub : 1 ≤ r := by omega
  have he : (r:ℚ)*(eligible:ℚ) = ((r:ℚ)-1)*(total:ℚ) := by exact_mod_cast hRatio
  have hE : (eligible:ℚ) = ((r:ℚ)-1)*(total:ℚ)/(r:ℚ) :=
    (eq_div_iff hr'.ne').2 (by nlinarith)
  have hm : (M:ℚ) = 3*((q:ℚ)*(B:ℚ))*(total:ℚ) := by exact_mod_cast hM
  push_cast [Nat.cast_sub hsub]
  rw [hm, hE]
  field_simp [hr'.ne', hq'.ne']
  ring

/-- The baseline here is the actual old literal row contraction at the
shifted pin arguments, not an arbitrary per-packet scalar. -/
def shiftBaseline (q B : ℕ) (s : ℕ → Bool) (a : FirstDigit.Address q B) : ZMod 2 :=
  ∏ x ∈ Finset.range (q*B),
    FirstDigit.row (s x)
      (FirstDigit.lowPin B (q*B) (x+FirstDigit.eligibleTime B a.1))
      (FirstDigit.highPin B (q*B) (x+FirstDigit.eligibleTime B a.1)) 0

theorem shiftBaseline_one (q B : ℕ) (s : ℕ → Bool) (a : FirstDigit.Address q B) :
    shiftBaseline q B s a = 1 := by
  unfold shiftBaseline
  refine Finset.prod_eq_one fun x _ => ?_
  rw [FirstDigit.row_formula, FirstDigit.low_shift_zero _ _ _ _
    (FirstDigit.time_interior q B a.1).1]
  ring

theorem actual_global_menu_card (ψ : ZMod 2 →+* F) (z : F) (hz : z ≠ 0) (q B : ℕ)
    {S : Type*} [Fintype S] (toTriple : S → T) (s : T → ℕ → Bool) :
    Nat.card (Set.range (globalMenu ψ z q B toTriple
      (fun t a => ψ (shiftBaseline q B (s t) a)))) =
      2^(Fintype.card S * (q*B-2*B)) := by
  apply global_menu_card ψ z hz
  intro t a
  rw [shiftBaseline_one, map_one]

/-- A single physical row-sign assignment used for every address. -/
def configuredSigns (q B : ℕ) {S : Type*} (toTriple : S → T)
    (w : S → FirstDigit.Address q B → Bool) (t : T) : ℕ → Bool := by
  classical
  exact if h : ∃ a, toTriple a = t then FirstDigit.signWord q B (w (Classical.choose h))
    else fun _ => false

omit [Fintype T] [DecidableEq T] in
theorem configuredSigns_at (q B : ℕ) {S : Type*} (toTriple : S → T)
    (ht : Function.Injective toTriple) (w : S → FirstDigit.Address q B → Bool) (a : S) :
    configuredSigns q B toTriple w (toTriple a) = FirstDigit.signWord q B (w a) := by
  classical
  unfold configuredSigns
  split_ifs with h
  · rw [ht (Classical.choose_spec h)]
  · exact False.elim (h ⟨a,rfl⟩)

def configuredMenu (ψ : ZMod 2 →+* F) (z : F) (q B : ℕ)
    {S : Type*} (toTriple : S → T) (w : S → FirstDigit.Address q B → Bool)
    (a : S × FirstDigit.Address q B) : F :=
  let s := configuredSigns q B toTriple w
  z * ψ (FirstDigit.singletonDigit (q*B) B (FirstDigit.eligibleTime B a.2.1)
    a.2.2 (s (toTriple a.1))) *
    ∏ t ∈ (Finset.univ : Finset T).erase (toTriple a.1), ψ (shiftBaseline q B (s t) a.2)

theorem configuredMenu_exact (ψ : ZMod 2 →+* F) (z : F) (q B : ℕ)
    {S : Type*} (toTriple : S → T) (ht : Function.Injective toTriple)
    (w : S → FirstDigit.Address q B → Bool) (a : S × FirstDigit.Address q B) :
    configuredMenu ψ z q B toTriple w a = FirstDigit.menu ψ z q B (w a.1) a.2 := by
  simp [configuredMenu, configuredSigns_at q B toTriple ht, shiftBaseline_one, FirstDigit.menu]

theorem configuredMenu_card (ψ : ZMod 2 →+* F) (z : F) (hz : z ≠ 0) (q B : ℕ)
    {S : Type*} [Fintype S] (toTriple : S → T) (ht : Function.Injective toTriple) :
    Nat.card (Set.range (configuredMenu ψ z q B toTriple)) =
      2^(Fintype.card S * (q*B-2*B)) := by
  have e :
      configuredMenu ψ z q B toTriple = globalMenu ψ z q B toTriple (fun _ _ => 1) := by
    funext w a
    rw [configuredMenu_exact ψ z q B toTriple ht]
    simp [globalMenu]
  rw [e]
  exact global_menu_card ψ z hz q B toTriple _ (fun _ _ => rfl)

#print axioms configuredSigns_at
#print axioms configuredMenu_exact
#print axioms configuredMenu_card
#print axioms actual_global_menu_card
#print axioms shiftBaseline_one
#print axioms row_degree
#print axioms col_degree
#print axioms physical_wires
#print axioms global_reads
#print axioms global_injective
#print axioms global_menu_card
#print axioms exponent_matches

end
end P10TripleUnion