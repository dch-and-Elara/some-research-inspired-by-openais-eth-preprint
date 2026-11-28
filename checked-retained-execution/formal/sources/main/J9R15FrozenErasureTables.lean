import J6R14SpecializedBoxPackedFile
import J6R11IntegralRetained
import J9R14LowPrecisionMenu

/-! Original clone equality tables and the disjoint remainder on the same J7 file. -/
namespace J9R15FrozenErasure
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral
open J7SourceLabels J7SeatSource J7ToJ8Incidence J7ToJ8Layout
open LiteralPortCompiler J6R14SpecializedBox
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R14LowPrecisionTiedCube

noncomputable section
set_option maxHeartbeats 1200000
set_option linter.unusedSectionVars false

/-- The usual literal equality table, with one clause pair per other port.
Including the anchor's tautological pair is harmless. -/
def star {P : Type*} (a : P) (l : List P) : CNF P :=
  (l.map (equality a)).flatten

theorem star_truth {R P : Type*} [MulZeroOneClass R] (a : P) (l : List P) (x : P → Bool) :
    (truth (star a l) x:R) = if ∀ u∈l, x a=x u then 1 else 0 := by
  induction l with
  | nil => simp [star,truth,satisfied,indicator]
  | cons b l ih =>
    rw [show star a (b::l)=equality a b ++ star a l from rfl,truth_append,ih,truth_equality]
    simp only [List.mem_cons,forall_eq_or_imp]
    by_cases h : x a=x b <;> simp [h]

variable {A Pair Row Col W : Type} [LinearOrder A]
variable [Fintype A] [Fintype Pair] [Fintype Row] [Fintype Col] [Fintype W] {t b : ℕ}
variable (row : W → Row) (col : W → OrdinaryColumn Pair Col)
variable (two : ∀ r, Nat.card {w : W // row w=r}=2)
variable (state : DState A Pair Row Col t)
variable (seat : Wire Pair W ↪ Physical (t+1) b A)
variable (preserve : ∀ w, physicalCell (J7SeatPacking.balancedMask (t+1) b) (seat w)
  = wordLabel row col state w)

local notation "E" => Wire Pair W
local notation "V" => Pin Pair ⊕ OrdinaryColumn Pair Col
local notation "N" => J7R13.network row col
local notation "D" => physicalLayout row col two state seat preserve
local notation "ER" => rowWire (Pair:=Pair) row two

def basePort (p : Pin Pair) : Ports col (.inl p) := ⟨.inl (p,true),rfl⟩

def canonicalOld (F : J8Physical.OldTables D) : J8Physical.OldTables D :=
  fun g v => match v with
    | ⟨.inl p,_⟩ => star (basePort col p) (Finset.univ : Finset (Ports col (.inl p))).toList
    | ⟨.inr q,hq⟩ => F g ⟨.inr q,hq⟩

theorem canon_exact_eq (F : J8Physical.OldTables D) (p : Pin Pair) (x : Ports col (.inl p) → Bool)
    {R : Type*} [MulZeroOneClass R] :
    (truth (canonicalOld row col two state seat preserve F ((D).colLabel (.inl p)) ⟨.inl p,rfl⟩) x:R) =
      if ∀ u v, x u=x v then 1 else 0 := by
  change (truth (star (basePort col p) (Finset.univ : Finset (Ports col (.inl p))).toList) x:R) = _
  rw [star_truth]
  have h : (∀ u ∈ (Finset.univ : Finset (Ports col (.inl p))).toList, x (basePort col p)=x u) ↔
      ∀ u v, x u=x v := by
    constructor
    · intro H u v
      exact (H u (by simp)).symm.trans (H v (by simp))
    · exact fun H u _ => H _ u
  by_cases hh : ∀ u v, x u=x v
  · rw [if_pos (h.mpr hh),if_pos hh]
  · rw [if_neg (fun h' => hh (h.mp h')),if_neg hh]

def cloneHosts : Finset (Option V) :=
  Finset.univ.image (fun p : Pin Pair => some (.inr (.inl p)))

theorem mem_cloneHosts_iff (v : Option V) :
    v ∈ cloneHosts (Pair:=Pair) (Col:=Col) ↔ ∃ p : Pin Pair, v = some (.inr (.inl p)) := by
  constructor
  · intro h
    obtain ⟨p,_,hp⟩ := Finset.mem_image.mp h
    exact ⟨p,hp.symm⟩
  · rintro ⟨p,rfl⟩
    exact Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩

theorem cloneHosts_card : (cloneHosts (Pair:=Pair) (Col:=Col)).card=2*Fintype.card Pair := by
  unfold cloneHosts
  rw [Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj (Sum.inr.inj (Option.some.inj h))),
    Finset.card_univ,Fintype.card_prod,Fintype.card_fin,mul_comm]

/-- All owners come from original J7 edges. Padding has no owner. -/
def seatOwner (s : Physical (t+1) b A) : Option V :=
  if h : ∃ e, seat e=s then some (colNode col (Classical.choose h)) else none

theorem seatOwner_edge (e : E) : seatOwner col seat (seat e) = some (colNode col e) := by
  have h : ∃ e', seat e'=seat e := ⟨e,rfl⟩
  rw [seatOwner,dif_pos h,seat.injective (Classical.choose_spec h)]

local notation "D'" => nativeSeats (fun e => seat e) (fun e => seat e)
local notation "old" => cloneHosts (Pair:=Pair) (Col:=Col)
local notation "OWN" => seatOwner col seat
variable {n : ℤ}
local notation "K" => kept D' old OWN n
local notation "PR" => protectedOwner D' old OWN n

def select (v : V) : Option (FreeOwner D' old OWN n) :=
  if h : some v∈K then some ⟨some v,h⟩ else none

theorem select_inj {v w : V} {u : FreeOwner D' old OWN n}
    (hv : select col seat (n:=n) v=some u) (hw : select col seat (n:=n) w=some u) : v=w := by
  unfold select at hv hw
  split at hv
  · split at hw
    · exact Option.some.inj ((congrArg Subtype.val (Option.some.inj hv)).trans
        (congrArg Subtype.val (Option.some.inj hw)).symm)
    · cases hw
  · cases hv

theorem protected_select (e : E) : PR e=select col seat (n:=n) (colNode col e) := by
  unfold protectedOwner select
  simp only [nativeSeats,seatOwner_edge]

theorem clonePorts_supply (u : Option V) (hu : u∈old) : ∃ e : E, OWN (seat e)=u := by
  obtain ⟨p,rfl⟩ := (mem_cloneHosts_iff u).mp hu
  exact ⟨.inl (p,true),seatOwner_edge col seat _⟩

theorem selected_clone {v : V} {u : FreeOwner D' old OWN n}
    (h : select col seat (n:=n) v=some u) :
    ∃ p : Pin Pair, v=.inr (.inl p) := by
  unfold select at h
  split at h
  · rename_i hv
    have hu : some v∈old := by
      letI : DecidableEq (Option V) := Classical.decEq _
      exact (Finset.mem_sdiff.mp hv).1
    obtain ⟨p,hp⟩ := (mem_cloneHosts_iff _).mp hu
    exact ⟨p,Option.some.inj hp⟩
  · cases h

/-- Exact old table as read by the unchanged packed assignment (before
its indicator is interpreted in a particular receiver). -/
def rawFlag (F : J8Physical.OldTables D) (sign : Pin Pair → Bool)
    (v : Subdivision Pair Row ⊕ V) (X : E → Bool) : Bool :=
  orientedFlag D F sign v (assignment (orientedNetwork D) (X ∘ ER) v)

theorem frozen_flag (F : J8Physical.OldTables D) (sign : Pin Pair → Bool) (f : ℤ[X])
    (ell p₀ : ℕ) (hf : f.Monic) (hp₀ : 0<p₀) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (v : Subdivision Pair Row⊕V) (x : E → Bool) :
    (sameSeatFile row col two state seat preserve f ell p₀ F sign v).frozen hf
        (assignment N x v) =
      (if rawFlag row col two state seat preserve F sign v x then 1 else 0 : IntRing f ell) := by
  rw [sameSeatFile_retained]
  exact J6R12Repack.canonical_lift_bool _ hp₀ _ hf hd _ hℓ _

theorem colFlag_congr (F : J8Physical.OldTables D) (sign : Pin Pair → Bool)
    (v : V) (X Y : E → Bool) (h : ∀ e, colNode col e=v  →  X e=Y e) :
    rawFlag row col two state seat preserve F sign (.inr v) X =
      rawFlag row col two state seat preserve F sign (.inr v) Y := by
  apply congrArg (orientedFlag D F sign (.inr v))
  funext q
  rcases q with ⟨q,hq⟩
  cases q with
  | inl e => cases hq
  | inr e =>
    apply h
    rw [← owner_layout row col two state seat preserve]
    exact Sum.inr.inj hq

theorem cloneFlag (F : J8Physical.OldTables D) (sign : Pin Pair → Bool) (p : Pin Pair) (X : E → Bool)
    {R : Type*} [MulZeroOneClass R] :
    (if rawFlag row col two state seat preserve
      (canonicalOld row col two state seat preserve F) sign (.inr (.inr (.inl p))) X
      then 1 else 0 : R) =
      if ∀ e e', colNode col e=.inr (.inl p)  →  colNode col e'=.inr (.inl p)  →  X e=X e'
      then 1 else 0 := by
  let u : Ports col (.inl p) → Bool := fun i =>
    X (ER (J8Physical.ordinaryWire D ⟨.inl p,i⟩))
  change (truth (canonicalOld row col two state seat preserve F ((D).colLabel (.inl p))
    ⟨.inl p,rfl⟩) u:R)=_
  rw [canon_exact_eq]
  have hu (i : Ports col (.inl p)) : ER (J8Physical.ordinaryWire D ⟨.inl p,i⟩)=i.val := by
    change ER (((ER).trans (colWire col).symm).symm (.inr ⟨.inl p,i⟩))=_
    simp only [Equiv.symm_trans_apply,Equiv.apply_symm_apply]
    rfl
  simp only [u,hu]
  have he : (∀ i j : Ports col (.inl p), X i.val=X j.val) ↔
      ∀ e e', colNode col e=.inr (.inl p)  →  colNode col e'=.inr (.inl p)  →  X e=X e' :=
    ⟨fun h e e' he he' => h ⟨e,he⟩ ⟨e',he'⟩,fun h i j => h i.val j.val i.property j.property⟩
  by_cases hh : ∀ e e', colNode col e=.inr (.inl p) → colNode col e'=.inr (.inl p) → X e=X e'
  · rw [if_pos (he.mpr hh),if_pos hh]
  · rw [if_neg (fun h' => hh (he.mp h')),if_neg hh]

#print axioms star_truth
#print axioms canon_exact_eq
#print axioms cloneHosts_card
#print axioms seatOwner_edge
#print axioms protected_select
#print axioms clonePorts_supply
#print axioms selected_clone
#print axioms frozen_flag
#print axioms colFlag_congr
#print axioms cloneFlag

end
end J9R15FrozenErasure
