
import J9R15FrozenErasureGeneric
import J9R15FrozenErasurePrecision
import J6R14SpecializedBoxParentFile

/-! P7 factors the exact R17-oriented EntryFile, with its original
creation precision and all real old columns. The protected set is not
limited to the pin-adjacent clone. -/
namespace J9R20SameFile
open scoped BigOperators Classical Polynomial
open Polynomial P11FullPacking J6R9Recursive J6R10Repack J6R11Integral J6R10Integral
open J6R14SpecializedBox J8EndToEnd J8Physical LiteralPortCompiler
open J9R14LowPrecisionGeometry J9R14LowPrecisionSlots J9R14LowPrecisionTiedCube
open J9R15FrozenErasurePhysical J9R15FrozenErasureGeneric J9R15FrozenErasurePrecision
open J6R9PacketScopes DenominatorBudget

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2600000

variable {Packet R S V G : Type} {U : V→Type} {L : ℕ}
variable (d : Layout Packet R S V G U L)
variable [Fintype R] [Fintype S] [Fintype V] [Fintype G]
variable [(v : V) → Fintype (U v)] [LinearOrder G]
local notation "E" => J8Physical.Wire R
local notation "C" => S⊕V
local notation "N" => orientedNetwork d

def literalFlag (F : OldTables d) (sign : S→Bool) (v : R⊕C) (x : E→Bool) : Bool :=
  orientedFlag d F sign v (assignment N x v)

theorem literal_col_local (F : OldTables d) (sign : S→Bool)
    (v : C) (x y : E→Bool) (h : ∀ w, (N).col w=v → x w=y w) :
    literalFlag d F sign (.inr v) x = literalFlag d F sign (.inr v) y := by
  unfold literalFlag
  apply congrArg (orientedFlag d F sign (.inr v))
  funext w
  rcases w with ⟨w,hw⟩
  cases w with
  | inl r => cases hw
  | inr u => exact h u (Sum.inr.inj hw)

theorem literal_frozen (F : OldTables d) (sign : S→Bool) (f : ℤ[X])
    (ell c : ℕ) (hc : 0<c) (hf : f.Monic) (hd : 0<f.natDegree) (hℓ : 0<ell)
    (v : R⊕C) (x : E→Bool) :
    (orientedEntryFile d f ell c F sign v).frozen hf (assignment N x v) =
       if literalFlag d F sign v x then 1 else 0 := by
  change canonicalLift c f hf ell (if literalFlag d F sign v x then 1 else 0) = _
  exact J6R12Repack.canonical_lift_bool c hc f hf hd ell hℓ _

def WireCloneLaw (F : OldTables d) (sign : S→Bool) (old : Finset (Option C)) : Prop :=
  ∀ v : V, some (.inr v)∈old → ∀ x : E→Bool,
    literalFlag d F sign (.inr (.inr v)) x=true ↔
      ∀ w w', (N).col w=.inr v → (N).col w'=.inr v → x w=x w'

/-- The relevant mathematical assumption is literal old-clone equality,
not a particular syntax or a replacement EntryFile. -/
def LocalCloneLaw (F : OldTables d) (old : Finset (Option C)) : Prop :=
  ∀ v : V, some (.inr v)∈old → ∀ x : U v→Bool,
    satisfied (F (d.colLabel v) ⟨v,rfl⟩) x=true ↔ ∀ j k, x j=x k

theorem standard_port_owner (v : V) (j : U v) :
    (N).col (ordinaryWire d ⟨v,j⟩)=.inr v := by
  simp [orientedNetwork,colOwner,ordinaryWire]

theorem standard_port_surjects_onto_owner (v : V) (w : E) (h : (N).col w=.inr v) :
    ∃ j : U v, w=ordinaryWire d ⟨v,j⟩ := by
  change Sum.map id Sigma.fst (d.column w) = .inr v at h
  rcases e : d.column w with p | ⟨u,j⟩
  · rw [e] at h; cases h
  · rw [e] at h
    have hv : u=v := Sum.inr.inj h
    subst u
    refine ⟨j,d.column.injective ?_⟩
    simp [ordinaryWire,e]

theorem local_implies_wire_law (F : OldTables d) (sign : S→Bool)
    (old : Finset (Option C)) (H : LocalCloneLaw d F old) :
    WireCloneLaw d F sign old := by
  intro v hv x
  change satisfied (F (d.colLabel v) ⟨v,rfl⟩) (fun j => x (ordinaryWire d ⟨v,j⟩))=true ↔ _
  rw [H v hv]
  constructor
  · intro h w w' hw hw'
    obtain ⟨j,rfl⟩ := standard_port_surjects_onto_owner d v w hw
    obtain ⟨j',rfl⟩ := standard_port_surjects_onto_owner d v w' hw'
    exact h j j'
  · intro h j k
    exact h _ _ (standard_port_owner d v j) (standard_port_owner d v k)

variable {a : ℕ} (P : PhysicalPacking (orientedNetwork d) a G)
variable (old : Finset (Option (S⊕V))) {t : ℤ}
local notation "ρ" => (fun w : E => P.seat w)
local notation "D" => nativeSeats ρ ρ

def nativeSeatOwner (s : Physical a P.copies G) : Option C :=
  dite (∃ w : E, P.seat w = s)
    (fun h => some ((N).col (Classical.choose h))) (fun _ => none)

theorem nativeSeatOwner_exact (w : E) :
    nativeSeatOwner d P (P.seat w)=some ((N).col w) := by
  have h : ∃ u : E, P.seat u=P.seat w := ⟨w,rfl⟩
  rw [nativeSeatOwner,dif_pos h,P.seat.injective (Classical.choose_spec h)]

local notation "OWN" => nativeSeatOwner d P
local notation "K" => kept D old OWN t
local notation "PR" => protectedOwner D old OWN t

def selected (v : C) : Option (FreeOwner D old OWN t) :=
  if h : some v∈K then some ⟨some v,h⟩ else none

theorem protected_selected (w : E) :
    PR w=selected d P (t:=t) old ((N).col w) := by
  unfold protectedOwner selected
  simp only [nativeSeats,nativeSeatOwner_exact]

theorem selected_of_kept (u : FreeOwner D old OWN t) {v : C} (h : u.val=some v) :
    selected d P (t:=t) old v=some u := by
  unfold selected
  rw [dif_pos (h ▸ u.property)]
  exact congrArg some (Subtype.ext h.symm)

theorem kept_of_selected {u : FreeOwner D old OWN t} {v : C}
    (h : selected d P (t:=t) old v=some u) : u.val=some v := by
  unfold selected at h
  split at h
  · exact congrArg Subtype.val (Option.some.inj h).symm
  · contradiction

theorem protected_owner_exact {u : FreeOwner D old OWN t} {v : C}
    (h : selected d P (t:=t) old v=some u) (w : E) :
    PR w=some u ↔ (N).col w=v := by
  rw [protected_selected]
  refine ⟨fun h' => Option.some.inj ((kept_of_selected d P old h').symm.trans
    (kept_of_selected d P old h)),fun h' => h' ▸ h⟩

theorem old_of_kept (u : FreeOwner D old OWN t) :
    u.val∈old := by
  letI : DecidableEq (Option (S⊕V)) := fun x y => Classical.propDecidable (x=y)
  have h := u.property
  unfold kept OuterNodePacking.untouched at h
  exact (Finset.mem_sdiff.mp h).1

def literalRest (F : OldTables d) (sign : S→Bool) (Y : E→Bool) (x : Rest PR→Bool) : Prop :=
  (∀ r : R, literalFlag d F sign (.inl r) Y=true) ∧
    ∀ v : C, selected d P (t:=t) old v=none →
      literalFlag d F sign (.inr v) (unlift PR x)=true

def nativeTail (F : OldTables d) (sign : S→Bool) :
    TailType P old OWN (t:=t) :=
  fun Y x => if literalRest d P (t:=t) old F sign Y x then 1 else 0

theorem unchanged_nonprotected_flag (F : OldTables d) (sign : S→Bool)
    (v : C) (h : selected d P (t:=t) old v=none) (X : E→Bool) :
    literalFlag d F sign (.inr v) (unlift PR (restrict PR X)) =
      literalFlag d F sign (.inr v) X := by
  apply literal_col_local
  intro w hw
  have hnone : PR w=none := by rw [protected_selected,hw,h]
  simp [unlift,hnone,restrict]

theorem source_flags_split (F : OldTables d) (sign : S→Bool)
    (oldTypes : ∀ u∈old, ∃ v : V, u=some (.inr v))
    (law : WireCloneLaw d F sign old) (Y X : E→Bool) :
    ((∀ r : R, literalFlag d F sign (.inl r) Y=true) ∧
      ∀ v : C, literalFlag d F sign (.inr v) X=true) ↔
      Tied PR X ∧ literalRest d P (t:=t) old F sign Y (restrict PR X) := by
  constructor
  · rintro ⟨hrow,hcol⟩
    refine ⟨?_,hrow,?_⟩
    · intro u w w' hw hw'
      have om := old_of_kept d P old u
      obtain ⟨v,hv⟩ := oldTypes u.val om
      have hs := selected_of_kept d P old u hv
      exact (law v (hv ▸ om) X).1 (hcol _) w w'
        ((protected_owner_exact d P old hs w).1 hw)
        ((protected_owner_exact d P old hs w').1 hw')
    · intro v hv
      rw [unchanged_nonprotected_flag d P old F sign v hv X]
      exact hcol v
  · rintro ⟨hTie,hrow,hRest⟩
    refine ⟨hrow,fun v => ?_⟩
    cases h : selected d P (t:=t) old v with
    | none =>
      exact (unchanged_nonprotected_flag d P old F sign v h X) ▸ hRest v h
    | some u =>
      have h0 := kept_of_selected d P old h
      have om := old_of_kept d P old u
      obtain ⟨w,hw⟩ := oldTypes u.val om
      have hv : v=.inr w := Option.some.inj (h0.symm.trans hw)
      subst v
      apply (law w (hw ▸ om) X).2
      intro x x' hx hx'
      exact hTie u x x' ((protected_owner_exact d P old h x).2 hx)
        ((protected_owner_exact d P old h x').2 hx')

private theorem prodFlag {A B : Type*} [Fintype A] [CommRing B] (p : A→Prop)
    [∀ i, Decidable (p i)] [Decidable (∀ i,p i)] :
    (∏ i, if p i then (1:B) else 0) = if ∀ i, p i then 1 else 0 := by
  by_cases h : ∀ i, p i
  · rw [if_pos h]; exact Finset.prod_eq_one (fun i _ => if_pos (h i))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨i,hi⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

private theorem mulFlag {B : Type*} [CommRing B] (p q : Prop)
    [Decidable p] [Decidable q] [Decidable (p∧q)] :
    (if p then (1:B) else 0)*(if q then 1 else 0) = if p∧q then 1 else 0 := by
  by_cases hp : p <;> by_cases hq : q <;> simp [hp,hq]

theorem oriented_frozen_split (F : OldTables d) (sign : S→Bool)
    (oldTypes : ∀ u∈old, ∃ v : V, u=some (.inr v))
    (law : WireCloneLaw d F sign old) (f : ℤ[X]) (ell c p : ℕ)
    (hf : f.Monic) (hc : 0<c) (hd : 0<f.natDegree) (hℓ : 0<ell) :
    FrozenSplit P p (orientedEntryFile d f ell c F sign) hf old OWN (t:=t)
      (nativeTail d P (t:=t) old F sign) := by
  intro Y X
  rw [rowProduct,colProduct,map_prod,map_prod]
  simp_rw [literal_frozen d F sign f ell c hc hf hd hℓ,apply_ite,map_one,map_zero]
  rw [prodFlag (fun r : R => literalFlag d F sign (.inl r) Y=true),
    prodFlag (fun v : C => literalFlag d F sign (.inr v) X=true),
    guard_weight,nativeTail,apply_ite (J6ZeroTransport.reduceAt p (box_two_nil p f ell)),
    map_one,map_zero,mulFlag,mulFlag]
  have h := source_flags_split d P old (t:=t) F sign oldTypes law Y X
  by_cases hh : Tied PR X ∧ literalRest d P (t:=t) old F sign Y (restrict PR X)
  · rw [if_pos (h.mpr hh),if_pos hh]
  · rw [if_neg (fun h' => hh (h.mp h')),if_neg hh]

theorem oriented_file_projection_erases (F : OldTables d) (sign : S→Bool)
    (oldTypes : ∀ u∈old, ∃ v : V, u=some (.inr v))
    (law : LocalCloneLaw d F old)
    (ports : ∀ u∈old, ∃ w : E, OWN (P.seat w)=u)
    (f : ℤ[X]) (ell c p q : ℕ) (hf : f.Monic) (hc : 0<c) (hd : 0<f.natDegree)
    (hℓ : 0<ell) (hqp : q≤p) (hkept : q≤(K).card)
    (i : Fin a) (ht : t≠0) (hv : padicValInt 2 t=i.val) (z : Box f ell p) (β : Mode i p P.mask →₀ ℕ) :
    lowerBox p q hqp f ell (actualProjection P i ht hv p z
      (orientedEntryFile d f ell c F sign) hf β)=0 := by
  exact projected_zero P i ht hv p z _ hf old OWN (nativeTail d P old F sign)
    (oriented_frozen_split d P old F sign oldTypes (local_implies_wire_law d F sign old law)
      f ell c p hf hc hd hℓ)
    (lowerBox p q hqp f ell) ports q (box_two_nil q f ell) hkept β

#print axioms literal_frozen
#print axioms standard_port_surjects_onto_owner
#print axioms local_implies_wire_law
#print axioms protected_owner_exact
#print axioms source_flags_split
#print axioms oriented_frozen_split
#print axioms oriented_file_projection_erases

end
end J9R20SameFile
