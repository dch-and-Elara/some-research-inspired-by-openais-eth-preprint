import J4R43LiteralOutsideBandFibers

/-! Seat an already-certified physical matching in the two bands,
retaining the real old labels and prescribing the actual distinguished
pin's last position. The same new packing works for every centre and
sign word. -/
namespace J4R43LiteralOutside
open scoped Classical BigOperators Polynomial
open P11FullPacking J7SeatPacking J6R10Repack
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option maxHeartbeats 4500000

theorem complete_with_fixed {X Y : Type*} [Fintype X] [Fintype Y]
    (good : X→Prop) (seat : Y→Prop)
    (cap : Nat.card X≤Nat.card Y) (cnt : Nat.card {y//seat y}≤Nat.card {x//good x})
    (pin : X) (target : Y) (hg : good pin) (hs : seat target) :
    ∃ j : X↪Y, (∀ w,seat (j w)→good w) ∧ (∀ y,seat y→∃ w,j w=y) ∧ j pin=target := by
  obtain ⟨j,marked,filled⟩ := J7SeatPacking.complete good seat cap cnt
  obtain ⟨w,hw⟩ := filled target hs
  have wg : good w := marked w (by rw [hw]; exact hs)
  let flip : Equiv.Perm X := Equiv.swap pin w
  use flip.toEmbedding.trans j
  refine ⟨?_,?_,?_⟩
  · intro x hx
    change seat (j (flip x)) at hx
    by_cases h₁ : x=pin
    · rwa [h₁]
    by_cases h₂ : x=w
    · rwa [h₂]
    change good x
    have a := marked (flip x) hx
    change good (Equiv.swap pin w x) at a
    rwa [Equiv.swap_apply_of_ne_of_ne h₁ h₂] at a
  · intro y hy
    obtain ⟨x,hx⟩ := filled y hy
    refine ⟨flip.symm x,?_⟩
    change j (flip (flip.symm x))=y
    rw [Equiv.apply_symm_apply,hx]
  · change j (Equiv.swap pin w pin)=target
    rw [Equiv.swap_apply_left,hw]

variable {E A B G : Type} [Fintype E] [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B}

abbrev InputCell (P : PhysicalPacking N a G) (c : Cell (Fin a) G) :=
  {e : E // declaredCell N P.rowLabel P.colLabel e=c}

structure BandSupply (P : PhysicalPacking N a G) (h : ℕ) (pin : E) where
  good : E→Prop
  row : ∀ e e',good e→good e'→N.row e=N.row e'→e=e'
  col : ∀ e e',good e→good e'→N.col e=N.col e'→e=e'
  pin_good : good pin
  hasCopy : 0<P.copies
  quota : ∀ c : Cell (Fin a) G, 2*h*P.copies≤Nat.card {w : InputCell P c // good w.val}

theorem same_cell_capacity (P : PhysicalPacking N a G) (c : Cell (Fin a) G) :
    Nat.card (InputCell P c)≤P.copies*2^a := by
  let e : InputCell P c→Fin (P.copies*2^a) :=
    fun x=>(fullSlotChart P.mask (P.seat x.val)).2
  have i : Function.Injective e := by
    intro x y eq
    apply Subtype.ext
    apply P.seat.injective
    apply (fullSlotChart P.mask).injective
    apply Prod.ext
    · simpa only [fullSlotChart_cell,P.exactCell,x.prop,y.prop]
    · exact eq
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective e i

theorem anchor_last_band (a h : ℕ) (hh : 0<h) :
    InBand (2^a) h (endpointIndex a true).val := by
  right
  change 2^a-h≤2^a-1
  omega

theorem last_index_exact (a : ℕ) : (endpointIndex a true).val+1=2^a := by
  change 2^a-1+1=2^a
  have h : 0<(2:ℕ)^a := by positivity
  omega

/-- This is the exact
source step from a finite per-cell matching supply to legal seating. -/
theorem realize_band_with_pin (P : PhysicalPacking N a G) (h : ℕ) (hh : 0<h) (hf : 2*h≤2^a)
    (pin : E) (D : BandSupply P h pin) :
    ∃ Q : PhysicalPacking N a G,
      Q.rowLabel=P.rowLabel ∧ Q.colLabel=P.colLabel ∧ Q.copies=P.copies ∧
      Q.mask=balancedMask a Q.copies ∧ BandCertificate Q h ∧ (Q.seat pin).2.val+1=2^a := by
  let f := declaredCell N P.rowLabel P.colLabel
  let site (c : Cell (Fin a) G) := inCellAt c (endpointIndex a true) (⟨0,D.hasCopy⟩ : Fin P.copies)
  have hLocal (c : Cell (Fin a) G) :
      ∃ j : InputCell P c ↪ SlotFiber (b:=P.copies) c,
        (∀ w,InBand (2^a) h (j w).val.2.val→D.good w.val) ∧
        (∀ z,InBand (2^a) h z.val.2.val→∃ w,j w=z) ∧
        (∀ w : InputCell P c,w.val=pin→j w=site c) := by
    have cap := (same_cell_capacity P c).trans_eq (card_slots (b:=P.copies) c).symm
    have cnt := (actual_cell_band_measure (b:=P.copies) c h hf).trans_le (D.quota c)
    by_cases atPin : f pin=c
    · let w : InputCell P c := ⟨pin,atPin⟩
      obtain ⟨j,hj,hz,hw⟩ := complete_with_fixed (fun x : InputCell P c=>D.good x.val)
        (fun z : SlotFiber (b:=P.copies) c=>InBand (2^a) h z.val.2.val)
        cap cnt w (site c) D.pin_good (anchor_last_band a h hh)
      refine ⟨j,hj,hz,?_⟩
      intro u eq
      exact (congrArg j (Subtype.ext eq : u=w)).trans hw
    · obtain ⟨j,hj,hz⟩ := J7SeatPacking.complete (fun x : InputCell P c=>D.good x.val)
        (fun z : SlotFiber (b:=P.copies) c=>InBand (2^a) h z.val.2.val) cap cnt
      exact ⟨j,hj,hz,fun w e=>(atPin (e ▸ w.prop)).elim⟩
  choose place gold cover fixed using hLocal
  let s (e : E) : Physical a P.copies G := (place (f e) ⟨e,rfl⟩).val
  have sCell (e : E) : physicalCell (balancedMask a P.copies) (s e)=f e :=
    (place (f e) ⟨e,rfl⟩).prop
  have sEq (c : Cell (Fin a) G) (e : InputCell P c) : s e.val=(place c e).val := by
    rcases e with ⟨e,he⟩
    change f e=c at he
    cases he
    rfl
  have sInj : Function.Injective s := by
    intro x y eq
    have he : f x=f y := (sCell x).symm.trans ((congrArg (physicalCell (balancedMask a P.copies)) eq).trans (sCell y))
    let xv : InputCell P (f x) := ⟨x,rfl⟩
    let yv : InputCell P (f x) := ⟨y,he.symm⟩
    apply congrArg Subtype.val (show xv=yv from (place (f x)).injective (Subtype.ext ?_))
    exact (sEq (f x) xv).symm.trans (eq.trans (sEq (f x) yv))
  let Q : PhysicalPacking N a G := ⟨P.rowLabel,P.colLabel,P.copies,balancedMask a P.copies,⟨s,sInj⟩,sCell,P.paddedBudget⟩
  have accepted (e : E) (band : InBand (2^a) h (Q.seat e).2.val) : D.good e :=
    gold (f e) ⟨e,rfl⟩ band
  have goodBand : BandCertificate Q h := by
    refine ⟨hh,hf,?_,?_,?_⟩
    · intro z band
      let c := physicalCell (balancedMask a P.copies) z
      let v : SlotFiber (b:=P.copies) c := ⟨z,rfl⟩
      obtain ⟨w,eq⟩ := cover c v band
      exact ⟨w.val,(sEq c w).trans (congrArg Subtype.val eq)⟩
    · intro e e' b b' eq
      exact D.row e e' (accepted e b) (accepted e' b') eq
    · intro e e' b b' eq
      exact D.col e e' (accepted e b) (accepted e' b') eq
  refine ⟨Q,rfl,rfl,rfl,rfl,goodBand,?_⟩
  have last := congrArg (fun z : SlotFiber (b:=P.copies) (f pin)=>z.val.2.val)
    (fixed (f pin) ⟨pin,rfl⟩ rfl)
  change (Q.seat pin).2.val=(endpointIndex a true).val at last
  rw [last,last_index_exact]

#print axioms complete_with_fixed
#print axioms same_cell_capacity
#print axioms anchor_last_band
#print axioms last_index_exact
#print axioms realize_band_with_pin
end
end J4R43LiteralOutside

