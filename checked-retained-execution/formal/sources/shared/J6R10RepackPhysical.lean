import J6R10Repack
import P11FullPackingPlacement

/-! Instantiate the repacker with the printed real/padded address chart.
A one-side capacity is a projection of the padded chart, not an assumption
on the output of a fresh labeler. The actual real labels may be uneven. -/
namespace J6R10Repack
open scoped Classical BigOperators
open P11FullPacking

variable {E A B G : Type*} [LinearOrder G] [Fintype G] {a : ℕ}

def atEnd (i : Fin a) (right : Bool) (c : Cell (Fin a) G) : G :=
  if right then (c i).2 else (c i).1

private def renameCells (g h : G) : Equiv.Perm (Cell (Fin a) G) :=
  Equiv.piCongrRight (fun _ => Equiv.prodCongr (Equiv.swap g h) (Equiv.swap g h))

theorem side_cell_card (i : Fin a) (right : Bool) (g : G) :
    Fintype.card G * Nat.card {c : Cell (Fin a) G // atEnd i right c = g}
      = Nat.card (Cell (Fin a) G) := by
  classical
  let X := Cell (Fin a) G
  let t : X → G := atEnd i right
  have he (h : G) : Nat.card {c : X // t c = h} = Nat.card {c : X // t c = g} := by
    let σ := Equiv.swap h g
    let e : Equiv.Perm X := renameCells h g
    have hc (x : X) : t (e x) = σ (t x) := by cases right <;> rfl
    exact Nat.card_congr
      { toFun := fun x => ⟨e x.val,by rw [hc,x.property]; exact Equiv.swap_apply_left h g⟩
        invFun := fun x => ⟨e.symm x.val,by
          apply σ.injective
          rw [← hc,e.apply_symm_apply,x.property]
          exact (Equiv.swap_apply_left h g).symm⟩
        left_inv := fun x => Subtype.ext (e.symm_apply_apply x.val)
        right_inv := fun x => Subtype.ext (e.apply_symm_apply x.val) }
  letI (g : G) : Fintype {c : X // t c = g} := Fintype.ofFinite _
  change _ * Nat.card {c : X // t c = g} = Nat.card X
  symm
  calc
    Nat.card X = Nat.card (Σ h : G, {c : X // t c = h}) :=
      Nat.card_congr (Equiv.sigmaFiberEquiv t).symm
    _ = ∑ h : G, Nat.card {c : X // t c = h} := by
      simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    _ = _ := by
      simp only [he,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      rfl

def declaredCell (N : Network E A B) (rowLabel : A → Fin a → G)
    (colLabel : B → Fin a → G) (e : E) : Cell (Fin a) G :=
  fun i => (rowLabel (N.row e) i,colLabel (N.col e) i)

def declaredGroup (rowLabel : A → Fin a → G) (colLabel : B → Fin a → G)
    (i : Fin a) : A ⊕ B → G := Sum.elim (fun v => rowLabel v i) (fun v => colLabel v i)

/-- The same placement addresses are used on both sides. No new vertex is
injected for an empty slot. Capacity refers to all padded addresses. -/
structure PhysicalPacking (N : Network E A B) (a : ℕ) (G : Type*)
    [LinearOrder G] [Fintype G] where
  rowLabel : A → Fin a → G
  colLabel : B → Fin a → G
  copies : ℕ
  mask : MaskFamily a copies G
  seat : E ↪ Physical a copies G
  exactCell : ∀ e, physicalCell mask (seat e) = declaredCell N rowLabel colLabel e
  paddedBudget : Nat.card (Cell (Fin a) G) * (copies * 2^a) ≤ 3 * Nat.card E

variable {N : Network E A B}

noncomputable def rankedPacking [Fintype E] (N : Network E A B)
    (rowLabel : A → Fin a → G) (colLabel : B → Fin a → G)
    (maxLoad : ℕ)
    (hload : ∀ c, Nat.card (RealFiber (declaredCell N rowLabel colLabel) c) ≤ maxLoad)
    (hcap : Nat.card (Cell (Fin a) G) * (ceilCopies (2^a) maxLoad * 2^a) ≤ 3*Nat.card E) :
    PhysicalPacking N a G where
  rowLabel := rowLabel
  colLabel := colLabel
  copies := ceilCopies (2^a) maxLoad
  mask := fun _ _ _ => false
  seat := seatReal (fun _ _ _ => false) (declaredCell N rowLabel colLabel)
    (padded_real_cap _ maxLoad hload) (fun _ => Equiv.refl _)
  exactCell e := seatReal_preserves _ _ _ _ e
  paddedBudget := hcap

private noncomputable def embedSide (P : PhysicalPacking N a G) (i : Fin a) (right : Bool) (g : G) :
    {e : E // atEnd i right (physicalCell P.mask (P.seat e)) = g} ↪
      {c : Cell (Fin a) G // atEnd i right c = g} × Fin (P.copies*2^a) where
  toFun p :=
    let z := fullSlotChart P.mask (P.seat p.val)
    (⟨z.1,p.property⟩,z.2)
  inj' := by
    intro x y h
    apply Subtype.ext
    apply P.seat.injective
    apply (fullSlotChart P.mask).injective
    have h₂ := congrArg Prod.snd h
    exact Prod.ext (congrArg (fun z => z.1.val) h) h₂

/-- Project the actual padded chart, in which each symbol occurs on a given
side in exactly 1/64 of addresses, then restrict to occupied ports. -/
theorem physical_side_cap (P : PhysicalPacking N a G) (hG : Fintype.card G = 64)
    (i : Fin a) (right : Bool) (g : G) :
    Nat.card {e : E // atEnd i right (physicalCell P.mask (P.seat e)) = g}
      ≤ 3 * Nat.card E / 64 := by
  have h := Nat.card_le_card_of_injective _ (embedSide P i right g).injective
  rw [Nat.card_prod,Nat.card_fin] at h
  have he := side_cell_card i right g
  rw [hG] at he
  have hh := Nat.mul_le_mul_left 64 h
  rw [← mul_assoc,he] at hh
  have hb := hh.trans P.paddedBudget
  omega

theorem physical_group_caps (P : PhysicalPacking N a G) (hG : Fintype.card G = 64)
    (i : Fin a) (g : G) :
    Nat.card (rowsIn N (declaredGroup P.rowLabel P.colLabel i) g) ≤ 3*Nat.card E/64 ∧
    Nat.card (colsIn N (declaredGroup P.rowLabel P.colLabel i) g) ≤ 3*Nat.card E/64 := by
  have ht (dir : Bool) (e : E) :
      atEnd i dir (physicalCell P.mask (P.seat e)) = atEnd i dir (declaredCell N P.rowLabel P.colLabel e) :=
    congrArg (atEnd i dir) (P.exactCell e)
  have hiffLink (dir : Bool) :
      {e : E // atEnd i dir (physicalCell P.mask (P.seat e)) = g} ≃
      {e : E // atEnd i dir (declaredCell N P.rowLabel P.colLabel e) = g} :=
    Equiv.subtypeEquivRight (fun e => by rw [ht dir e])
  constructor
  · simpa only [Nat.card_congr (hiffLink false)] using physical_side_cap P hG i false g
  · simpa only [Nat.card_congr (hiffLink true)] using physical_side_cap P hG i true g

/-- The exact real edge and degree bounds for a positive parent call under
the physical source addresses. The only numeric promises are the printed
complete padded slot cap and the inherited parent degree cap. -/
theorem physical_child_invariants [Finite E] (P : PhysicalPacking N a G)
    (hG : Fintype.card G = 64) (hM : 0 < Nat.card E)
    (i : Fin a) (g : G) (Δ : ℕ) (hL : 2*2^a ≤ Δ)
    (hr : ∀ v, Nat.card {e : E // N.row e = v} ≤ Δ)
    (hc : ∀ v, Nat.card {e : E // N.col e = v} ≤ Δ) :
    let gr := declaredGroup P.rowLabel P.colLabel i
    let n := Nat.card (ChildEdge N gr g)
    32*n ≤ 3*Nat.card E ∧ 8*n ≤ Nat.card E ∧ n < Nat.card E ∧
    (∀ v : Old gr g,
      Nat.card {p : ChildEdge N gr g // (child N gr (fun e => (P.seat e).1) g).row p = v} ≤ Δ) ∧
    (∀ k : Page a P.copies G,
      Nat.card (PacketPorts N gr (fun e => (P.seat e).1) g k) ≤ Δ) := by
  obtain ⟨h₁,h₂⟩ := physical_group_caps P hG i g
  obtain ⟨hs₀,hs₁,hs₂⟩ := printed_child_shrink N _ g _ hM h₁ h₂
  exact ⟨hs₀,hs₁,hs₂,printed_child_degrees N _ P.seat g hr hc hL⟩

theorem physical_packet_count (P : PhysicalPacking N a G) :
    Nat.card (Page a P.copies G) * 2^a ≤ 3*Nat.card E := by
  rw [total_slots P.mask]
  exact P.paddedBudget

#print axioms side_cell_card
#print axioms rankedPacking
#print axioms physical_side_cap
#print axioms physical_group_caps
#print axioms physical_child_invariants
#print axioms physical_packet_count
end J6R10Repack
