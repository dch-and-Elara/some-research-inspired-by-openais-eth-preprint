import V8NativeMessageLower
import J6R10RepackRounded
import BalancedUnion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3000000

/-! The old-side availability density of the same frozen five-copy
layout. Use the real unrounded collision certificate, not padded slots
as though they were original clause ports. -/
namespace V8NativeMessage.C2Physical
open scoped Classical BigOperators
open V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu V8PooledMenu.FiveCopy
open V8NativeMessage.Five J6R10Repack P11FullPacking
noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G}

abbrev OrderedCells (V : Type) [Fintype V] := Cell (Fin (rootA V)) (Fin 64)

def cell (P : Packing G p) : Edge V E→OrderedCells V :=
  declaredCell (network G p) P.rowLabel P.colLabel

def cellCount (V : Type) [Fintype V] : ℕ := Nat.card (OrderedCells V)

theorem cellCount_printed : cellCount V = J9PrintedSchedule.arrayCard (rootA V) := by
  unfold cellCount J9PrintedSchedule.arrayCard OrderedCells
  rw [total_cells,Fintype.card_fin]

theorem cellCount_pos : 0<cellCount V := by
  rw [cellCount_printed]; unfold J9PrintedSchedule.arrayCard; positivity

def VarianceOK (P : Packing G p) (Δ : ℕ) : Prop :=
  varianceScore (cell P)≤2*(wireSize V:ℚ)*Δ

def Margin (V : Type) [Fintype V] (Δ : ℕ) : Prop :=
  2*(cellCount V)^2*Δ≤wireSize V

theorem exact_cell_cap (P : Packing G p) (Δ : ℕ) (hv : VarianceOK P Δ)
    (hm : Margin V Δ) (c : OrderedCells V) :
    cellCount V * Nat.card (Fiber (cell P) c)≤2*wireSize V := by
  let M := wireSize V
  let d := cellCount V
  let x := Nat.card (Fiber (cell P) c)
  have hd : (0:ℚ)<d := by exact_mod_cast cellCount_pos (V:=V)
  have hsize : Nat.card (Edge V E)=M := by
    rw [Nat.card_eq_fintype_card,wires_card G p]
    rfl
  have hv' : ((x:ℚ)-(M:ℚ)/d)^2≤2*(M:ℚ)*Δ := by
    unfold VarianceOK varianceScore at hv
    rw [hsize] at hv
    refine (Finset.single_le_sum
      (f:=fun k : OrderedCells V => ((Nat.card (Fiber (cell P) k):ℚ)-(M:ℚ)/d)^2)
      (fun k _ => sq_nonneg _) (Finset.mem_univ c)).trans ?_
    exact hv
  have hq : 2*(d:ℚ)^2*(Δ:ℚ)≤(M:ℚ) := by exact_mod_cast hm
  have hsquare : 2*(M:ℚ)*Δ≤((M:ℚ)/d)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hd _)).mpr
    calc
      _ = (2*(d:ℚ)^2*(Δ:ℚ))*(M:ℚ) := by ring
      _ ≤ (M:ℚ)*(M:ℚ) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := by ring
  have hcap : (x:ℚ)≤2*((M:ℚ)/d) := by
    by_contra! hn
    have hpos₁ := sub_pos.mpr hn
    have hpos₂ : (0:ℚ)<x := (by positivity : (0:ℚ)≤2*((M:ℚ)/d)).trans_lt hn
    nlinarith only [hv'.trans hsquare,mul_pos hpos₁ hpos₂]
  have hm' : (x:ℚ)*(d:ℚ)≤2*(M:ℚ) := by
    apply (le_div_iff₀ hd).mp
    simpa only [mul_div_assoc] using hcap
  have hn : x*d≤2*M := by exact_mod_cast hm'
  change d*x≤2*M
  rw [Nat.mul_comm d x]
  exact hn

abbrev SideCells (i : Fin (rootA V)) (g : Fin 64) :=
  {c : OrderedCells V // atEnd i false c=g}

abbrev SideWires (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :=
  {w : Edge V E // atEnd i false (cell P w)=g}

def sideCellChart (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :
    SideWires P i g ≃ Σ c : SideCells i g, Fiber (cell P) c.val where
  toFun w := ⟨⟨cell P w.val,w.property⟩,⟨w.val,rfl⟩⟩
  invFun q := ⟨q.2.val,by rw [q.2.property]; exact q.1.property⟩
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨c,hc⟩,⟨w,h⟩⟩
    dsimp at h
    subst c
    rfl

theorem side_wire_count (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :
    Nat.card (SideWires P i g)=∑ c : SideCells i g, Nat.card (Fiber (cell P) c.val) := by
  letI (c : SideCells i g) : Fintype (Fiber (cell P) c.val) := Fintype.ofFinite _
  rw [Nat.card_congr (sideCellChart P i g)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

theorem side_cells_exact (i : Fin (rootA V)) (g : Fin 64) :
    64*Nat.card (SideCells i g)=cellCount V := by
  simpa only [Fintype.card_fin,cellCount] using side_cell_card i false g

theorem side_cells_pos (i : Fin (rootA V)) (g : Fin 64) : 0<Nat.card (SideCells i g) := by
  have h := side_cells_exact i g
  have hn := cellCount_pos (V:=V)
  omega

theorem occupied_side_cap (P : Packing G p) (Δ : ℕ) (hv : VarianceOK P Δ)
    (hm : Margin V Δ) (i : Fin (rootA V)) (g : Fin 64) :
    64*Nat.card (SideWires P i g)≤2*wireSize V := by
  let S := SideCells i g
  let C := Nat.card S
  have hsum : cellCount V * Nat.card (SideWires P i g)≤C*(2*wireSize V) := by
    rw [side_wire_count,Finset.mul_sum]
    calc
      _ ≤ ∑ _c : S, 2*wireSize V := Finset.sum_le_sum (fun c _ => exact_cell_cap P Δ hv hm c.val)
      _ = _ := by simp [C,Nat.card_eq_fintype_card]
  rw [← side_cells_exact i g] at hsum
  have hcalc : C*(64*Nat.card (SideWires P i g))≤C*(2*wireSize V) := by
    simpa only [C,Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using hsum
  exact Nat.le_of_mul_le_mul_left hcalc (side_cells_pos i g)

abbrev Switches (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :=
  {v : V // switchGroup P i v=g}

def switchWire (v : V) (b : Bool) : Edge V E := ((.inl (.inr v),b),false)

omit [Fintype E] in
theorem switchWire_side (P : Packing G p) (i : Fin (rootA V)) (v : V) (b : Bool) :
    atEnd i false (cell P (switchWire (E:=E) v b))=switchGroup P i v := rfl

def embedSwitchPorts (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :
    Switches P i g × Bool ↪ SideWires P i g where
  toFun q := ⟨switchWire q.1.val q.2,(switchWire_side P i q.1.val q.2).trans q.1.property⟩
  inj' := by
    rintro ⟨⟨v,hv⟩,b⟩ ⟨⟨w,hw⟩,c⟩ h
    have e := congrArg Subtype.val h
    change switchWire (E:=E) v b=switchWire w c at e
    unfold switchWire at e
    have hfirst := congrArg Prod.fst e
    have hbc : b=c := congrArg Prod.snd hfirst
    have hd : (.inl (.inr v):ClauseId V E)=.inl (.inr w) := congrArg Prod.fst hfirst
    exact Prod.ext (Subtype.ext (Sum.inr.inj (Sum.inl.inj hd))) hbc

theorem both_switch_ports (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :
    2*Nat.card (Switches P i g)≤Nat.card (SideWires P i g) := by
  have hh := Nat.card_le_card_of_injective _ (embedSwitchPorts P i g).injective
  simpa only [Nat.card_prod,Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool,
    Nat.mul_comm (Nat.card (Switches P i g)) 2] using hh

theorem switch_cap (P : Packing G p) (Δ : ℕ) (hv : VarianceOK P Δ)
    (hm : Margin V Δ) (i : Fin (rootA V)) (g : Fin 64) :
    64*Nat.card (Switches P i g)≤wireSize V := by
  have h := (Nat.mul_le_mul_left 64 (both_switch_ports P i g)).trans
    (occupied_side_cap P Δ hv hm i g)
  omega

theorem quarter_atom (P : Packing G p) (Δ : ℕ) (hv : VarianceOK P Δ)
    (hm : Margin V Δ) (i : Fin (rootA V)) (g : Fin 64) :
    4*Nat.card (Switches P i g)≤3*Fintype.card V := by
  have h := switch_cap P Δ hv hm i g
  unfold wireSize at h
  omega

theorem balanced_real_switch_union (P : Packing G p) (Δ : ℕ) (hv : VarianceOK P Δ)
    (hm : Margin V Δ) (hN : 0<Fintype.card V) (i : Fin (rootA V)) :
    ∃ T : Finset (Fin 64),
      Fintype.card V≤4*min (BalancedUnion.vertexUnion (switchGroup P i) T).card
        (Fintype.card V-(BalancedUnion.vertexUnion (switchGroup P i) T).card) := by
  letI : Nonempty V := Fintype.card_pos_iff.mp hN
  have hcap (g : Fin 64) :
      (SourceDensity.fiberCount (switchGroup P i) g : ℚ)≤(3/4:ℚ)*Fintype.card V := by
    have he : Nat.card (Switches P i g)=SourceDensity.fiberCount (switchGroup P i) g := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    have h := quarter_atom P Δ hv hm i g
    rw [he] at h
    have h' : 4*(SourceDensity.fiberCount (switchGroup P i) g : ℚ)≤3*Fintype.card V := by
      exact_mod_cast h
    linarith only [h']
  obtain ⟨T,hT⟩ := BalancedUnion.exists_balanced_vertex_union (switchGroup P i) hcap
  refine ⟨T,?_⟩
  exact_mod_cast (show (Fintype.card V:ℚ)≤
    4*(min (BalancedUnion.vertexUnion (switchGroup P i) T).card
      (Fintype.card V-(BalancedUnion.vertexUnion (switchGroup P i) T).card):ℕ) by linarith only [hT])

#print axioms cellCount_printed
#print axioms exact_cell_cap
#print axioms sideCellChart
#print axioms side_wire_count
#print axioms occupied_side_cap
#print axioms switchWire_side
#print axioms embedSwitchPorts
#print axioms both_switch_ports
#print axioms switch_cap
#print axioms quarter_atom
#print axioms balanced_real_switch_union
end
end V8NativeMessage.C2Physical
