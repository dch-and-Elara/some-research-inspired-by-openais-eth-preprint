import P5D1LiteralAgenda
import P5D1LiteralTerms
import J6R10RepackRounded
import BalancedUnion

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 3500000

/-! Original N4 density uses one actual old clause-side wire per pin in
the four-copy network and the unrounded collision certificate. The
different factor of two in C2 is not used here. -/
namespace V8NativeMessage.N4
open scoped Classical BigOperators Polynomial
open P11FullPacking J6R10Repack J6R12Blueprint J1PPrinted Paper5.HybridClosure Paper5.D1Literal
noncomputable section

section General
variable {E A B : Type*} [Fintype E] {N : Network E A B} {a : ℕ}
abbrev C (a : ℕ) := Cell (Fin a) (Fin 64)

def actualCell (P : PhysicalPacking N a (Fin 64)) : E→C a :=
  declaredCell N P.rowLabel P.colLabel

theorem cell_num (a : ℕ) : Nat.card (C a)=J9PrintedSchedule.arrayCard a := by
  unfold C J9PrintedSchedule.arrayCard
  rw [total_cells,Fintype.card_fin]

omit [Fintype E] in
theorem finite_cell_cap (P : PhysicalPacking N a (Fin 64)) (Δ : ℕ)
    (hv : varianceScore (actualCell P)≤2*(Nat.card E:ℚ)*Δ)
    (hm : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E) (c : C a) :
    Nat.card (C a)*Nat.card (Fiber (actualCell P) c)≤2*Nat.card E := by
  let M := Nat.card E
  let d := Nat.card (C a)
  let x := Nat.card (Fiber (actualCell P) c)
  have hd : (0:ℚ)<d := by exact_mod_cast (show 0<d by
    change 0<Nat.card (C a)
    rw [cell_num]
    unfold J9PrintedSchedule.arrayCard
    positivity)
  have hs : ((x:ℚ)-(M:ℚ)/d)^2≤2*(M:ℚ)*Δ :=
    (Finset.single_le_sum
      (f:=fun k : C a => ((Nat.card (Fiber (actualCell P) k):ℚ)-(M:ℚ)/d)^2)
      (fun _ _ => sq_nonneg _) (Finset.mem_univ c)).trans hv
  have hnum : 2*d^2*Δ≤M := by simpa only [d,cell_num,M] using hm
  have hq : 2*(d:ℚ)^2*(Δ:ℚ)≤(M:ℚ) := by exact_mod_cast hnum
  have hsquare : 2*(M:ℚ)*Δ≤((M:ℚ)/d)^2 := by
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hd _)).mpr
    calc
      _ = (2*(d:ℚ)^2*(Δ:ℚ))*(M:ℚ) := by ring
      _ ≤ (M:ℚ)*(M:ℚ) := mul_le_mul_of_nonneg_right hq (by positivity)
      _ = _ := by ring
  have hcap : (x:ℚ)≤2*((M:ℚ)/d) := by
    by_contra! hn
    have ha := sub_pos.mpr hn
    have hb : (0:ℚ)<x := (by positivity : (0:ℚ)≤2*((M:ℚ)/d)).trans_lt hn
    nlinarith only [hs.trans hsquare,mul_pos ha hb]
  have hc : (x:ℚ)*(d:ℚ)≤2*(M:ℚ) := by
    apply (le_div_iff₀ hd).mp
    simpa only [mul_div_assoc] using hcap
  change d*x≤2*M
  rw [Nat.mul_comm d x]
  exact_mod_cast hc

abbrev RowCells {a : ℕ} (i : Fin a) (g : Fin 64) := {c : C a // atEnd i false c=g}
abbrev RowWires (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (g : Fin 64) :=
  {w : E // atEnd i false (actualCell P w)=g}

def rowChart (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (g : Fin 64) :
    RowWires P i g ≃ Σ c : RowCells i g, Fiber (actualCell P) c.val where
  toFun w := ⟨⟨actualCell P w.val,w.property⟩,⟨w.val,rfl⟩⟩
  invFun q := ⟨q.2.val,by rw [q.2.property]; exact q.1.property⟩
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨c,hc⟩,⟨w,he⟩⟩; dsimp at he; subst c; rfl

theorem row_wire_count (P : PhysicalPacking N a (Fin 64)) (i : Fin a) (g : Fin 64) :
    Nat.card (RowWires P i g)=∑ c : RowCells i g, Nat.card (Fiber (actualCell P) c.val) := by
  letI (c : RowCells i g) : Fintype (Fiber (actualCell P) c.val) := Fintype.ofFinite _
  rw [Nat.card_congr (rowChart P i g)]
  simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]

theorem occupied_row_cap (P : PhysicalPacking N a (Fin 64)) (Δ : ℕ)
    (hv : varianceScore (actualCell P)≤2*(Nat.card E:ℚ)*Δ)
    (hm : 2*(J9PrintedSchedule.arrayCard a)^2*Δ≤Nat.card E)
    (i : Fin a) (g : Fin 64) :
    64*Nat.card (RowWires P i g)≤2*Nat.card E := by
  let I := RowCells i g
  let n := Nat.card I
  have hr := row_wire_count P i g
  have hn : 64*n=Nat.card (C a) := by
    simpa only [Fintype.card_fin] using side_cell_card i false g
  have hd : (0:ℕ)<Nat.card (C a) := by rw [cell_num]; unfold J9PrintedSchedule.arrayCard; positivity
  have hpos : 0<n := by omega
  have hsum : Nat.card (C a)*Nat.card (RowWires P i g)≤n*(2*Nat.card E) := by
    rw [hr,Finset.mul_sum]
    calc
      _ ≤ ∑ _c : I, 2*Nat.card E := Finset.sum_le_sum (fun c _ => finite_cell_cap P Δ hv hm c.val)
      _ = _ := by simp [n,Nat.card_eq_fintype_card]
  rw [← hn] at hsum
  have he : n*(64*Nat.card (RowWires P i g))≤n*(2*Nat.card E) := by
    simpa only [Nat.mul_left_comm,Nat.mul_comm,Nat.mul_assoc] using hsum
  exact Nat.le_of_mul_le_mul_left he hpos

end General

section Four
variable {W : Type} [Fintype W] [DecidableEq W]
  {F : Finset (W×W)} {reg : ∀ v, GraphCutMoments.degree F v=3} {f : ℤ[X]}
local notation "S" => (printedParams (f:=f) (ell:=1) (oldRowSize F))
local notation "Δ" => sourceDelta (oldRowSize F)
local notation "r*" => oldRowRoot F reg f (fun _=>false)

def pinGroup (P : RootPacking F reg f) (i : rootKept F f) (v : W) : Fin 64 :=
  rootLabels F reg f P v i

abbrev Pins (P : RootPacking F reg f) (i : rootKept F f) (g : Fin 64) :=
  {v : W // pinGroup P i v=g}

def realPinWire (v : W) : DWire F := (.inl v,true)

theorem actual_pin_group (P : RootPacking F reg f) (i : rootKept F f) (v : W) :
    atEnd i.val false (physicalCell P.mask (P.seat (realPinWire (F:=F) v)))=pinGroup P i v := by
  rw [P.exactCell]
  rfl

def pinEmbed (P : RootPacking F reg f) (i : rootKept F f) (g : Fin 64) :
    Pins P i g ↪ RowWires P i.val g where
  toFun v := ⟨realPinWire v.val,v.property⟩
  inj' := by
    intro v w h
    apply Subtype.ext
    exact Sum.inl.inj (congrArg (fun q : RowWires P i.val g => q.val.1) h)

theorem original_pin_density (P : RootPacking F reg f)
    (d : Ready S Δ r*) (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ)
    (i : rootKept F f) (g : Fin 64) :
    4*Nat.card (Pins P i g)≤3*Fintype.card W := by
  have h0 := Nat.card_le_card_of_injective _ (pinEmbed P i g).injective
  have hm : 2*(J9PrintedSchedule.arrayCard ((S).levelBits 0))^2*Δ≤Nat.card (DWire F) := by
    rw [Nat.card_eq_fintype_card]
    exact d.collision
  have h := (Nat.mul_le_mul_left 64 h0).trans (occupied_row_cap P Δ hv hm i.val g)
  rw [Nat.card_eq_fintype_card (α:=DWire F),d_physical_wire_count F reg] at h
  omega

def switchUnion (P : RootPacking F reg f) (i : rootKept F f) (T : Finset (Fin 64)) : Finset W :=
  BalancedUnion.vertexUnion (pinGroup P i) T

theorem mem_switch_union (P : RootPacking F reg f) (i : rootKept F f) (T : Finset (Fin 64))
    (v : W) : v∈switchUnion P i T ↔ pinGroup P i v∈T := by
  simp only [switchUnion,BalancedUnion.vertexUnion,Finset.mem_filter,Finset.mem_univ,true_and]

theorem original_balanced_union (P : RootPacking F reg f)
    (d : Ready S Δ r*) (hv : varianceScore (actualCell P)≤2*(Nat.card (DWire F):ℚ)*Δ)
    (i : rootKept F f) :
    ∃ T : Finset (Fin 64), Fintype.card W≤4*min (switchUnion P i T).card
      (Fintype.card W-(switchUnion P i T).card) := by
  have hM : 0<Fintype.card (DWire F) := Nat.zero_lt_of_lt d.active
  rw [d_physical_wire_count F reg] at hM
  letI : Nonempty W := Fintype.card_pos_iff.mp (by omega)
  have hcap (g : Fin 64) : (SourceDensity.fiberCount (pinGroup P i) g:ℚ)≤(3/4:ℚ)*Fintype.card W := by
    have h := original_pin_density P d hv i g
    have he : Nat.card (Pins P i g)=SourceDensity.fiberCount (pinGroup P i) g := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    rw [he] at h
    have h' : 4*(SourceDensity.fiberCount (pinGroup P i) g:ℚ)≤3*Fintype.card W := by exact_mod_cast h
    linarith only [h']
  obtain ⟨T,ht⟩ := BalancedUnion.exists_balanced_vertex_union (pinGroup P i) hcap
  refine ⟨T,?_⟩
  exact_mod_cast (show (Fintype.card W:ℚ)≤
    4*(min (switchUnion P i T).card (Fintype.card W-(switchUnion P i T).card):ℕ) by
      unfold switchUnion; linarith only [ht])

end Four

#print axioms finite_cell_cap
#print axioms rowChart
#print axioms row_wire_count
#print axioms occupied_row_cap
#print axioms actual_pin_group
#print axioms pinEmbed
#print axioms original_pin_density
#print axioms original_balanced_union
end
end V8NativeMessage.N4
