import J6R10RepackState
import J45CostNative
import J45CostTrace
import J45ParityNative

/-! Actual J5 tile and table-size guards, from the original packed
slots and the existing padded-slot budget. No separate tile chart or
estimate of the number of real packets is a premise. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open P11FullPacking J6R10Repack J6R9PacketScopes
open J6R9PacketTiles

noncomputable section
variable {E A B G : Type*} [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

/-- Tile size and D_t at the actual valuation coordinate. -/
def tileLen (i : Fin a) : ℕ := 2^(a-(i.val+1))
def D (i : Fin a) : ℕ := 2^(a-i.val)

theorem tileLen_pos (i : Fin a) : 0<tileLen i := by unfold tileLen; positivity

theorem tileLen_mul_base (i : Fin a) : tileLen i*2^(i.val+1)=2^a := by
  unfold tileLen
  rw [←pow_add,Nat.sub_add_cancel i.isLt]

theorem two_tileLen (i : Fin a) : 2*tileLen i=D i := by
  unfold tileLen D
  conv_lhs => lhs; change (2:ℕ)^1
  rw [←pow_add]
  congr 1
  omega

theorem tileLen_eq_half (i : Fin a) : tileLen i=D i/2 := by
  rw [←two_tileLen,Nat.mul_div_cancel_left _ (by decide : 0<2)]

theorem d_times_stride (i : Fin a) : D i*2^i.val=2^a := by
  unfold D
  rw [←pow_add,Nat.sub_add_cancel i.isLt.le]

theorem d_eq_dyadic (i : Fin a) : D i=(2^a)/2^i.val := by
  rw [←d_times_stride i,Nat.mul_div_cancel _ (by positivity : 0<(2:ℕ)^i.val)]

theorem twice_packet (i : Fin a) : 2^(i.val+1)*D i=2*2^a := by
  rw [pow_succ]
  calc
    2^i.val*2*D i=2*(D i*2^i.val) := by ac_rfl
    _=_ := by rw [d_times_stride]

theorem ordinal_lt (i : Fin a) (x : Fin (2^a)) : coord i.val x.val<tileLen i := by
  unfold coord
  apply (Nat.div_lt_iff_lt_mul (by positivity : 0<(2:ℕ)^(i.val+1))).2
  simpa only [mul_comm (2^(i.val+1)) (tileLen i),tileLen_mul_base] using x.isLt

variable (P : PhysicalPacking N a G) (i : Fin a)

abbrev Tile := Page a P.copies G × Fin (2^(i.val+1))

def tileOf (e : E) : Tile P i :=
  ((P.seat e).1,⟨tile i.val (P.seat e).2.val,(tile_coordinates _ _).1⟩)

def ordinal (e : E) : Fin (tileLen i) :=
  ⟨coord i.val (P.seat e).2.val,ordinal_lt i (P.seat e).2⟩

theorem same_tile_ordinal_injective (k : Tile P i) :
    Function.Injective (fun x : {e : E // tileOf P i e=k} => ordinal P i x.val) := by
  intro e₁ e₂ h
  apply Subtype.ext
  apply P.seat.injective
  have e : tileOf P i e₁.val=tileOf P i e₂.val := e₁.prop.trans e₂.prop.symm
  have ep : (P.seat e₁.val).1=(P.seat e₂.val).1 := congrArg (fun z : Tile P i=>z.1) e
  have et : tile i.val (P.seat e₁.val).2.val=tile i.val (P.seat e₂.val).2.val :=
    congrArg (fun s : Tile P i=>s.2.val) e
  have eo : coord i.val (P.seat e₁.val).2.val=coord i.val (P.seat e₂.val).2.val :=
    congrArg Fin.val h
  apply Prod.ext ep
  apply Fin.ext
  exact ((tile_coordinates _ _).2).trans ((congrArg₂ (fun t j=>t+2^(i.val+1)*j) et eo).trans
    (tile_coordinates _ _).2.symm)

theorem real_tile_card (k : Tile P i) :
    Nat.card {e : E // tileOf P i e=k} ≤ D i/2 := by
  rw [←tileLen_eq_half]
  exact (Nat.card_le_card_of_injective _ (same_tile_ordinal_injective P i k)).trans
    (Nat.card_fin _).le

theorem source_pages_limit :
    Nat.card (Page a P.copies G)*2^a≤3*Nat.card E :=
  (P11FullPacking.total_slots P.mask).le.trans P.paddedBudget

theorem source_tile_limit :
    Nat.card (Tile P i)*D i≤6*Nat.card E := by
  calc
    Nat.card (Tile P i)*D i=2*(Nat.card (Page a P.copies G)*2^a) := by
      rw [Nat.card_prod,Nat.card_fin,mul_assoc,twice_packet]
      ac_rfl
    _≤2*(3*Nat.card E) := Nat.mul_le_mul_left 2 (source_pages_limit P)
    _=6*Nat.card E := by ring

theorem source_tile_quotient :
    Nat.card (Tile P i)≤6*Nat.card E/D i := by
  have pos : 0<D i := by unfold D; positivity
  exact (Nat.le_div_iff_mul_le pos).2 (source_tile_limit P i)

theorem source_two_feature_limit :
    Nat.card (Tile P i × Bool)*D i≤12*Nat.card E := by
  rw [Nat.card_prod,Nat.card_eq_fintype_card (α:=Bool),Fintype.card_bool,mul_comm _ 2,mul_assoc]
  have h := Nat.mul_le_mul_left 2 (source_tile_limit P i)
  omega

variable {p : ℕ}

def modeTile (m : Mode i p P.mask) : Tile P i := (m.page,m.tile)

def shortModes (g : G) (bmax : ℕ) :=
  {m : Mode i p P.mask // source P.mask i m=g ∧ m.order.val≤bmax}

def shortModeChart (g : G) (bmax : ℕ) :
    shortModes (p:=p) P i g bmax ↪ Tile P i × Fin (bmax+1) where
  toFun m := (modeTile P i m.val,⟨m.val.order.val,m.prop.2 |> Nat.lt_succ_of_le⟩)
  inj' := by
    intro m n h
    apply Subtype.ext
    have ep := congrArg (fun x=>x.1.1) h
    have et := congrArg (fun x=>x.1.2) h
    have eo := congrArg (fun x=>x.2.val) h
    have eqo : m.val.order=n.val.order := Fin.ext eo
    rcases m with ⟨⟨m₁,m₂,m₃,hm⟩,hm'⟩
    rcases n with ⟨⟨n₁,n₂,n₃,hn⟩,hn'⟩
    cases ep
    cases et
    cases eqo
    rfl

theorem source_mode_count (g : G) (bmax : ℕ) :
    Nat.card (shortModes (p:=p) P i g bmax) ≤ Nat.card (Tile P i)*(bmax+1) := by
  have h := Nat.card_le_card_of_injective _ (shortModeChart (p:=p) P i g bmax).injective
  simpa only [Nat.card_prod,Nat.card_fin] using h

#print axioms tileLen_mul_base
#print axioms tileLen_eq_half
#print axioms d_eq_dyadic
#print axioms ordinal_lt
#print axioms same_tile_ordinal_injective
#print axioms real_tile_card
#print axioms source_pages_limit
#print axioms source_tile_limit
#print axioms source_tile_quotient
#print axioms source_two_feature_limit
#print axioms source_mode_count
end
end J5R41LiteralChildCost