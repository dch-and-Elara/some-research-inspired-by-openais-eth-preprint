import V8PooledMenuRoot

set_option autoImplicit false
set_option warningAsError true

/-! Literal N9 moments on actual physical wires. Characteristic two retains
precisely the whole tile and the odd within-tile-coordinate parity. -/
namespace V8NativeMessage
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R9PacketTiles J6R9PacketScopes J6R10Repack
noncomputable section

theorem bit_map {R S : Type*} [Semiring R] [Semiring S] (ψ : R →+* S) (b : Bool) :
    ψ (bit R b) = bit S b := by cases b <;> simp [bit]

theorem cast_parity {R : Type*} [CommRing R] (h₂ : (2:R)=0) (n : ℕ) :
    (n:R) = bit R (decide (n%2=1)) := by
  have h := congrArg (fun q : ℕ => (q:R)) (Nat.mod_add_div n 2)
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,h₂,zero_mul,add_zero] at h
  have hm := Nat.mod_lt n (by decide : 0<2)
  have hs : n%2=0 ∨ n%2=1 := by omega
  rcases hs with hs | hs <;> rw [← h,hs] <;> simp [bit]

theorem power_tile_parity {R : Type*} [CommRing R] (h₂ : (2:R)=0)
    (n j : ℕ) (b : Bool) :
    (n:R)^j * bit R b =
      bit R ((if j=0 then true else decide (n%2=1)) && b) := by
  by_cases hj : j=0
  · simp [hj]
  · rw [cast_parity h₂ n]
    cases decide (n%2=1) <;> cases b <;> simp [bit,hj]

variable {E A B G : Type} [Fintype E] [LinearOrder G] [Fintype G]
  {a : ℕ} {N : Network E A B}

abbrev TileForm (P : PhysicalPacking N a G) (i : Fin a) :=
  Page a P.copies G × (Fin (2^(i.val+1)) × Bool)

/-- A page, a physical tile, and one bit distinguishing its two actual
Boolean forms. Distinct positive orders share the second form. -/
def modeForm (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ} (m : Mode i p P.mask) :
    TileForm P i := (m.page,m.tile,decide (m.order.val≠0))

def formSource (P : PhysicalPacking N a G) (i : Fin a) (c : TileForm P i) : G :=
  colGroup P.mask i (c.1,tileIndex i c.2.1)

omit [Fintype E] in
theorem formSource_mode (P : PhysicalPacking N a G) (i : Fin a) {p : ℕ}
    (m : Mode i p P.mask) : formSource P i (modeForm P i m) = (childSource P i m).1 := rfl

def fillColumn (P : PhysicalPacking N a G) (i : Fin a) (g : G)
    (v : PhysicalState P i g) (q : E) : Bool :=
  if h : colGroup P.mask i (P.seat q)=g then v.2 ⟨q,h⟩ else false

def formValue {R : Type*} [CommRing R] (P : PhysicalPacking N a G) (i : Fin a)
    (c : TileForm P i) (X : E → Bool) : R :=
  ∑ q ∈ columns (fun q => (P.seat q).1) (fun q => (P.seat q).2.val) i.val c.1 c.2.1.val,
    bit R ((if c.2.2 then decide (coord i.val (P.seat q).2.val % 2=1) else true) && X q)

theorem map_formValue {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) (P : PhysicalPacking N a G) (i : Fin a) (c : TileForm P i) (X : E → Bool) :
    ψ (formValue P i c X) = formValue P i c X := by
  simp only [formValue,map_sum,bit_map]

theorem literal_moment_charTwo {R S : Type*} [CommRing R] [CommRing S]
    (ψ : R →+* S) (h₂ : (2:S)=0) (P : PhysicalPacking N a G) (i : Fin a) (p : ℕ) (g : G)
    (v : PhysicalState P i g) (m : Mode i p P.mask) (hs : (childSource P i m).1=g) :
    ψ (stateMoment (R:=R) P i g p v m) =
      formValue (R:=S) P i (modeForm P i m) (fillColumn P i g v) := by
  change source P.mask i m=g at hs
  subst g
  simp only [stateMoment]
  have hX : (fun q : {q : E // colGroup P.mask i (P.seat q)=source P.mask i m} =>
      fillColumn P i (source P.mask i m) v q.val) = v.2 := by
    funext q
    simp only [fillColumn,dif_pos q.property]
  rw [← hX, J6R9PacketChild.moment_exact (R:=R)]
  simp only [dif_pos True.intro,L,formValue,map_sum,map_mul,map_pow,map_natCast,bit_map,modeForm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  rw [power_tile_parity h₂]
  by_cases hj : m.order.val=0 <;> simp [hj]

theorem formValue_binary {R : Type*} [CommRing R] (h₂ : (2:R)=0)
    (P : PhysicalPacking N a G) (i : Fin a) (c : TileForm P i) (X : E → Bool) :
    formValue (R:=R) P i c X=0 ∨ formValue (R:=R) P i c X=1 := by
  unfold formValue
  generalize (columns (fun q : E => (P.seat q).1) (fun q => (P.seat q).2.val)
    i.val c.1 c.2.1.val) = s
  induction s using Finset.induction_on with
  | empty => simp
  | insert e s he ih =>
    rw [Finset.sum_insert he]
    cases (if c.2.2 then decide (coord i.val (P.seat e).2.val % 2=1) else true) && X e
    · simpa only [bit,Bool.false_eq_true,if_false,zero_add] using ih
    · simp only [bit,if_true] at ⊢
      rcases ih with ih | ih
      · right
        unfold bit at ih
        rw [ih,add_zero]
      · left
        unfold bit at ih
        rw [ih,one_add_one_eq_two,h₂]
#print axioms cast_parity
#print axioms power_tile_parity
#print axioms formSource_mode
#print axioms map_formValue
#print axioms literal_moment_charTwo
#print axioms formValue_binary

end
end V8NativeMessage