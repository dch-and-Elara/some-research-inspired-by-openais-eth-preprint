import J8PhysicalWiring

/-!
The physical source tile, including real pin and nonpin ports, and its
actual local coordinate j=(y-τ)/2. These definitions feed the bit decoder
and the public source/background computations without an assumed
Vandermonde distinctness premise.
-/

namespace J8Physical

open scoped Polynomial BigOperators Classical

noncomputable section

variable {Packet R S V G : Type*} {P : V → Type*} {L : ℕ}
variable (d : Layout Packet R S V G P L)

def SameTile (x y : Wire R) : Prop :=
  (d.seat x).1 = (d.seat y).1 ∧ (d.seat x).2.val % 2 = (d.seat y).2.val % 2

theorem sameTile_colLabel {x y : Wire R} (h : SameTile d x y) :
    actualColLabel d x = actualColLabel d y := by
  unfold actualColLabel
  rw [d.columnOrientation x, d.columnOrientation y, h.1, h.2]

/-- Index of a real port in its physical tile. Since τ=y mod 2, this is
exactly (y-τ)/2. -/
def ordinal (w : Wire R) : ℕ := (d.seat w).2.val / 2

theorem ordinal_equation (w : Wire R) :
    (d.seat w).2.val = (d.seat w).2.val % 2 + 2 * ordinal d w := by
  unfold ordinal
  omega

theorem onTile_ordinal_injective {x y z : Wire R} (hx : SameTile d x z) (hy : SameTile d y z)
    (h : ordinal d x = ordinal d y) : x = y := by
  apply d.seat.injective
  apply Prod.ext (hx.1.trans hy.1.symm)
  apply Fin.ext
  rw [ordinal_equation d x, ordinal_equation d y, hx.2, hy.2, h]

def ordinaryWire (p : Sigma P) : Wire R := d.column.symm (Sum.inr p)

@[simp] theorem ordinaryWire_column (p : Sigma P) : d.column (ordinaryWire d p) = Sum.inr p :=
  d.column.apply_symm_apply _

abbrev LocalPin (g : G) := {p : S // d.pinLabel p = g}
abbrev PinTile (anchor : S) := {p : S // SameTile d (pinWire d p) (pinWire d anchor)}
abbrev OldTile (anchor : S) := {v : Sigma P // SameTile d (ordinaryWire d v) (pinWire d anchor)}
abbrev LocalBits (g : G) := (v : LocalColumn d g) → LocalPort d v → Bool

def tilePinInSource {a : S} (p : PinTile d a) : LocalPin d (d.pinLabel a) :=
  ⟨p.1, by
    have h := sameTile_colLabel d p.2
    simpa only [pinWire_colLabel] using h⟩

def tileOldInSource {a : S} (p : OldTile d a) :
    Sigma (LocalPort d (g := d.pinLabel a)) :=
  ⟨⟨p.1.1, by
    have h := sameTile_colLabel d p.2
    rw [pinWire_colLabel, actualColLabel, ordinaryWire_column] at h
    exact h⟩, p.1.2⟩

variable [DecidableEq Packet]

instance (a : S) : DecidablePred (fun p : S => SameTile d (pinWire d p) (pinWire d a)) :=
  fun _ => by unfold SameTile; infer_instance

instance (a : S) : DecidablePred (fun p : Sigma P => SameTile d (ordinaryWire d p) (pinWire d a)) :=
  fun _ => by unfold SameTile; infer_instance

section Pins

variable [Fintype S]

def pinEnumeration (a : S) : Fin (Fintype.card (PinTile d a)) ≃ PinTile d a :=
  (Fintype.equivFin _).symm

def coordinates (a : S) (i : Fin (Fintype.card (PinTile d a))) : ℚ :=
  ordinal d (pinWire d (pinEnumeration d a i).1)

theorem coordinates_injective (a : S) : Function.Injective (coordinates d a) := by
  intro i j h
  have nat_eq : ordinal d (pinWire d (pinEnumeration d a i).1) =
      ordinal d (pinWire d (pinEnumeration d a j).1) := by
    unfold coordinates at h
    exact_mod_cast h
  have same := onTile_ordinal_injective d (pinEnumeration d a i).2 (pinEnumeration d a j).2 nat_eq
  apply (pinEnumeration d a).injective
  apply Subtype.ext
  exact Sum.inl.inj ((pinWire_column d (pinEnumeration d a i).1).symm.trans
    ((congrArg d.column same).trans (pinWire_column d (pinEnumeration d a j).1)))

theorem pins_per_tile (a : S) (hL : Even L) : Fintype.card (PinTile d a) ≤ L/2 := by
  let f : PinTile d a → Fin (L/2) := fun p =>
    ⟨ordinal d (pinWire d p.1), by
      have hl := (d.seat (pinWire d p.1)).2.isLt
      obtain ⟨k,hk⟩ := hL
      unfold ordinal
      omega⟩
  have inj : Function.Injective f := by
    intro u v h
    have h' := onTile_ordinal_injective d u.2 v.2 (congrArg Fin.val h)
    apply Subtype.ext
    have hs := congrArg d.column h'
    simpa only [pinWire_column, Sum.inl.injEq] using hs
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f inj

theorem singleton_weight_legal (a : S) (hL : Even L) (p : ℕ) (hp : L/2 < p)
    (b : Fin (Fintype.card (PinTile d a))) : (b : ℕ) + 1 < p := by
  have hb := b.isLt
  have hN := pins_per_tile d a hL
  omega

end Pins

section ActualTables

variable [Fintype R] [DecidableEq R] [Fintype V] [DecidableEq V] [DecidableEq G]
variable [∀ v, Fintype (P v)] [∀ v, DecidableEq (P v)]

/-- Ordinary physical parts of an enumerated source moment. Each occurrence
is counted once at its own physical tile coordinate, even when two
occurrences belong to the same old column tensor. -/
def tileBackground (a : S) (b : ℕ) (x : LocalBits d (d.pinLabel a)) : ℚ :=
  ∑ q : OldTile d a,
    (ordinal d (ordinaryWire d q.1) : ℚ)^b *
      NativeChildRealization.bitValue ℚ (x (tileOldInSource d q).1 (tileOldInSource d q).2)

def localChild (e : EndpointSeating d) (even : Even L) (g : G) (c : ℚ)
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v)) :
    J8SourceMoment.Child (LocalRow d g) (LocalBits d g) :=
  J8SourceMoment.literalChild (groupWiring d e even g) c F

variable [Fintype S] [DecidableEq S]

omit [DecidableEq Packet] in
/-- The public baseline and every targeted local derivative constant
depend only on physical old nonpin tables, not on the unary pin signs.
The higher probe coefficients need not enjoy this independence. -/
theorem physicalMarked_constant (e : EndpointSeating d) (even : Even L) (g : G) (c : ℚ)
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v))
    (sign : LocalPin d g → Bool)
    (higher : ((LocalPin d g → Bool) × LocalBits d g) → LocalRow d g → Bool → ℚ[X])
    (marked : Option (LocalRow d g × Bool)) :
    (J8SourceMoment.genuineChild (localChild d e even g c F) sign higher marked (fun _ => 1)).coeff 0 =
      ∑ x : LocalBits d g, J8SourceMoment.weighted (localChild d e even g c F) marked x := by
  rw [J8SourceMoment.childConstant]
  simp only [mul_one]

omit [DecidableEq Packet] in
theorem physicalMarked_sign_independent (e : EndpointSeating d) (even : Even L) (g : G) (c : ℚ)
    (F : (v : LocalColumn d g) → LiteralPortCompiler.CNF (LocalPort d v))
    (sign sign' : LocalPin d g → Bool)
    (higher higher' : ((LocalPin d g → Bool) × LocalBits d g) → LocalRow d g → Bool → ℚ[X])
    (marked : Option (LocalRow d g × Bool)) :
    (J8SourceMoment.genuineChild (localChild d e even g c F) sign higher marked (fun _ => 1)).coeff 0 =
      (J8SourceMoment.genuineChild (localChild d e even g c F) sign' higher' marked (fun _ => 1)).coeff 0 := by
  rw [physicalMarked_constant, physicalMarked_constant]

end ActualTables

#print axioms ordinal_equation
#print axioms coordinates_injective
#print axioms pins_per_tile
#print axioms singleton_weight_legal
#print axioms physicalMarked_constant
#print axioms physicalMarked_sign_independent

end
end J8Physical
