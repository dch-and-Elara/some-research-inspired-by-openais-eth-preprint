import J7SeatSource
import J8Physical

/-! # Canonical conversion of subdivision and old-column physical ports -/
open scoped BigOperators Classical

namespace J7ToJ8Incidence
open J7SourceLabels J7SeatSource J7FullWordAssembly

noncomputable section

variable {Pair Row Col W : Type*}

abbrev Subdivision (Pair Row : Type*) := Pin Pair ⊕ Row

abbrev Ports (col : W → OrdinaryColumn Pair Col) (v : OrdinaryColumn Pair Col) :=
  {w : Wire Pair W // colNode col w = .inr v}

def rowPrivateFiber (row : W → Row) (p : Pin Pair) :
    {e : Wire Pair W // rowNode row e = .inl p} ≃ Bool where
  toFun e := match e.val with
    | .inl (_,b) => b
    | .inr _ => false
  invFun b := ⟨.inl (p,b),rfl⟩
  left_inv := by
    rintro ⟨e,h⟩
    cases e with
    | inl x =>
      obtain ⟨q,b⟩ := x
      have hh : q = p := Sum.inl.inj h
      subst q
      rfl
    | inr w => cases h
  right_inv _ := rfl

def rowOrdinaryFiber (row : W → Row) (v : Row) :
    {e : Wire Pair W // rowNode row e = .inr v} ≃ {w : W // row w = v} where
  toFun e := match e with
    | ⟨.inl (_, _),h⟩ => nomatch h
    | ⟨.inr w,h⟩ => ⟨w,Sum.inr.inj h⟩
  invFun w := ⟨.inr w.val,congrArg Sum.inr w.prop⟩
  left_inv := by
    rintro ⟨⟨p,b⟩|w,h⟩
    · cases h
    · rfl
  right_inv := by rintro ⟨w,h⟩; rfl

private def boolOfCard (X : Type*) (h : Nat.card X = 2) : X ≃ Bool := by
  letI : Finite X := Nat.finite_of_card_ne_zero (by rw [h]; decide)
  letI : Fintype X := Fintype.ofFinite X
  apply Fintype.equivOfCardEq
  rw [← Nat.card_eq_fintype_card, h, Fintype.card_bool]

def rowFiber (row : W → Row) (two : ∀ v, Nat.card {w : W // row w = v} = 2) :
    (v : Subdivision Pair Row) → {e : Wire Pair W // rowNode row e = v} ≃ Bool
  | .inl p => rowPrivateFiber row p
  | .inr v => (rowOrdinaryFiber row v).trans (boolOfCard _ (two v))

/-- Every actual subdivision has two ports. No port from an ordinary
row is invented or discarded; its two incidences are enumerated once. -/
def rowWire (row : W → Row) (two : ∀ v, Nat.card {w : W // row w = v} = 2) :
    J8Physical.Wire (Subdivision Pair Row) ≃ Wire Pair W :=
  ((Equiv.sigmaEquivProd (Subdivision Pair Row) Bool).symm.trans
    (Equiv.sigmaCongrRight (fun v => (rowFiber (Pair:=Pair) row two v).symm))).trans
      (Equiv.sigmaFiberEquiv (rowNode (Pair:=Pair) row))

theorem rowWire_owner (row : W → Row) (two : ∀ v, Nat.card {w : W // row w = v} = 2)
    (w : J8Physical.Wire (Subdivision Pair Row)) :
    rowNode row (rowWire row two w) = w.1 :=
  ((rowFiber row two w.1).symm w.2).prop

/-- Column ports are precisely the actual fibres of the old vertices;
the pin wires are enumerated separately by their original pin identifiers. -/
def colWire (col : W → OrdinaryColumn Pair Col) :
    J8Physical.ColPort (Pin Pair) (Ports col) ≃ Wire Pair W where
  toFun x := match x with
    | .inl p => pinEmbed Pair W p
    | .inr w => w.2.val
  invFun e := match h : colNode col e with
    | .inl p => .inl p
    | .inr v => .inr ⟨v,⟨e,h⟩⟩
  left_inv := by
    rintro (p | ⟨v,w⟩)
    · rfl
    · have hs := w.prop
      simp only
      split
      · rename_i vp hp
        rw [hs] at hp
        cases hp
      · rename_i vp hp
        have he : vp = v := Sum.inr.inj (hp.symm.trans hs)
        subst vp
        rfl
  right_inv := by
    rintro (⟨p,k⟩ | w)
    · cases k <;> rfl
    · rfl

theorem colWire_owner (col : W → OrdinaryColumn Pair Col)
    (x : J8Physical.ColPort (Pin Pair) (Ports col)) :
    colNode col (colWire col x) = Sum.map id Sigma.fst x := by
  rcases x with p | ⟨v,w⟩
  · rfl
  · exact w.prop

theorem colWire_pin (col : W → OrdinaryColumn Pair Col) (p : Pin Pair) :
    colWire col (.inl p) = pinEmbed Pair W p := rfl

/-- Private equality column ports: its selected private leg and exactly
the ordinary legs that really hit it. -/
def clonePorts (col : W → OrdinaryColumn Pair Col) (p : Pin Pair) :
    Ports col (.inl p) ≃ Unit ⊕ {w : W // col w = .inl p} where
  toFun e := match e with
    | ⟨.inl (_,false),h⟩ => nomatch h
    | ⟨.inl (_,true),_⟩ => .inl ()
    | ⟨.inr w,h⟩ => .inr ⟨w,Sum.inr.inj h⟩
  invFun e := match e with
    | .inl _ => ⟨.inl (p,true),rfl⟩
    | .inr w => ⟨.inr w.val,congrArg Sum.inr w.prop⟩
  left_inv := by
    rintro ⟨⟨q,k⟩|w,h⟩
    · cases k
      · cases h
      · have hh : q = p := Sum.inl.inj (Sum.inr.inj h)
        subst q
        rfl
    · rfl
  right_inv := by rintro (⟨⟩|⟨w,h⟩) <;> rfl

def ordinaryPorts (col : W → OrdinaryColumn Pair Col) (c : Col) :
    Ports col (.inr c) ≃ {w : W // col w = .inr c} where
  toFun e := match e with
    | ⟨.inl (_,false),h⟩ => nomatch h
    | ⟨.inl (_,true),h⟩ => nomatch h
    | ⟨.inr w,h⟩ => ⟨w,Sum.inr.inj h⟩
  invFun w := ⟨.inr w.val,congrArg Sum.inr w.prop⟩
  left_inv := by
    rintro ⟨⟨p,k⟩|w,h⟩
    · cases k <;> cases h
    · rfl
  right_inv := by rintro ⟨w,h⟩; rfl

#print axioms rowWire
#print axioms rowWire_owner
#print axioms colWire
#print axioms colWire_owner
#print axioms clonePorts
#print axioms ordinaryPorts

end
end J7ToJ8Incidence
