import P5MainBalanceM6SparseFamilies

/-! Typed actual port chart of each sparse equation witness, including
the distinct neutral slot at every assignment variable. Label choices
are still the original input-independent placement choices. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator
open scoped BigOperators Classical

variable {V Copy I B : Type*} [LinearOrder B]

def uFactorOf (G : Finset (V×V)) : UPort G→UFactor G
  | .inl (.inl v) => .inl (.inl v)
  | .inl (.inr (e,_)) => .inl (.inr e)
  | .inr v => .inr v

def uOwnerOf (G : Finset (V×V)) : UPort G→V
  | .inl (.inl v) => v
  | .inl (.inr (e,false)) => e.val.1
  | .inl (.inr (e,true)) => e.val.2
  | .inr v => v

def cFactorOf (G : Finset (V×V)) : CPort G→CFactor G
  | .inl e => .inl (Direct.factorOf G e)
  | .inr v => .inr v

def cOwnerOf (G : Finset (V×V)) (left right : G→Fin 4) : CPort G→V×Fin 4
  | .inl e => Direct.ownerOf G left right e
  | .inr v => v

def uMark (G : Finset (V×V)) : V↪UPort G :=
  ⟨fun v=>.inl (.inl v),fun _ _ h=>Sum.inl.inj (Sum.inl.inj h)⟩

def cMark (G : Finset (V×V)) : V↪CPort G :=
  ⟨fun v=>.inl (.inl v),fun _ _ h=>Sum.inl.inj (Sum.inl.inj h)⟩

structure UChart (G : Finset (V×V)) where
  physical : SourceLayout (UPort G) V (UFactor G) Copy I B
  factor_is : physical.factor=uFactorOf G
  owner_is : physical.placement.owner=uOwnerOf G

structure CChart (G : Finset (V×V)) (left right : G→Fin 4) where
  physical : SourceLayout (CPort G) (V×Fin 4) (CFactor G) Copy I B
  factor_is : physical.factor=cFactorOf G
  owner_is : physical.placement.owner=cOwnerOf G left right

variable {G : Finset (V×V)} {left right : G→Fin 4}

def UChart.pin (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) (v : V) :
    {e : UPort G // L.physical.factor e=.inl (.inl v)} :=
  ⟨.inl (.inl v),by rw [L.factor_is]; rfl⟩

def UChart.edge (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) (e : G) (b : Bool) :
    {p : UPort G // L.physical.factor p=.inl (.inr e)} :=
  ⟨.inl (.inr (e,b)),by rw [L.factor_is]; rfl⟩

def CChart.pin (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) (v : V) :
    {e : CPort G // L.physical.factor e=.inl (.inl v)} :=
  ⟨.inl (.inl v),by rw [L.factor_is]; rfl⟩

def CChart.edge (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) (e : G) (b : Bool) :
    {p : CPort G // L.physical.factor p=.inl (.inr (.inl e))} :=
  ⟨.inl (.inr (.inl (e,b))),by rw [L.factor_is]; rfl⟩

def CChart.cycle (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) (v : V) (i : Fin 4) (b : Bool) :
    {p : CPort G // L.physical.factor p=.inl (.inr (.inr (v,i)))} :=
  ⟨.inl (.inr (.inr (v,i,b))),by rw [L.factor_is]; rfl⟩

theorem UChart.pin_owner (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) (v : V) :
    signedOwner L.physical (uMark G) v=.inl (.inl v) := by
  simp only [signedOwner,Function.comp_apply,L.factor_is]
  rfl

theorem CChart.pin_owner (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) (v : V) :
    signedOwner L.physical (cMark G) v=.inl (.inl v) := by
  simp only [signedOwner,Function.comp_apply,L.factor_is]
  rfl

def UChart.sign (L : UChart (Copy:=Copy) (I:=I) (B:=B) G) (v : V)
    (s : {v' : V // signedOwner L.physical (uMark G) v'=.inl (.inl v)}→Bool) : Bool :=
  s ⟨v,L.pin_owner v⟩

def CChart.sign (L : CChart (Copy:=Copy) (I:=I) (B:=B) G left right) (v : V)
    (s : {v' : V // signedOwner L.physical (cMark G) v'=.inl (.inl v)}→Bool) : Bool :=
  s ⟨v,L.pin_owner v⟩

#print axioms UChart.pin_owner
#print axioms CChart.pin_owner
end P5MainBalance.M6.Sparse
