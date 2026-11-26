import J6R10RowPrinted

/-! A public definitional interface for the printed child; downstream
packet replay need not refer to the private generic helper in RowPrinted. -/
namespace J6R11RowFormula
open scoped BigOperators Classical
open P11FullPacking J6R9PacketScopes J6R9PacketChild
open J6R10RowPrinted J6R10RowIdentity J6R10RowAffine J6R10PacketAssembly

noncomputable def canonicalChild {R I M G K : Type*} [CommRing R]
    [Fintype I] [Fintype M] [Fintype G] [Fintype K]
    {V : G → Type*} [∀ g, Fintype (V g)]
    (block : I → G × K) (target source : M → G × K)
    (old : ∀ g, V g → R) (L : ∀ m, V (source m).1 → R)
    (bit : ∀ g, V g → I → Bool) (base : ∀ g, V g → I → R)
    (cross : ∀ g, V g → I → M → R) (β : M →₀ ℕ) (g : G) : R :=
  J6RecursiveModes.child target source (actualRows block) old bit base cross
    (fun g y m => if h : (source m).1 = g then L m (h.symm ▸ y) else 0) β g

variable {A Q S R : Type*} [Fintype A] [Fintype Q] [LinearOrder S] [CommRing R] {a b : ℕ}
  [Fintype S] [Fintype (Page a b S)]

theorem reconstructedChild_formula (ρ : A → Physical a b S) (κ : Q → Physical a b S)
    (mask : MaskFamily a b S) (i : Fin a) {t : ℤ}
    (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2:R)^p=0) (z : R)
    (old : ∀ g, State ρ κ mask i g→R) (β : Mode i p mask→₀ℕ) (g : S) :
    reconstructedChild ρ κ mask i ht hv p hnil z old β g =
      canonicalChild (block ρ mask i) (targetGP mask i) (sourceGP mask i)
        old (fun m v => moment κ mask i m v.2)
        (groupBit ρ κ mask i) (groupBase ρ κ mask i t p hnil z)
        (fun _ _ r m => scaledRow mask i ht hv p hnil z (ρ r) m) β g := rfl

#print axioms reconstructedChild_formula
end J6R11RowFormula
