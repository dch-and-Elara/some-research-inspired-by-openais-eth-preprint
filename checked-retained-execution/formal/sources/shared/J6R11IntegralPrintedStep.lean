import J6R11IntegralParent
import J6R10IntegralPrinted

/-! At one genuine physical probe, no free old table remains: the literal
integral Taylor polynomial equals the printed row/mode sum with old
factors at their own stored creation precision. -/
namespace J6R11Integral
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking P1DyadicGrid J6R9Recursive
open J6R10Repack J6R10Integral J6R9PacketScopes J6R9PacketChild J6R10RowAffine

variable {E A B G : Type*} [Fintype E] [Fintype A] [Fintype B] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell : ℕ}

theorem actual_parent_probe (P : PhysicalPacking N a G) [Fintype (Page a P.copies G)]
    (i : Fin a) {t : ℤ} (htM : t ∈ grid a) (ht : t ≠ 0) (hv : padicValInt 2 t = i.val)
    (p : ℕ) (hp : 0 < p) (z : Box f ell p)
    (file : EntryFile f ell N) (hf : f.Monic) :
    ((parentJet P file hf t).map (reduce p f ell)).eval z =
      ∑ β ∈ J6RecursiveMenu.menu p (weight i p P.mask), ∏ g,
        J6R10RowPrinted.reconstructedChild (fun e => P.seat e) (fun e => P.seat e) P.mask i
          ht hv p (box_two_nil p f ell) z (fun g v => oldState P i g p file hf v) β g := by
  let e := Equiv.refl E
  have pair : ∀ r : E, (fun x => P.seat x) (e r) = P.seat r := fun _ => rfl
  unfold parentJet parentAtlas
  exact finite_from_printed_children (fun x => P.seat x) (fun x => P.seat x)
    P.seat.injective e pair P.mask i htM ht hv p hp z (rowProduct N file hf)
    (colProduct N file hf) (fun g v => oldState P i g p file hf v)
    (oldState_factors P i p file hf)

#print axioms actual_parent_probe
end J6R11Integral
