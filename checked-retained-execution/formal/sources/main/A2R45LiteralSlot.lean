
import A2R45LiteralGate
import A1R43LiteralShift
import J6R15PlantedIdentityCenter
import J6R12RepackReadNatural

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 15000000
set_option maxRecDepth 1950
set_option linter.unusedSectionVars false

/-! Actual A2 physical contraction at the prescribed nonzero center -1,
zero probe and zero mode. Use the real local coefficients and all 64
actual child returns; a logical count callback is not an input. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial J6R9Recursive J6R10Repack J6R10Integral J6R11Integral P11FullPacking
open FixedHostAcquisition Acquisition A1R43Literal A1R43Literal.General J6R12Repack

noncomputable section
variable {n : ℕ} {Pad : Type} [Fintype Pad] {a : ℕ}
local notation "N" => nativeNetwork n Pad
local notation "E" => NativeWire n Pad

theorem physical_pair_argument (P : PhysicalPacking N a (Fin 64))
    (f : ℤ[X]) (p : ℕ) (d : DecidableEq (Page a P.copies (Fin 64)))
    (placed : ∀ u : Wire n,unitPredecessor P (oddWire (Wire n) Pad u) (evenWire (Wire n) Pad u))
    (x : E→Bool) (u : Wire n) :
    actualArgument (@finiteEntry E (Page a P.copies (Fin 64)) d a p f 1 (parentAtlas P) (-1) 0)
      x (oddWire (Wire n) Pad u)= -bit (x (evenWire (Wire n) Pad u)) := by
  have exactEntry (r q : E) :
      @finiteEntry E (Page a P.copies (Fin 64)) d a p f 1 (parentAtlas P) (-1) 0 r q =
        if unitPredecessor P r q then -1 else 0 := by
    have e (d' : DecidableEq (Page a P.copies (Fin 64))) :
        @finiteEntry E (Page a P.copies (Fin 64)) d a p f 1 (parentAtlas P) (-1) 0 r q =
        @finiteEntry E (Page a P.copies (Fin 64)) d' a p f 1 (parentAtlas P) (-1) 0 r q :=
      congrArg (fun j : DecidableEq (Page a P.copies (Fin 64)) =>
        @finiteEntry E (Page a P.copies (Fin 64)) j a p f 1 (parentAtlas P) (-1) 0 r q)
        (Subsingleton.elim _ _)
    exact (e _).trans (actual_kernel_minus_one P f 1 p r q)
  unfold actualArgument
  rw [Finset.sum_eq_single (evenWire (Wire n) Pad u)]
  · rw [exactEntry,if_pos (placed u)]
    cases x (evenWire (Wire n) Pad u) <;> simp [bit]
  · intro j _ h
    rw [exactEntry,if_neg (fun hx=>h (unitPredecessor_unique P _ _ _ hx (placed u)))]
    split <;> rfl
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem physical_parent_is_shifted (P : PhysicalPacking N a (Fin 64))
    (w : Input n) (f : ℤ[X]) (base p : ℕ) (hb : 0<base) (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : ∀ u : Wire n,unitPredecessor P (oddWire (Wire n) Pad u) (evenWire (Wire n) Pad u))
    (earlier : Wire n→Option (Wire n)) :
    ((parentJet P (file w f base) hf (-1)).map (reduce p f 1)).eval 0 =
      (shiftedHost w.enabled earlier : Box f 1 p) := by
  letI : DecidableEq (Page a P.copies (Fin 64)) := Classical.decEq _
  rw [parentJet,network_finite]
  have rr : reduce p f 1 ∘ J6R11Integral.rowProduct N (file w f base) hf =
      (Acquisition.rowProduct (rowTable w.enabled)) ∘ oddBits :=
    funext (rowProduct_receives w f base p hb hf hd)
  have cc : reduce p f 1 ∘ J6R11Integral.colProduct N (file w f base) hf =
      sourceColumns FixedHostAcquisition.columnTable :=
    funext (colProduct_receives w f base p hb hf hd)
  rw [rr,cc,shiftedHost,pairedRegister_collapse]
  exact filled_contract_eq_shifted _ _ _ (physical_pair_argument P f p _ placed)

theorem native_zero_polynomial (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (hi : i.val=0) (w : Input n) (f : ℤ[X]) (base p : ℕ)
    (hb : 0<base) (hp : 0<p) (hf : f.Monic) (hd : 0<f.natDegree) (hn : 0<n)
    (placed : ∀ u : Wire n,unitPredecessor P (oddWire (Wire n) Pad u) (evenWire (Wire n) Pad u)) :
    (J6R14ZeroMode.polynomial P i (-1) p (file w f base) hf).eval 0 =
      (count w.enabled:Box f 1 p) := by
  rw [J6R15PlantedIdentity.zero_eq_parentJet P i (minus_one_mem_grid a)
    (by decide : (-1:ℤ)≠0) (minus_one_odd_index a i hi) p hp (file w f base) hf,
    physical_parent_is_shifted P w f base p hb hf hd placed (fun _=>none),
    shiftedHost_eq hn]

theorem actual_named_slot (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (hi : i.val=0) (w : Input n) (f : ℤ[X]) (base p : ℕ)
    (hb : 0<base) (hp : 0<p) (hf : f.Monic) (hd : 0<f.natDegree) (hn : 0<n)
    (placed : ∀ u : Wire n,unitPredecessor P (oddWire (Wire n) Pad u) (evenWire (Wire n) Pad u)) :
    (∏ g : Fin 64, reduce p f 1
      (actualChildTruth P i (by decide : (-1:ℤ)≠0) (minus_one_odd_index a i hi)
        p 0 (file w f base) hf 0 g))=(count w.enabled:Box f 1 p) := by
  rw [← J6R14ZeroMode.polynomial_eval P i (by decide : (-1:ℤ)≠0)
    (minus_one_odd_index a i hi) p (file w f base) hf 0]
  exact native_zero_polynomial P i hi w f base p hb hp hf hd hn placed

#print axioms physical_pair_argument
#print axioms physical_parent_is_shifted
#print axioms native_zero_polynomial
#print axioms actual_named_slot
end
end A2R45Literal
