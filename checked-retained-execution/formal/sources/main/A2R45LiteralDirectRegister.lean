import A2R45LiteralDirectNative
import A2R45LiteralAllModesSparse
import J6R12RepackReadNatural

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 13500000
set_option maxRecDepth 2300
set_option linter.unusedSectionVars false

/-! The direct A2 graph's own native -1, zero-probe, zero-mode product;
not the ordinary clause compiler or independent-set switch graph.
A legal matching layout and its precision remain supplied. -/
namespace A2R45Literal
open scoped Classical BigOperators Polynomial
open Polynomial Std.Sat J7R9Compiler Acquisition
open A1R43Literal A1R43Literal.General J6R10Repack J6R9Recursive J6R11Integral
open J6R10Integral P11FullPacking J6R12Repack

noncomputable section
variable {V : Type} [DecidableEq V] [Fintype V] (F : CNF V) {Pad : Type} [Fintype Pad] {a : ℕ}
local notation "U" => DirectWire F
local notation "E" => SplitWire U Pad
local notation "N" => directPhysical (Pad:=Pad) F

def pairedDirect (P : PhysicalPacking N a (Fin 64)) : Prop :=
  ∀ u : U,unitPredecessor P (oddWire U Pad u) (evenWire U Pad u)

theorem direct_literal_finite_argument (P : PhysicalPacking N a (Fin 64))
    (f : ℤ[X]) (p : ℕ) (d : DecidableEq (Page a P.copies (Fin 64)))
    (placed : pairedDirect F P) (x : E→Bool) (u : U) :
    actualArgument (@finiteEntry E (Page a P.copies (Fin 64)) d a p f 1 (parentAtlas P) (-1) 0)
      x (oddWire U Pad u)= -bit (x (evenWire U Pad u)) := by
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
  rw [Finset.sum_eq_single (evenWire U Pad u)]
  · rw [exactEntry,if_pos (placed u)]
    cases x (evenWire U Pad u) <;> simp [bit]
  · intro j _ h
    rw [exactEntry,if_neg (fun hx=>h (unitPredecessor_unique P _ _ _ hx (placed u)))]
    split <;> rfl
  · intro h
    exact (h (Finset.mem_univ _)).elim

theorem direct_literal_parent_minus_one (P : PhysicalPacking N a (Fin 64))
    (f : ℤ[X]) (p : ℕ) (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : pairedDirect F P) (occurs : AllOccur F) :
    ((parentJet P (directNativeFile F f (Fintype.card V+1)) hf (-1)).map (reduce p f 1)).eval 0 =
      (PinnedCNF.modelCount F : Box f 1 p) := by
  letI : DecidableEq (Page a P.copies (Fin 64)) := Classical.decEq _
  rw [parentJet,network_finite]
  have rr : reduce p f 1 ∘ J6R11Integral.rowProduct N
      (directNativeFile F f (Fintype.card V+1)) hf =
      (Acquisition.rowProduct (fun r z=>bit (directGateTable F r z)) ∘ oddBits) :=
    funext (direct_rows_exact F f p _ (Nat.succ_pos _) hf hd)
  have cc : reduce p f 1 ∘ J6R11Integral.colProduct N
      (directNativeFile F f (Fintype.card V+1)) hf = sourceColumns (directColumnTensor F) :=
    funext (direct_cols_exact F f p _ (Nat.succ_pos _) hf hd)
  rw [rr,cc,filled_contract_eq_shifted _ _ _ (direct_literal_finite_argument F P f p _ placed)]
  exact actual_direct_counting_tensor F occurs

theorem direct_literal_completed_mode (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (hi : i.val=0) (f : ℤ[X]) (p : ℕ)
    (hp : 0<p) (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : pairedDirect F P) (occurs : AllOccur F) :
    (∏ g : Fin 64,reduce p f 1
      (actualChildTruth P i (by decide : (-1:ℤ)≠0) (minus_one_odd_index a i hi)
        p 0 (directNativeFile F f (Fintype.card V+1)) hf 0 g)) =
          (PinnedCNF.modelCount F : Box f 1 p) := by
  rw [← J6R14ZeroMode.polynomial_eval P i (by decide : (-1:ℤ)≠0)
    (minus_one_odd_index a i hi) p (directNativeFile F f (Fintype.card V+1)) hf 0,
    J6R15PlantedIdentity.zero_eq_parentJet P i (minus_one_mem_grid a)
      (by decide : (-1:ℤ)≠0) (minus_one_odd_index a i hi) p hp
      (directNativeFile F f (Fintype.card V+1)) hf]
  exact direct_literal_parent_minus_one F P f p hf hd placed occurs

theorem direct_literal_completed_integer (P : PhysicalPacking N a (Fin 64))
    (i : Fin a) (hi : i.val=0) (f : ℤ[X]) (p : ℕ)
    (hp : Fintype.card V+1≤p) (hf : f.Monic) (hd : 0<f.natDegree)
    (placed : pairedDirect F P) (occurs : AllOccur F) :
    boxNatural f 1 p hf (∏ g : Fin 64,reduce p f 1
      (actualChildTruth P i (by decide : (-1:ℤ)≠0) (minus_one_odd_index a i hi)
        p 0 (directNativeFile F f (Fintype.card V+1)) hf 0 g)) =
          PinnedCNF.modelCount F := by
  have hp0 : 0<p := (Nat.succ_pos _).trans_le hp
  rw [direct_literal_completed_mode F P i hi f p hp0 hf hd placed occurs]
  apply boxNatural_of_nat f 1 p hf hp0 (by decide) hd
  exact (raw_models_fit F f).trans_le (Nat.pow_le_pow_right (by decide) hp)

#print axioms direct_literal_finite_argument
#print axioms direct_literal_parent_minus_one
#print axioms direct_literal_completed_mode
#print axioms direct_literal_completed_integer
end
end A2R45Literal
