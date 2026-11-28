import V8PooledMenuPolynomial
import V8PooledMenuGrid
import J6R10IntegralFinite

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000

namespace V8PooledMenu

open scoped BigOperators Polynomial Classical
open Polynomial P1DyadicGrid P11FullPacking J6R10Repack J6R9Recursive
open J6R9PacketScopes J6R10Integral

noncomputable section

/-- Exact projection through the literal two quotients. -/
def observe (f : ℤ[X]) (p q : ℕ) (hle : q≤p) : Residue f 1 p →+* Residue f 1 q :=
  adjoinMap (NativeProbeRing.reduceScalar q p hle f) (X^1) (X^1) (by simp)

theorem observe_address (f : ℤ[X]) (p q : ℕ) (hle : q≤p) (w : Fin f.natDegree→Bool) :
    observe f p q hle (J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f w)) =
      J6ActiveInterpolation.scalarIn q f 1 (NativeProbeRing.probe q f w) := by
  unfold observe J6ActiveInterpolation.scalarIn
  rw [adjoinMap_of]
  congr 1
  exact NativeProbeRing.same_probe_at_higher_precision q p hle f w

namespace FiveCopy
open V8PooledRange V8PooledRange.NativeOrigin

variable (V : Type) [Fintype V]

def rootSize : ℕ := 25*Fintype.card V/2+3
def wireSize : ℕ := 30*Fintype.card V+4

/-- Literal printed epsilon = 1/(128*1024). -/
def rootU : ℕ := Nat.clog 2 (rootSize V)/(128*1024)
def rootA : ℕ := 2*rootU V

theorem root_sizes {E : Type} [Fintype E] (G : Graph V E) (p : ThreePorts G) :
    wireSize V = Fintype.card (Edge V E) ∧
    rootSize V = Fintype.card (Variable V)+Fintype.card (ClauseId V E) := by
  exact ⟨(wires_card G p).symm,(source_register_dimensions G p).2.1.symm⟩

abbrev Site := Center (rootA V) (wireSize V) (rootU V)

structure PublicPrecision where
  prec : Fin (rootU V) → ℕ
  positive : ∀ i, 0<prec i
  cap : ∀ i, prec i≤rootA V+1-i.val

variable {V}

def rootIndex (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V) : Fin (rootA V) :=
  (level hu huM t).castLE (by unfold rootA; omega)

theorem rootIndex_val (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V) :
    padicValInt 2 t.val = (rootIndex hu huM t).val := rfl

theorem nonzero_site (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V) : t.val≠0 :=
  ((active_iff hu huM).mp t.property).2.1

def high (t : Site V) : ℕ :=
  J6ActiveSchedule.childPrecision (rootPrec V) (rootA V) (wireSize V) (rootU V) t.val

def low (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (lowPrecision : PublicPrecision V) (t : Site V) : ℕ :=
  lowPrecision.prec (level hu huM t)

theorem precision_fits (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (P : PublicPrecision V) (t : Site V) :
    low hu huM P t ≤ high t := by
  have hcap := (P.cap (level hu huM t)).trans (Nat.sub_le _ _)
  apply hcap.trans
  have hM : 0<8*wireSize V := by unfold wireSize; omega
  have hm : rootA V+1 ≤ 8*wireSize V*(rootA V+1) :=
    Nat.le_mul_of_pos_left _ hM
  unfold high J6ActiveSchedule.childPrecision J9PrintedSchedule.precision
  omega

/-- Public prescribed words for the exact printed number of interpolation
probes at each active center. Addresses are fixed before the input signs. -/
def probeCount (V : Type) [Fintype V] : ℕ :=
  J9PrintedSchedule.probeCount (wireSize V) (2^rootA V)

structure Probes (V : Type) [Fintype V] (f : ℤ[X]) where
  word : Site V → Fin (probeCount V) →
    Fin f.natDegree → Bool
  distinct : ∀ t, Function.Injective (word t)

variable {E : Type} [Fintype E] {G : Graph V E} {p : ThreePorts G} {f : ℤ[X]}

abbrev Packing (G : Graph V E) (p : ThreePorts G) :=
  PhysicalPacking (network G p) (rootA V) (Fin 64)

structure Address (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V) (t : Site V) where
  probeIdx : Fin (probeCount V)
  beta : Mode (rootIndex hu huM t) (high t) P.mask →₀ ℕ
  legal : beta ∈ J6RecursiveMenu.menu (high t) (J6R10RowAffine.weight (rootIndex hu huM t) (high t) P.mask)

abbrev PublicTape (hu : 0<rootU V) (huM : rootU V≤wireSize V) (L : PublicPrecision V) :=
  Tape (a:=rootA V) hu huM L.prec

abbrev WholeMenu (f : ℤ[X]) (P : Packing G p)
    (hu : 0<rootU V) (huM : rootU V≤wireSize V) (L : PublicPrecision V) :=
  (t : Site V) → Address P hu huM t → Residue f 1 (low hu huM L t)

def readProbe (f : ℤ[X]) (p : ℕ) (bits : Fin f.natDegree→Bool) : Residue f 1 p :=
  J6ActiveInterpolation.scalarIn p f 1 (NativeProbeRing.probe p f bits)

def encodeWhole (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (L : PublicPrecision V) (s : V → Bool) : PublicTape hu huM L :=
  fun t => digits (low hu huM L t)
    (wholeScaled P (rootIndex hu huM t) t.val (flags G p s))

def nativeMenu (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (L : PublicPrecision V) (probes : Probes V f) (hf : f.Monic) (s : V → Bool) :
    WholeMenu f P hu huM L :=
  fun t adr =>
    observe f (high t) (low hu huM L t) (precision_fits hu huM L t)
      (slot P (rootIndex hu huM t) (nonzero_site hu huM t) (rootIndex_val hu huM t)
        (high t) (box_two_nil (high t) f 1)
        (readProbe f (high t) (probes.word t adr.probeIdx))
        (file f G p s) hf adr.beta)

def decodeWhole (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (L : PublicPrecision V) (probes : Probes V f) (tape : PublicTape hu huM L) :
    WholeMenu f P hu huM L :=
  fun t adr => if adr.beta=0 then
    TruncatedProbeMenu.reconstruct (tape t) (readProbe f (low hu huM L t) (probes.word t adr.probeIdx))
    else 0

/-- At every active signed center, every admissible original mode and
every prescribed original probe is reconstructed from the very same
input's base tape. The root and packing are independent of the signs. -/
theorem nativeMenu_eq (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (L : PublicPrecision V) (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree)
    (s : V → Bool) :
    nativeMenu P hu huM L probes hf s = decodeWhole P hu huM L probes (encodeWhole P hu huM L s) := by
  funext t adr
  have hcap : low hu huM L t ≤ rootA V+1-(rootIndex hu huM t).val := L.cap (level hu huM t)
  unfold nativeMenu decodeWhole encodeWhole file
  rw [receive_actual_slot P (rootIndex hu huM t) (nonzero_site hu huM t)
    (rootIndex_val hu huM t) (flags G p s) (rootPrec V) (rootPrec_pos V) hf hd
    (high t) (box_two_nil (high t) f 1) _ adr.beta
    (observe f (high t) (low hu huM L t) (precision_fits hu huM L t)) hcap
    (box_two_nil (low hu huM L t) f 1)]
  unfold readProbe
  rw [observe_address]

theorem tape_budget (hu : 0<rootU V) (huM : rootU V≤wireSize V) (L : PublicPrecision V) :
    Fintype.card (PublicTape hu huM L) = 2^pooledBits (rootA V) (rootU V) L.prec :=
  exact_tape_card hu huM (by unfold rootA; omega) L.prec

theorem whole_menu_capacity (P : Packing G p) (hu : 0<rootU V) (huM : rootU V≤wireSize V)
    (L : PublicPrecision V) (probes : Probes V f) (hf : f.Monic) (hd : 0<f.natDegree) :
    Nat.card (Set.range (nativeMenu P hu huM L probes hf)) ≤
      2^pooledBits (rootA V) (rootU V) L.prec := by
  have hsub : Set.range (nativeMenu P hu huM L probes hf) ⊆ Set.range (decodeWhole P hu huM L probes) := by
    rintro x ⟨s,rfl⟩
    exact ⟨encodeWhole P hu huM L s,(nativeMenu_eq P hu huM L probes hf hd s).symm⟩
  calc
    _ ≤ Nat.card (Set.range (decodeWhole P hu huM L probes)) :=
      Nat.card_le_card_of_injective (Set.inclusion hsub) (Set.inclusion_injective hsub)
    _ ≤ Nat.card (PublicTape hu huM L) := Finite.card_range_le _
    _ = _ := by rw [Nat.card_eq_fintype_card,tape_budget]

theorem source_C4_strict (L : PublicPrecision V) :
    pooledBits (rootA V) (rootU V) L.prec <
      (2*2^rootA V)*triangle (rootA V+1) :=
  pooledBits_strict (by unfold rootA; omega) L.prec L.cap

#print axioms root_sizes
#print axioms precision_fits
#print axioms nativeMenu_eq
#print axioms tape_budget
#print axioms whole_menu_capacity
#print axioms source_C4_strict

end FiveCopy
end
end V8PooledMenu
