import A1R11Packed
import AOracleSuccinctPhysical

/-! Numeric source moments. The p-bit unsigned representative of a
public tile quotient enters a metered scalar power loop, and the result
is embedded as the literal (U^0,V^0) word. No numeric moment table is
required. The geometric address/bit extraction is not part of this loop. -/

open scoped Polynomial
namespace A1R11
open A1R10 AOracleMachineTime AOracleMachineTimeLocal AOracleMachineTimeTape
open AOracleCoordinates Polynomial AOracleSuccinctPacket

def wordPow {p : ℕ} (a : A1R10.Word p) : ℕ → Meter (A1R10.Word p)
  | 0 => ⟨wordOne p,p+2⟩
  | n+1 =>
    let t := wordPow a n
    let y := mulWord t.result a
    ⟨y.result,t.steps+y.steps+4⟩

theorem wordPow_exact {p : ℕ} (hp : 0<p) (a : A1R10.Word p) (n : ℕ) :
    wordRead (wordPow a n).result=wordRead a^n ∧
    (wordPow a n).steps≤p+2+n*(32*(p+1)^2+4) := by
  induction n with
  | zero => simp [wordPow,wordOne_read p hp]
  | succ n ih =>
    let t := wordPow a n
    let v := mulWord t.result a
    constructor
    · change wordRead v.result=_
      rw [show wordRead v.result=_ from mulWord_read _ _,ih.1,pow_succ]
    · change t.steps+v.steps+4≤p+2+(n+1)*(32*(p+1)^2+4)
      have hc := (wordOps p hp).mul_cost t.result a
      change v.steps≤32*(p+1)^2 at hc
      rw [Nat.succ_mul n]
      have h := ih.2
      change t.steps≤_ at h
      omega

def scalarUV {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : A1R10.Word p) : UVBlock f ell :=
  let b : UBlock f := ⟨constantTape (wordOps p hp).toGates f.length z,constantTape_len _ _ he _⟩
  ⟨constantTape (uGates hp f) ell b,constantTape_len _ _ hv _⟩

noncomputable def scalarToUV {p : ℕ} (hp : 0<p) (f : List (A1R10.Word p)) (ell : ℕ) :
    ZMod (2^p) →+* Truncated (Modulus p hp f) ell :=
  (AdjoinRoot.of ((X : (AdjoinRoot (Modulus p hp f))[X])^ell)).comp
      (AdjoinRoot.of (Modulus p hp f))

theorem scalarUV_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : A1R10.Word p) :
    uvRead hp f ell (scalarUV hp he hv z)=scalarToUV hp f ell (wordRead z) := by
  let b : UBlock f := ⟨constantTape (wordOps p hp).toGates f.length z,constantTape_len _ _ he _⟩
  change AdjoinRoot.mk _ (decode (uOps hp f) (constantTape (uOps hp f).toGates ell b))=_
  rw [constantTape_read]
  change AdjoinRoot.mk _ (C (AdjoinRoot.mk _ (decode (wordOps p hp)
    (constantTape (wordOps p hp).toGates f.length z))))=_
  rw [constantTape_read]
  rfl

def momentCell {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (slotQuot : A1R10.Word p) (e : ℕ) :
    Meter (UVBlock f ell) :=
  let w := wordPow slotQuot e
  ⟨scalarUV hp he hv w.result,w.steps+uvWidth f.length ell p⟩

theorem momentCell_exact {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (slotQuot : A1R10.Word p) (i y e : ℕ)
    (hslot : wordRead slotQuot=(quotient i y:ZMod (2^p))) :
    uvRead hp f ell (momentCell hp he hv slotQuot e).result=
      (quotient i y:Truncated (Modulus p hp f) ell)^e ∧
    (momentCell hp he hv slotQuot e).steps≤p+2+e*(32*(p+1)^2+4)+uvWidth f.length ell p := by
  obtain ⟨hr,hc⟩ := wordPow_exact hp slotQuot e
  constructor
  · change uvRead hp f ell (scalarUV hp he hv (wordPow slotQuot e).result)=_
    rw [scalarUV_read,hr,hslot,map_pow,map_natCast]
  · exact Nat.add_le_add_right hc _

#print axioms wordPow_exact
#print axioms scalarUV_read
#print axioms momentCell_exact
end A1R11
