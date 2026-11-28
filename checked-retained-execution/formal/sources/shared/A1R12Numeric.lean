import A1R12Table

/-! Full native numeric cell producer for fixed physical addresses and
a supplied probe register. Its tapes contain no input-dependent
assignment records or externally supplied Cauchy/crossing values. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleCoordinates
open AOracleSuccinctPacket AOracleSuccinctKernel AOracleSuccinctPhysical P1DyadicGrid

def localCellCap (e ell p a : ℕ) (hp : 0<p) : ℕ :=
  modularGenCap e ell p a hp+8*(a+3)^2

def localCellGen {p ell r c packets G a : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (t : ℤ)
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a)) (j : Fin r) (k : Fin c) :
    Meter (UVBlock f ell) :=
  padCost (modularGen hp he hv z a t (((col.slot k).val:ℤ)-((row.slot j).val:ℤ))) (8*(a+3)^2)

theorem localCellGen_exact {p ell r c packets G a : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (t : ℤ) (ht : t∈grid a)
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a)) (j : Fin r) (k : Fin c) :
    uvRead hp f ell (localCellGen hp he hv z t row col j k).result=
      modular p a t (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) (uvRead hp f ell z) ∧
    (localCellGen hp he hv z t row col j k).steps≤localCellCap f.length ell p a hp := by
  obtain ⟨hr,hc⟩ := modularGen_exact hp he hv z a t _ ht (literal_slot_difference (row.slot j) (col.slot k))
  exact ⟨hr,Nat.add_le_add_right hc _⟩

theorem crossingCap_mono (e ell p a i b B : ℕ) (hp : 0<p) (h : b≤B) :
    crossingGenCap e ell p a i b hp≤crossingGenCap e ell p a i B hp := by
  unfold crossingGenCap crossScaleCap crossPowerCap scaleCap
  gcongr

def crossCellGen {p ell r packets G a i : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (t : ℤ)
    (row : Ports r packets G (2^a)) (j : Fin r) (k : Mode packets G i p) : Meter (UVBlock f ell) :=
  crossingGen hp he hv z a i k.exponent.val t (row.slot j).val k.tile.val

theorem crossCellGen_exact {p ell r packets G a i : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (t : ℤ) (ht : t∈grid a)
    (row : Ports r packets G (2^a)) (j : Fin r) (k : Mode packets G i p) :
    uvRead hp f ell (crossCellGen hp he hv z t row j k).result=
      crossCell p a i k.exponent.val t (row.slot j).val k.tile.val (uvRead hp f ell z) ∧
    (crossCellGen hp he hv z t row j k).steps≤crossingGenCap f.length ell p a i p hp := by
  obtain ⟨hr,hc⟩ := crossingGen_exact hp he hv z a i k.exponent.val t _ _ ht
    (row.slot j).isLt k.tile.isLt
  have hm : k.exponent.val≤p := by have := k.exponent.isLt; omega
  exact ⟨hr,hc.trans (crossingCap_mono _ _ _ _ _ _ _ hp hm)⟩

def quotientCap (p a i : ℕ) : ℕ := 16*(a+i+p+4)^2

def quotientGen (p a i : ℕ) (slot : Fin (2^a)) : Meter (A1R10.Word p) :=
  ⟨natWord p (slot.val >>> (i+1)),quotientCap p a i⟩

theorem quotientGen_exact (p a i : ℕ) (slot : Fin (2^a)) :
    wordRead (quotientGen p a i slot).result=(quotient i slot.val:ZMod (2^p)) := by
  unfold quotientGen quotient
  rw [natWord_read,Nat.shiftRight_eq_div_pow]

structure Numeric {p : ℕ} (f : List (A1R10.Word p)) (ell : ℕ) where
  locals : List (List (UVBlock f ell))
  crosses : List (List (UVBlock f ell))
  quotients : List (A1R10.Word p)

def numericGen {p ell r c m packets G a i : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (t : ℤ)
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) : Meter (Numeric f ell) :=
  let w := uvWidth f.length ell p
  let l := matrixMap (localCellGen hp he hv z t row col) w
  let c := matrixMap (fun j k => crossCellGen hp he hv z t row j (modes k)) w
  let q := vectorMap (fun k => quotientGen p a i (col.slot k)) p
  ⟨⟨l.result,c.result,q.result⟩,l.steps+c.steps+q.steps+6⟩

def numericCap (r c m e ell p a i : ℕ) (hp : 0<p) : ℕ :=
  r*(c*(localCellCap e ell p a hp+uvWidth e ell p+4)+4)+
   r*(m*(crossingGenCap e ell p a i p hp+uvWidth e ell p+4)+4)+
   c*(quotientCap p a i+p+4)+6

def Numeric.localAt {p ell r c : ℕ} {f : List (A1R10.Word p)}
    (hp : 0<p) (T : Numeric f ell) (j : Fin r) (k : Fin c) : UVBlock f ell :=
  (T.locals.getD j.val []).getD k.val (uvZero hp f ell)

def Numeric.crossAt {p ell r m : ℕ} {f : List (A1R10.Word p)}
    (hp : 0<p) (T : Numeric f ell) (j : Fin r) (k : Fin m) : UVBlock f ell :=
  (T.crosses.getD j.val []).getD k.val (uvZero hp f ell)

def Numeric.quotientAt {p ell c : ℕ} {f : List (A1R10.Word p)}
    (T : Numeric f ell) (k : Fin c) : A1R10.Word p :=
  T.quotients.getD k.val (wordZero p)

theorem numericGen_exact {p ell r c m packets G a i : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (z : UVBlock f ell) (t : ℤ) (ht : t∈grid a)
    (row : Ports r packets G (2^a)) (col : Ports c packets G (2^a))
    (modes : Fin m → Mode packets G i p) :
    let u := numericGen hp he hv z t row col modes
    (∀ j k,uvRead hp f ell (u.result.localAt hp j k)=
      modular p a t (((col.slot k).val:ℤ)-((row.slot j).val:ℤ)) (uvRead hp f ell z)) ∧
    (∀ j k,uvRead hp f ell (u.result.crossAt hp j k)=
      crossCell p a i (modes k).exponent.val t (row.slot j).val
        (modes k).tile.val (uvRead hp f ell z)) ∧
    (∀ k,wordRead (u.result.quotientAt k)=(quotient i (col.slot k).val:ZMod (2^p))) ∧
    u.steps≤numericCap r c m f.length ell p a i hp := by
  let L := localCellGen hp he hv z t row col
  let C := fun j k => crossCellGen hp he hv z t row j (modes k)
  let Q := fun k => quotientGen p a i (col.slot k)
  obtain ⟨hl,hlc⟩ := matrixMap_exact L (uvWidth f.length ell p) (localCellCap f.length ell p a hp)
    (fun j k => (localCellGen_exact hp he hv z t ht row col j k).2)
  obtain ⟨hc,hcc⟩ := matrixMap_exact C (uvWidth f.length ell p) (crossingGenCap f.length ell p a i p hp)
    (fun j k => (crossCellGen_exact hp he hv z t ht row j (modes k)).2)
  obtain ⟨hq,hqc⟩ := vectorMap_exact Q p (quotientCap p a i) (fun _ => le_rfl)
  refine ⟨?_,?_,?_,?_⟩
  · intro j k
    change uvRead hp f ell (((matrixMap L _).result.getD j.val []).getD k.val (uvZero hp f ell))=_
    rw [hl,getD_ofFn,getD_ofFn]
    exact (localCellGen_exact hp he hv z t ht row col j k).1
  · intro j k
    change uvRead hp f ell (((matrixMap C _).result.getD j.val []).getD k.val (uvZero hp f ell))=_
    rw [hc,getD_ofFn,getD_ofFn]
    exact (crossCellGen_exact hp he hv z t ht row j (modes k)).1
  · intro k
    change wordRead ((vectorMap Q p).result.getD k.val (wordZero p))=_
    rw [hq,getD_ofFn]
    exact quotientGen_exact p a i (col.slot k)
  · exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hlc hcc) hqc) _

#print axioms localCellGen_exact
#print axioms crossingCap_mono
#print axioms crossCellGen_exact
#print axioms quotientGen_exact
#print axioms numericGen_exact
end A1R12
