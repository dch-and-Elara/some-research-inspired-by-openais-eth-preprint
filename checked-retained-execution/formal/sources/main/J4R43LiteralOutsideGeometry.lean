import V8NativeMessageN7LiteralSupportGeometry

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 5500000

/-! Real geometric guards for the entire J4 signed outer band.  There
is one physical packing, independent of the signs and the query node.
No single-node assertion enters the proof of the band geometry. -/
namespace J4R43LiteralOutside
open P11FullPacking J6R10Repack V8NativeMessage.N7LiteralSupport
open scoped Classical

variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ}
variable {N : Network E A B}

/-- First and last h mesh positions of a packet. -/
def InBand (L h j : ℕ) : Prop := j<h ∨ L-h≤j

def rowHit (P : PhysicalPacking N a G) (t : ℤ) (r : E) : Prop := ∃ q : E, V8NativeMessage.N7LiteralSupport.Matches P t r q
def columnHit (P : PhysicalPacking N a G) (t : ℤ) (q : E) : Prop := ∃ r : E, V8NativeMessage.N7LiteralSupport.Matches P t r q

/-- The original geometric object produced by the endpoint-band seating:
all stated seats are real and their wires are a single physical matching.
No assertion about a particular slot value is built in. -/
structure BandCertificate (P : PhysicalPacking N a G) (h : ℕ) : Prop where
  positive : 0<h
  fit : 2*h≤2^a
  full : ∀ z : Physical a P.copies G, InBand (2^a) h z.2.val → ∃ e, P.seat e=z
  row_separated : ∀ e e', InBand (2^a) h (P.seat e).2.val →
    InBand (2^a) h (P.seat e').2.val → N.row e=N.row e' → e=e'
  col_separated : ∀ e e', InBand (2^a) h (P.seat e).2.val →
    InBand (2^a) h (P.seat e').2.val → N.col e=N.col e' → e=e'

theorem match_in_both_bands (P : PhysicalPacking N a G) {h : ℕ} {t : ℤ}
    {r q : E} (wide : 2^a-h≤t.natAbs) (m : V8NativeMessage.N7LiteralSupport.Matches P t r q) :
    InBand (2^a) h (P.seat r).2.val ∧ InBand (2^a) h (P.seat q).2.val := by
  have dr := (P.seat r).2.isLt
  have dq := (P.seat q).2.isLt
  have k := m.2
  by_cases ts : 0≤t
  · have htt : (t.natAbs:ℤ)=t := Int.natAbs_of_nonneg ts
    exact ⟨Or.inl (by omega),Or.inr (by omega)⟩
  · have htt : (t.natAbs:ℤ)=-t := by
      rw [←Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    exact ⟨Or.inr (by omega),Or.inl (by omega)⟩

theorem single_row_hit (P : PhysicalPacking N a G) {h : ℕ}
    (guard : BandCertificate P h) {t : ℤ} (wide : 2^a-h≤t.natAbs)
    {r r' : E} (h1 : rowHit P t r) (h2 : rowHit P t r') (same : N.row r=N.row r') :
    r=r' := by
  obtain ⟨_,m⟩ := h1
  obtain ⟨_,m'⟩ := h2
  exact guard.row_separated r r' (match_in_both_bands P wide m).1
    (match_in_both_bands P wide m').1 same

theorem single_column_hit (P : PhysicalPacking N a G) {h : ℕ}
    (guard : BandCertificate P h) {t : ℤ} (wide : 2^a-h≤t.natAbs)
    {q q' : E} (h1 : columnHit P t q) (h2 : columnHit P t q') (same : N.col q=N.col q') :
    q=q' := by
  obtain ⟨_,m⟩ := h1
  obtain ⟨_,m'⟩ := h2
  exact guard.col_separated q q' (match_in_both_bands P wide m).2
    (match_in_both_bands P wide m').2 same

theorem last_seat_is_matched (P : PhysicalPacking N a G) {h : ℕ}
    (guard : BandCertificate P h) (e : E) (last : (P.seat e).2.val+1=2^a) :
    columnHit P (((2^a:ℕ):ℤ)-1) e := by
  let first : Physical a P.copies G := ((P.seat e).1,⟨0,by positivity⟩)
  obtain ⟨r,hr⟩ := guard.full first (Or.inl guard.positive)
  refine ⟨r,?_⟩
  unfold V8NativeMessage.N7LiteralSupport.Matches
  rw [hr]
  change _ ∧ ((P.seat e).2.val:ℤ)-0=(↑(2^a:ℕ):ℤ)-1
  exact ⟨rfl,by omega⟩

/-- For the paper's band width floor(L/(8D)), its smaller fixed-ratio
outer interval needs no probabilistic input *once that band is seated*.
D is the reciprocal of the explicit positive survival probability. -/
theorem printed_fraction_in_band (L D k : ℕ) (hd : 0<D)
    (outer : (16*D)*(L-k)≤L) : L-L/(8*D)≤k := by
  have hd8 : 0<8*D := by positivity
  have hd16 : 0<16*D := by positivity
  have hmon : 8*D≤16*D := by omega
  have h : L-k≤L/(8*D) := (Nat.le_div_iff_mul_le hd8).mpr (by
    calc
      (L-k)*(8*D) ≤ (L-k)*(16*D) := Nat.mul_le_mul_left _ hmon
      _ ≤ L := by simpa only [Nat.mul_comm] using outer)
  omega

#print axioms match_in_both_bands
#print axioms single_row_hit
#print axioms single_column_hit
#print axioms last_seat_is_matched
#print axioms printed_fraction_in_band
end J4R43LiteralOutside

