import A1R12Combine
import J6ActiveNormalizer

/-! Explicit finite Z=X-at-a-centre arithmetic over the already
verified U/V bit kernel. Z is a third, local, ordinary truncated
coordinate, not substituted for the packet's V variable. The
normalizer and sample coefficient tapes are inputs at this boundary;
their preparation is not given free computation credit. -/
namespace J6R22Active
open scoped Polynomial
open A1R10 A1R11 A1R12 AOracleCoordinates AOracleMachineTime
open AOracleSuccinctNative Polynomial

section Jet
variable {p ell : ℕ} {fw : List (Word p)}

abbrev Coeff (hp : 0<p) (fw : List (Word p)) (ell : ℕ) :=
  Truncated (Modulus p hp fw) ell

def jetEntryWidth (e ell p : ℕ) : ℕ := uvWidth e ell p

def jetGateFee (e ell p : ℕ) (hp : 0<p) : ℕ :=
  addCap e ell p hp+subCap e ell p hp+mulCap e ell p

def jetGates (hp : 0<p) (he : 0<fw.length) (ell : ℕ) : Gates (UVBlock fw ell) where
  zero := uvZero hp fw ell
  add := uvAdd hp
  mul := uvMul hp
  sub := uvSub hp he
  move := jetEntryWidth fw.length ell p
  budget := jetGateFee fw.length ell p hp

noncomputable def jetOps (hp : 0<p) (he : 0<fw.length) (ell : ℕ) :
    Ops (UVBlock fw ell) (Coeff hp fw ell) where
  toGates := jetGates hp he ell
  read := uvRead hp fw ell
  zero_read := uvZero_read hp fw ell
  add_read a b := (uvAdd_exact hp a b).1
  mul_read a b := (uvMul_exact hp a b).1
  sub_read a b := (uvSub_exact hp he a b).1
  add_cost a b := (show (uvAdd hp a b).steps≤addCap fw.length ell p hp from (uvAdd_exact hp a b).2).trans (by change addCap fw.length ell p hp≤jetGateFee fw.length ell p hp; unfold jetGateFee; omega)
  mul_cost a b := (show (uvMul hp a b).steps≤mulCap fw.length ell p from (uvMul_native_bit_cost hp a b).2).trans (by change mulCap fw.length ell p≤jetGateFee fw.length ell p hp; unfold jetGateFee; omega)
  sub_cost a b := (show (uvSub hp he a b).steps≤subCap fw.length ell p hp from (uvSub_exact hp he a b).2).trans (by change subCap fw.length ell p hp≤jetGateFee fw.length ell p hp; unfold jetGateFee; omega)

abbrev JetTape (fw : List (Word p)) (ell k : ℕ) :=
  {xs : List (UVBlock fw ell)//xs.length=k}

noncomputable def jetRead (hp : 0<p) (he : 0<fw.length) {k : ℕ} (x : JetTape fw ell k) :
    AdjoinRoot ((X : (Coeff hp fw ell)[X])^k) :=
  AdjoinRoot.mk _ (decode (jetOps hp he ell) x.val)

def jetZero (hp : 0<p) (he : 0<fw.length) (k : ℕ) : JetTape fw ell k :=
  ⟨zeros (jetGates hp he ell) k,zeros_len ..⟩

theorem jetZero_exact (hp : 0<p) (he : 0<fw.length) (k : ℕ) :
    jetRead hp he (jetZero hp he (ell:=ell) k)=0 := by
  let o := jetOps hp he ell
  change AdjoinRoot.mk _ (decode o (zeros o.toGates k))=0
  rw [decode_zeros,map_zero]

def jetOne (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (k : ℕ) (hk : 0<k) :
    JetTape fw ell k :=
  ⟨constantTape (jetGates hp he ell) k (uvOne hp he hv),constantTape_len _ _ hk _⟩

theorem jetOne_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) (k : ℕ) (hk : 0<k) :
    jetRead hp he (jetOne hp he hv k hk)=1 := by
  let o := jetOps hp he ell
  change AdjoinRoot.mk _ (decode o (constantTape o.toGates k (uvOne hp he hv)))=1
  rw [constantTape_read o k _,show o.read (uvOne hp he hv)=1 from uvOne_read hp he hv,
    C_1,map_one]

def jetMult (hp : 0<p) (he : 0<fw.length) {k : ℕ} (a b : JetTape fw ell k) :
    Meter (JetTape fw ell k) :=
  let y := convolve (jetGates hp he ell) a.val b.val
  let len := (convolve_exact (jetOps hp he ell) a.val b.val).1
  have hd : (y.result.drop k).length=k := by
    change ((convolve (jetOps hp he ell) a.val b.val).result.drop k).length=k
    simp [len,a.property,b.property]
  ⟨⟨y.result.drop k,hd⟩,y.steps+(6*k+2)*(jetEntryWidth fw.length ell p+1)⟩

def jetMulFee (e ell p k : ℕ) (hp : 0<p) : ℕ :=
  (k+1)*(k+k+1)*(4*(jetGateFee e ell p hp+4*(jetEntryWidth e ell p+1)))+
    (6*k+2)*(jetEntryWidth e ell p+1)

theorem jetMult_exact (hp : 0<p) (he : 0<fw.length) {k : ℕ} (a b : JetTape fw ell k) :
    jetRead hp he (jetMult hp he a b).result=jetRead hp he a*jetRead hp he b ∧
    (jetMult hp he a b).steps≤jetMulFee fw.length ell p k hp := by
  let o := jetOps hp he ell
  obtain ⟨hlen,hread,hsteps⟩ := convolve_exact o a.val b.val
  rw [a.property,b.property] at hlen hsteps
  constructor
  · change AdjoinRoot.mk _ (decode o ((convolve o a.val b.val).result.drop k))=_
    rw [decode_drop_quotient o _ k k hlen,hread,map_mul]
    rfl
  · exact Nat.add_le_add_right hsteps _

def jetAdd (hp : 0<p) (he : 0<fw.length) {k : ℕ} (a b : JetTape fw ell k) :
    Meter (JetTape fw ell k) :=
  let y := addRows (jetGates hp he ell) a.val b.val
  have h := (addRows_exact (jetOps hp he ell) a.val b.val (a.property.trans b.property.symm)).1
  ⟨⟨y.result,h.trans a.property⟩,y.steps⟩

def jetAddFee (e ell p k : ℕ) (hp : 0<p) : ℕ :=
  k*(jetGateFee e ell p hp+4*(jetEntryWidth e ell p+1))

theorem jetAdd_exact (hp : 0<p) (he : 0<fw.length) {k : ℕ} (a b : JetTape fw ell k) :
    jetRead hp he (jetAdd hp he a b).result=jetRead hp he a+jetRead hp he b ∧
    (jetAdd hp he a b).steps≤jetAddFee fw.length ell p k hp := by
  let o := jetOps hp he ell
  have h := addRows_exact o a.val b.val (a.property.trans b.property.symm)
  refine ⟨?_,?_⟩
  · change AdjoinRoot.mk _ (decode o (addRows o a.val b.val).result)=_
    rw [h.2.1,map_add]
    rfl
  · simpa only [jetAdd,jetAddFee,o,a.property] using h.2.2

def jetSub (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (a b : JetTape fw ell k) :
    Meter (JetTape fw ell k) :=
  let y := subtractScaled (jetGates hp he ell) (uvOne hp he hv) b.val a.val
  have h := (subtractScaled_exact (jetOps hp he ell) (uvOne hp he hv) b.val a.val
    (b.property.trans_le a.property.ge)).1
  ⟨⟨y.result,h.trans a.property⟩,y.steps+jetEntryWidth fw.length ell p⟩

def jetSubFee (e ell p k : ℕ) (hp : 0<p) : ℕ :=
  k*(2*jetGateFee e ell p hp+4*(jetEntryWidth e ell p+1))+jetEntryWidth e ell p

theorem jetSub_exact (hp : 0<p) (he : 0<fw.length) (hv : 0<ell) {k : ℕ} (a b : JetTape fw ell k) :
    jetRead hp he (jetSub hp he hv a b).result=jetRead hp he a-jetRead hp he b ∧
    (jetSub hp he hv a b).steps≤jetSubFee fw.length ell p k hp := by
  let o := jetOps hp he ell
  have h := subtractScaled_exact o (uvOne hp he hv) b.val a.val
    (b.property.trans_le a.property.ge)
  refine ⟨?_,?_⟩
  · change AdjoinRoot.mk _ (decode o (subtractScaled o (uvOne hp he hv) b.val a.val).result)=_
    rw [h.2.1,a.property,b.property,Nat.sub_self,pow_zero,one_mul,
      show o.read (uvOne hp he hv)=1 from uvOne_read hp he hv,C_1,one_mul,map_sub]
    rfl
  · have h' := h.2.2
    change _≤b.val.length*(2*jetGateFee fw.length ell p hp+4*(jetEntryWidth fw.length ell p+1)) at h'
    rw [b.property] at h'
    exact Nat.add_le_add_right h' _

end Jet

#print axioms jetZero_exact
#print axioms jetOne_exact
#print axioms jetMult_exact
#print axioms jetAdd_exact
#print axioms jetSub_exact
end J6R22Active


