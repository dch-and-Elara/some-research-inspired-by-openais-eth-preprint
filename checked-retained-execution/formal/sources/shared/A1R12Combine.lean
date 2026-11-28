import A1R12Geometry

/-! Metered composition. Source coefficients are built from fresh
literal bit work, not represented by a series of ring-level assumptions. -/

namespace A1R12
open A1R10 A1R11 AOracleMachineTime AOracleCoordinates AOracleSuccinctNative

def addM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (a b : Meter (UVBlock f ell)) : Meter (UVBlock f ell) :=
  let q := uvAdd hp a.result b.result
  ⟨q.result,a.steps+b.steps+q.steps+2⟩

def mulM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (a b : Meter (UVBlock f ell)) : Meter (UVBlock f ell) :=
  let q := uvMul hp a.result b.result
  ⟨q.result,a.steps+b.steps+q.steps+2⟩

def invM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : Meter (UVBlock f ell)) : Meter (UVBlock f ell) :=
  let q := uvOddInverse hp he hv a.result
  ⟨q.result,a.steps+q.steps+2⟩

def powM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : Meter (UVBlock f ell)) (n : ℕ) : Meter (UVBlock f ell) :=
  let q := uvPow hp he hv a.result n
  ⟨q.result,a.steps+q.steps+2⟩

@[simp] theorem addM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (a b : Meter (UVBlock f ell)) :
    uvRead hp f ell (addM hp a b).result = uvRead hp f ell a.result+uvRead hp f ell b.result :=
  (uvAdd_exact hp a.result b.result).1

@[simp] theorem mulM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (a b : Meter (UVBlock f ell)) :
    uvRead hp f ell (mulM hp a b).result = uvRead hp f ell a.result*uvRead hp f ell b.result :=
  (uvMul_exact hp a.result b.result).1

@[simp] theorem invM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : Meter (UVBlock f ell)) :
    uvRead hp f ell (invM hp he hv a).result=oddInverse p (uvRead hp f ell a.result) :=
  (uvOddInverse_exact hp he hv a.result).1

@[simp] theorem powM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : Meter (UVBlock f ell)) (n : ℕ) :
    uvRead hp f ell (powM hp he hv a n).result=uvRead hp f ell a.result^n :=
  (uvPow_exact hp he hv a.result n).1

theorem addM_cost {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)} (a b : Meter (UVBlock f ell)) :
    (addM hp a b).steps≤a.steps+b.steps+addCap f.length ell p hp+2 :=
  Nat.add_le_add_right (Nat.add_le_add_left (uvAdd_exact hp a.result b.result).2 _) _

theorem mulM_cost {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)} (a b : Meter (UVBlock f ell)) :
    (mulM hp a b).steps≤a.steps+b.steps+mulCap f.length ell p+2 :=
  Nat.add_le_add_right (Nat.add_le_add_left (uvMul_native_bit_cost hp a.result b.result).2 _) _

theorem invM_cost {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : Meter (UVBlock f ell)) :
    (invM hp he hv a).steps≤a.steps+oddCap f.length ell p hp+2 :=
  Nat.add_le_add_right (Nat.add_le_add_left (uvOddInverse_exact hp he hv a.result).2 _) _

theorem powM_cost {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : Meter (UVBlock f ell)) (n : ℕ) :
    (powM hp he hv a n).steps≤a.steps+(uvWidth f.length ell p+n*(mulCap f.length ell p+4))+2 :=
  Nat.add_le_add_right (Nat.add_le_add_left (uvPow_exact hp he hv a.result n).2 _) _

def oneM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) : Meter (UVBlock f ell) :=
  ⟨uvOne hp he hv,uvWidth f.length ell p⟩

@[simp] theorem oneM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) : uvRead hp f ell (oneM hp he hv).result = 1 :=
  uvOne_read hp he hv

def scalarM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : A1R10.Word p) : Meter (UVBlock f ell) :=
  ⟨scalarUV hp he hv a,uvWidth f.length ell p⟩

@[simp] theorem scalarM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (a : A1R10.Word p) :
    uvRead hp f ell (scalarM hp he hv a).result=scalarToUV hp f ell (wordRead a) :=
  scalarUV_read hp he hv a

def padCost {A : Type*} (a : Meter A) (extra : ℕ) : Meter A :=
  ⟨a.result,a.steps+extra⟩

def twoM {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (k : ℕ) : Meter (UVBlock f ell) :=
  padCost (scalarM hp he hv (dyadicWord p k)) (4*(p+k+1))

@[simp] theorem twoM_read {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (k : ℕ) :
    uvRead hp f ell (twoM hp he hv k).result=(2:Truncated (Modulus p hp f) ell)^k := by
  change uvRead hp f ell (scalarM hp he hv (dyadicWord p k)).result=_
  rw [scalarM_read,dyadicWord_read,map_pow,map_ofNat]

def foldM {A : Type*} {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (g : A → Meter (UVBlock f ell)) :
    List A → Meter (UVBlock f ell)
  | [] => oneM hp he hv
  | a::as => mulM hp (g a) (foldM hp he hv g as)

theorem foldM_exact {A : Type*} {p ell : ℕ} (hp : 0<p) {f : List (A1R10.Word p)}
    (he : 0<f.length) (hv : 0<ell) (as : List A) (g : A → Meter (UVBlock f ell))
    (F : A → Truncated (Modulus p hp f) ell) (cap : ℕ)
    (h : ∀ a∈as,uvRead hp f ell (g a).result=F a ∧ (g a).steps≤cap) :
    uvRead hp f ell (foldM hp he hv g as).result=(as.map F).prod ∧
    (foldM hp he hv g as).steps≤uvWidth f.length ell p+as.length*(cap+mulCap f.length ell p+2) := by
  induction as with
  | nil => simp [foldM,oneM]
  | cons a as ih =>
    obtain ⟨ha,hac⟩ := h a List.mem_cons_self
    obtain ⟨ht,htc⟩ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    have hm := mulM_cost hp (g a) (foldM hp he hv g as)
    constructor
    · simp [foldM,ha,ht]
    · change (mulM hp (g a) (foldM hp he hv g as)).steps ≤ _
      rw [List.length_cons,Nat.succ_mul as.length]
      omega

#print axioms mulM_read
#print axioms invM_read
#print axioms twoM_read
#print axioms foldM_exact
end A1R12
