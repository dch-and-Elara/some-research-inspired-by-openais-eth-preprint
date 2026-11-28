import J6R16ModeCostPath

/-! At every reachable *active* printed centre, the exact child
precision is small enough for the R15 tuple budget. The dyadic
absorption and all floor steps are proved from the printed guard. -/
namespace J6R16ModeCost
open scoped Polynomial
open J1PPrinted J6ActiveRun J6ActiveSchedule J6R10Reachable
open J6R12Blueprint J6R11Blueprint

def siteConstant (C : ℕ) : ℕ := 41*C+40

theorem floor_scale (lam d : ℕ) (hu : 0<stepU lam d) :
    lam≤(2*epsDen*2^d)*stepU lam d := by
  let w := epsDen*2^d
  let u := stepU lam d
  have hw : 0<w := by unfold w epsDen; positivity
  have he : lam%w+w*u=lam := Nat.mod_add_div lam w
  have hm := Nat.mod_lt lam hw
  have held : w≤w*u := Nat.le_mul_of_pos_right _ hu
  change lam≤(2*epsDen*2^d)*u
  have H : (2*epsDen*2^d)*u=w*u+w*u := by unfold w; ring
  rw [H]
  omega

variable {f : ℤ[X]} {ell s C : ℕ}
variable (cfg : RootBounds s C f)
variable (sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s))
include cfg

theorem register_envelope {r c : Call (PhysicalHost f ell)}
    (h : NativeReach (Plan sel) r c) (hr : Stable s C r) (hzero : r.depth=0)
    (hroot : r.prec≤C*s)
    (ha : (printedParams (f:=f) (ell:=ell) s).cutoff<c.edges)
    (t : Center (printedParams (f:=f) (ell:=ell) s) c) :
    let lam := Nat.clog 2 s
    let u := stepU lam c.depth
    let a := stepA lam c.depth
    let D := 2^(a-padicValInt 2 t.val)
    let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
    0<u ∧ 0<p ∧ 6*c.edges≤p ∧ p*u≤siteConstant C*c.edges*D := by
  let lam := Nat.clog 2 s
  let u := stepU lam c.depth
  let a := stepA lam c.depth
  let i := padicValInt 2 t.val
  let D := (2:ℕ)^(a-i)
  have hSt := stable_reachable cfg sel h hr
  have hp0 : 0<lam := (by decide : 0<(1024:ℕ)).trans_le (root_lambda_large cfg)
  obtain ⟨hu,_,huM⟩ :=
    printed_taper_legal s c.edges C c.depth cfg.widthPos cfg.constPos cfg.size ha hSt.sizeByDepth
  have hi : i<u := center_level a c.edges u t.property
  obtain ⟨hD,hlD,_⟩ := scale_at_center lam c.depth i hi
  have hp5 := printed_u_four_fifths s c.edges C c.depth cfg.constPos cfg.size ha hSt.sizeByDepth
  have hdom := dominant_dyadic lam u (root_lambda_large cfg) hp5
  have hs : s≤c.edges*(lam+1) :=
    (cutoff_scale s lam c.edges hp0 ha).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  have hul : u≤lam+1 := (u_le_lam lam c.depth).trans (Nat.le_succ _)
  have hal : a+1≤lam+1 := Nat.succ_le_succ (bits_le_lam lam c.depth)
  have hPrec := input_precision_polynomial_factor cfg sel h hr hzero hroot
  have hInherited : c.prec*u≤41*C*c.edges*D := by
    calc
      _≤(41*C*s*(lam+1)^2*2^priorBits lam c.depth)*u :=
        Nat.mul_le_mul_right _ hPrec
      _=(41*C)*(lam+1)^2*2^priorBits lam c.depth*(s*u) := by ring
      _≤(41*C)*(lam+1)^2*2^priorBits lam c.depth*((c.edges*(lam+1))*(lam+1)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul hs hul)
      _=(41*C*c.edges)*((lam+1)^4*2^priorBits lam c.depth) := by ring
      _≤(41*C*c.edges)*((2:ℕ)^u*2^priorBits lam c.depth) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hdom)
      _=(41*C*c.edges)*2^(priorBits lam c.depth+u) := by rw [pow_add,mul_comm (2^u)]
      _≤_ := Nat.mul_le_mul_left _ hlD
  have hGeometry : u*(a+1)≤D := by
    calc
      _≤(lam+1)*(lam+1) := Nat.mul_le_mul hul hal
      _=(lam+1)^2 := (pow_two _).symm
      _≤(lam+1)^4 := Nat.pow_le_pow_right (by omega) (by decide)
      _≤2^u := hdom
      _≤2^(priorBits lam c.depth+u) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      _≤_ := hlD
  let H := height c.edges u
  have hHu : H*u≤4*c.edges := (height_bounds c.edges u hu huM).2
  have hE : 0<c.edges := Nat.zero_lt_of_lt ha
  have hD' : (2:ℕ)^a/2^i=D := hD
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) c t
  have hp : p=c.prec+8*H*D+8*c.edges*(a+1) := by
    change c.prec+8*H*(2^a/2^i)+8*c.edges*(a+1)=_
    rw [hD']
  have hlower : 6*c.edges≤p := by
    have ht : 8*c.edges≤8*c.edges*(a+1) := Nat.le_mul_of_pos_right _ (by omega)
    rw [hp]
    omega
  refine ⟨hu,?_,hlower,?_⟩
  · omega
  · change p*u≤siteConstant C*c.edges*D
    rw [hp]
    calc
      _=c.prec*u+(8*D)*(H*u)+(8*c.edges)*(u*(a+1)) := by ring
      _≤41*C*c.edges*D+(8*D)*(4*c.edges)+(8*c.edges)*D :=
        Nat.add_le_add (Nat.add_le_add hInherited (Nat.mul_le_mul_left _ hHu))
          (Nat.mul_le_mul_left _ hGeometry)
      _=_ := by unfold siteConstant; ring

#print axioms floor_scale
#print axioms register_envelope
end J6R16ModeCost

