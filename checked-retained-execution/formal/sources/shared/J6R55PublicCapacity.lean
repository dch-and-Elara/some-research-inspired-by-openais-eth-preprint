import J6R55PublicReserve

/-! A single uniform raw centre width can leave enough depth-counter
slack after every emitted public key. The check depends on genuine
address fields, not on an assumed per-site ReadyOnStack. -/
namespace J6R55Public
open scoped Classical Polynomial
open Polynomial AOracleMachineTime
open J6Mesh J6OrientedHost J6R24LegalLayout J6R24MeteredRecursion
open J6R26StablePreparedRoot J6R28GeneratedRootFrame J6R14ZeroMode
open J6R34RootAtlas J6R32RootGeneratedRegistryInputs
open J6R15ModeCost J6R25PreparedSupply J6R54PublicFamily J6R16ModeCost
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 13500000
set_option maxRecDepth 3400

noncomputable section
variable {V : Type} [Fintype V] {f : ℤ[X]} {m n base native : ℕ} {A : Plant V m n}
variable {G : RootShape f m (printedHalf m) base native (printedRankWidth m) A (constantRootWord m)}
variable {ell q rr cc dd prec kp bw tc tj tw edgew : ℕ}
variable [Fact (Irreducible (NativeProbeRing.residuePoly f))]
variable (W : Widths m native tc tj tw edgew) (C : Compiled G ell q rr cc dd prec kp bw)
variable (i : J6Recovery.Addr m) (j : Fin (literalDegree m native+1)) (g : Fin 64)

theorem real_issuance_has_uniform_depth_capacity
    (slack : 2*m+1+pathLimit (physicalSize m native) 2<2^tc) :
    (literalSite W C i j g).issue.result.val-1+pathLimit (physicalSize m native) 2 <
      2^KeyWidth kp tc tj := by
  let d := pathLimit (physicalSize m native) 2
  let X := literalSite W C i j g
  let H := (prepareHead W i j).result
  let A := (realAddress H.data g).result
  let high := joinKey A.sample A.group
  let low := joinKey C.mark A.centre
  have ec : A.centre.val=index m i :=
    (congrArg Word.val (real_address_exact H.data g).1).trans H.centreOK
  have sc : A.centre.val+d<2^tc := by
    have bound := i.isLt
    rw [ec]
    unfold index
    change 2*m+1+d<2^tc at slack
    omega
  have one : 0<(2:ℕ)^kp := by positivity
  have mul : d≤2^kp*d := by
    calc
      _ = 1*d := (Nat.one_mul d).symm
      _ ≤ _ := Nat.mul_le_mul_right _ (by omega)
  have small : low.val+d<2^(kp+tc) := by
    calc
      _=C.mark.val+2^kp*A.centre.val+d := by rw [show low.val=_ from joined_unsigned_value _ _]
      _≤C.mark.val+2^kp*(A.centre.val+d) := by rw [Nat.mul_add]; omega
      _<2^kp+2^kp*(A.centre.val+d) := Nat.add_lt_add_right (val_lt C.mark) _
      _=2^kp*(A.centre.val+d+1) := by ring
      _≤2^kp*2^tc := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt sc)
      _=_ := (pow_add _ _ _).symm
  have key : X.issue.result.val=low.val+2^(kp+tc)*high.val := by
    change (issueExterior C.mark A).result.val=_
    rw [(issued_exterior_exact C.mark A).1,joined_unsigned_value,joined_unsigned_value]
    change C.mark.val+2^kp*(A.centre.val+2^tc*high.val)=_
    rw [show low.val=_ from joined_unsigned_value _ _,pow_add]
    ring
  have top : X.issue.result.val+d<2^KeyWidth kp tc tj := by
    calc
      _ = (low.val+d)+2^(kp+tc)*high.val := by rw [key]; omega
      _ < 2^(kp+tc)+2^(kp+tc)*high.val := Nat.add_lt_add_right small _
      _ = 2^(kp+tc)*(high.val+1) := by ring
      _ ≤ 2^(kp+tc)*2^(tj+6) := Nat.mul_le_mul_left _ (Nat.succ_le_of_lt (val_lt high))
      _ = _ := by
        rw [←pow_add]
        congr 1
        unfold KeyWidth
        omega
  change X.issue.result.val-1+d<_
  omega

#print axioms real_issuance_has_uniform_depth_capacity
end
end J6R55Public

