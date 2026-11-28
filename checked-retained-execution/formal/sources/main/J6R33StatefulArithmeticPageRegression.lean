import J6R33StatefulArithmeticPageJob
import J6R23PaddingCensusCodec
import J6R18ChildWriteRun

/-! Regressions against broadcasting one capsule to every Page, and
against replacing a positive exponent at a row-empty site by the empty
product value. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape A1R10 A1R11 A1R12
open J6R21Ancestor J6R30ProducedGateRegistry J6R26DescriptorTree
open P11FullPacking P1DyadicGrid J6R23PaddingCensus J6R18ChildWrite

private def specimen (a : ℕ) (copy : Fin 2) : Page a 2 (Fin 64) :=
  ⟨⟨fun _=>(0,0),fun _=>le_rfl⟩,copy,fun _=>false⟩

private def specimenWord (a : ℕ) (copy : Fin 2) : J6R15ModeCost.Word (1+13*a) :=
  ⟨(pageWord 1 (specimen a copy)).val,(pageWord 1 (specimen a copy)).property⟩

private theorem two_different (a : ℕ) : specimenWord a 0≠specimenWord a 1 := by
  intro eq
  have heq : specimen a 0=specimen a 1 := (page_code_injective (a:=a) (b:=2) 1 (by decide))
    (congrArg (fun x : J6R15ModeCost.Word (1+13*a)=>bitsValue x.bits) eq)
  have h : (0:ℕ)=1 := congrArg (fun x : Page a 2 (Fin 64)=>x.2.1.val) heq
  omega

set_option maxHeartbeats 4500000 in
theorem one_creator_distinct_true_pages {f : ℤ[X]} {ell prec tw bw : ℕ}
    (S : FrameShape f prec) (z : UVBlock S.old ell) (ctx : CentreContext tw bw) :
    let k0 := specimenWord S.a 0
    let k1 := specimenWord S.a 1
    let A : OriginFields S.a S.p ell S.w S.old S.i := ⟨z,[],[],[]⟩
    let B : OriginFields S.a S.p ell S.w S.old S.i := ⟨z,[J6R15ModeCost.word 0],[],[]⟩
    let entry : DirRow 2 := ⟨J6R15ModeCost.word 1,S.birth.bits⟩
    let row := publishedRow entry S.birth ctx
      (⟨S,[⟨k0,A⟩,⟨k1,B⟩]⟩ : PagedEnvelope f ell prec (1+13*S.a))
    locate entry.id [row]=⟨some row.payload,refHeadFee 2⟩ ∧
      locate k0 row.payload.payload.pages=⟨some A,refHeadFee (1+13*S.a)⟩ ∧
      locate k1 row.payload.payload.pages=⟨some B,2*refHeadFee (1+13*S.a)⟩ ∧ A≠B := by
  dsimp only
  refine ⟨ref_head_exact _ _,ref_head_exact _ _,?_,?_⟩
  · let k0 := specimenWord S.a 0
    let k1 := specimenWord S.a 1
    let A : OriginFields S.a S.p ell S.w S.old S.i := ⟨z,[],[],[]⟩
    let B : OriginFields S.a S.p ell S.w S.old S.i := ⟨z,[J6R15ModeCost.word 0],[],[]⟩
    change locate k1 [⟨k0,A⟩,⟨k1,B⟩]=⟨some B,2*refHeadFee (1+13*S.a)⟩
    have neq : ∀ row∈([⟨k0,A⟩] : List (RefRow (1+13*S.a) _)),row.address≠k1 := by
      intro x hx
      obtain rfl := List.mem_singleton.mp hx
      exact two_different S.a
    have scan := reference_front_fee k1 [⟨k0,A⟩] [⟨k1,B⟩] neq
    rw [ref_head_exact ⟨k1,B⟩ []] at scan
    simpa only [List.singleton_append,List.length_singleton,Nat.one_mul,two_mul] using scan
  · intro eq
    exact (List.noConfusion (congrArg OriginFields.rows eq))

theorem row_empty_positive_zero {p ell a q m : ℕ} (hp : 0<p) {fw : List (A1R10.Word p)}
    (he : 0<fw.length) (hv : 0<ell) (z : UVBlock fw ell) (t : ℤ) (ht : t∈grid a)
    (i : Fin a) (b : ℕ) (hq : 0<q) (hb : m+1≤2^b)
    (cols : List (SlotBit a)) (modes : Fin m→ModeInput a p i q)
    (hc : ∀ j,(modes j).code=encodeBits b j.succ.val)
    (j : Fin m) (active : (modes j).targeted=true) (positive : 0<(modes j).beta.val) :
    uvRead hp fw ell (packetResult hp he hv z t i b [] cols (List.ofFn modes)).result=0 := by
  classical
  have pos := (packetResult_exact hp he hv z t ht i b hq hb [] cols
    (by simp) modes hc).1
  have bad : (0 : Fin m→₀ℕ)≠requestedProfile modes := by
    intro eq
    have h := congrArg (fun d : Fin m→₀ℕ=>d j) eq
    change (0 : Fin m→₀ℕ) j=requestedProfile modes j at h
    simp [requestedProfile_read,active] at h
    omega
  rw [pos]
  simp only [List.map_nil,rowsPoly,List.prod_nil,MvPolynomial.coeff_one,if_neg bad,zero_mul]

#print axioms one_creator_distinct_true_pages
#print axioms row_empty_positive_zero
end J6R33StatefulArithmeticPage
