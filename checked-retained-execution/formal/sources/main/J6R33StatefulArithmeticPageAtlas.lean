import J6R33StatefulArithmeticPageProducer
import J6R33PageIndexedBirthAtlas

/-! The symbolic order in the exact tree proof is implemented by the
full raw cell/copy header reader. Each Page is emitted with its actual
binary key; the outer invocation is still issued exactly once. -/
namespace J6R33StatefulArithmeticPage
open scoped Polynomial
open AOracleMachineTime A1R10 J6R21Ancestor J6R24MeteredRecursion
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R30ProducedGateRegistry J6R26DescriptorTree
open P11FullPacking J6R32ChildResidentTransfer J6R33PageIndexedBirth

variable {f : ℤ[X]} {ell s C key prec tw bw : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
variable {port edge dep tc tz tm code b : ℕ}

noncomputable def fromTrueAtlas (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issue : Meter (J6R15ModeCost.Word key)) (ctx : CentreContext tw bw) (S : FrameShape f prec)
    (actual : S.p=ticket.child.prec) (w : ℕ)
    (raw : Meter (Common S.old S.a S.w code (w+13*S.a))) (hv : 0<ell) (fit : S.i.val+1≤S.w)
    (hw : 0<S.w) (copies : J6R15ModeCost.Word S.w) (count : copies.val=b) (addrFit : b≤2^w)
    (field : Page S.a b (Fin 64)→OriginFields S.a S.p ell S.w S.old S.i)
    (accepted : ∀ k,((raw.result.atRequest (sourceRequest S.w w k)).compile S.pPos hv fit).result=some (field k)) :
    Birth T ticket key prec tw bw (w+13*S.a) :=
  fromPaidAtlas J issue ctx S actual raw (writeRequests S.a w hw copies) hv fit (orderedChildPages S.a b)
    (child_pages_complete S.a b).1 (sourceRequest S.w w)
    (child_page_key_injective w addrFit) (write_requests_exact S.a w hw copies count addrFit).1
    field (fun k _=>accepted k)

theorem physical_birth_all_pages (J : NativeJob T ticket port edge dep prec tc tz tm)
    (issue : Meter (J6R15ModeCost.Word key)) (ctx : CentreContext tw bw) (S : FrameShape f prec)
    (actual : S.p=ticket.child.prec) (w : ℕ)
    (raw : Meter (Common S.old S.a S.w code (w+13*S.a))) (hv : 0<ell) (fit : S.i.val+1≤S.w)
    (hw : 0<S.w) (copies : J6R15ModeCost.Word S.w) (count : copies.val=b) (addrFit : b≤2^w)
    (field : Page S.a b (Fin 64)→OriginFields S.a S.p ell S.w S.old S.i)
    (accepted : ∀ k,((raw.result.atRequest (sourceRequest S.w w k)).compile S.pPos hv fit).result=some (field k))
    (maxFee : ℕ)
    (fee : ∀ k : Page S.a b (Fin 64),((raw.result.atRequest (sourceRequest S.w w k)).compile S.pPos hv fit).steps≤maxFee) :
    let born := fromTrueAtlas J issue ctx S actual w raw hv fit hw copies count addrFit field accepted
    (∀ k,(locate (childPageKey w k) born.rows).result=some (field k)) ∧
      born.rows.length=pagesCount S.a b ∧
      born.compilePages.steps≤raw.steps+requestsFee S.a w S.w b+
        pagesCount S.a b*(maxFee+onePageFee (w+13*S.a)+5)+6 := by
  let born := fromTrueAtlas J issue ctx S actual w raw hv fit hw copies count addrFit field accepted
  obtain ⟨_,_,hit,cost⟩ := compile_atlas_exact raw.result S.pPos hv fit hw copies count addrFit field accepted fee
  let run := compileAtlas raw.result S.pPos hv fit hw copies
  have H : born.compilePages.steps=raw.steps+run.steps := by
    simp only [born,fromTrueAtlas,fromPaidAtlas,paidAtlas,run,compileAtlas,Nat.add_assoc]
  have hLen : born.rows.length=(orderedChildPages S.a b).length := List.length_map _
  rw [(child_pages_complete S.a b).2.2] at hLen
  refine ⟨hit,hLen,?_⟩
  rw [H]
  change run.steps≤_ at cost
  omega

#print axioms physical_birth_all_pages
end J6R33StatefulArithmeticPage
