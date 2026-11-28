import J6R105OuterPublication

/-! The real parent half-row tape is scanned even on rejected rows.
These hypotheses describe the encoded input, not an upper bound on a
callback. The count is metered independently of its numeric value. -/
namespace J6R106OuterHeader
open AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R32RootGeneratedRegistryInputs
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 12000000

theorem ripple_fee_even_at_word_wrap {q : ℕ} (w : Word q) :
    (increment w).steps=13*q+4 := by
  have h := (addBits_exact w.bits (encodeBits q 1) (by rw [w.size,encodeBits_length])).2.2
  change (addBits w.bits (encodeBits q 1)).steps+q+4=_
  rw [h,w.size]
  omega

theorem count_fee_even_at_word_wrap {A : Type*} (b : ℕ) (xs : List A) :
    (countList b xs).steps=b+3+xs.length*(13*b+8) := by
  induction xs with
  | nil => simp [countList]
  | cons x xs ih =>
    change (countList b xs).steps+(increment (countList b xs).result).steps+4=
      b+3+(xs.length+1)*(13*b+8)
    rw [ih,ripple_fee_even_at_word_wrap,Nat.add_mul,Nat.one_mul]
    omega

theorem fixed_row_charges {A : Type*} (xs : List A) (f : A → ℕ) (c : ℕ)
    (h : ∀ x ∈ xs, f x=c) : (xs.map f).sum=xs.length*c := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.map_cons,List.sum_cons,List.length_cons,h x List.mem_cons_self,
      ih (fun z hz=>h z (List.mem_cons_of_mem _ hz)),Nat.add_mul,Nat.one_mul,Nat.add_comm c]

theorem flat_rows_size {w : ℕ} (xs : List (PortRow w)) (body : ℕ)
    (shape : ∀ x ∈ xs, x.body.length=body) :
    (xs.flatMap rowBytes).length=xs.length*(w+6+body) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,
      ih (fun z hz=>shape z (List.mem_cons_of_mem _ hz)),Nat.add_mul,Nat.one_mul]
    unfold rowBytes
    rw [List.length_append,List.length_append,x.address.size,x.group.size,
      shape x List.mem_cons_self,Nat.add_assoc w,Nat.add_comm (_+_)]

def encodedBytes (coords prec depth edgeWidth w body hits : ℕ) : ℕ :=
  coords+prec+depth+edgeWidth+hits*(w+6+body)

def headerClock (issued coords prec depth edgeWidth key w body cnt hits : ℕ) : ℕ :=
  issued+(3+cnt*(2*w+3*body+81)+(edgeWidth+3+hits*(13*edgeWidth+8))+4)+
    (13*depth+4)+(2+hits*(6*(w+6+body)+5))+
    (6*(prec+depth+edgeWidth)+3*(hits*(w+6+body))+2*key+9)+6+
    (3*encodedBytes coords prec depth edgeWidth w body hits+1)+3*coords+5

theorem actual_job_fee_and_bytes_from_the_scanned_parent
    {w b d prec key : ℕ} (J : Job w b d prec) (issued : Meter (Word key)) (body : ℕ)
    (shape : ∀ x ∈ J.ports, x.body.length=body) :
    let hits := (selectPorts J.group J.ports).result.length
    (J.make issued).result.bytes.length=encodedBytes J.coordinates.length prec d b w body hits ∧
    (J.make issued).steps=headerClock issued.steps J.coordinates.length prec d b key w body J.ports.length hits ∧
    hits≤J.ports.length := by
  let C := selectPorts J.group J.ports
  let A := childPortsWithCount (b:=b) J.group J.ports
  let S := childStage (b:=b) issued J.group J.precision J.parentDepth J.ports
  have sel := select_ports_exact J.group J.ports
  have C1 : C.result=J.ports.filter (fun row=>(cmpAddr J.group row.group).result) := sel.1
  have Cs : C.steps=3+J.ports.length*(2*w+3*body+81) := by
    change C.steps=_; rw [show C.steps=3+(J.ports.map rowScanFee).sum from sel.2,
      fixed_row_charges _ rowScanFee _ (fun x hx=>by rw [rowScanFee,shape x hx])]
  have cshape : ∀ x ∈ C.result, x.body.length=body := fun x hx=>
    shape x (List.mem_filter.mp (C1 ▸ hx)).1
  have bodyLen := flat_rows_size C.result body cshape
  have serial : serializeFee C.result=2+C.result.length*(6*(w+6+body)+5) := by
    unfold serializeFee
    rw [fixed_row_charges _ _ _ (fun x hx=>by rw [cshape x hx])]
  have Abill : A.steps=3+J.ports.length*(2*w+3*body+81)+(b+3+C.result.length*(13*b+8))+4 := by
    change C.steps+(countList b C.result).steps+4=_
    rw [Cs,count_fee_even_at_word_wrap]
  have Sexact := child_stage_exact (b:=b) issued J.group J.precision J.parentDepth J.ports
  have Sbytes := Sexact.2.1
  change S.result.bytes=childHeaderBytes J.precision (increment J.parentDepth).result
    A.result.2 (C.result.flatMap rowBytes) at Sbytes
  have seen : S.result.bytes.length=prec+d+b+C.result.length*(w+6+body) := by
    rw [Sbytes]
    unfold childHeaderBytes
    simp only [List.length_append,J.precision.size,
      (increment J.parentDepth).result.size,A.result.2.size,bodyLen]

  have countHit : C.result.length≤J.ports.length := by rw [C1]; exact List.length_filter_le _ _
  have outBytes : (J.make issued).result.bytes.length=
      encodedBytes J.coordinates.length prec d b w body C.result.length := by
    rw [J.make_bytes issued]
    change (J.coordinates++S.result.bytes).length=_
    rw [List.length_append,seen]
    unfold encodedBytes
    omega
  refine ⟨outBytes,?_,countHit⟩
  change S.steps+(copyBytes (J.coordinates++S.result.bytes)).steps+3*J.coordinates.length+5=_
  rw [copyBytes_exact,List.length_append,seen]
  have paid := Sexact.2.2
  change S.steps=issued.steps+A.steps+(increment J.parentDepth).steps+serializeFee C.result+
    (6*(prec+d+b)+3*(C.result.flatMap rowBytes).length+2*key+9)+6 at paid
  rw [paid,Abill,ripple_fee_even_at_word_wrap,serial,bodyLen]
  unfold headerClock encodedBytes
  dsimp only [C]
  ring

#print axioms actual_job_fee_and_bytes_from_the_scanned_parent
end J6R106OuterHeader
