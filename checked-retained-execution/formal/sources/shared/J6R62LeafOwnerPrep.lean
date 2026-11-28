import J6R62LeafWirePrep
import J6R53TerminalGateOwner

set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 28000000
set_option maxRecDepth 3900

/-! Price the exact old-owner compiler in both syntax branches, including
failed searches and no-payload branches. No success or fee premise. -/
namespace J6R62Leaf
open scoped Classical Polynomial
open Polynomial AOracleMachineTime AOracleMachineTimeTape J6R15ModeCost J6R21Ancestor
open J6R34ChildPath J6R36ChildFramedRoute J6R52Terminal J6R53TerminalGate
open J6R53OldOwner J6R50Leaf J6R27OriginalGate J6R49SourceLayout
open A1R9

def gateSigns {A : Type} : CodeGate A → ℕ
  | .clause _ xs => xs.length
  | _ => 0

def GateFit {A : Type} (d : ℕ) (g : CodeGate A) : Prop :=
  gatePorts g≤d ∧ gateSigns g≤d

theorem gather_result_length {A D : Type*} (s : ℕ) (f : A → Meter (Option D))
    (xs : List A) : ∀ out, (gatherOptions s f xs).result=some out → out.length=xs.length := by
  induction xs with
  | nil =>
    intro out h
    obtain rfl := Option.some.inj h
    rfl
  | cons x xs ih =>
    intro out h
    cases hz : (f x).result with
    | none => simp [gatherOptions,hz] at h
    | some ready =>
      cases he : (gatherOptions s f xs).result with
      | none => simp [gatherOptions,hz,he] at h
      | some rs =>
        simp only [gatherOptions,hz,he,Option.bind_some,Option.map_some,Option.some.injEq] at h
        subst out
        simp only [List.length_cons,ih rs he]

theorem scan_ordinal_fee {a b : ℕ} (q : Word a) (pos : Word b) (xs : List (Word a)) :
    (scanOrdinal q pos xs).steps≤2+xs.length*missFee a b := by
  induction xs generalizing pos with
  | nil => simp [scanOrdinal]
  | cons x xs ih =>
    have hm := (cmpAddr_exact q x).2
    have hi : (increment pos).steps=13*b+4 := by
      have h := (addBits_exact pos.bits (encodeBits b 1) (by rw [pos.size,encodeBits_length])).2.2
      change (addBits pos.bits (encodeBits b 1)).steps+b+4=_
      rw [h,pos.size]
      omega
    have hh : (scanOrdinal q (increment pos).result xs).steps≤2+xs.length*(10*a+13*b+15) :=
      ih (increment pos).result
    dsimp only [scanOrdinal]
    split <;> dsimp only <;>
      rw [hm,List.length_cons,Nat.add_mul,one_mul,missFee] <;> omega

theorem find_ordinal_fee {a : ℕ} (q : Word a) (b : ℕ) (xs : List (Word a)) :
    (findOrdinal b q xs).steps≤portOrdinalFee a b xs.length := by
  have h := scan_ordinal_fee q (word (q:=b) 0) xs
  change (scanOrdinal q (word (q:=b) 0) xs).steps+b+3≤_
  unfold portOrdinalFee hitFee
  omega

theorem compiled_gate_syntax_fee {w : ℕ} (book : List (Word w)) (b d : ℕ)
    (g : CodeGate (Word w)) (hg : GateFit d g) :
    (compileCurrentGate b book g).steps≤currentGateFee w b book.length d := by
  obtain ⟨p,s⟩ := hg
  cases g with
  | free =>
    change 2≤8+_
    omega
  | equal ks =>
    change ks.length≤d at p
    have h := gather_options_bound b (portOrdinalFee w b book.length) (fun u=>findOrdinal b u book)
      ks (fun u _=>find_ordinal_fee u b book)
    have h' := h.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (portOrdinalFee w b book.length+b+6) p) 3)
    change (gatherOptions b (fun u=>findOrdinal b u book) ks).steps+4≤
      8+d*(portOrdinalFee w b book.length+b+9)
    rw [show d*(portOrdinalFee w b book.length+b+9)=d*(portOrdinalFee w b book.length+b+6)+3*d by ring]
    omega
  | clause ks signs =>
    change ks.length≤d at p
    change signs.length≤d at s
    have h := gather_options_bound b (portOrdinalFee w b book.length) (fun u=>findOrdinal b u book)
      ks (fun u _=>find_ordinal_fee u b book)
    have h' := h.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right (portOrdinalFee w b book.length+b+6) p) 3)
    change (gatherOptions b (fun u=>findOrdinal b u book) ks).steps+(copyBytes signs).steps+4≤
      8+d*(portOrdinalFee w b book.length+b+9)
    rw [copyBytes_exact,show d*(portOrdinalFee w b book.length+b+9)=
      d*(portOrdinalFee w b book.length+b+6)+3*d by ring]
    dsimp only
    omega

theorem reroute_syntax_fee {w W : ℕ} (tbl : List (RefRow w (Word W))) (d : ℕ)
    (g : CodeGate (Word w)) (hg : GateFit d g) :
    (rerouteGate tbl g).steps≤8+d*(locateFee w tbl.length+W+9) ∧
      ∀ ans, (rerouteGate tbl g).result=some ans → GateFit d ans := by
  obtain ⟨p,s⟩ := hg
  cases g with
  | free =>
    refine ⟨by change 2≤8+_; omega,?_⟩
    intro ans he
    obtain rfl := Option.some.inj he
    simp [GateFit,gatePorts,gateSigns]
  | equal ks =>
    change ks.length≤d at p
    let go := gatherOptions W (fun a=>locate a tbl) ks
    have h : go.steps≤3+ks.length*(locateFee w tbl.length+W+6) :=
      gather_options_bound W (locateFee w tbl.length) (fun a=>locate a tbl)
      ks (fun a _=>locate_bound a tbl)
    have h' := h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (locateFee w tbl.length+W+6) p) 3)
    constructor
    · change go.steps+4≤_
      rw [show d*(locateFee w tbl.length+W+9)=d*(locateFee w tbl.length+W+6)+3*d by ring]
      omega
    · intro ans h
      change go.result.map CodeGate.equal=some ans at h
      cases he : go.result with
      | none => simp [he] at h
      | some w =>
        simp only [he,Option.map_some,Option.some.injEq] at h
        subst ans
        exact ⟨(gather_result_length W _ _ w he).le.trans p,Nat.zero_le _⟩
  | clause ks signs =>
    change ks.length≤d at p
    change signs.length≤d at s
    let go := gatherOptions W (fun a=>locate a tbl) ks
    have h : go.steps≤3+ks.length*(locateFee w tbl.length+W+6) :=
      gather_options_bound W (locateFee w tbl.length) (fun a=>locate a tbl)
      ks (fun a _=>locate_bound a tbl)
    have h' := h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right (locateFee w tbl.length+W+6) p) 3)
    constructor
    · change go.steps+(copyBytes signs).steps+4≤_
      rw [copyBytes_exact,show d*(locateFee w tbl.length+W+9)=d*(locateFee w tbl.length+W+6)+3*d by ring]
      dsimp only
      omega
    · intro ans h
      change go.result.map (fun ps=>CodeGate.clause ps (copyBytes signs).result)=some ans at h
      cases he : go.result with
      | none => simp [he] at h
      | some w =>
        simp only [he,Option.map_some,Option.some.injEq] at h
        subst ans
        exact ⟨(gather_result_length W _ _ w he).le.trans p,by simpa only [copyBytes_exact] using s⟩

def retainedScanCap (W own E U : ℕ) := 3+E*(10*own+11+wireFee W U)
def freshScanCap (W page E U : ℕ) := 3+E*(10*page+11+wireFee W U)
def emitCap (W E U : ℕ) := 4+E*(E*seekStride W+3*U+12)

def keptPageCap (W own key prec page E U : ℕ) :=
  originFee key prec page true+retainedScanCap W own E U+(4*U+6)+emitCap W E U+8

def savedGateCap (w W own E U b d : ℕ) :=
  retainedScanCap W own E U+(3+E*(17+8*w+3*W+5*U))+
    (8+d*(locateFee w E+W+9))+currentGateFee W b E d+7

theorem same_owner_page_compilation_fee {W own key prec page U E : ℕ}
    (fs : List (FramedEdge W own key prec page)) (fit : FramesFit fs U) (n : fs.length≤E)
    (book : List (Word W)) (nb : book.length≤E) (id : Word own) (tag : Origin key prec page) :
    (compileKeptPage id tag book fs).steps≤keptPageCap W own key prec page E U := by
  let req := collectRetained id fs
  have hs := retained_scan_bounded fs fit id
  have hreq : req.result.length≤E := hs.1.trans n
  have hm : req.steps≤retainedScanCap W own E U :=
    hs.2.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ n) _)
  have hd : (requestDepth req.result).steps≤4*U+6 := request_depth_fee req.result hs.2.1
  have hwire : (emitWires book req.result).steps≤emitCap W E U := (wire_emission_fee book req.result hs.2.1).trans
    (Nat.add_le_add_left (Nat.mul_le_mul hreq
      (by exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_right _ nb) _) _)) _)
  have oc := copy_origin_exact tag
  unfold compileKeptPage
  dsimp only
  rw [oc]
  cases pg : tag.pageKey with
  | none =>
    change originFee key prec page false+4≤_
    have ho := origin_fee_upper key prec page false
    unfold keptPageCap
    omega
  | some p =>
    change (match (requestDepth req.result).result with
      | none => ⟨none,originFee key prec page true+req.steps+(requestDepth req.result).steps+6⟩
      | some d => ⟨(emitWires book req.result).result.map (.packet tag.stamp.creator p d),
          originFee key prec page true+req.steps+(requestDepth req.result).steps+
          (emitWires book req.result).steps+8⟩ : Meter (Option (ReadCmd key page))).steps≤_
    cases (requestDepth req.result).result
    all_goals dsimp only; unfold keptPageCap; omega

theorem same_owner_gate_compilation_fee {w W own key prec page U E : ℕ}
    (fs : List (FramedEdge W own key prec page)) (fit : FramesFit fs U) (n : fs.length≤E)
    (book : List (Word W)) (nb : book.length≤E) (id : Word own) (b d : ℕ)
    (g : CodeGate (Word w)) (hg : GateFit d g) :
    (compileSavedGate b book fs id g).steps≤savedGateCap w W own E U b d := by
  let req := collectRetained id fs
  let tbl := suffixTable w req.result
  let route := rerouteGate tbl.result g
  have hs := retained_scan_bounded fs fit id
  have hN : req.result.length≤E := hs.1.trans n
  have hreq : req.steps≤retainedScanCap W own E U :=
    hs.2.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ n) _)
  obtain ⟨hL,hT⟩ := suffix_table_fee w U req.result hs.2.1
  have hT' : tbl.steps≤3+E*(17+8*w+3*W+5*U) :=
    hT.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hN) _)
  have loc : locateFee w tbl.result.length≤locateFee w E := by
    unfold locateFee
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (hL.trans_le hN)) _
  obtain ⟨hR,hShape⟩ := reroute_syntax_fee tbl.result d g hg
  have hR' : route.steps≤8+d*(locateFee w E+W+9) :=
    hR.trans (Nat.add_le_add_left (Nat.mul_le_mul_left d
      (Nat.add_le_add_right (Nat.add_le_add_right loc _) _)) _)
  change (match route.result with
    | none => ⟨none,req.steps+tbl.steps+route.steps+4⟩
    | some x => ⟨(compileCurrentGate b book x).result.map (ReadCmd.gate b),
        req.steps+tbl.steps+route.steps+(compileCurrentGate b book x).steps+7⟩ :
          Meter (Option (ReadCmd key page))).steps ≤ _
  cases hh : route.result with
  | none => unfold savedGateCap; dsimp only; omega
  | some x =>
    have hC := compiled_gate_syntax_fee book b d x (hShape x hh)
    have hC' : currentGateFee W b book.length d≤currentGateFee W b E d := by
      unfold currentGateFee portOrdinalFee
      gcongr
    unfold savedGateCap
    dsimp only
    omega

#print axioms gather_result_length
#print axioms compiled_gate_syntax_fee
#print axioms reroute_syntax_fee
#print axioms same_owner_page_compilation_fee
#print axioms same_owner_gate_compilation_fee

end J6R62Leaf
