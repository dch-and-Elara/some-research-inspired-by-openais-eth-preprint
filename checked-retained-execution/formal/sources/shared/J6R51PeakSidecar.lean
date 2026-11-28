
import J6R41StructuredAllPathsSite
import J6R16ModeCostUniform

/-! Selected physical addon tape and its installed indexed sidecar.
Both true half-ports of the source parent are present. This is a
bound at the two-tape installation phase, not a claim that the
returned Meter or all future frames retain both encodings. -/
namespace J6R51Peak
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R41StructuredAllPaths
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun J6R16ModeCost

set_option autoImplicit false
set_option maxHeartbeats 9500000
set_option maxRecDepth 3300

def originWords {key prec page : ℕ} (x : Origin key prec page) : List Bool :=
  x.stamp.creator.bits++x.stamp.created.bits++[x.pageKey.isSome]++x.pageKey.toList.flatMap Word.bits

theorem origin_words_exact {key prec page : ℕ} (x : Origin key prec page) :
    (originWords x).length=key+prec+1+(if x.pageKey.isSome then page else 0) := by
  cases h : x.pageKey with
  | none =>
    simp only [originWords,h,List.length_append,x.stamp.creator.size,x.stamp.created.size,
      Option.isSome_none,Option.toList_none,List.flatMap_nil,List.length_cons,List.length_nil,
      Bool.false_eq_true,if_false,Nat.add_zero]
  | some w =>
    simp only [originWords,h,List.length_append,x.stamp.creator.size,x.stamp.created.size,
      Option.isSome_some,Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_cons,List.length_nil,w.size,if_true]

def addonWords {owner a key prec page : ℕ} (x : Addon owner a key prec page) : List Bool :=
  x.oldOwner.bits++originWords x.oldOrigin++[x.parentWasCol]++x.parentSlot.bits++x.newPage.bits

def addonCap (owner a key prec page : ℕ) : ℕ := owner+a+key+prec+2+2*page

theorem literal_addon_width {owner a key prec page : ℕ} (x : Addon owner a key prec page) :
    (addonWords x).length=owner+a+key+prec+2+page+
      (if x.oldOrigin.pageKey.isSome then page else 0) := by
  simp only [addonWords,List.length_append,origin_words_exact,x.oldOwner.size,x.parentSlot.size,
    x.newPage.size,List.length_cons,List.length_nil]
  omega

theorem literal_addon_word_cap {owner a key prec page : ℕ} (x : Addon owner a key prec page) :
    (addonWords x).length≤addonCap owner a key prec page := by
  rw [literal_addon_width,addonCap]
  split <;> omega

theorem flat_words_bound {A : Type*} (xs : List A) (bits : A→List Bool) (U : ℕ)
    (fit : ∀ x∈xs,(bits x).length≤U) :
    (xs.flatMap bits).length≤xs.length*U := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,List.length_cons,Nat.add_mul,Nat.one_mul]
    exact (Nat.add_le_add (fit x List.mem_cons_self)
      (ih fun y hy=>fit y (List.mem_cons_of_mem _ hy))).trans_eq (Nat.add_comm _ _)

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {B : Birth T v key prec tw bw page}
variable {prev : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}

theorem actual_addon_tapes_count_both_half_ports (S : SiteInputs B prev) :
    S.input.length=2*v.parent.edges ∧ S.bank.length=2*v.parent.edges := by
  letI : Fintype v.parent.host.Edge := v.parent.host.finiteEdge
  have card := full_roster_length B.native.physical.order B.native.physical.nodup B.native.physical.complete
  change B.native.physical.order.length=Nat.card (v.parent.host.Edge⊕v.parent.host.Edge) at card
  have m : Fintype.card v.parent.host.Edge=v.parent.edges := (ticketReady T v).edgeCount
  rw [Nat.card_sum,Nat.card_eq_fintype_card,m] at card
  have size : B.native.physical.order.length=2*v.parent.edges := by omega
  exact ⟨by rw [S.aligned,List.length_map,size],by rw [S.bank_exact,List.length_map,size]⟩

def pairedAddonPayload (S : SiteInputs B prev) : List Bool :=
  (S.input.flatMap addonWords)++
    (S.bank.flatMap (fun x=>x.address.bits++addonWords x.payload))

theorem true_sidecar_install_fields_bound (S : SiteInputs B prev) :
    (pairedAddonPayload S).length≤
      (2*v.parent.edges)*(B.port+2*addonCap S.ownerWidth (dim v) key prec page) := by
  let U := addonCap S.ownerWidth (dim v) key prec page
  have raw := flat_words_bound S.input addonWords U (fun x _=>literal_addon_word_cap x)
  have dst := flat_words_bound S.bank (fun x=>x.address.bits++addonWords x.payload) (B.port+U) (fun x _=>by
    rw [List.length_append,x.address.size]
    exact Nat.add_le_add_left (literal_addon_word_cap x.payload) _)
  obtain ⟨one,two⟩ := actual_addon_tapes_count_both_half_ports S
  rw [one] at raw
  rw [two] at dst
  rw [pairedAddonPayload,List.length_append]
  exact (Nat.add_le_add raw dst).trans_eq (by unfold U; ring)

#print axioms origin_words_exact
#print axioms literal_addon_width
#print axioms actual_addon_tapes_count_both_half_ports
#print axioms true_sidecar_install_fields_bound
end J6R51Peak
