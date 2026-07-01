import Hqiv.Physics.HepDecayReadout

/-!
# HEP decay channel routing (Lean mirror of Python contact selection)

Python mirror: `scripts/hqiv_hep_decay_ledger_contact.py` and
`scripts/hqiv_hep_multichannel_expansion.py` (ledger-derived routing + generative topology).

Computes `OpenFlavourContactKind` from finite species/daughter tags for the
benchmark decay graph.  Contact **weights** remain in `HepDecayReadout`; this
module proves the routing selects the correct kind on curated rows.
-/

namespace Hqiv.Physics

/-! ## Patch ledger -/

structure HadronPatchLedger where
  q3 : ℤ
  strangeness : ℤ
  charm : ℤ
  bottom : ℤ
  a3 : ℤ
  deriving DecidableEq, Repr

def HadronPatchLedger.zero : HadronPatchLedger :=
  { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }

def HadronPatchLedger.add (L₁ L₂ : HadronPatchLedger) : HadronPatchLedger :=
  { q3 := L₁.q3 + L₂.q3
    strangeness := L₁.strangeness + L₂.strangeness
    charm := L₁.charm + L₂.charm
    bottom := L₁.bottom + L₂.bottom
    a3 := L₁.a3 + L₂.a3 }

inductive HepDecaySpecies
  | D0 | D_plus | Ds_plus | B0 | B_plus | Bs
  | pi_plus | pi_minus | pi_zero
  | K_plus | K_minus | K0 | K0_bar
  | p | n | lambda_c | sigma_c | xi_c | omega_c
  | delta_p | delta_pp
  | lambda | sigma_plus | sigma_zero | sigma_minus | xi_zero | xi_minus | omega_hyp
  | rho_zero | rho_plus | omega_meson
  | Jpsi | Upsilon
  | mu_plus | mu_minus | gamma | e_plus | e_minus
  | phi | eta
  deriving DecidableEq, Repr

inductive HepDecayChannel
  | strong | weak | electromagnetic | weak_hadron | stable
  deriving DecidableEq

def HepDecaySpecies.isKaon (s : HepDecaySpecies) : Bool :=
  match s with
  | .K_plus | .K_minus | .K0 | .K0_bar => true
  | _ => false

def HepDecaySpecies.isChargedKaon (s : HepDecaySpecies) : Bool :=
  s == .K_plus || s == .K_minus

def HepDecaySpecies.isNeutralKaon (s : HepDecaySpecies) : Bool :=
  s == .K0 || s == .K0_bar

def HepDecaySpecies.isOpenCharm (s : HepDecaySpecies) : Bool :=
  match s with
  | .D0 | .D_plus | .Ds_plus => true
  | _ => false

def HepDecaySpecies.isPion (s : HepDecaySpecies) : Bool :=
  match s with
  | .pi_plus | .pi_minus | .pi_zero => true
  | _ => false

def speciesLedger : HepDecaySpecies → HadronPatchLedger
  | .D0 => { q3 := 0, strangeness := 0, charm := 1, bottom := 0, a3 := 0 }
  | .D_plus => { q3 := 3, strangeness := 0, charm := 1, bottom := 0, a3 := 0 }
  | .Ds_plus => { q3 := 3, strangeness := 1, charm := 1, bottom := 0, a3 := 0 }
  | .B0 => { q3 := 0, strangeness := 0, charm := 0, bottom := 1, a3 := 0 }
  | .B_plus => { q3 := 3, strangeness := 0, charm := 0, bottom := 1, a3 := 0 }
  | .Bs => { q3 := 0, strangeness := -1, charm := 0, bottom := 1, a3 := 0 }
  | .pi_plus => { q3 := 3, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .pi_minus => { q3 := -3, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .pi_zero => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .K_plus => { q3 := 3, strangeness := 1, charm := 0, bottom := 0, a3 := 0 }
  | .K_minus => { q3 := -3, strangeness := -1, charm := 0, bottom := 0, a3 := 0 }
  | .K0 => { q3 := 0, strangeness := 1, charm := 0, bottom := 0, a3 := 0 }
  | .K0_bar => { q3 := 0, strangeness := -1, charm := 0, bottom := 0, a3 := 0 }
  | .p => { q3 := 3, strangeness := 0, charm := 0, bottom := 0, a3 := 3 }
  | .n => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 3 }
  | .lambda_c => { q3 := 3, strangeness := 0, charm := 1, bottom := 0, a3 := 3 }
  | .sigma_c => { q3 := 3, strangeness := 0, charm := 1, bottom := 0, a3 := 3 }
  | .xi_c => { q3 := 0, strangeness := 0, charm := 1, bottom := 0, a3 := 3 }
  | .omega_c => { q3 := 0, strangeness := 0, charm := 1, bottom := 0, a3 := 3 }
  | .delta_p => { q3 := 3, strangeness := 0, charm := 0, bottom := 0, a3 := 3 }
  | .delta_pp => { q3 := 6, strangeness := 0, charm := 0, bottom := 0, a3 := 3 }
  | .lambda => { q3 := 0, strangeness := -1, charm := 0, bottom := 0, a3 := 3 }
  | .sigma_plus => { q3 := 3, strangeness := -1, charm := 0, bottom := 0, a3 := 3 }
  | .sigma_zero => { q3 := 0, strangeness := -1, charm := 0, bottom := 0, a3 := 3 }
  | .sigma_minus => { q3 := -3, strangeness := -1, charm := 0, bottom := 0, a3 := 3 }
  | .xi_zero => { q3 := 0, strangeness := -2, charm := 0, bottom := 0, a3 := 3 }
  | .xi_minus => { q3 := -3, strangeness := -2, charm := 0, bottom := 0, a3 := 3 }
  | .omega_hyp => { q3 := -3, strangeness := -3, charm := 0, bottom := 0, a3 := 3 }
  | .rho_zero => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .rho_plus => { q3 := 3, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .omega_meson => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .Jpsi => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .Upsilon => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .mu_plus => { q3 := 3, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .mu_minus => { q3 := -3, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .gamma => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .e_plus => { q3 := 3, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .e_minus => { q3 := -3, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .phi => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }
  | .eta => { q3 := 0, strangeness := 0, charm := 0, bottom := 0, a3 := 0 }

def ledgerSum (ds : List HepDecaySpecies) : HadronPatchLedger :=
  ds.foldl (fun acc s => HadronPatchLedger.add acc (speciesLedger s)) HadronPatchLedger.zero

def hasChargedKaon (ds : List HepDecaySpecies) : Bool :=
  ds.any HepDecaySpecies.isChargedKaon

def hasNeutralKaon (ds : List HepDecaySpecies) : Bool :=
  ds.any HepDecaySpecies.isNeutralKaon

def hasOpenCharm (ds : List HepDecaySpecies) : Bool :=
  ds.any HepDecaySpecies.isOpenCharm

def hasPion (ds : List HepDecaySpecies) : Bool :=
  ds.any HepDecaySpecies.isPion

def SingleWChargeLoad (parent total : HadronPatchLedger) : Prop :=
  Int.natAbs (parent.q3 - total.q3) ≤ 3

def ledgerDelta (parent total : HadronPatchLedger) : HadronPatchLedger :=
  { q3 := total.q3 - parent.q3
    strangeness := total.strangeness - parent.strangeness
    charm := total.charm - parent.charm
    bottom := total.bottom - parent.bottom
    a3 := total.a3 - parent.a3 }

def singleWChargeLoadOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  let p := speciesLedger parent
  let t := ledgerSum ds
  Int.natAbs (p.q3 - t.q3) ≤ 3

def isOpenCharmMeson (s : HepDecaySpecies) : Bool :=
  s == .D_plus || s == .D0 || s == .Ds_plus

def isOpenBottomMeson (s : HepDecaySpecies) : Bool :=
  s == .B_plus || s == .B0 || s == .Bs

def isCharmedBaryon (s : HepDecaySpecies) : Bool :=
  s == .lambda_c || s == .sigma_c || s == .xi_c || s == .omega_c

def parentChargedPionId (parent : HepDecaySpecies) : Option HepDecaySpecies :=
  let q3 := (speciesLedger parent).q3
  if q3 > 0 then some .pi_plus
  else if q3 < 0 then some .pi_minus
  else if parent == .D0 then some .pi_minus
  else none

def kaonOutletSignOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  let pq3 := (speciesLedger parent).q3
  ds.all fun s =>
    if s.isChargedKaon then
      let kq3 := (speciesLedger s).q3
      if kq3 == 0 then true
      else if pq3 > 0 then kq3 ≤ 0
      else if pq3 < 0 then kq3 ≥ 0
      else kq3 ≥ 0
    else true

def countSpecies (ds : List HepDecaySpecies) (target : HepDecaySpecies) : Nat :=
  ds.filter (· == target) |>.length

def openCharmKaonModeOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  let n := ds.length
  if !ds.any HepDecaySpecies.isKaon then false
  else if ds.any (· == .K0_bar) then false
  else if n == 2 then
    match parentChargedPionId parent with
    | some π => ds.contains π
    | none => false
  else if n == 3 then
    match parentChargedPionId parent with
    | some π =>
      ds.contains π && countSpecies ds .pi_zero == 1 &&
        (ds.filter HepDecaySpecies.isKaon).length == 1 &&
        ds.all fun d => d.isKaon || d.isPion
    | none => false
  else false

def openCharmPionOnlyOk (ds : List HepDecaySpecies) : Bool :=
  countSpecies ds .pi_plus == 1 && countSpecies ds .pi_minus == 1 && countSpecies ds .pi_zero == 1

def isBottomHeavy (s : HepDecaySpecies) : Bool :=
  s == .D0 || s == .D_plus

def bottomHeavyDaughterOk (parent heavy : HepDecaySpecies) : Bool :=
  if parent == .Bs then heavy == .Ds_plus
  else if parent == .B_plus || parent == .B0 then heavy == .D0 || heavy == .D_plus
  else true

def bottomTwoBodyOk (parent heavy light : HepDecaySpecies) : Bool :=
  let p := speciesLedger parent
  let h := speciesLedger heavy
  let l := speciesLedger light
  let totalQ3 := h.q3 + l.q3
  totalQ3 == p.q3 ||
    (h.q3 == 0 && l.q3 == p.q3) ||
    (h.q3 == p.q3 && l.q3 == -p.q3)

def bottomThreeBodyOk (parent heavy : HepDecaySpecies) (lights : List HepDecaySpecies) : Bool :=
  match lights with
  | [a, b] =>
    let pions := [a, b]
    if !pions.all HepDecaySpecies.isPion then false
    else if countSpecies pions .pi_zero != 1 then false
    else
      let other := if a == .pi_zero then b else a
      let p := speciesLedger parent
      let h := speciesLedger heavy
      let o := speciesLedger other
      if p.q3 == 0 then heavy == .D0 && other == .pi_plus
      else
        match parentChargedPionId parent with
        | some π => (heavy == .D0 && other == π) || (h.q3 == p.q3 && o.q3 == -p.q3)
        | none => h.q3 == p.q3 && o.q3 == -p.q3
  | _ => false

def weakBottomMesonSparse (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  match ds.filter isBottomHeavy with
  | [heavy] =>
    if !bottomHeavyDaughterOk parent heavy then false
    else
      let lights := ds.filter fun s => s != heavy
      if lights.isEmpty then false
      else if !singleWChargeLoadOk parent ds then false
      else if ds.length == 2 then
        if parent == .B0 then true
        else match lights with
          | [light] => bottomTwoBodyOk parent heavy light
          | _ => false
      else if ds.length == 3 then
        bottomThreeBodyOk parent heavy lights
      else false
  | _ => false

def visibleChargeQ3 (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : ℤ :=
  (speciesLedger parent).q3 - (ledgerSum ds).q3

def visibleChargeCloses (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  visibleChargeQ3 parent ds == 0

def hasOpenCharmHadron (ds : List HepDecaySpecies) : Bool :=
  ds.any fun s => s == .D0 || s == .D_plus || s == .Ds_plus

def hasHiddenStrangenessVector (ds : List HepDecaySpecies) : Bool :=
  !hasOpenCharmHadron ds && ds.length == 2 && ds.all fun s => s == .phi || s.isPion

def isLightHadronDischarge (s : HepDecaySpecies) : Bool :=
  let l := speciesLedger s
  l.a3 == 0 && l.charm == 0 && l.bottom == 0

def isNeutralLightDischarge (s : HepDecaySpecies) : Bool :=
  isLightHadronDischarge s && (speciesLedger s).q3 == 0

def isChargedLightDischarge (s : HepDecaySpecies) : Bool :=
  isLightHadronDischarge s && (speciesLedger s).q3 != 0

def hasNeutralLightDischarge (ds : List HepDecaySpecies) : Bool :=
  ds.any isNeutralLightDischarge

def hasChargedLightDischarge (ds : List HepDecaySpecies) : Bool :=
  ds.any isChargedLightDischarge

def hasLightPseudoscalarDischarge (ds : List HepDecaySpecies) : Bool :=
  ds.any fun s => isLightHadronDischarge s && !s.isKaon

def isCharmedBaryonPKLightDischarge (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  (parent == .lambda_c || parent == .sigma_c) && ds.length == 3 &&
    ds.any (fun s => s == .p || s == .n) && hasChargedKaon ds && hasLightPseudoscalarDischarge ds

def isCharmedBaryonFourBody (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  parent == .lambda_c && ds.length == 4 && countSpecies ds .pi_zero == 1 &&
    isCharmedBaryonPKLightDischarge parent (ds.filter (· != .pi_zero))

def isXiCascade (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  (parent == .xi_c || parent == .omega_c) && ds.length == 2 &&
    (ds.contains .lambda_c || ds.contains .sigma_c) &&
    ds.any isLightHadronDischarge

def isXiCascadeLambdaGround (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  parent == .xi_c && ds == [.lambda_c, .pi_zero]

def lambdaCWeakSparse (ds : List HepDecaySpecies) : Bool :=
  let n := ds.length
  !ds.any HepDecaySpecies.isOpenCharm &&
    (if n == 2 then
      visibleChargeCloses .lambda_c ds &&
        ds.any (fun s => s == .p || s == .n) &&
        ds.all fun s => s == .p || s == .n || s == .pi_zero || s == .K_plus || s == .K_minus
     else if n == 3 then isCharmedBaryonPKLightDischarge .lambda_c ds
     else if n == 4 then isCharmedBaryonFourBody .lambda_c ds
     else false)

def dsWeakSparse (ds : List HepDecaySpecies) : Bool :=
  let n := ds.length
  !ds.any HepDecaySpecies.isOpenCharm &&
    (if n == 1 then ds == [.K_plus]
     else if n == 2 || n == 3 then
       singleWChargeLoadOk .Ds_plus ds &&
         (ds == [.K_plus, .pi_zero] ||
           (ds.length == 3 && ds.contains .K_plus && ds.contains .K_minus &&
              match parentChargedPionId .Ds_plus with
              | some π => ds.contains π && ds.all fun d => d.isKaon || d.isPion
              | none => false) ||
           (kaonOutletSignOk .Ds_plus ds &&
             (if ds.any HepDecaySpecies.isKaon then
                if n == 2 then
                  match parentChargedPionId .Ds_plus with
                  | some π => ds.contains π
                  | none => false
                else
                  match parentChargedPionId .Ds_plus with
                  | some π =>
                    ds.contains π && countSpecies ds .pi_zero == 1 &&
                      (ds.filter HepDecaySpecies.isKaon).length == 1 &&
                      ds.all fun d => d.isKaon || d.isPion || d == .eta
                  | none => false
              else
                match parentChargedPionId .Ds_plus with
                | some π => ds.contains .eta && ds.contains π
                | none => false)))
     else false)

def bsWeakSparse (ds : List HepDecaySpecies) : Bool :=
  ds.length == 2 &&
    (ds == [.phi, .phi] ||
      (ds.contains .Ds_plus &&
        singleWChargeLoadOk .Bs ds &&
        match ds.filter (· != .Ds_plus) with
        | [light] => light.isPion || light.isKaon || light == .eta
        | _ => false))

def xiCCascadeSparse (ds : List HepDecaySpecies) : Bool :=
  isXiCascade .xi_c ds

def omegaCCascadeSparse (ds : List HepDecaySpecies) : Bool :=
  isXiCascade .omega_c ds

def isLightStrangeBaryon (s : HepDecaySpecies) : Bool :=
  s == .lambda || s == .sigma_plus || s == .sigma_zero || s == .sigma_minus ||
    s == .xi_zero || s == .xi_minus || s == .omega_hyp

def isLightKaon (s : HepDecaySpecies) : Bool :=
  s == .K_plus || s == .K_minus || s == .K0

def isIsospinHalfWeakParent (s : HepDecaySpecies) : Bool :=
  s == .lambda || s == .K_plus || s == .K_minus || s == .K0

def isNeutralIsovectorPionOnlyOutlet (ds : List HepDecaySpecies) : Bool :=
  ds.contains .pi_zero && countSpecies ds .pi_plus == 0 && countSpecies ds .pi_minus == 0

def isLightSemileptonicWeakOutlet (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  singleWChargeLoadOk parent ds &&
    ((parent == .K_plus && ds == [.mu_plus]) ||
      (parent == .K_minus && ds == [.mu_minus]))

def isVisibleChargedLepton (s : HepDecaySpecies) : Bool :=
  s == .mu_plus || s == .mu_minus || s == .e_plus || s == .e_minus

def isOpenCharmSemileptonicWeakOutlet (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  (parent == .D_plus && (ds == [.mu_plus] || ds == [.e_plus]) ||
    parent == .D0 && (ds == [.mu_minus] || ds == [.e_minus])) &&
    singleWChargeLoadOk parent ds

def isCharmedBaryonSemileptonicWeakOutlet (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  parent == .lambda_c && (ds == [.mu_plus] || ds == [.e_plus]) &&
    singleWChargeLoadOk parent ds

def isSemileptonicWeakOutlet (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  isLightSemileptonicWeakOutlet parent ds ||
    isOpenCharmSemileptonicWeakOutlet parent ds ||
    isCharmedBaryonSemileptonicWeakOutlet parent ds

def isHiddenCharmQuarkonium (s : HepDecaySpecies) : Bool :=
  s == .Jpsi

def isHiddenBottomQuarkonium (s : HepDecaySpecies) : Bool :=
  s == .Upsilon

def isNeutralLightCascade (ds : List HepDecaySpecies) : Bool :=
  let t := ledgerSum ds
  t.q3 == 0 && t.strangeness == 0

def isDecupletBaryon (s : HepDecaySpecies) : Bool :=
  s == .delta_p || s == .delta_pp

def isLightVectorMeson (s : HepDecaySpecies) : Bool :=
  s == .rho_zero || s == .rho_plus || s == .omega_meson || s == .phi

def isOpenCharmWeakVectorDaughter (s : HepDecaySpecies) : Bool :=
  isLightVectorMeson s

def hasOpenCharmWeakVectorDaughter (ds : List HepDecaySpecies) : Bool :=
  ds.any isOpenCharmWeakVectorDaughter

def hasLightVectorMeson (ds : List HepDecaySpecies) : Bool :=
  ds.any isLightVectorMeson

/-- Three-light-meson weak span: π⁺/ρ⁺ tag with π⁻ and π⁰ (Python ``_open_charm_light_pseudoscalar_ok``). -/
def openCharmLightPseudoscalarSpanOk (ds : List HepDecaySpecies) : Bool :=
  ds.length == 3 && countSpecies ds .pi_minus == 1 && countSpecies ds .pi_zero == 1 &&
    (countSpecies ds .pi_plus == 1 || countSpecies ds .rho_plus == 1)

/-- Open-charm $K + \rho/\omega/K^*$ two-body weak outlet (vector / excited-strange discharge). -/
def openCharmKaonVectorModeOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  if ds.length != 2 then false
  else if (ds.filter HepDecaySpecies.isKaon).length != 1 then false
  else if (ds.filter isOpenCharmWeakVectorDaughter).length != 1 then false
  else if parent == .D0 && !(ds.any HepDecaySpecies.isNeutralKaon) then false
  else singleWChargeLoadOk parent ds && kaonOutletSignOk parent ds

/-- Open-charm $K + \eta$ two-body weak outlet (isoscalar pseudoscalar leak on the kaon pole). -/
def openCharmKaonEtaModeOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  if ds.length != 2 then false
  else if (ds.filter HepDecaySpecies.isKaon).length != 1 then false
  else if !ds.any (· == .eta) then false
  else if ds.any (· == .K0_bar) then false
  else if !(ds.any HepDecaySpecies.isNeutralKaon) then false
  else singleWChargeLoadOk parent ds && kaonOutletSignOk parent ds

def isLightBaryonDaughter (s : HepDecaySpecies) : Bool :=
  s == .p || s == .n || s == .lambda || s == .sigma_plus || s == .sigma_zero ||
    s == .xi_zero || s == .xi_minus

def vectorPionDischargeOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  if parent == .rho_zero && ds.length == 2 then
    ds.all HepDecaySpecies.isPion && countSpecies ds .pi_plus == 1 && countSpecies ds .pi_minus == 1
  else true

def lightStrongTopologyOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  if !vectorPionDischargeOk parent ds then false
  else if parent == .omega_meson then ds.length == 3 && ds.all HepDecaySpecies.isPion
  else if parent == .phi then
    (ds.length == 2 && ds.all HepDecaySpecies.isKaon) ||
      (ds.length == 3 && ds.all HepDecaySpecies.isPion)
  else if parent == .rho_zero || parent == .rho_plus then
    ds.length == 2 && ds.all HepDecaySpecies.isPion
  else if parent == .delta_p || parent == .delta_pp then
    ds.length == 2 &&
      (ds.filter isLightBaryonDaughter).length == 1 &&
      (ds.filter HepDecaySpecies.isPion).length == 1
  else if parent == .sigma_plus then
    ds.length == 2 && ds.contains .p &&
      countSpecies ds .pi_zero == 1 && countSpecies ds .pi_plus == 0 && countSpecies ds .pi_minus == 0
  else if parent == .sigma_minus then
    ds.length == 2 && ds.contains .n && countSpecies ds .pi_minus == 1 &&
      countSpecies ds .pi_zero == 0
  else if parent == .sigma_zero || parent == .xi_zero then
    ds.length == 2 && ds.contains .lambda && ds.any HepDecaySpecies.isPion
  else if parent == .xi_minus then
    ds.length == 2 && ds.contains .lambda && ds.any HepDecaySpecies.isPion
  else false

def lightWeakHadronicTopologyOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  if !singleWChargeLoadOk parent ds then false
  else if isLightKaon parent then
    let n := ds.length
    if parent == .K0 then n == 1 && ds == [.pi_zero]
    else if n == 1 then ds.length == 1 && ds.all HepDecaySpecies.isPion
    else if n == 3 then
      match parentChargedPionId parent with
      | some π =>
        ds.contains π && countSpecies ds .pi_zero == 2 && ds.all HepDecaySpecies.isPion
      | none => false
    else false
  else if isLightStrangeBaryon parent then
    ds.length == 2 &&
      (ds.filter isLightBaryonDaughter).length == 1 &&
      (ds.filter HepDecaySpecies.isPion).length == 1
  else false

def strongCurvatureAllowed (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  let p := speciesLedger parent
  let t := ledgerSum ds
  t.q3 == p.q3 && t.a3 == p.a3

def strongChannelAllowed (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  strongCurvatureAllowed parent ds && lightStrongTopologyOk parent ds

def weakHadronicAllowed (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  let p := speciesLedger parent
  let t := ledgerSum ds
  if t.a3 != p.a3 then false
  else
    let d := ledgerDelta p t
    if Int.natAbs d.strangeness > 1 then false
    else if isOpenCharmMeson parent then d.charm == -1 && d.bottom == 0
    else if isOpenBottomMeson parent then d.bottom == -1 && (d.charm == 0 || d.charm == 1)
    else if parent == .xi_c || parent == .omega_c then d.bottom == 0 && (d.charm == 0 || d.charm == -1)
    else if parent == .lambda_c || parent == .sigma_c then d.charm == -1 && d.bottom == 0
    else if isLightKaon parent then
      let ps := (speciesLedger parent).strangeness
      d.charm == 0 && d.bottom == 0 && d.strangeness == -ps
    else if isLightStrangeBaryon parent then d.charm == 0 && d.bottom == 0 && Int.natAbs d.strangeness ≤ 1
    else false

def weakTopologySparse (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  if parent == .Ds_plus then dsWeakSparse ds
  else if isLightKaon parent || isLightStrangeBaryon parent then lightWeakHadronicTopologyOk parent ds
  else if parent == .lambda_c then lambdaCWeakSparse ds
  else if parent == .Bs then bsWeakSparse ds
  else if parent == .xi_c then xiCCascadeSparse ds
  else if parent == .omega_c then omegaCCascadeSparse ds
  else if parent == .D_plus || parent == .D0 then
    let n := ds.length
    n ≥ 2 && n ≤ 3 && !ds.any HepDecaySpecies.isOpenCharm &&
      singleWChargeLoadOk parent ds && kaonOutletSignOk parent ds &&
      (if openCharmKaonVectorModeOk parent ds then true
       else if openCharmKaonEtaModeOk parent ds then true
       else if ds.any HepDecaySpecies.isKaon then openCharmKaonModeOk parent ds
       else if openCharmLightPseudoscalarSpanOk ds then true
       else openCharmPionOnlyOk ds)
  else if parent == .B_plus || parent == .B0 then
    weakBottomMesonSparse parent ds
  else if parent == .sigma_c then
    ds.length == 3 && ds.any (fun s => s == .p || s == .n) && hasChargedKaon ds && hasPion ds
  else false

def weakSemileptonicHadronicLedgerOk (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  let p := speciesLedger parent
  let t := ledgerSum ds
  let d := ledgerDelta p t
  if isCharmedBaryonSemileptonicWeakOutlet parent ds then
    d.charm == -1 && d.bottom == 0
  else if isOpenCharmSemileptonicWeakOutlet parent ds || isLightSemileptonicWeakOutlet parent ds then
    weakHadronicAllowed parent ds
  else false

def weakChannelAllowed (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  (isSemileptonicWeakOutlet parent ds && weakSemileptonicHadronicLedgerOk parent ds) ||
    (weakHadronicAllowed parent ds && weakTopologySparse parent ds)

/-! ## Finite spanning certificates (benchmark parents) -/

def lambdaCWeakModes : List (List HepDecaySpecies) := [
  [.p, .pi_zero], [.n, .K_plus], [.p, .K_minus, .pi_plus], [.p, .K_minus, .pi_zero],
  [.p, .K_plus, .pi_minus], [.p, .K_minus, .pi_plus, .pi_zero]
]

theorem lambdaCWeakModes_count_six : lambdaCWeakModes.length = 6 := by decide

theorem weakChannelAllowed_lambdaC_modes :
    ∀ ds ∈ lambdaCWeakModes, weakChannelAllowed .lambda_c ds := by
  decide

theorem weakChannelAllowed_Bs_DsK :
    weakChannelAllowed .Bs [.Ds_plus, .K_minus] := by decide

theorem weakChannelAllowed_Bs_phi :
    weakChannelAllowed .Bs [.phi, .phi] := by decide

theorem weakChannelAllowed_xi_c_lambda_pi0 :
    weakChannelAllowed .xi_c [.lambda_c, .pi_zero] := by decide

theorem weakChannelAllowed_ds_Kplus :
    weakChannelAllowed .Ds_plus [.K_plus] := by decide

theorem weakChannelAllowed_B0_D0pi0 :
    weakChannelAllowed .B0 [.D0, .pi_zero] := by decide

theorem weakChannelAllowed_Bplus_D0piplus :
    weakChannelAllowed .B_plus [.D0, .pi_plus] := by decide

theorem weakChannelAllowed_lambda_c_PKpi_sibling :
    weakChannelAllowed .lambda_c [.p, .K_plus, .pi_minus] := by decide

def isCharmPionOnlyWeak (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  (parent == .D_plus || parent == .D0) && !ds.any HepDecaySpecies.isKaon &&
    (openCharmPionOnlyOk ds || openCharmLightPseudoscalarSpanOk ds)

def isCabibboChargedKaonOutlet (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  (parent == .D_plus || parent == .D0) && hasChargedKaon ds && !hasNeutralKaon ds

def isBottomExternalWeak (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  (parent == .B_plus || parent == .B0) &&
    (ds == [.D0, .pi_plus] || ds == [.D_plus, .pi_minus])

def isNeutralBottomSpectator (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  parent == .B0 && ds == [.D0, .pi_zero] && visibleChargeCloses parent ds

def isHiddenStrangenessPoleDischarge (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  parent == .Ds_plus && ds == [.phi]

def isOziSuppressedOpenCharmStrangeStrong (parent : HepDecaySpecies) (ds : List HepDecaySpecies) : Bool :=
  parent == .Ds_plus && ds != [.phi] && ds.all isLightHadronDischarge

/-! ## Weak outlet property classification (Python ``WeakOutletChannel`` mirror) -/

inductive WeakOutletProperty
  | semileptonicVisibleLepton
  | kaonHadronicMonogamyCharged
  | kaonHadronicMonogamyNeutral
  | isospinHalfChargedHadronic
  | isospinHalfNeutralPionBaryon
  | isospinHalfNeutralPionMeson
  | charmPionOnly
  | charmKaonVectorOutlet
  | charmKaonEtaOutlet
  | charmKaonCabibboExclusion
  | charmedBaryonPkLight
  | cascadeLambdaGround
  | cascadeNeutralSpectator
  | cascadeChargedExclusion
  | bottomExternalWeak
  | bottomNeutralSpectator
  | bottomStrangeOpenCharm
  | bottomStrangeHiddenPhi
  | bottomStrangeDsSpectator
  | finiteOpenBottomCompletion
  | finiteDsCompletion
  | unitOutlet
  deriving DecidableEq, Repr

def classifyWeakOutletProperty (parent : HepDecaySpecies) (ds : List HepDecaySpecies)
    : WeakOutletProperty :=
  if isOpenCharmSemileptonicWeakOutlet parent ds || isCharmedBaryonSemileptonicWeakOutlet parent ds then
    .semileptonicVisibleLepton
  else if isCharmPionOnlyWeak parent ds then .charmPionOnly
  else if (parent == .D_plus || parent == .D0) && hasOpenCharmWeakVectorDaughter ds then .charmKaonVectorOutlet
  else if (parent == .D_plus || parent == .D0) && openCharmKaonEtaModeOk parent ds then .charmKaonEtaOutlet
  else if (parent == .D_plus || parent == .D0) && openCharmKaonModeOk parent ds then .charmKaonCabibboExclusion
  else if isCabibboChargedKaonOutlet parent ds then .charmKaonCabibboExclusion
  else if parent == .Ds_plus && ds.length ≥ 2 then .finiteDsCompletion
  else if isCharmedBaryonPKLightDischarge parent ds || isCharmedBaryonFourBody parent ds then
    .charmedBaryonPkLight
  else if isXiCascade parent ds then
    if isXiCascadeLambdaGround parent ds then .cascadeLambdaGround
    else if hasNeutralLightDischarge ds then .cascadeNeutralSpectator
    else if hasChargedLightDischarge ds then .cascadeChargedExclusion
    else .unitOutlet
  else if isBottomExternalWeak parent ds then .bottomExternalWeak
  else if isNeutralBottomSpectator parent ds then .bottomNeutralSpectator
  else if parent == .Bs && hasOpenCharmHadron ds then .bottomStrangeOpenCharm
  else if parent == .Bs && hasHiddenStrangenessVector ds then .bottomStrangeHiddenPhi
  else if parent == .Bs && ds.contains .Ds_plus then .bottomStrangeDsSpectator
  else if (parent == .B_plus || parent == .B0) && hasOpenCharm ds then .finiteOpenBottomCompletion
  else if isLightSemileptonicWeakOutlet parent ds then .semileptonicVisibleLepton
  else if parent == .K_plus || parent == .K_minus || parent == .K0 then
    if isNeutralIsovectorPionOnlyOutlet ds then .kaonHadronicMonogamyNeutral
    else .kaonHadronicMonogamyCharged
  else if isIsospinHalfWeakParent parent then
    if isNeutralIsovectorPionOnlyOutlet ds then
      if isLightStrangeBaryon parent then .isospinHalfNeutralPionBaryon
      else .isospinHalfNeutralPionMeson
    else .isospinHalfChargedHadronic
  else .unitOutlet

def openFlavourContactKindFromWeakOutlet (parent : HepDecaySpecies) (ds : List HepDecaySpecies)
    (w : WeakOutletProperty) : OpenFlavourContactKind :=
  match w with
  | .semileptonicVisibleLepton =>
    if parent == .K_plus || parent == .K_minus then .lightKaonSemileptonicNeutrinoCompletion
    else if parent == .D_plus || parent == .D0 || parent == .lambda_c then .openCharmSemileptonicNeutrinoCompletion
    else .leptonNeutrinoWeakOutlet
  | .kaonHadronicMonogamyCharged =>
    if parent == .K_plus || parent == .K_minus then .isospinHalfHadronicSemileptonicCompetition
    else .isospinHalfHadronicMonogamyExclusion
  | .kaonHadronicMonogamyNeutral =>
    if parent == .K_plus || parent == .K_minus then .isospinHalfNeutralHadronicSemileptonicCompetition
    else .isospinHalfNeutralHadronicMonogamyExclusion
  | .isospinHalfChargedHadronic => .isospinHalfWeak
  | .isospinHalfNeutralPionBaryon => .lightBaryonNeutralIsospinOutlet
  | .isospinHalfNeutralPionMeson => .isospinHalfNeutralOutlet
  | .charmPionOnly => .charmPionOnly
  | .charmKaonVectorOutlet => .hiddenStrangenessVectorLeak
  | .charmKaonEtaOutlet => .hiddenStrangenessVectorLeak
  | .charmKaonCabibboExclusion => .openCharmHadronicMonogamyExclusion
  | .charmedBaryonPkLight =>
    if parent == .lambda_c then .charmedBaryonSemileptonicHadronic
    else if kaonOutletSignOk parent ds then .charmedBaryonDoubleMonogamy else .doubleMonogamyExclusion
  | .cascadeLambdaGround => .cascadeLambdaGround
  | .cascadeNeutralSpectator => .neutralSpectatorComplement
  | .cascadeChargedExclusion => .doubleMonogamyExclusion
  | .bottomExternalWeak => .bottomExternalWeak
  | .bottomNeutralSpectator => .bottomNeutralSpectator
  | .bottomStrangeOpenCharm => .bottomStrangeDoubleMonogamy
  | .bottomStrangeHiddenPhi => .bottomStrangeDoubleMonogamy
  | .bottomStrangeDsSpectator => .spectatorHalfMonogamy
  | .finiteOpenBottomCompletion => .finiteOpenBottomCompletion
  | .finiteDsCompletion => .finiteChannelCompletion
  | .unitOutlet => .unitSeed

def openFlavourContactKind (parent : HepDecaySpecies) (channel : HepDecayChannel)
    (ds : List HepDecaySpecies) : OpenFlavourContactKind :=
  if channel == .strong then
    if parent == .phi && ds.length == 3 && ds.all HepDecaySpecies.isPion then
      .hiddenStrangenessVectorLeak
    else if parent == .phi && ds.length == 2 && ds.all HepDecaySpecies.isKaon then
      .hiddenStrangenessKkRetention
    else if isHiddenStrangenessPoleDischarge parent ds then .hiddenStrangenessPoleDischarge
    else if isOziSuppressedOpenCharmStrangeStrong parent ds then .oziSuppressedStrong
    else .unitSeed
  else if channel != .weak then .unitSeed
  else openFlavourContactKindFromWeakOutlet parent ds (classifyWeakOutletProperty parent ds)

def openFlavourContactKind_legacy (parent : HepDecaySpecies) (channel : HepDecayChannel)
    (ds : List HepDecaySpecies) : OpenFlavourContactKind :=
  if channel == .strong then
    if parent == .phi && ds.length == 3 && ds.all HepDecaySpecies.isPion then
      .hiddenStrangenessVectorLeak
    else if parent == .phi && ds.length == 2 && ds.all HepDecaySpecies.isKaon then
      .hiddenStrangenessKkRetention
    else if isHiddenStrangenessPoleDischarge parent ds then .hiddenStrangenessPoleDischarge
    else if isOziSuppressedOpenCharmStrangeStrong parent ds then .oziSuppressedStrong
    else .unitSeed
  else if channel != .weak then .unitSeed
  else if isOpenCharmSemileptonicWeakOutlet parent ds then
    if parent == .D_plus || parent == .D0 || parent == .lambda_c then .openCharmSemileptonicNeutrinoCompletion
    else .leptonNeutrinoWeakOutlet
  else if isCharmedBaryonSemileptonicWeakOutlet parent ds then .leptonNeutrinoWeakOutlet
  else if isCharmPionOnlyWeak parent ds then .charmPionOnly
  else if (parent == .D_plus || parent == .D0) && hasOpenCharmWeakVectorDaughter ds then .hiddenStrangenessVectorLeak
  else if (parent == .D_plus || parent == .D0) && openCharmKaonEtaModeOk parent ds then .hiddenStrangenessVectorLeak
  else if (parent == .D_plus || parent == .D0) && openCharmKaonModeOk parent ds then .openCharmHadronicMonogamyExclusion
  else if isCabibboChargedKaonOutlet parent ds then .doubleMonogamyExclusion
  else if parent == .Ds_plus && ds.length ≥ 2 then .finiteChannelCompletion
  else if isCharmedBaryonPKLightDischarge parent ds || isCharmedBaryonFourBody parent ds then
    if parent == .lambda_c && kaonOutletSignOk parent ds then .charmedBaryonSemileptonicHadronic
    else if kaonOutletSignOk parent ds then .charmedBaryonDoubleMonogamy else .doubleMonogamyExclusion
  else if isXiCascade parent ds then
    if isXiCascadeLambdaGround parent ds then .cascadeLambdaGround
    else if hasNeutralLightDischarge ds then .neutralSpectatorComplement
    else if hasChargedLightDischarge ds then .doubleMonogamyExclusion
    else .unitSeed
  else if isBottomExternalWeak parent ds then .bottomExternalWeak
  else if isNeutralBottomSpectator parent ds then .neutralSpectatorComplement
  else if parent == .Bs && hasOpenCharmHadron ds then .bottomStrangeDoubleMonogamy
  else if parent == .Bs && hasHiddenStrangenessVector ds then .bottomStrangeDoubleMonogamy
  else if parent == .Bs && ds.contains .Ds_plus then .spectatorHalfMonogamy
  else if (parent == .B_plus || parent == .B0) && hasOpenCharm ds then .finiteChannelCompletion
  else if channel == .weak && isLightSemileptonicWeakOutlet parent ds then
    if parent == .K_plus || parent == .K_minus then .semileptonicNeutrinoChannelCompletion
    else .leptonNeutrinoWeakOutlet
  else if channel == .weak && (parent == .K_plus || parent == .K_minus || parent == .K0) then
    if isNeutralIsovectorPionOnlyOutlet ds then
      if parent == .K_plus || parent == .K_minus then .isospinHalfNeutralHadronicSemileptonicCompetition
      else .isospinHalfNeutralHadronicMonogamyExclusion
    else if parent == .K_plus || parent == .K_minus then .isospinHalfHadronicSemileptonicCompetition
    else .isospinHalfHadronicMonogamyExclusion
  else if channel == .weak && isIsospinHalfWeakParent parent then
    if isNeutralIsovectorPionOnlyOutlet ds then
      if isLightStrangeBaryon parent then .lightBaryonNeutralIsospinOutlet
      else .isospinHalfNeutralOutlet
    else .isospinHalfWeak
  else .unitSeed

/-! ## Light-hadron spanning certificates (ledger enumeration mirror) -/

def deltaPStrongModes : List (List HepDecaySpecies) := [
  [.p, .pi_zero], [.n, .pi_plus]
]

def deltaPPStrongModes : List (List HepDecaySpecies) := [
  [.p, .pi_plus]
]

def rhoZeroStrongModes : List (List HepDecaySpecies) := [
  [.pi_plus, .pi_minus]
]

def lambdaWeakModes : List (List HepDecaySpecies) := [
  [.p, .pi_minus], [.n, .pi_zero]
]

def KplusWeakModes : List (List HepDecaySpecies) := [
  [.pi_plus], [.pi_zero], [.pi_plus, .pi_zero, .pi_zero]
]

def sigmaPlusStrongModes : List (List HepDecaySpecies) := [
  [.p, .pi_zero]
]

def sigmaZeroStrongModes : List (List HepDecaySpecies) := [
  [.lambda, .pi_zero]
]

def sigmaMinusStrongModes : List (List HepDecaySpecies) := [
  [.n, .pi_minus]
]

def xiZeroStrongModes : List (List HepDecaySpecies) := [
  [.lambda, .pi_zero]
]

def xiMinusStrongModes : List (List HepDecaySpecies) := [
  [.lambda, .pi_minus]
]

def upsilonNeutralCascadeModes : List (List HepDecaySpecies) := [
  [.Jpsi, .pi_plus, .pi_minus],
  [.Jpsi, .pi_zero, .pi_zero]
]

theorem strongChannelAllowed_deltaP_modes :
    ∀ ds ∈ deltaPStrongModes, strongChannelAllowed .delta_p ds := by decide

theorem strongChannelAllowed_deltaPP_ppiplus :
    strongChannelAllowed .delta_pp [.p, .pi_plus] := by decide

theorem strongChannelAllowed_rhoZero_pipi :
    strongChannelAllowed .rho_zero [.pi_plus, .pi_minus] := by decide

theorem strongChannelAllowed_rhoZero_pi0pi0_forbidden :
    ¬ strongChannelAllowed .rho_zero [.pi_zero, .pi_zero] := by decide

theorem strongChannelAllowed_sigmaPlus_modes :
    ∀ ds ∈ sigmaPlusStrongModes, strongChannelAllowed .sigma_plus ds := by decide

theorem strongChannelAllowed_sigmaZero_modes :
    ∀ ds ∈ sigmaZeroStrongModes, strongChannelAllowed .sigma_zero ds := by decide

theorem strongChannelAllowed_sigmaMinus_modes :
    ∀ ds ∈ sigmaMinusStrongModes, strongChannelAllowed .sigma_minus ds := by decide

theorem strongChannelAllowed_xiZero_modes :
    ∀ ds ∈ xiZeroStrongModes, strongChannelAllowed .xi_zero ds := by decide

theorem strongChannelAllowed_xiMinus_modes :
    ∀ ds ∈ xiMinusStrongModes, strongChannelAllowed .xi_minus ds := by decide

theorem upsilonNeutralCascade_Jpsi_pipi :
    let ds := [HepDecaySpecies.Jpsi, HepDecaySpecies.pi_plus, HepDecaySpecies.pi_minus]
    ds.head? = some HepDecaySpecies.Jpsi ∧ isNeutralLightCascade ds := by
  decide

theorem upsilonNeutralCascade_Jpsi_pi0pi0 :
    let ds := [HepDecaySpecies.Jpsi, HepDecaySpecies.pi_zero, HepDecaySpecies.pi_zero]
    ds.head? = some HepDecaySpecies.Jpsi ∧ isNeutralLightCascade ds := by
  decide

theorem weakChannelAllowed_lambda_modes :
    ∀ ds ∈ lambdaWeakModes, weakChannelAllowed .lambda ds := by decide

theorem weakChannelAllowed_Kplus_modes :
    ∀ ds ∈ KplusWeakModes, weakChannelAllowed .K_plus ds := by decide

def K0WeakModes : List (List HepDecaySpecies) := [
  [.pi_zero]
]

def KminusWeakModes : List (List HepDecaySpecies) := [
  [.pi_minus], [.pi_zero], [.pi_minus, .pi_zero, .pi_zero]
]

def KplusSemileptonicWeakModes : List (List HepDecaySpecies) := [
  [.mu_plus]
]

def KminusSemileptonicWeakModes : List (List HepDecaySpecies) := [
  [.mu_minus]
]

def phiStrongModes : List (List HepDecaySpecies) := [
  [.K_plus, .K_minus], [.pi_plus, .pi_minus, .pi_zero]
]

def DplusWeakModes : List (List HepDecaySpecies) := [
  [.K_minus, .pi_plus], [.K_minus, .rho_plus],
  [.K0_bar, .omega_meson], [.K0_bar, .rho_zero], [.K0_bar, .rho_plus],
  [.K0, .omega_meson], [.K0, .rho_zero], [.K0, .pi_plus], [.K0, .rho_plus],
  [.K0, .eta],
  [.K_minus, .pi_plus, .pi_zero], [.pi_minus, .pi_plus, .pi_zero],
  [.pi_minus, .pi_zero, .rho_plus], [.K0, .pi_plus, .pi_zero]
]

def D0WeakModes : List (List HepDecaySpecies) := [
  [.K0, .pi_minus], [.K_plus, .pi_minus],
  [.K0_bar, .omega_meson], [.K0_bar, .rho_zero], [.K0_bar, .rho_plus],
  [.K0, .omega_meson], [.K0, .rho_zero],
  [.K0, .rho_plus], [.K0, .eta],
  [.K0, .pi_minus, .pi_zero], [.pi_minus, .pi_plus, .pi_zero],
  [.pi_minus, .pi_zero, .rho_plus], [.K_plus, .pi_minus, .pi_zero]
]

def DplusSemileptonicWeakModes : List (List HepDecaySpecies) := [
  [.mu_plus], [.e_plus]
]

def D0SemileptonicWeakModes : List (List HepDecaySpecies) := [
  [.mu_minus], [.e_minus]
]

def LambdaCSemileptonicWeakModes : List (List HepDecaySpecies) := [
  [.mu_plus], [.e_plus]
]

def DplusFullWeakModes : List (List HepDecaySpecies) :=
  DplusWeakModes ++ DplusSemileptonicWeakModes

def D0FullWeakModes : List (List HepDecaySpecies) :=
  D0WeakModes ++ D0SemileptonicWeakModes

def LambdaCFullWeakModes : List (List HepDecaySpecies) :=
  lambdaCWeakModes ++ LambdaCSemileptonicWeakModes

def BsWeakModes : List (List HepDecaySpecies) := [
  [.Ds_plus, .K_minus], [.phi, .phi]
]

def BplusWeakModes : List (List HepDecaySpecies) := [
  [.D_plus, .K_minus], [.D_plus, .pi_minus], [.D_plus, .K0_bar], [.D_plus, .eta],
  [.D_plus, .pi_zero], [.D_plus, .omega_meson], [.D_plus, .rho_zero],
  [.D0, .pi_plus], [.D0, .rho_plus], [.D0, .K_plus], [.D_plus, .K0],
  [.D_plus, .pi_minus, .pi_zero], [.D0, .pi_plus, .pi_zero]
]

def B0WeakModes : List (List HepDecaySpecies) := [
  [.D0, .K_minus], [.D_plus, .K_minus], [.D0, .pi_minus], [.D_plus, .pi_minus],
  [.D0, .K0_bar], [.D_plus, .K0_bar], [.D0, .eta], [.D_plus, .eta],
  [.D0, .pi_zero], [.D_plus, .pi_zero], [.D0, .omega_meson], [.D_plus, .omega_meson],
  [.D0, .rho_zero], [.D_plus, .rho_zero], [.D0, .K0], [.D0, .pi_plus],
  [.D0, .rho_plus], [.D0, .K_plus], [.D_plus, .K0], [.D0, .pi_plus, .pi_zero]
]

theorem DplusWeakModes_count_fourteen : DplusWeakModes.length = 14 := by decide

theorem D0WeakModes_count_thirteen : D0WeakModes.length = 13 := by decide

theorem DplusSemileptonicWeakModes_count_two : DplusSemileptonicWeakModes.length = 2 := by decide

theorem D0SemileptonicWeakModes_count_two : D0SemileptonicWeakModes.length = 2 := by decide

theorem LambdaCSemileptonicWeakModes_count_two : LambdaCSemileptonicWeakModes.length = 2 := by decide

theorem DplusFullWeakModes_count_sixteen : DplusFullWeakModes.length = 16 := by decide

theorem D0FullWeakModes_count_fifteen : D0FullWeakModes.length = 15 := by decide

theorem LambdaCFullWeakModes_count_eight : LambdaCFullWeakModes.length = 8 := by decide

theorem BsWeakModes_count_two : BsWeakModes.length = 2 := by decide

theorem BplusWeakModes_count_thirteen : BplusWeakModes.length = 13 := by decide

theorem B0WeakModes_count_twenty : B0WeakModes.length = 20 := by decide

theorem weakChannelAllowed_Dplus_modes :
    ∀ ds ∈ DplusWeakModes, weakChannelAllowed .D_plus ds := by decide

theorem weakChannelAllowed_D0_modes :
    ∀ ds ∈ D0WeakModes, weakChannelAllowed .D0 ds := by decide

theorem weakChannelAllowed_Dplus_semileptonic_modes :
    ∀ ds ∈ DplusSemileptonicWeakModes, weakChannelAllowed .D_plus ds := by decide

theorem weakChannelAllowed_D0_semileptonic_modes :
    ∀ ds ∈ D0SemileptonicWeakModes, weakChannelAllowed .D0 ds := by decide

theorem weakChannelAllowed_lambdaC_semileptonic_modes :
    ∀ ds ∈ LambdaCSemileptonicWeakModes, weakChannelAllowed .lambda_c ds := by decide

theorem weakChannelAllowed_Dplus_full_modes :
    ∀ ds ∈ DplusFullWeakModes, weakChannelAllowed .D_plus ds := by decide

theorem weakChannelAllowed_D0_full_modes :
    ∀ ds ∈ D0FullWeakModes, weakChannelAllowed .D0 ds := by decide

theorem weakChannelAllowed_lambdaC_full_modes :
    ∀ ds ∈ LambdaCFullWeakModes, weakChannelAllowed .lambda_c ds := by decide

theorem weakChannelAllowed_Bs_modes :
    ∀ ds ∈ BsWeakModes, weakChannelAllowed .Bs ds := by decide

theorem weakChannelAllowed_Bplus_modes :
    ∀ ds ∈ BplusWeakModes, weakChannelAllowed .B_plus ds := by decide

theorem weakChannelAllowed_B0_modes :
    ∀ ds ∈ B0WeakModes, weakChannelAllowed .B0 ds := by decide

theorem openFlavourContactKind_agrees_legacy_Dplus_Kpi :
    openFlavourContactKind .D_plus .weak [.K_minus, .pi_plus] =
      openFlavourContactKind_legacy .D_plus .weak [.K_minus, .pi_plus] := by decide

theorem openFlavourContactKind_agrees_legacy_Bplus_D0pi :
    openFlavourContactKind .B_plus .weak [.D0, .pi_plus] =
      openFlavourContactKind_legacy .B_plus .weak [.D0, .pi_plus] := by decide

theorem openFlavourContactKind_eq_from_classifyWeakOutlet_on_weak
    (parent : HepDecaySpecies) (ds : List HepDecaySpecies) :
    openFlavourContactKind parent .weak ds =
      openFlavourContactKindFromWeakOutlet parent ds (classifyWeakOutletProperty parent ds) := by
  simp [openFlavourContactKind]

theorem classifyWeakOutlet_Dplus_Kpi :
    classifyWeakOutletProperty .D_plus [.K_minus, .pi_plus] = .charmKaonCabibboExclusion := by
  decide

theorem classifyWeakOutlet_Bplus_D0pi :
    classifyWeakOutletProperty .B_plus [.D0, .pi_plus] = .bottomExternalWeak := by decide

def rhoPlusStrongModes : List (List HepDecaySpecies) := [
  [.pi_plus, .pi_zero]
]

def omegaMesonStrongModes : List (List HepDecaySpecies) := [
  [.pi_plus, .pi_minus, .pi_zero]
]

def isCertifiedStrongDischargeParent (s : HepDecaySpecies) : Bool :=
  s == .phi || s == .rho_zero || s == .rho_plus || s == .omega_meson ||
    s == .delta_p || s == .delta_pp || s == .sigma_plus || s == .sigma_zero ||
    s == .sigma_minus || s == .xi_zero || s == .xi_minus

theorem weakChannelAllowed_K0_modes :
    ∀ ds ∈ K0WeakModes, weakChannelAllowed .K0 ds := by decide

theorem weakChannelAllowed_Kminus_modes :
    ∀ ds ∈ KminusWeakModes, weakChannelAllowed .K_minus ds := by decide

theorem kaonWeakStrangenessDelta_Kplus_piplus :
    let p := speciesLedger .K_plus
    let t := ledgerSum [.pi_plus]
    (ledgerDelta p t).strangeness = -p.strangeness := by decide

theorem kaonWeakStrangenessDelta_Kminus_piminus :
    let p := speciesLedger .K_minus
    let t := ledgerSum [.pi_minus]
    (ledgerDelta p t).strangeness = -p.strangeness := by decide

theorem kaonWeakStrangenessDelta_K0_pi0 :
    let p := speciesLedger .K0
    let t := ledgerSum [.pi_zero]
    (ledgerDelta p t).strangeness = -p.strangeness := by decide

theorem strongChannelAllowed_phi_modes :
    ∀ ds ∈ phiStrongModes, strongChannelAllowed .phi ds := by decide

theorem strongChannelAllowed_rhoPlus_modes :
    ∀ ds ∈ rhoPlusStrongModes, strongChannelAllowed .rho_plus ds := by decide

theorem strongChannelAllowed_omegaMeson_modes :
    ∀ ds ∈ omegaMesonStrongModes, strongChannelAllowed .omega_meson ds := by decide

theorem strongChannelAllowed_deltaP_forbidden_p_piplus :
    ¬ strongChannelAllowed .delta_p [.p, .pi_plus] := by decide

theorem strongChannelAllowed_phi_pipi_forbidden :
    ¬ strongChannelAllowed .phi [.pi_plus, .pi_minus] := by decide

theorem strongChannelAllowed_omega_two_pion_forbidden :
    ¬ strongChannelAllowed .omega_meson [.pi_plus, .pi_minus] := by decide

theorem strongChannelAllowed_rhoPlus_pi0pi0_forbidden :
    ¬ strongChannelAllowed .rho_plus [.pi_zero, .pi_zero] := by decide

theorem weakChannelAllowed_sigma_plus_lambda_piplus :
    weakChannelAllowed .sigma_plus [.lambda, .pi_plus] := by decide

theorem routing_Ds_strong_phi_pole_discharge :
    openFlavourContactKind .Ds_plus .strong [.phi] = .hiddenStrangenessPoleDischarge := by decide

theorem routing_Ds_strong_pipi_ozi_suppressed :
    openFlavourContactKind .Ds_plus .strong [.pi_plus, .pi_zero] = .oziSuppressedStrong := by
  decide

theorem contactWeight_Ds_strong_pipi_ozi_eq_one_tenth :
    openFlavourContactWeight (openFlavourContactKind .Ds_plus .strong [.pi_plus, .pi_zero]) =
      (1 : ℝ) / 10 := by
  rw [routing_Ds_strong_pipi_ozi_suppressed, openFlavourContactWeight_oziSuppressedStrong]

/-! ## Curated routing certificates -/

theorem routing_B0_D0pi0_bottomNeutralSpectator :
    openFlavourContactKind .B0 .weak [.D0, .pi_zero] = .bottomNeutralSpectator := by
  decide

theorem routing_Bplus_D0piplus_externalWeak :
    openFlavourContactKind .B_plus .weak [.D0, .pi_plus] = .bottomExternalWeak := by
  decide

theorem routing_Bplus_DplusKminus_finiteOpenBottom :
    openFlavourContactKind .B_plus .weak [.D_plus, .K_minus] = .finiteOpenBottomCompletion := by
  decide

theorem routing_Dplus_muplus_openCharmSemileptonic :
    openFlavourContactKind .D_plus .weak [.mu_plus] = .openCharmSemileptonicNeutrinoCompletion := by
  decide

theorem contactWeight_Dplus_muplus_eq_two_ninths :
    openFlavourContactWeight (openFlavourContactKind .D_plus .weak [.mu_plus]) =
      (2 : ℝ) / 9 := by
  rw [routing_Dplus_muplus_openCharmSemileptonic,
    openFlavourContactWeight_openCharmSemileptonicNeutrinoCompletion]

theorem routing_D0_muminus_openCharmSemileptonic :
    openFlavourContactKind .D0 .weak [.mu_minus] = .openCharmSemileptonicNeutrinoCompletion := by
  decide

theorem routing_lambda_c_muplus_openCharmSemileptonic :
    openFlavourContactKind .lambda_c .weak [.mu_plus] = .openCharmSemileptonicNeutrinoCompletion := by
  decide

theorem contactWeight_lambda_c_muplus_eq_two_ninths :
    openFlavourContactWeight (openFlavourContactKind .lambda_c .weak [.mu_plus]) =
      (2 : ℝ) / 9 := by
  rw [routing_lambda_c_muplus_openCharmSemileptonic,
    openFlavourContactWeight_openCharmSemileptonicNeutrinoCompletion]

theorem routing_lambda_c_PKpi_semileptonicHadronic :
    openFlavourContactKind .lambda_c .weak [.p, .K_minus, .pi_plus] =
      .charmedBaryonSemileptonicHadronic := by
  decide

theorem routing_lambda_c_PKpi_sibling_semileptonicHadronic :
    openFlavourContactKind .lambda_c .weak [.p, .K_minus, .pi_zero] =
      .charmedBaryonSemileptonicHadronic := by
  decide

theorem routing_Dplus_Kminus_piplus_openCharmMonogamy :
    openFlavourContactKind .D_plus .weak [.K_minus, .pi_plus] = .openCharmHadronicMonogamyExclusion := by
  decide

theorem routing_xi_c_charged_pion_exclusion :
    openFlavourContactKind .xi_c .weak [.lambda_c, .pi_plus] = .doubleMonogamyExclusion := by
  decide

theorem routing_xi_c_sigma_pi0_neutralSpectator :
    openFlavourContactKind .xi_c .weak [.sigma_c, .pi_zero] = .neutralSpectatorComplement := by
  decide

theorem routing_xi_c_lambda_pi0_cascadeLambdaGround :
    openFlavourContactKind .xi_c .weak [.lambda_c, .pi_zero] = .cascadeLambdaGround := by
  decide

theorem routing_Bs_DsK_bottomStrangeSharedPole :
    openFlavourContactKind .Bs .weak [.Ds_plus, .K_minus] = .bottomStrangeDoubleMonogamy := by
  decide

theorem routing_Bs_phi_bottomStrange :
    openFlavourContactKind .Bs .weak [.phi, .phi] = .bottomStrangeDoubleMonogamy := by
  decide

theorem routing_lambda_c_wrong_sign_semileptonicHadronic :
    openFlavourContactKind .lambda_c .weak [.p, .K_plus, .pi_minus] =
      .charmedBaryonSemileptonicHadronic := by
  decide

theorem routing_lambda_piminus_isospinHalfWeak :
    openFlavourContactKind .lambda .weak [.p, .pi_minus] = .isospinHalfWeak := by
  decide

theorem routing_lambda_npi0_lightBaryonNeutralIsospinOutlet :
    openFlavourContactKind .lambda .weak [.n, .pi_zero] = .lightBaryonNeutralIsospinOutlet := by
  decide

theorem routing_Kplus_piplus_semileptonicCompetition :
    openFlavourContactKind .K_plus .weak [.pi_plus] =
      .isospinHalfHadronicSemileptonicCompetition := by
  decide

theorem routing_Kplus_pi0_semileptonicCompetition :
    openFlavourContactKind .K_plus .weak [.pi_zero] =
      .isospinHalfNeutralHadronicSemileptonicCompetition := by decide

theorem routing_Kplus_pipi0pi0_semileptonicCompetition :
    openFlavourContactKind .K_plus .weak [.pi_plus, .pi_zero, .pi_zero] =
      .isospinHalfHadronicSemileptonicCompetition := by decide

theorem routing_Kminus_piminus_semileptonicCompetition :
    openFlavourContactKind .K_minus .weak [.pi_minus] =
      .isospinHalfHadronicSemileptonicCompetition := by
  decide

theorem routing_Kminus_pi0_semileptonicCompetition :
    openFlavourContactKind .K_minus .weak [.pi_zero] =
      .isospinHalfNeutralHadronicSemileptonicCompetition := by decide

theorem routing_Kminus_piminus_pi0pi0_semileptonicCompetition :
    openFlavourContactKind .K_minus .weak [.pi_minus, .pi_zero, .pi_zero] =
      .isospinHalfHadronicSemileptonicCompetition := by decide

theorem routing_K0_pi0_hadronicNeutralMonogamyExclusion :
    openFlavourContactKind .K0 .weak [.pi_zero] =
      .isospinHalfNeutralHadronicMonogamyExclusion := by decide

theorem routing_Kplus_muplus_lightKaonSemileptonic :
    openFlavourContactKind .K_plus .weak [.mu_plus] =
      .lightKaonSemileptonicNeutrinoCompletion := by decide

theorem routing_Kminus_muminus_lightKaonSemileptonic :
    openFlavourContactKind .K_minus .weak [.mu_minus] =
      .lightKaonSemileptonicNeutrinoCompletion := by decide

theorem routing_phi_strong_KK_retention :
    openFlavourContactKind .phi .strong [.K_plus, .K_minus] = .hiddenStrangenessKkRetention := by
  decide

theorem routing_phi_strong_three_pion_leak :
    openFlavourContactKind .phi .strong [.pi_plus, .pi_minus, .pi_zero] =
      .hiddenStrangenessVectorLeak := by decide

theorem contactWeight_phi_KK_retention_eq_twentyone_twentyfive :
    openFlavourContactWeight (openFlavourContactKind .phi .strong [.K_plus, .K_minus]) =
      (21 : ℝ) / 25 := by
  rw [routing_phi_strong_KK_retention, openFlavourContactWeight_hiddenStrangenessKkRetention]

theorem contactWeight_Kplus_muplus_eq_209_over_1800 :
    openFlavourContactWeight (openFlavourContactKind .K_plus .weak [.mu_plus]) =
      (209 : ℝ) / 1800 := by
  rw [routing_Kplus_muplus_lightKaonSemileptonic,
    openFlavourContactWeight_lightKaonSemileptonicNeutrinoCompletion]

theorem routing_rhoPlus_strong_pipi0_unit_seed :
    openFlavourContactKind .rho_plus .strong [.pi_plus, .pi_zero] = .unitSeed := by decide

theorem routing_omega_strong_three_pion_unit_seed :
    openFlavourContactKind .omega_meson .strong [.pi_plus, .pi_minus, .pi_zero] = .unitSeed := by
  decide

theorem contactWeight_Kplus_piplus_eq_30576_over_101250 :
    openFlavourContactWeight (openFlavourContactKind .K_plus .weak [.pi_plus]) =
      (30576 : ℝ) / 101250 := by
  rw [routing_Kplus_piplus_semileptonicCompetition,
    openFlavourContactWeight_isospinHalfHadronicSemileptonicCompetition]

theorem contactWeight_Kplus_pi0_eq_13104_over_101250 :
    openFlavourContactWeight (openFlavourContactKind .K_plus .weak [.pi_zero]) =
      (13104 : ℝ) / 101250 := by
  rw [routing_Kplus_pi0_semileptonicCompetition,
    openFlavourContactWeight_isospinHalfNeutralHadronicSemileptonicCompetition]

theorem contactWeight_Kminus_piminus_eq_30576_over_101250 :
    openFlavourContactWeight (openFlavourContactKind .K_minus .weak [.pi_minus]) =
      (30576 : ℝ) / 101250 := by
  rw [routing_Kminus_piminus_semileptonicCompetition,
    openFlavourContactWeight_isospinHalfHadronicSemileptonicCompetition]

theorem contactWeight_K0_pi0_eq_1008_over_10125 :
    openFlavourContactWeight (openFlavourContactKind .K0 .weak [.pi_zero]) =
      (1008 : ℝ) / 10125 := by
  rw [routing_K0_pi0_hadronicNeutralMonogamyExclusion,
    openFlavourContactWeight_isospinHalfNeutralHadronicMonogamyExclusion]

theorem isospinHalfWeakContact_gt_neutralOutlet :
    isospinHalfNeutralOutletContact < isospinHalfWeakContact := by
  simp [isospinHalfNeutralOutletContact, isospinHalfWeakContact, gamma_eq_2_5]
  norm_num

theorem routing_forall_lambdaWeakModes :
    ∀ ds ∈ lambdaWeakModes,
      openFlavourContactKind .lambda .weak ds =
        (if isNeutralIsovectorPionOnlyOutlet ds then .lightBaryonNeutralIsospinOutlet else .isospinHalfWeak) := by
  decide

theorem routing_forall_KplusWeakModes :
    ∀ ds ∈ KplusWeakModes,
      openFlavourContactKind .K_plus .weak ds =
        (if isNeutralIsovectorPionOnlyOutlet ds then .isospinHalfNeutralHadronicSemileptonicCompetition
         else .isospinHalfHadronicSemileptonicCompetition) := by
  decide

theorem routing_forall_KminusWeakModes :
    ∀ ds ∈ KminusWeakModes,
      openFlavourContactKind .K_minus .weak ds =
        (if isNeutralIsovectorPionOnlyOutlet ds then .isospinHalfNeutralHadronicSemileptonicCompetition
         else .isospinHalfHadronicSemileptonicCompetition) := by
  decide

theorem routing_from_weakChannel_lambda_modes :
    ∀ ds ∈ lambdaWeakModes, weakChannelAllowed .lambda ds →
      openFlavourContactKind .lambda .weak ds =
        (if isNeutralIsovectorPionOnlyOutlet ds then .lightBaryonNeutralIsospinOutlet else .isospinHalfWeak) := by
  intro ds hmem hallowed
  exact routing_forall_lambdaWeakModes ds hmem

theorem routing_from_weakChannel_Kplus_modes :
    ∀ ds ∈ KplusWeakModes, weakChannelAllowed .K_plus ds →
      openFlavourContactKind .K_plus .weak ds =
        (if isNeutralIsovectorPionOnlyOutlet ds then .isospinHalfNeutralHadronicSemileptonicCompetition
         else .isospinHalfHadronicSemileptonicCompetition) := by
  intro ds hmem hallowed
  exact routing_forall_KplusWeakModes ds hmem

theorem routing_from_weakChannel_Kminus_modes :
    ∀ ds ∈ KminusWeakModes, weakChannelAllowed .K_minus ds →
      openFlavourContactKind .K_minus .weak ds =
        (if isNeutralIsovectorPionOnlyOutlet ds then .isospinHalfNeutralHadronicSemileptonicCompetition
         else .isospinHalfHadronicSemileptonicCompetition) := by
  intro ds hmem hallowed
  exact routing_forall_KminusWeakModes ds hmem

theorem routing_from_weakChannel_K0_modes :
    ∀ ds ∈ K0WeakModes, weakChannelAllowed .K0 ds →
      openFlavourContactKind .K0 .weak ds = .isospinHalfNeutralHadronicMonogamyExclusion := by
  rintro ds hmem _
  simp only [K0WeakModes, List.mem_singleton] at hmem
  subst hmem
  exact routing_K0_pi0_hadronicNeutralMonogamyExclusion

theorem contactWeight_lambda_piminus_eq_seven_fifths :
    openFlavourContactWeight (openFlavourContactKind .lambda .weak [.p, .pi_minus]) =
      (7 : ℝ) / 5 := by
  rw [routing_lambda_piminus_isospinHalfWeak, openFlavourContactWeight_isospinHalfWeak]

theorem contactWeight_lambda_npi0_eq_eighteen_twenty_thirds :
    openFlavourContactWeight (openFlavourContactKind .lambda .weak [.n, .pi_zero]) =
      (18 : ℝ) / 23 := by
  rw [routing_lambda_npi0_lightBaryonNeutralIsospinOutlet,
    openFlavourContactWeight_lightBaryonNeutralIsospinOutlet]

theorem routing_from_weakChannel_B0_D0pi0 :
    weakChannelAllowed .B0 [.D0, .pi_zero] →
      openFlavourContactKind .B0 .weak [.D0, .pi_zero] = .bottomNeutralSpectator := by
  intro _; exact routing_B0_D0pi0_bottomNeutralSpectator

theorem routing_from_weakChannel_lambda_c_PKpi :
    weakChannelAllowed .lambda_c [.p, .K_minus, .pi_plus] →
      openFlavourContactKind .lambda_c .weak [.p, .K_minus, .pi_plus] =
        .charmedBaryonSemileptonicHadronic := by
  intro _; exact routing_lambda_c_PKpi_semileptonicHadronic

theorem contactWeight_B0_D0pi0_eq_three_halves :
    openFlavourContactWeight (openFlavourContactKind .B0 .weak [.D0, .pi_zero]) =
      (3 : ℝ) / 2 := by
  rw [routing_B0_D0pi0_bottomNeutralSpectator, openFlavourContactWeight_bottomNeutralSpectator]

theorem routing_Kplus_mu_lightKaonSemileptonic :
    openFlavourContactKind .K_plus .weak [.mu_plus] = .lightKaonSemileptonicNeutrinoCompletion := by
  decide

theorem contactWeight_Kplus_mu_eq_209_over_1800 :
    openFlavourContactWeight (openFlavourContactKind .K_plus .weak [.mu_plus]) =
      (209 : ℝ) / 1800 := by
  rw [routing_Kplus_mu_lightKaonSemileptonic, openFlavourContactWeight_lightKaonSemileptonicNeutrinoCompletion]

theorem contactWeight_Bplus_D0piplus_eq_seven_halves :
    openFlavourContactWeight (openFlavourContactKind .B_plus .weak [.D0, .pi_plus]) = (7 : ℝ) / 2 := by
  rw [routing_Bplus_D0piplus_externalWeak, openFlavourContactWeight_bottomExternalWeak]

theorem contactWeight_Bplus_DplusKminus_eq_one_fifteenth :
    openFlavourContactWeight (openFlavourContactKind .B_plus .weak [.D_plus, .K_minus]) =
      (1 : ℝ) / 15 := by
  rw [routing_Bplus_DplusKminus_finiteOpenBottom, openFlavourContactWeight_finiteOpenBottomCompletion]

theorem contactWeight_lambda_c_PKpi_eq_eightyfour_elevenths :
    openFlavourContactWeight (openFlavourContactKind .lambda_c .weak [.p, .K_minus, .pi_plus]) =
      (84 : ℝ) / 11 := by
  rw [routing_lambda_c_PKpi_semileptonicHadronic, openFlavourContactWeight_charmedBaryonSemileptonicHadronic]

theorem contactWeight_lambda_c_PKpi_sibling_eq_eightyfour_elevenths :
    openFlavourContactWeight (openFlavourContactKind .lambda_c .weak [.p, .K_minus, .pi_zero]) =
      (84 : ℝ) / 11 := by
  rw [routing_lambda_c_PKpi_sibling_semileptonicHadronic, openFlavourContactWeight_charmedBaryonSemileptonicHadronic]

theorem contactWeight_lambda_c_wrong_sign_eq_eightyfour_elevenths :
    openFlavourContactWeight (openFlavourContactKind .lambda_c .weak [.p, .K_plus, .pi_minus]) =
      (84 : ℝ) / 11 := by
  rw [routing_lambda_c_wrong_sign_semileptonicHadronic, openFlavourContactWeight_charmedBaryonSemileptonicHadronic]

theorem contactWeight_xi_c_charged_pion_eq_twentyone_twentyfive :
    openFlavourContactWeight (openFlavourContactKind .xi_c .weak [.lambda_c, .pi_plus]) =
      (21 : ℝ) / 25 := by
  rw [routing_xi_c_charged_pion_exclusion, openFlavourContactWeight_doubleMonogamyExclusion]

theorem contactWeight_xi_c_sigma_pi0_eq_five_thirds :
    openFlavourContactWeight (openFlavourContactKind .xi_c .weak [.sigma_c, .pi_zero]) =
      (5 : ℝ) / 3 := by
  rw [routing_xi_c_sigma_pi0_neutralSpectator, openFlavourContactWeight_neutralSpectatorComplement]

theorem contactWeight_xi_c_lambda_pi0_eq_163_over_sixty :
    openFlavourContactWeight (openFlavourContactKind .xi_c .weak [.lambda_c, .pi_zero]) =
      (163 : ℝ) / 60 := by
  rw [routing_xi_c_lambda_pi0_cascadeLambdaGround, openFlavourContactWeight_cascadeLambdaGround]

theorem contactWeight_Ds_strong_phi_eq_eight_fifths :
    openFlavourContactWeight (openFlavourContactKind .Ds_plus .strong [.phi]) =
      (8 : ℝ) / 5 := by
  rw [routing_Ds_strong_phi_pole_discharge, openFlavourContactWeight_hiddenStrangenessPoleDischarge]

theorem contactWeight_Bs_DsK_eq_twentyfive_fourths :
    openFlavourContactWeight (openFlavourContactKind .Bs .weak [.Ds_plus, .K_minus]) =
      (25 : ℝ) / 4 := by
  rw [routing_Bs_DsK_bottomStrangeSharedPole, openFlavourContactWeight_bottomStrangeDoubleMonogamy]

theorem singleWChargeLoad_B0_D0pi0 :
    SingleWChargeLoad (speciesLedger .B0) (ledgerSum [.D0, .pi_zero]) := by
  simp [SingleWChargeLoad, speciesLedger, ledgerSum, HadronPatchLedger.add, HadronPatchLedger.zero]

#check contactWeight_B0_D0pi0_eq_three_halves
#check contactWeight_lambda_c_PKpi_eq_eightyfour_elevenths
#check contactWeight_xi_c_charged_pion_eq_twentyone_twentyfive
theorem routing_Dplus_Kminus_rhoplus_vectorLeak :
    openFlavourContactKind .D_plus .weak [.K_minus, .rho_plus] = .hiddenStrangenessVectorLeak := by
  decide

theorem contactWeight_Dplus_Kminus_rhoplus_eq_four_twentyfive :
    openFlavourContactWeight (openFlavourContactKind .D_plus .weak [.K_minus, .rho_plus]) =
      (4 : ℝ) / 25 := by
  rw [routing_Dplus_Kminus_rhoplus_vectorLeak, openFlavourContactWeight_hiddenStrangenessVectorLeak]

#check routing_Dplus_Kminus_piplus_openCharmMonogamy

/-! ## Gauge-sector curvature routing on decay channels -/

noncomputable def hepDecayChannelCurvatureReadout
    (parent : HepDecaySpecies) (ch : HepDecayChannel) (ds : List HepDecaySpecies) : ℝ :=
  match ch with
  | .strong => strongGaugeCurvatureReadout
  | .electromagnetic => emGaugeCurvatureReadout
  | .weak | .weak_hadron =>
      if isSemileptonicWeakOutlet parent ds then weakGaugeSemileptonicCurvatureReadout
      else weakGaugeHadronicCurvatureReadout
  | .stable => 1

/-- Gauge curvature dress on partial widths (outlet-aware; mirrors Python width kernel). -/
noncomputable def hepDecayGaugeCurvatureWidthFactor
    (parent : HepDecaySpecies) (ch : HepDecayChannel) (ds : List HepDecaySpecies) : ℝ :=
  match ch with
  | .weak | .weak_hadron =>
      match classifyWeakOutletProperty parent ds with
      | .bottomStrangeHiddenPhi | .bottomStrangeOpenCharm => weakGaugeHadronicCurvatureReadout
      | .semileptonicVisibleLepton => weakGaugeSemileptonicCurvatureReadout
      | _ => weakGaugeHadronicCurvatureReadout
  | .strong => strongGaugeCurvatureReadout
  | .electromagnetic => emGaugeCurvatureReadout
  | .stable => 1

theorem hepDecayGaugeCurvatureWidthFactor_Bplus_D0piplus_eq_one_seventyone_over_13696 :
    hepDecayGaugeCurvatureWidthFactor .B_plus .weak [.D0, .pi_plus] = (171 : ℝ) / 13696 := by
  unfold hepDecayGaugeCurvatureWidthFactor
  simp only [classifyWeakOutlet_Bplus_D0pi]
  exact weakGaugeHadronicCurvatureReadout_eq_one_seventyone_over_13696

theorem hepDecayGaugeCurvatureWidthFactor_Dplus_muplus_eq_four_thirtyseven_over_12840 :
    hepDecayGaugeCurvatureWidthFactor .D_plus .weak [.mu_plus] = (437 : ℝ) / 12840 := by
  have hout : classifyWeakOutletProperty .D_plus [.mu_plus] = .semileptonicVisibleLepton := by
    decide
  unfold hepDecayGaugeCurvatureWidthFactor
  simp only [hout]
  exact weakGaugeSemileptonicCurvatureReadout_eq_four_thirtyseven_over_12840

theorem hepDecayGaugeCurvatureWidthFactor_phi_KK_eq_fourteen_over_321 :
    hepDecayGaugeCurvatureWidthFactor .phi .strong [.K_plus, .K_minus] = (14 : ℝ) / 321 := by
  unfold hepDecayGaugeCurvatureWidthFactor
  rw [strongGaugeCurvatureReadout_eq_fourteen_over_321]

theorem hepDecayChannelCurvatureReadout_phi_KK_eq_fourteen_over_321 :
    hepDecayChannelCurvatureReadout .phi .strong [.K_plus, .K_minus] = (14 : ℝ) / 321 := by
  unfold hepDecayChannelCurvatureReadout
  rw [strongGaugeCurvatureReadout_eq_fourteen_over_321]

#check hepDecayGaugeCurvatureWidthFactor_Bplus_D0piplus_eq_one_seventyone_over_13696

end Hqiv.Physics
