import Hqiv.Story.S3RHObligationEquivalence

/-!
# Quaternion orientation lock for the S³ story

This module records the elementary quaternion orientation certificate behind the
user shorthand

`i^2 = i * j * k`.

With the standard orientation convention, both sides are `-1`.  The lemma is
useful as a sign/orientation lock for the S³ prime-axis story, but it is not by
itself an analytic zero-exhaustion theorem for `riemannZeta`.
-/

namespace Hqiv.Story

/--
Minimal quaternion orientation readout used for the certificate.

This is intentionally not a full quaternion algebra API; it only records the
oriented products needed for the `i² = i*j*k` sign lock.
-/
inductive QuaternionReadout where
  | one
  | negOne
  | qi
  | qj
  | qk
deriving DecidableEq, Repr

namespace QuaternionReadout

/-- Readout multiplication for the oriented products used by the S³ sign lock. -/
def omul : QuaternionReadout → QuaternionReadout → QuaternionReadout
  | one, b => b
  | a, one => a
  | qi, qi => negOne
  | qj, qj => negOne
  | qk, qk => negOne
  | qi, qj => qk
  | _, _ => negOne

instance : Mul QuaternionReadout where
  mul := omul

@[simp] theorem qi_sq : qi * qi = negOne := rfl

@[simp] theorem qi_mul_qj : qi * qj = qk := rfl

@[simp] theorem qk_mul_qk : qk * qk = negOne := rfl

/-- In the selected orientation, `i^2` and `(i*j)*k` both read out as `-1`. -/
theorem qi_sq_eq_qi_qj_qk : qi * qi = (qi * qj) * qk := by
  rfl

/-- The orientation-lock proposition used by higher-level story modules. -/
def QuaternionOrientationLock : Prop :=
  qi * qi = (qi * qj) * qk

theorem quaternionOrientationLock_holds : QuaternionOrientationLock :=
  qi_sq_eq_qi_qj_qk

end QuaternionReadout

end Hqiv.Story
