import Mathlib

/-!
# Blum's speedup theorem: the construction

We work in the concrete model of computation given by Mathlib's `Nat.Partrec.Code`, whose
step-bounded evaluator is `Nat.Partrec.Code.evaln`.  The running time of a program `c` on an
input `n` is the least step bound for which `evaln` returns an answer (`CS.steps`).

This file contains the construction of a total computable function `f` with the property that
every program for `f` can be sped up (by a prescribed computable monotone factor `r`) by another
program for `f`, almost everywhere.  The final statement is assembled in `RequestProject.Main`.
-/

set_option autoImplicit false

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The running time of the program `c` on input `n`: the least step bound at which the
step-bounded evaluator `evaln` produces an output (`0` if the program diverges). -/
noncomputable def steps (c : Code) (n : ℕ) : ℕ := sInf {k | (evaln k c n).isSome = true}

/-- The family of programs derived from a "self-referential" code `c`: `fam c k t` is the
program computing the `(k, t)`-th member of the family coded by `c`. -/
def fam (c : Code) (k t : ℕ) : Code := c.curry (Nat.pair k t)

/-- All members of the family at level `k` with table index `≤ m` halt on input `m` within
`B` steps. -/
def Halts (c : Code) (k m B : ℕ) : Prop :=
  ∀ t ≤ m, (evaln B (fam c k t) m).isSome = true

instance instDecidableHalts (c : Code) (k m B : ℕ) : Decidable (Halts c k m B) := by
  unfold Halts; infer_instance

/-- The least uniform step bound for the level-`k` family members on input `m`. -/
noncomputable def Mc (c : Code) (k m : ℕ) : ℕ := sInf {B | Halts c k m B}

section Canonical

variable (r : ℕ → ℕ)

/-- The budget granted to program `e` at stage `m`. -/
noncomputable def bud (c : Code) (e m : ℕ) : ℕ := r (Mc c (e + 1) m) + 1

/-- Program `e` *acts* at stage `n` if `n` is the first stage after `e` at which `e` halts
within its budget. -/
def acts (c : Code) (e n : ℕ) : Prop :=
  e < n ∧ (evaln (bud r c e n) (Denumerable.ofNat Code e) n).isSome = true ∧
    ∀ m < n, e < m → (evaln (bud r c e m) (Denumerable.ofNat Code e) m).isSome ≠ true

/-- The value output by program `e` at stage `n` (within its budget). -/
noncomputable def outv (c : Code) (e n : ℕ) : ℕ :=
  ((evaln (bud r c e n) (Denumerable.ofNat Code e) n)).getD 0

/-- The diagonal value at stage `n` for the level-`k` member: the least value different
from all values produced by the programs `e ≥ k` acting at stage `n`. -/
noncomputable def diag (c : Code) (k n : ℕ) : ℕ :=
  sInf {v | ∀ e, k ≤ e → e < n → acts r c e n → outv r c e n ≠ v}

/-- The `(k, t)`-th member of the family: the finite table `t` overrides the diagonal values. -/
noncomputable def Fval (c : Code) (k t n : ℕ) : ℕ :=
  if n < (Denumerable.ofNat (List ℕ) t).length then (Denumerable.ofNat (List ℕ) t).getD n 0
  else diag r c k n

end Canonical

section Effective

variable (cr : Code)

/-- Evaluation of the speedup factor `r` (coded by `cr`) inside the construction, using the
second component of the global budget `B`. -/
def rB (B x : ℕ) : ℕ := ((evaln B.unpair.2 cr x)).getD 0

/-- Effective version of `Mc`, searched below the first component of the global budget `B`. -/
def McB (c : Code) (B k m : ℕ) : ℕ :=
  (List.range (B.unpair.1 + 1)).findIdx (fun B' => decide (Halts c k m B'))

/-- Effective version of `bud`. -/
def budB (c : Code) (B e m : ℕ) : ℕ := rB cr B (McB c B (e + 1) m) + 1

/-- Effective version of `acts`. -/
def actsB (c : Code) (B e n : ℕ) : Prop :=
  e < n ∧ (evaln (budB cr c B e n) (Denumerable.ofNat Code e) n).isSome = true ∧
    ∀ m < n, e < m → (evaln (budB cr c B e m) (Denumerable.ofNat Code e) m).isSome ≠ true

instance instDecidableActsB (c : Code) (B e n : ℕ) : Decidable (actsB cr c B e n) := by
  unfold actsB; infer_instance

/-- Effective version of `outv`. -/
def outvB (c : Code) (B e n : ℕ) : ℕ :=
  ((evaln (budB cr c B e n) (Denumerable.ofNat Code e) n)).getD 0

/-- Effective version of `diag`. -/
def diagB (c : Code) (B k n : ℕ) : ℕ :=
  (List.range (n + 1)).findIdx
    (fun v => decide (∀ e < n, k ≤ e → actsB cr c B e n → outvB cr c B e n ≠ v))

/-- Effective version of `Fval`. -/
def FvalB (c : Code) (B k t n : ℕ) : ℕ :=
  if n < (Denumerable.ofNat (List ℕ) t).length then (Denumerable.ofNat (List ℕ) t).getD n 0
  else diagB cr c B k n

/-- The property required of the global budget `B` at stage `(k, n)`: all *higher level* family
members halt on all inputs `≤ n` within `B.unpair.1` steps, and the speedup factor `r` can be
evaluated on all inputs `≤ B.unpair.1` within `B.unpair.2` steps. -/
def Wprop (c : Code) (k n B : ℕ) : Prop :=
  (∀ k' ≤ n, k < k' → ∀ t ≤ n, ∀ m ≤ n, (evaln B.unpair.1 (fam c k' t) m).isSome = true) ∧
    (∀ x ≤ B.unpair.1, (evaln B.unpair.2 cr x).isSome = true)

instance instDecidableWprop (c : Code) (k n B : ℕ) : Decidable (Wprop cr c k n B) := by
  unfold Wprop; infer_instance

/-- The partial function computed by the self-referential code. -/
def Psi (c : Code) (x : ℕ) : Part ℕ :=
  (Nat.rfind fun B => Part.some (decide (Wprop cr c x.unpair.1.unpair.1 x.unpair.2 B))).map
    fun B => FvalB cr c B x.unpair.1.unpair.1 x.unpair.1.unpair.2 x.unpair.2

end Effective

end CS

import Mathlib
/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true

set_option grind.warning false

/-!
## Blum's speedup theorem

We work in the concrete model of computation given by Mathlib's `Nat.Partrec.Code`, whose
step-bounded evaluator is `Nat.Partrec.Code.evaln`.  The running time of a program `c` on an
input `n` is the least step bound for which `evaln` returns an answer.

The theorem proved below (`CS.blum_speedup`) says: for every computable monotone `r` there is a
total computable function `f` such that *every* program computing `f` can be sped up by the
factor `r`, almost everywhere.  In particular `f` has no fastest algorithm
(`CS.no_fastest_algorithm`).
-/

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The running time of the program `c` on input `n`: the least step bound at which the
step-bounded evaluator `evaln` produces an output (`0` if the program diverges). -/
noncomputable def steps (c : Code) (n : ℕ) : ℕ := sInf {k | (evaln k c n).isSome = true}

/-- The family of programs derived from a "self-referential" code `c`: `fam c k t` is the
program computing the `(k, t)`-th member of the family coded by `c`. -/
def fam (c : Code) (k t : ℕ) : Code := c.curry (Nat.pair k t)

/-- All members of the family at level `k` with table index `≤ m` halt on input `m` within
`B` steps. -/
def Halts (c : Code) (k m B : ℕ) : Prop :=
  ∀ t ≤ m, (evaln B (fam c k t) m).isSome = true

instance (c : Code) (k m B : ℕ) : Decidable (Halts c k m B) := by
  unfold Halts; infer_instance

/-- The least uniform step bound for the level-`k` family members on input `m`. -/
noncomputable def Mc (c : Code) (k m : ℕ) : ℕ := sInf {B | Halts c k m B}

section Canonical

variable (r : ℕ → ℕ)

/-- The budget granted to program `e` at stage `m`. -/
noncomputable def bud (c : Code) (e m : ℕ) : ℕ := r (Mc c (e + 1) m) + 1

/-- Program `e` *acts* at stage `n` if `n` is the first stage after `e` at which `e` halts
within its budget. -/
def acts (c : Code) (e n : ℕ) : Prop :=
  e < n ∧ (evaln (bud r c e n) (Denumerable.ofNat Code e) n).isSome = true ∧
    ∀ m, e < m → m < n → (evaln (bud r c e m) (Denumerable.ofNat Code e) m).isSome ≠ true

/-- The value output by program `e` at stage `n` (within its budget). -/
noncomputable def outv (c : Code) (e n : ℕ) : ℕ :=
  ((evaln (bud r c e n) (Denumerable.ofNat Code e) n)).getD 0

/-- The diagonal value at stage `n` for the level-`k` member: the least value `≤ n` different
from all values produced by the programs `e ≥ k` acting at stage `n`. -/
noncomputable def diag (c : Code) (k n : ℕ) : ℕ :=
  sInf {v | ∀ e, k ≤ e → e < n → acts r c e n → outv r c e n ≠ v}

/-- The `(k, t)`-th member of the family: the finite table `t` overrides the diagonal values. -/
noncomputable def Fval (c : Code) (k t n : ℕ) : ℕ :=
  if n < (Denumerable.ofNat (List ℕ) t).length then (Denumerable.ofNat (List ℕ) t).getD n 0
  else diag r c k n

end Canonical

section Effective

variable (cr : Code)

/-- Evaluation of the speedup factor `r` (coded by `cr`) inside the construction, using the
second component of the global budget `B`. -/
def rB (B x : ℕ) : ℕ := ((evaln B.unpair.2 cr x)).getD 0

/-- Effective version of `Mc`, searched below the first component of the global budget `B`. -/
def McB (c : Code) (B k m : ℕ) : ℕ :=
  (List.range (B.unpair.1 + 1)).findIdx (fun B' => decide (Halts c k m B'))

/-- Effective version of `bud`. -/
def budB (c : Code) (B e m : ℕ) : ℕ := rB cr B (McB c B (e + 1) m) + 1

/-- Effective version of `acts`. -/
def actsB (c : Code) (B e n : ℕ) : Prop :=
  e < n ∧ (evaln (budB cr c B e n) (Denumerable.ofNat Code e) n).isSome = true ∧
    ∀ m, e < m → m < n → (evaln (budB cr c B e m) (Denumerable.ofNat Code e) m).isSome ≠ true

instance (c : Code) (B e n : ℕ) : Decidable (actsB cr c B e n) := by
  unfold actsB; infer_instance

/-- Effective version of `outv`. -/
def outvB (c : Code) (B e n : ℕ) : ℕ :=
  ((evaln (budB cr c B e n) (Denumerable.ofNat Code e) n)).getD 0

/-- Effective version of `diag`. -/
def diagB (c : Code) (B k n : ℕ) : ℕ :=
  (List.range (n + 1)).findIdx
    (fun v => decide (∀ e < n, k ≤ e → actsB cr c B e n → outvB cr c B e n ≠ v))

/-- Effective version of `Fval`. -/
def FvalB (c : Code) (B k t n : ℕ) : ℕ :=
  if n < (Denumerable.ofNat (List ℕ) t).length then (Denumerable.ofNat (List ℕ) t).getD n 0
  else diagB cr c B k n

/-- The property of the global budget `B` used at stage `(k, n)`: all *higher level* family
members halt on all inputs `≤ n` within `B.unpair.1` steps, and the speedup factor `r` can be
evaluated on all inputs `≤ B.unpair.1` within `B.unpair.2` steps. -/
def Wprop (c : Code) (k n B : ℕ) : Prop :=
  (∀ k' ≤ n, k < k' → ∀ t ≤ n, ∀ m ≤ n, (evaln B.unpair.1 (fam c k' t) m).isSome = true) ∧
    (∀ x ≤ B.unpair.1, (evaln B.unpair.2 cr x).isSome = true)

instance (c : Code) (k n B : ℕ) : Decidable (Wprop c k n B) := by
  unfold Wprop; infer_instance

/-- The partial function that the self-referential code will compute. -/
def Psi (c : Code) (x : ℕ) : Part ℕ :=
  (Nat.rfind fun B => Part.some (decide (Wprop cr c x.unpair.1.unpair.1 x.unpair.2 B))).map
    fun B => FvalB cr c B x.unpair.1.unpair.1 x.unpair.1.unpair.2 x.unpair.2

end Effective

end CS

