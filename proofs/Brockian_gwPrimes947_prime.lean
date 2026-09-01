/-
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires the `import` lines to precede every command, including module
-- docstrings, so the header above is repeated verbatim as a module docstring below.)

import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

`Brockian.GoldbachWheelK2_947` extends the `GoldbachWheelK2` family to the wheel
modulus `947`: every even number `n` with `4 ≤ n ≤ 2 * 947 = 1894` is a sum of two
primes (`K = 2` summands).

Mathlib contains no Goldbach-type theorem to appeal to (the Goldbach conjecture is
open), so the finite range covered by this wheel is verified by an explicit
certificate:

* `gwPrimes947` is the list of all primes below `1894`; each entry is checked with
  the `Nat.Prime` extension of `norm_num` in `gwPrimes947_prime`.
* `gwWit947 i` is the least prime `p` for which `(4 + 2 * i) - p` is prime; the
  data is stored in `gwWitChunks947`.
* `gwCert947` checks, by kernel evaluation (`decide`), that for every `i < 946`
  both `gwWit947 i` and `4 + 2 * i - gwWit947 i` occur in `gwPrimes947`.
-/

set_option maxHeartbeats 4000000
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false

namespace Brockian

/-- All prime numbers below `2 * 947 = 1894`. -/
def gwPrimes947 : List Nat :=
[
  2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
  97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
  193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293,
  307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419,
  421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541,
  547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653,
  659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787,
  797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919,
  929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033,
  1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129,
  1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249,
  1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367,
  1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453, 1459, 1471, 1481,
  1483, 1487, 1489, 1493, 1499, 1511, 1523, 1531, 1543, 1549, 1553, 1559, 1567, 1571, 1579,
  1583, 1597, 1601, 1607, 1609, 1613, 1619, 1621, 1627, 1637, 1657, 1663, 1667, 1669, 1693,
  1697, 1699, 1709, 1721, 1723, 1733, 1741, 1747, 1753, 1759, 1777, 1783, 1787, 1789, 1801,
  1811, 1823, 1831, 1847, 1861, 1867, 1871, 1873, 1877, 1879, 1889
]

/-- Every entry of `gwPrimes947` is prime. -/
theorem gwPrimes947_prime : ∀ p ∈ gwPrimes947, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

/-- Witness data for the Goldbach wheel of modulus `947`, split into blocks of `100`.

Reading the blocks in order, the entry at position `i` is the least prime `p` such
that `(4 + 2 * i) - p` is prime as well.  The `946` entries cover every even number
`4, 6, …, 2 * 947 = 1894`. -/
def gwWitChunks947 : List (List Nat) :=
[
  [
   2, 3, 3, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3,
   5, 7, 3, 5, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11,
   13, 19, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3,
   5, 7, 11, 11, 3, 3, 5, 3, 3 ],
  [
   5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 13, 3, 5, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 5, 7,
   3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 31, 3, 5, 3, 3,
   5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 3, 5, 7, 29, 11, 3, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7,
   3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5 ],
  [
   3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3,
   5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 3, 5, 7, 31, 3, 5, 3, 5, 7, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19,
   11, 13, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 3, 5, 7, 3, 5, 7, 47, 11, 3, 5, 7, 3, 5, 7, 3, 3,
   5, 7, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3 ],
  [
   3, 5, 7, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 3, 5, 7, 23, 11, 3, 3, 5, 3, 5, 7, 3, 5, 7,
   3, 3, 5, 7, 11, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 7,
   17, 11, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5, 7, 3, 5, 3, 5, 7, 13, 3, 5,
   3, 5, 7, 13, 11, 13, 19, 3, 5, 7, 23, 11, 3, 5 ],
  [
   7, 19, 11, 13, 3, 3, 5, 7, 11, 11, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 11, 13, 31, 3,
   5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5, 3, 3, 5, 3, 5, 7, 13, 11, 13, 19, 17, 19, 31, 3,
   5, 3, 5, 7, 13, 3, 5, 7, 17, 11, 3, 5, 7, 19, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 43, 11, 13,
   31, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5, 7, 73, 3, 5, 7, 3, 5 ],
  [
   7, 23, 11, 13, 3, 5, 3, 5, 7, 3, 3, 5, 7, 11, 11, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 3, 5, 7,
   11, 11, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 3, 5,
   7, 31, 3, 5, 7, 3, 5, 7, 3, 5, 7, 29, 11, 13, 41, 17, 19, 41, 23, 3, 3, 5, 7, 11, 11, 3, 5,
   7, 19, 3, 5, 7, 17, 11, 3, 5, 7, 3, 5, 7, 3, 5, 7, 31 ],
  [
   3, 5, 7, 17, 11, 13, 3, 5, 3, 5, 7, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 3, 5, 7, 29,
   11, 3, 5, 7, 19, 11, 13, 37, 17, 19, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 3, 3, 5, 3, 5, 7,
   13, 11, 13, 3, 3, 5, 7, 3, 5, 7, 17, 11, 13, 23, 17, 19, 29, 23, 31, 47, 29, 31, 41, 41, 3,
   5, 7, 3, 5, 7, 3, 5, 7, 61, 3, 5, 7, 17, 11, 13, 23, 17, 19, 3 ],
  [
   5, 7, 41, 11, 3, 5, 7, 19, 11, 13, 43, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5, 3, 3, 5, 7,
   3, 5, 7, 17, 11, 13, 3, 5, 7, 29, 11, 3, 3, 5, 3, 3, 5, 3, 5, 7, 3, 5, 7, 19, 11, 13, 3, 5,
   7, 31, 11, 13, 3, 5, 7, 43, 3, 5, 7, 17, 11, 13, 3, 5, 7, 3, 5, 3, 5, 7, 3, 5, 7, 19, 3, 5,
   3, 5, 7, 13, 3, 5, 3, 5, 7, 13, 11, 13, 19, 3, 5 ],
  [
   3, 5, 7, 3, 3, 5, 3, 5, 7, 3, 3, 5, 7, 3, 5, 7, 17, 11, 3, 5, 7, 19, 11, 13, 31, 17, 19, 31,
   3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13, 17, 17, 19, 23, 23, 31, 3, 5, 3, 3, 5, 7, 11, 11, 3,
   5, 7, 19, 11, 13, 3, 3, 5, 7, 11, 11, 3, 5, 7, 19, 3, 5, 7, 3, 5, 7, 3, 5, 7, 3, 5, 7, 47,
   11, 13, 41, 17, 19, 3, 5, 7, 3, 5, 3, 3, 5, 7, 11, 11, 13 ],
  [
   3, 5, 7, 23, 11, 3, 5, 7, 19, 11, 13, 3, 5, 7, 31, 3, 5, 7, 17, 11, 13, 23, 17, 3, 5, 7, 67,
   11, 13, 31, 3, 5, 7, 3, 5, 3, 3, 5, 3, 3, 5, 7, 11, 11, 3, 5 ]
]

/-- The witness prime recorded for the even number `4 + 2 * i`. -/
def gwWit947 (i : Nat) : Nat :=
  (gwWitChunks947.getD (i / 100) []).getD (i % 100) 0

set_option maxRecDepth 40000 in
theorem gwCert947_block0 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (0 + r) ∈ gwPrimes947 ∧
      4 + 2 * (0 + r) - gwWit947 (0 + r) ∈ gwPrimes947 ∧
      gwWit947 (0 + r) ≤ 4 + 2 * (0 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block1 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (100 + r) ∈ gwPrimes947 ∧
      4 + 2 * (100 + r) - gwWit947 (100 + r) ∈ gwPrimes947 ∧
      gwWit947 (100 + r) ≤ 4 + 2 * (100 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block2 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (200 + r) ∈ gwPrimes947 ∧
      4 + 2 * (200 + r) - gwWit947 (200 + r) ∈ gwPrimes947 ∧
      gwWit947 (200 + r) ≤ 4 + 2 * (200 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block3 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (300 + r) ∈ gwPrimes947 ∧
      4 + 2 * (300 + r) - gwWit947 (300 + r) ∈ gwPrimes947 ∧
      gwWit947 (300 + r) ≤ 4 + 2 * (300 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block4 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (400 + r) ∈ gwPrimes947 ∧
      4 + 2 * (400 + r) - gwWit947 (400 + r) ∈ gwPrimes947 ∧
      gwWit947 (400 + r) ≤ 4 + 2 * (400 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block5 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (500 + r) ∈ gwPrimes947 ∧
      4 + 2 * (500 + r) - gwWit947 (500 + r) ∈ gwPrimes947 ∧
      gwWit947 (500 + r) ≤ 4 + 2 * (500 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block6 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (600 + r) ∈ gwPrimes947 ∧
      4 + 2 * (600 + r) - gwWit947 (600 + r) ∈ gwPrimes947 ∧
      gwWit947 (600 + r) ≤ 4 + 2 * (600 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block7 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (700 + r) ∈ gwPrimes947 ∧
      4 + 2 * (700 + r) - gwWit947 (700 + r) ∈ gwPrimes947 ∧
      gwWit947 (700 + r) ≤ 4 + 2 * (700 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block8 :
    ∀ r ∈ Finset.range 100,
      gwWit947 (800 + r) ∈ gwPrimes947 ∧
      4 + 2 * (800 + r) - gwWit947 (800 + r) ∈ gwPrimes947 ∧
      gwWit947 (800 + r) ≤ 4 + 2 * (800 + r) := by
  decide

set_option maxRecDepth 40000 in
theorem gwCert947_block9 :
    ∀ r ∈ Finset.range 46,
      gwWit947 (900 + r) ∈ gwPrimes947 ∧
      4 + 2 * (900 + r) - gwWit947 (900 + r) ∈ gwPrimes947 ∧
      gwWit947 (900 + r) ≤ 4 + 2 * (900 + r) := by
  decide

/-- Certificate for the whole wheel: for every `i < 946` the recorded witness
`gwWit947 i` and its complement `4 + 2 * i - gwWit947 i` both occur in the list of
primes `gwPrimes947`, and the witness does not exceed `4 + 2 * i`. -/
theorem gwCert947 :
    ∀ i ∈ Finset.range 946,
      gwWit947 i ∈ gwPrimes947 ∧
      4 + 2 * i - gwWit947 i ∈ gwPrimes947 ∧
      gwWit947 i ≤ 4 + 2 * i := by
  intro i hi
  simp only [Finset.mem_range] at hi
  rcases (by omega : i < 100 ∨ 100 ≤ i ∧ i < 200 ∨ 200 ≤ i ∧ i < 300 ∨ 300 ≤ i ∧ i < 400 ∨
      400 ≤ i ∧ i < 500 ∨ 500 ≤ i ∧ i < 600 ∨ 600 ≤ i ∧ i < 700 ∨ 700 ≤ i ∧ i < 800 ∨
      800 ≤ i ∧ i < 900 ∨ 900 ≤ i) with h | h | h | h | h | h | h | h | h | h
  · have h := gwCert947_block0 (i - 0) (by simp only [Finset.mem_range]; omega)
    rwa [show 0 + (i - 0) = i from by omega] at h
  · have h := gwCert947_block1 (i - 100) (by simp only [Finset.mem_range]; omega)
    rwa [show 100 + (i - 100) = i from by omega] at h
  · have h := gwCert947_block2 (i - 200) (by simp only [Finset.mem_range]; omega)
    rwa [show 200 + (i - 200) = i from by omega] at h
  · have h := gwCert947_block3 (i - 300) (by simp only [Finset.mem_range]; omega)
    rwa [show 300 + (i - 300) = i from by omega] at h
  · have h := gwCert947_block4 (i - 400) (by simp only [Finset.mem_range]; omega)
    rwa [show 400 + (i - 400) = i from by omega] at h
  · have h := gwCert947_block5 (i - 500) (by simp only [Finset.mem_range]; omega)
    rwa [show 500 + (i - 500) = i from by omega] at h
  · have h := gwCert947_block6 (i - 600) (by simp only [Finset.mem_range]; omega)
    rwa [show 600 + (i - 600) = i from by omega] at h
  · have h := gwCert947_block7 (i - 700) (by simp only [Finset.mem_range]; omega)
    rwa [show 700 + (i - 700) = i from by omega] at h
  · have h := gwCert947_block8 (i - 800) (by simp only [Finset.mem_range]; omega)
    rwa [show 800 + (i - 800) = i from by omega] at h
  · have h := gwCert947_block9 (i - 900) (by simp only [Finset.mem_range]; omega)
    rwa [show 900 + (i - 900) = i from by omega] at h

/-- **Goldbach wheel `K = 2`, modulus `947`.**

Every even number `n` with `4 ≤ n ≤ 2 * 947` is the sum of two primes. -/
theorem GoldbachWheelK2_947 (n : Nat) (hEven : Even n) (h4 : 4 ≤ n) (hn : n ≤ 2 * 947) :
    ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨k, hk⟩ := hEven
  obtain ⟨hp, hq, hle⟩ := gwCert947 (k - 2) (by simp only [Finset.mem_range]; omega)
  exact ⟨_, _, gwPrimes947_prime _ hp, gwPrimes947_prime _ hq, by omega⟩

end Brockian

