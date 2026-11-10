/-
What the combined model predicts with any memory in place of EPAM's net.

M2 is left open: `retrieve` says what a problem's code calls up, a stored
code or nothing, with probabilities. The trial (`trialWith`) is CogLib's
composition `Cog.recognizeRetrieve`, so every theorem CogLib proves about it
applies here directly: strategy nesting (`RR.backup_prob`), retrieved answers
(`RR.retrieved_prob`, `RR.retrieved_depends_only_on_route`), confusion
(`RR.confusion_gives_neighbours_answer`, `RR.wrong_eq_retrieved_of_sharp`),
confident errors (`RR.confident_errors`) and harmless confusions
(`RR.same_correct_confusion_harmless`), with problems coded by the encoding
and `Problem.sum` as the correct answer. This file adds what concerns digits:

* `commuted_confusion_harmless`: confusing `a + b` with `b + a` costs nothing.
* `confused_digit`, `near_miss_200`, `near_miss_20` need `AgreesOn`: what a
  code calls up agrees with it on the features of the digits concerned.
* `learning_preserves_trial` needs `StableRetrieval`: studying one problem
  leaves the retrieval of another, retrieved as itself for certain,
  unchanged.
-/

import MultiDigit.Postulates

namespace MD

open Cog Dist

/-- The stored problem `q`'s associations are *sharp* at criterion `cc`: no
answer but `q`'s sum clears it. -/
abbrev Sharp (str : Item → Nat → Rat) (cc : Rat) (y : Item) (q : Problem) : Prop :=
  RR.Sharp str cc y q.sum

namespace AnyMemory

variable (retrieve : Item → Dist (Option Item)) (E : Encoding) (str : Item → Nat → Rat)
  (as : List Nat) (cc : Rat) (n : Nat) (backup : Problem → Dist Nat)

/-- **Commuted confusions are harmless**: confusing `a + b` with `b + a`. -/
theorem commuted_confusion_harmless (x : Problem)
    (hq : retrieve (E.code x.swap) = pure (some (E.code x.swap)))
    (hx : retrieve (E.code x) = pure (some (E.code x.swap))) :
    prob (trialWith retrieve E str as cc n backup x) (wholeWrong x) =
      prob (trialWith retrieve E str as cc n backup x.swap) (wholeWrong x.swap) :=
  RR.same_correct_confusion_harmless E.code retrieve str as cc n backup Problem.sum x x.swap hq hx
    (by simp [Problem.sum, Problem.swap, Nat.add_comm])

/-- A problem that can call up `q` has `q`'s digit wherever retrieval agrees
on all of that digit's features (`AgreesOn`). -/
theorem confused_digit (x q : Problem) (i : Addend) (j : Place)
    (hagree : Phenomena.AgreesOn retrieve (E.code x) (E.features i j))
    (hx : (retrieve (E.code x)).Possible (some (E.code q))) :
    x.digit i j = q.digit i j :=
  Phenomena.confusion_preserves_of retrieve E.code _ (fun p => p.digit i j)
    (fun p q => E.determines p q i j) x q hagree hx

/-- **Near misses: within 200, with any memory that agrees on the hundreds
digits.** -/
theorem near_miss_200 (x q : Problem)
    (hagree : ∀ i, Phenomena.AgreesOn retrieve (E.code x) (E.features i .hundreds))
    (hx : (retrieve (E.code x)).Possible (some (E.code q)))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 200 ∧ x.sum < q.sum + 200 := by
  have h1 := confused_digit retrieve E x q .first .hundreds (hagree .first) hx
  have h2 := confused_digit retrieve E x q .second .hundreds (hagree .second) hx
  simp only [Problem.digit, Problem.addend, digitOf] at h1 h2
  simp only [Problem.sum]
  omega

/-- **Near misses: within 20**, when retrieval also agrees on the tens
digits. -/
theorem near_miss_20 (x q : Problem)
    (hagree : ∀ i, ∀ j, j ≠ Place.units → Phenomena.AgreesOn retrieve (E.code x) (E.features i j))
    (hx : (retrieve (E.code x)).Possible (some (E.code q)))
    (hxa : x.a < 1000) (hxb : x.b < 1000) (hqa : q.a < 1000) (hqb : q.b < 1000) :
    q.sum < x.sum + 20 ∧ x.sum < q.sum + 20 := by
  have h1 := confused_digit retrieve E x q .first .hundreds (hagree .first _ (by decide)) hx
  have h2 := confused_digit retrieve E x q .second .hundreds (hagree .second _ (by decide)) hx
  have h3 := confused_digit retrieve E x q .first .tens (hagree .first _ (by decide)) hx
  have h4 := confused_digit retrieve E x q .second .tens (hagree .second _ (by decide)) hx
  simp only [Problem.digit, Problem.addend, digitOf] at h1 h2 h3 h4
  simp only [Problem.sum]
  omega

/-- **Practiced problems stay practiced, with any memory that has stable
retrieval.** Studying a code other than `q`'s never changes how `q`, which
calls up itself for certain, is answered. -/
theorem learning_preserves_trial {S : Type} (R : Retriever S Item)
    (hst : Phenomena.StableRetrieval R) (s : S) (q : Problem) (z : Item)
    (hq : R.retrieve s (E.code q) = pure (some (E.code q))) (hz : E.code q ≠ z) :
    trialWith (R.retrieve (R.study s z)) E str as cc n backup q =
      trialWith (R.retrieve s) E str as cc n backup q := by
  unfold trialWith recognizeRetrieve
  rw [hst s z _ hq hz]

end AnyMemory
end MD
