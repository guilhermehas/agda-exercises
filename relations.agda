import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Data.Nat using (_≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;+-monoʳ-≤; +-monoˡ-≤; +-mono-≤)

*-mono-≤ : ∀ {m n p q : ℕ}
  → m ≤ n
  → p ≤ q
  -------------
  → m * p ≤ n * q

*-mono-≤ z≤n p≤q = z≤n
*-mono-≤ {suc m} {suc n} {p} {q} (s≤s m≤n) p≤q = +-mono-≤ p≤q (*-mono-≤ m≤n p≤q)


data even : ℕ → Set
data odd  : ℕ → Set

data even where
  zero :
    ---------
    even zero

  suc  : ∀ {n : ℕ}
    → odd n
    ------------
    → even (suc n)

data odd where
  suc   : ∀ {n : ℕ}
    → even n
    -----------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
  ------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
  -----------
  → odd (m + n)

e+o≡o : ∀ {m n : ℕ}
  → even m
  → odd n
  -----------
  → odd (m + n)

o+o≡e : ∀ {m n : ℕ}
  → odd m
  → odd n
  → even (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)
e+o≡o zero on = on
e+o≡o (suc em) on = suc (o+o≡e em on)

o+o≡e (suc em) on = suc (e+o≡o em on)

≤-iff-<ʳ : {m n : ℕ} → suc m ≤ n → m < n
≤-iff-<ʳ {m} {zero} ()
≤-iff-<ʳ {zero} {suc n} (s≤s z≤n) = s≤s z≤n
≤-iff-<ʳ {suc m} {suc n} (s≤s ineq) = s≤s ineq

≤-iff-<ˡ : {m n : ℕ}  → m < n → suc m ≤ n
≤-iff-<ˡ {m} {zero} ()
≤-iff-<ˡ {zero} {suc n} ineq = s≤s z≤n
≤-iff-<ˡ {suc m} {suc n} (s≤s ineq) = s≤s ineq
