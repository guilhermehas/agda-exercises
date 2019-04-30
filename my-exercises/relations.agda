import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Empty using (⊥)
open import Data.Empty.Irrelevant using (⊥-elim)
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

<-trans : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans {zero} {n} {zero} m<n ()
<-trans {zero} {zero} {suc p} zero<n n<p = s≤s z≤n
<-trans {zero} {suc n} {suc p} zero<n n<p = s≤s z≤n
<-trans {suc m} {n} {zero} m<n ()
<-trans {suc m} {zero} {suc p} () n<p
<-trans {suc m} {suc (suc n)} {suc (suc (suc p))} (s≤s (s≤s m<n)) (s≤s (s≤s (s≤s n<p))) = s≤s (<-trans (s≤s m<n) (s≤s (s≤s n<p)))

data Ordering : ℕ → ℕ → Set where
  less : {m n : ℕ} → .(m < n) → Ordering m n
  equal : {m n : ℕ} → .(m ≡ n) → Ordering m n
  greater : {m n : ℕ} → .(n < m) → Ordering m n

≡-same : ∀ {m n : ℕ} → m ≡ n → n ≡ m
≡-same refl = refl

<-≡-disjoint : ∀ {m n} → (m < n) → (m ≡ n) → ⊥
<-≡-disjoint {zero} {.0} () refl
<-≡-disjoint {suc m} {.(suc m)} (s≤s m<n) refl = <-≡-disjoint m<n refl 

<->-disjoint : ∀ {m n} → (m < n) → (n < m) → ⊥
<->-disjoint {zero} {.(suc _)} (s≤s m<n) ()
<->-disjoint {suc m} {.(suc _)} (s≤s m<n) (s≤s n<m) = <->-disjoint m<n n<m

trichotomy : ∀ {m n : ℕ} → (x : Ordering m n) → (y : Ordering m n) → x ≡ y
trichotomy (less x) (less y) = refl
trichotomy (less x) (equal y) = ⊥-elim (<-≡-disjoint x y)
trichotomy (less x) (greater y) = ⊥-elim  (<->-disjoint x y)
trichotomy (equal x) (less y) = ⊥-elim  (<-≡-disjoint y x)
trichotomy (equal x) (equal y) = refl
trichotomy (equal x) (greater y) = ⊥-elim  (<-≡-disjoint y (≡-same x))
trichotomy (greater x) (less y) = ⊥-elim  (<->-disjoint y x)
trichotomy (greater x) (equal y) = ⊥-elim (<-≡-disjoint x (≡-same y))
trichotomy (greater x) (greater y) = refl

≤-iff-<ʳ : {m n : ℕ} → suc m ≤ n → m < n
≤-iff-<ʳ {m} {zero} ()
≤-iff-<ʳ {zero} {suc n} (s≤s z≤n) = s≤s z≤n
≤-iff-<ʳ {suc m} {suc n} (s≤s ineq) = s≤s ineq

≤-iff-<ˡ : {m n : ℕ}  → m < n → suc m ≤ n
≤-iff-<ˡ {m} {zero} ()
≤-iff-<ˡ {zero} {suc n} ineq = s≤s z≤n
≤-iff-<ˡ {suc m} {suc n} (s≤s ineq) = s≤s ineq

≤-sucʳ : {m n : ℕ} → m ≤ n → m ≤ suc n
≤-sucʳ z≤n = z≤n
≤-sucʳ (s≤s eq) = s≤s (≤-sucʳ eq)

<-trans-revisited : ∀ {m n p : ℕ} → m < n → n < p → m < p
<-trans-revisited (s≤s z≤n) (s≤s (s≤s n<p)) = s≤s z≤n
<-trans-revisited (s≤s (s≤s m<n)) (s≤s (s≤s (s≤s n<p))) = s≤s (s≤s (≤-sucʳ ( ≤-trans m<n n<p)))
