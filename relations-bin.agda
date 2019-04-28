import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm; *-comm)
open import Data.Nat using (_≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-trans; ≤-antisym; ≤-total;+-monoʳ-≤; +-monoˡ-≤; +-mono-≤)
open import Data.Nat.DivMod using (_%_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import naturals
open import Data.Bool using (true; false)

data One : Bin → Set
data Can : Bin → Set

data One where
  one : One (x1 nil)
  x0_ : {n : Bin} → One n → One (x0_ n)
  x1_ : {n : Bin} → One n → One (x1_ n)

data Can where
  zero : Can (x0 nil)
  one : {n : Bin} → One n → Can n

getOne : {n : Bin} → Can (inc n) → One (inc n)
getOne {nil} (one x) = x
getOne {x0 n} (one x) = x
getOne {x1 nil} (one x) = x
getOne {x1 (x0 n)} (one x) = x
getOne {x1 (x1 nil)} (one x) = x
getOne {x1 (x1 (x0 n))} (one x) = x
getOne {x1 (x1 (x1 n))} (one x) = x

canInc : {n : Bin} → Can n → Can (inc n)
canInc {.(x0 nil)} zero = one one
canInc {.(x1 nil)} (one one) = one (x0 one)
canInc {.(x0 _)} (one (x0 x)) = one (x1 x)
canInc {.(x1 (x1 nil))} (one (x1 one)) = one (x0 (x0 one))
canInc {(x1 (x0 n))} (one (x1 (x0 x))) with getOne (canInc (one x))
... | one1 = one (x0 (x1 one1))
canInc {.(x1 (x1 _))} (one (x1 (x1 x))) with getOne (canInc (one (x1 x)))
... | one1 = one (x0 one1)
