open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

+-example : 3 + 4 ≡ 7
+-example =
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    suc (suc 5)
  ≡⟨⟩
    suc 6
  ≡⟨⟩
    7
  ∎

*-example : 3 * 4 ≡ 12
*-example =
  begin
    3 * 4
  ≡⟨⟩
    3 + (3 * 3)
  ≡⟨⟩
    3 + (3 + (2 * 3))
  ≡⟨⟩
    3 + (3 + (3 + (1 * 3)))
  ≡⟨⟩
    3 + (3 + (3 + (3 + (0 * 3))))
  ≡⟨⟩
    12
  ∎

∸-examples-1 : 5 ∸ 3 ≡ 2
∸-examples-1 =
  begin
    5 ∸ 3
  ≡⟨⟩
    4 ∸ 2
  ≡⟨⟩
    3 ∸ 1
  ≡⟨⟩
    2
  ∎

∸-examples-2 : 3 ∸ 5 ≡ 0
∸-examples-2 =
  begin
    3 ∸ 5
  ≡⟨⟩
    2 ∸ 4
  ≡⟨⟩
    1 ∸ 3
  ≡⟨⟩
    0
  ∎

_^_ : ℕ → ℕ → ℕ
n ^ zero = 1
n ^ suc m = n * (n ^ m)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = nil
inc (x0 n) = x1_ n
inc (x1 nil) = x0 x1 nil
inc (x1 (x0 n)) = x0 x1 (inc n)
inc (x1 (x1 n)) = x0 (inc (x1 n))

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * from n
from (x1 n) = 2 * from n + 1

to : ℕ → Bin
to zero = x0_ nil
to (suc n) = inc (to n)
