open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Nat.DivMod using (_%_; _div_)

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
