open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Nat.DivMod using (_%_; _div_)

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1_ nil
inc (x0 n) = x1_ n
inc (x1 n) = x0_ (inc n)

from : Bin → ℕ
from nil = 0
from (x0 n) = 2 * from n
from (x1 n) = 2 * from n + 1

to : ℕ → Bin
to zero = x0_ nil
to (suc n) = inc (to n)
