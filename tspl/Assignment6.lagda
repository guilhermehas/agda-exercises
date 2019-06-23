# Imports

\begin{code}
open import Function using (_∘_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_)
\end{code}

# Exercise 1

## a
\begin{code}
data Tree (A : Set) : Set where
  leaf : A → Tree A
  _branch_ : Tree A → Tree A → Tree A

data AllT (A : Set) (P : A → Set) : Tree A → Set where
  leaf : {x : A} → P x → AllT A P (leaf x)
  _branch_ : {xt yt : Tree A} → AllT A P xt → AllT A P yt → AllT A P (xt branch yt)

data AnyT (A : Set) (P : A → Set) : Tree A → Set where
  leaf : {x : A} → P x → AnyT A P (leaf x)
  left : {xt yt : Tree A} → AnyT A P xt → AnyT A P (xt branch yt)
  right : {xt yt : Tree A} → AnyT A P yt → AnyT A P (xt branch yt)

All¬T→¬AnyT : ∀ {A : Set} {P : A → Set} → {xt : Tree A} → AllT A (¬_ ∘ P) xt → ¬ (AnyT A P xt)
All¬T→¬AnyT (leaf ¬Px) (leaf Px) = ¬Px Px
All¬T→¬AnyT (allLeft branch _) (left anyLeft) = All¬T→¬AnyT allLeft anyLeft
All¬T→¬AnyT (_ branch allRight) (right anyRight) =  All¬T→¬AnyT allRight anyRight

\end{code}
