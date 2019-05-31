---
title     : "PUC-Assignment3: PUC Assignment 3"
layout    : page
permalink : /PUC-Assignment3/
---

\begin{code}
module Assignment3 where
\end{code}

## YOUR NAME AND EMAIL GOES HERE
# Name
Guilherme Horta Alvares da Silva

# Email
guilhermehas@hotmail.com

## Introduction

You must do _all_ the exercises labelled "(recommended)".

Exercises labelled "(stretch)" are there to provide an extra challenge.
You don't need to do all of these, but should attempt at least a few.

Exercises without a label are optional, and may be done if you want
some extra practice.

Please ensure your files execute correctly under Agda!

## Imports

\begin{code}
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Bool.Base using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.String.Unsafe using (_≟_)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (_∘_)
open import Algebra.Structures using (IsMonoid)
open import Level using (Level)
open import Relation.Unary using (Decidable)
open import plfa.Relations using (_<_; z<s; s<s)
open import plfa.Isomorphism using (_≃_; ≃-sym; ≃-trans; _≲_; extensionality)
open plfa.Isomorphism.≃-Reasoning
open import plfa.Lists using (List; []; _∷_; [_]; [_,_]; [_,_,_]; [_,_,_,_];
  _++_; reverse; map; foldr; sum; All; Any; here; there; _∈_)
open import plfa.Lambda hiding (ƛ′_⇒_; case′_[zero⇒_|suc_⇒_]; μ′_⇒_; plus′)
open import plfa.Properties hiding (value?; unstuck; preserves; wttdgs)
\end{code}

## Lambda

#### Exercise `mul` (recommended)

Write out the definition of a lambda term that multiplies
two natural numbers.

\begin{code}
mul : Term
mul = μ "*" ⇒ ƛ "m" ⇒ ƛ "n" ⇒
    case ` "m"
      [zero⇒ `zero
      |suc "m" ⇒ (plus · ` "n" · (` "*" · ` "m" · ` "n")) ]
\end{code}

#### Exercise `primed` (stretch)

We can make examples with lambda terms slightly easier to write
by adding the following definitions.
\begin{code}
ƛ′_⇒_ : Term → Term → Term
ƛ′ (` x) ⇒ N  =  ƛ x ⇒ N
ƛ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥

case′_[zero⇒_|suc_⇒_] : Term → Term → Term → Term → Term
case′ L [zero⇒ M |suc (` x) ⇒ N ]  =  case L [zero⇒ M |suc x ⇒ N ]
case′ _ [zero⇒ _ |suc _ ⇒ _ ]      =  ⊥-elim impossible
  where postulate impossible : ⊥

μ′_⇒_ : Term → Term → Term
μ′ (` x) ⇒ N  =  μ x ⇒ N
μ′ _ ⇒ _      =  ⊥-elim impossible
  where postulate impossible : ⊥
\end{code}
The definition of `plus` can now be written as follows.
\begin{code}
plus′ : Term
plus′ = μ′ + ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ n
            |suc m ⇒ `suc (+ · m · n) ]
  where
  +  =  plus
  m  =  ` "m"
  n  =  ` "n"
\end{code}
Write out the definition of multiplication in the same style.

\begin{code}
mul′ : Term
mul′ = μ′ * ⇒ ƛ′ m ⇒ ƛ′ n ⇒
          case′ m
            [zero⇒ `zero
            |suc m ⇒ (+ · n · (* · m · n)) ]
  where
  *  =  ` "*"
  +  =  ` "+"
  m  =  ` "m"
  n  =  ` "n"
\end{code}

#### Exercise `_[_:=_]′` (stretch)

The definition of substitution above has three clauses (`ƛ`, `case`,
and `μ`) that invoke a with clause to deal with bound variables.
Rewrite the definition to factor the common part of these three
clauses into a single function, defined by mutual recursion with
substitution.

\begin{code}
mutual
  subs : Id → Term → Id → Term → Term
  subs x N y V with x ≟ y
  subs x N y V | yes _ = N
  subs x N y V | no _ = N [ y :== V ]

  _[_:==_] : Term → Id → Term → Term
  (` x) [ y :== V ] with x ≟ y
  ... | yes _          =  V
  ... | no  _          =  ` x
  (ƛ x ⇒ N) [ y :== V ] = ƛ x ⇒ (subs x N y V)
  (N₁ · N₂) [ y :== V ] = (N₁ [ y :== V ]) · (N₂ [ y :== V ])
  `zero [ y :== V ] = `zero
  (`suc N) [ y :== V ] = `suc N [ y :== V ]
  case L [zero⇒ M |suc x ⇒ N ] [ y :== V ] = case L [ y :== V ] [zero⇒ M [ y :== V ] |suc x ⇒ subs x N y V ]
  (μ x ⇒ N) [ y :== V ] = μ x ⇒ subs x N y V
\end{code}

#### Exercise `—↠≃—↠′`

Show that the two notions of reflexive and transitive closure
above are isomorphic.

\begin{code}
—↠≲—↠′ : ∀ {M N}
  → M —↠ N ≲ M —↠′ N
—↠≲—↠′ = record {
  to = to ;
  from = from ;
  from∘to = from∘to
  }
  where
  to : ∀ {M N} → M —↠ N → M —↠′ N
  to (M _—↠_.∎) = refl′
  to (L —→⟨ L—↠M ⟩ M—↠N) = trans′ (step′ L—↠M) (to M—↠N)

  _—↠trans_ : ∀ {L M N}
    → L —↠ M
    → M —↠ N
    -----------
    → L —↠ N
  (M _—↠_.∎) —↠trans M→N = M→N
  (L —→⟨ L→M₁ ⟩ M₁→M) —↠trans M→N =
    L
    —→⟨ L→M₁ ⟩
    (M₁→M —↠trans M→N)

  from : ∀ {M N} → M —↠′ N → M —↠ N
  from {M} {N} (step′ M—→N) =
    plfa.Lambda.begin
      M
    —→⟨ M—→N ⟩
      N
    _—↠_.∎
  from {M} refl′ = M _—↠_.∎
  from {L} {N} (trans′ {L} {M}  L—↠′M M—↠′N) = from L—↠′M —↠trans from M—↠′N

  from∘to : ∀ {M N} → (x : M —↠ N) → from (to x) ≡ x
  from∘to (M _—↠_.∎) = refl
  from∘to (L —→⟨ L→M ⟩ M→N) = cong (λ x → L —→⟨ L→M ⟩ x) (from∘to M→N)
\end{code}

#### Exercise `plus-example`

Write out the reduction sequence demonstrating that one plus one is two.

\begin{code}
one : Term
one = `suc `zero

⊢one : ∀ {Γ} → Γ ⊢ one ⦂ `ℕ
⊢one = ⊢suc ⊢zero

⊢1+1 : ∅ ⊢ plus · one · one ⦂ `ℕ
⊢1+1 = ⊢plus · ⊢one · ⊢one

-- _ : plus · one · one —↠ `suc `suc `zero
-- _ = 
  -- (μ "+" ⇒
  --   (ƛ "m" ⇒
  --   (ƛ "n" ⇒
  --     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --     ])))
  -- · `suc `zero
  -- · `suc `zero
  -- —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
  -- (ƛ "m" ⇒
  --   (ƛ "n" ⇒
  --   case ` "m" [zero⇒ ` "n" |suc "m" ⇒
  --   `suc
  --   ((μ "+" ⇒
  --     (ƛ "m" ⇒
  --       (ƛ "n" ⇒
  --       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --       ])))
  --     · ` "m"
  --     · ` "n")
  --   ]))
  -- · `suc `zero
  -- · `suc `zero
  -- —→⟨ ξ-·₁ (β-ƛ (V-suc V-zero)) ⟩
  -- (ƛ "n" ⇒
  --   case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
  --   `suc
  --   ((μ "+" ⇒
  --     (ƛ "m" ⇒
  --     (ƛ "n" ⇒
  --       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --       ])))
  --   · ` "m"
  --   · ` "n")
  --   ])
  -- · `suc `zero
  -- —→⟨ β-ƛ (V-suc V-zero) ⟩
  -- case `suc `zero [zero⇒ `suc `zero |suc "m" ⇒
  -- `suc
  -- ((μ "+" ⇒
  --   (ƛ "m" ⇒
  --     (ƛ "n" ⇒
  --     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --     ])))
  --   · ` "m"
  --   · `suc `zero)
  -- ]
  -- —→⟨ β-suc V-zero ⟩
  -- `suc
  -- ((μ "+" ⇒
  --   (ƛ "m" ⇒
  --     (ƛ "n" ⇒
  --     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --     ])))
  --   · `zero
  --   · `suc `zero)
  -- —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
  -- `suc
  -- ((ƛ "m" ⇒
  --   (ƛ "n" ⇒
  --     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
  --     `suc
  --     ((μ "+" ⇒
  --       (ƛ "m" ⇒
  --       (ƛ "n" ⇒
  --         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --         ])))
  --     · ` "m"
  --     · ` "n")
  --     ]))
  --   · `zero
  --   · `suc `zero)
  -- —→⟨ ξ-suc (ξ-·₁ (β-ƛ V-zero)) ⟩
  -- `suc
  -- ((ƛ "n" ⇒
  --   case `zero [zero⇒ ` "n" |suc "m" ⇒
  --   `suc
  --   ((μ "+" ⇒
  --     (ƛ "m" ⇒
  --       (ƛ "n" ⇒
  --       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --       ])))
  --     · ` "m"
  --     · ` "n")
  --   ])
  --   · `suc `zero)
  -- —→⟨ ξ-suc (β-ƛ (V-suc V-zero)) ⟩
  -- `suc
  -- case `zero [zero⇒ `suc `zero |suc "m" ⇒
  -- `suc
  -- ((μ "+" ⇒
  --   (ƛ "m" ⇒
  --     (ƛ "n" ⇒
  --     case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
  --     ])))
  --   · ` "m"
  --   · `suc `zero)
  -- ]
  -- —→⟨ ξ-suc β-zero ⟩ `suc (`suc `zero) _—↠_.∎
\end{code}

#### Exercise `mul-type` (recommended)

Using the term `mul` you defined earlier, write out the derivation
showing that it is well-typed.

\begin{code}
⊢mul : ∀ {Γ} → Γ ⊢ mul ⦂ `ℕ ⇒ `ℕ ⇒ `ℕ
⊢mul = ⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S (m ≠ n) Z)) ⊢zero (((⊢μ (⊢ƛ (⊢ƛ (⊢case (⊢` (S (m ≠ n) Z))
  (⊢` Z) (⊢suc (((⊢` (S (+ ≠ m) (S (+ ≠ n) (S (+ ≠ m) Z)))) ·
  ⊢` Z) · ⊢` (S (n ≠ m) Z))))))) · ⊢` (S (n ≠ m) Z)) ·
  (((⊢` (S (* ≠ m) (S (* ≠ n) (S (* ≠ m) Z)))) ·
  ⊢` Z) · ⊢` (S (n ≠ m) Z))))))
  where
  m = "m"
  n = "n"
  + = "+"
  * = "*"
\end{code}

## Properties


#### Exercise `Progress-≃`

Show that `Progress M` is isomorphic to `Value M ⊎ ∃[ N ](M —→ N)`.

\begin{code}
proIsomorph : ∀ {M} → Progress M ≃ Value M ⊎ ∃[ N ](M —→ N)
proIsomorph = record {
  to = to ;
  from = from ;
  from∘to = from∘to ;
  to∘from = to∘from }
  where
  to : ∀ {M} → Progress M → Value M ⊎ ∃[ N ](M —→ N)
  to {M} (step {N} M→N) = inj₂ ⟨ N , M→N ⟩
  to {M} (done VM) = inj₁ VM

  from : ∀ {M} → Value M ⊎ ∃[ N ](M —→ N) → Progress M
  from {M} (inj₁ vm) = done vm
  from {M} (inj₂ ⟨ N , M→N ⟩) = step M→N

  from∘to : ∀ {M} → (pm : Progress M) → from (to pm) ≡ pm
  from∘to (step _) = refl
  from∘to (done _) = refl

  to∘from : ∀ {M} → (x : Value M ⊎ ∃[ N ](M —→ N)) → to (from x) ≡ x
  to∘from (inj₁ _) = refl
  to∘from (inj₂ _) = refl
\end{code}

#### Exercise `progress′`

Write out the proof of `progress′` in full, and compare it to the
proof of `progress` above.

\begin{code}
progress` : ∀ M {A} → ∅ ⊢ M ⦂ A → Value M ⊎ ∃[ N ](M —→ N)
progress` M vm with proIsomorph {M}
progress` M vm
  | record { to = to ; from = from ; from∘to = from∘to ; to∘from = to∘from }
  = to (progress vm)
\end{code}

#### Exercise `value?`

Combine `progress` and `—→¬V` to write a program that decides
whether a well-typed term is a value.
\begin{code}
value? : ∀ {A M} → ∅ ⊢ M ⦂ A → Dec (Value M)
value? (⊢` ())
value? (⊢ƛ ma) = yes V-ƛ
value? (ma · LA) = no ¬value
  where
  ¬value : ∀ {L M} →  ¬ Value (L · M)
  ¬value ()
value? ⊢zero = yes V-zero
value? (⊢suc ma) with value? ma
value? (⊢suc ma) | yes p = yes (V-suc p)
value? (⊢suc ma) | no ¬p = no (¬value-nat ma ¬p)
  where
  ¬value-nat : ∀ {M} → ∅ ⊢ M ⦂ `ℕ → ¬ Value M → ¬ Value (`suc M)
  ¬value-nat exp vm (V-suc vsuc) = vm vsuc
value? (⊢case ma ma₁ ma₂) = no ¬value
  where
  ¬value : ∀ {L M x N} → ¬ Value (case L [zero⇒ M |suc x ⇒ N ])
  ¬value ()
value? (⊢μ ma) = no (¬value (⊢μ ma))
  where
  ¬value : ∀ {x A M} → ∅ ⊢ μ x ⇒ M ⦂ A → ¬ (Value (μ x ⇒ M))
  ¬value (⊢μ exp) ()
\end{code}


#### Exercise `subst′` (stretch)

Rewrite `subst` to work with the modified definition `_[_:=_]′`
from the exercise in the previous chapter.  As before, this
should factor dealing with bound variables into a single function,
defined by mutual recursion with the proof that substitution
preserves types.

\begin{code}
mutual
  rec-subs : ∀ {Γ x y V N A B C}
    → ∅ ⊢ V ⦂ A
    → Γ , y ⦂ A , x ⦂ B ⊢ N ⦂ C
    -----------------------------
    → Γ , x ⦂ B ⊢ subs x N y V ⦂ C
  rec-subs {Γ} {x} {y} ⊢V ⊢N with x ≟ y
  rec-subs {Γ} {x} {.x} ⊢V ⊢N | yes refl = drop ⊢N
  rec-subs {Γ} {x} {y} ⊢V ⊢N | no x≠y = subst` ⊢V (swap x≠y ⊢N)


  subst` : ∀ {Γ x N V A B}
    → ∅ ⊢ V ⦂ A
    → Γ , x ⦂ A ⊢ N ⦂ B
    --------------------
    → Γ ⊢ N [ x :== V ] ⦂ B

  subst` {x = y} ⊢V (⊢` {x = x} Z) with x ≟ y
  subst` {x = y} ⊢V (⊢` {x = y} Z) | yes refl = weaken ⊢V
  subst` {x = y} ⊢V (⊢` {x = y} Z) | no x≠y = ⊥-elim (x≠y refl)
  subst` {x = y} ⊢V (⊢` {x = x} (S x≠y w)) with x ≟ y
  subst` {x = x} ⊢V (⊢` {x = x} (S x≠y w)) | yes refl = ⊥-elim (x≠y refl)
  subst` {x = y} ⊢V (⊢` {x = x} (S x≠y w)) | no _ = ⊢` w
  subst` {x = y} ⊢V (⊢ƛ ⊢M) = ⊢ƛ (rec-subs ⊢V ⊢M)
  subst` {x = y} ⊢V (⊢M · ⊢N) = subst` ⊢V ⊢M · subst` ⊢V ⊢N
  subst` {x = y} ⊢V ⊢zero = ⊢zero
  subst` {x = y} ⊢V (⊢suc ⊢M) = ⊢suc (subst` ⊢V ⊢M)
  subst` {x = y} ⊢V (⊢case {x = x} ⊢L ⊢M ⊢N) = ⊢case (subst` ⊢V ⊢L) (subst` ⊢V ⊢M) (rec-subs ⊢V ⊢N)
  subst` {x = y} ⊢V (⊢μ ⊢M) = ⊢μ (rec-subs ⊢V ⊢M)
\end{code}

#### Exercise `mul-example` (recommended)

Using the evaluator, confirm that two times two is four.

\begin{code}
⊢2*2 : ∅ ⊢ mul · two · two ⦂ `ℕ
⊢2*2 = ⊢mul · ⊢two · ⊢two

-- _ : eval (gas 100) ⊢2*2 ≡
--   steps
--   ((μ "*" ⇒
--     (ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "n"
--       · (` "*" · ` "m" · ` "n")
--       ])))
--   · `suc (`suc `zero)
--   · `suc (`suc `zero)
--   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--   (ƛ "m" ⇒
--     (ƛ "n" ⇒
--     case ` "m" [zero⇒ `zero |suc "m" ⇒
--     (μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "n"
--     ·
--     ((μ "*" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--           (ƛ "m" ⇒
--           (ƛ "n" ⇒
--             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--             ])))
--         · ` "n"
--         · (` "*" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ]))
--   · `suc (`suc `zero)
--   · `suc (`suc `zero)
--   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
--     (μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · ` "n"
--     ·
--     ((μ "*" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--         · ` "n"
--         · (` "*" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   · `suc (`suc `zero)
--   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--   case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
--   (μ "+" ⇒
--     (ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "*" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "n"
--       · (` "*" · ` "m" · ` "n")
--       ])))
--     · ` "m"
--     · `suc (`suc `zero))
--   ]
--   —→⟨ β-suc (V-suc V-zero) ⟩
--   (μ "+" ⇒
--     (ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "*" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "n"
--       · (` "*" · ` "m" · ` "n")
--       ])))
--     · `suc `zero
--     · `suc (`suc `zero))
--   —→⟨ ξ-·₁ (ξ-·₁ β-μ) ⟩
--   (ƛ "m" ⇒
--     (ƛ "n" ⇒
--     case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ]))
--   · `suc (`suc `zero)
--   ·
--   ((μ "*" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "n"
--       · (` "*" · ` "m" · ` "n")
--       ])))
--     · `suc `zero
--     · `suc (`suc `zero))
--   —→⟨ ξ-·₁ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((μ "*" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "n"
--       · (` "*" · ` "m" · ` "n")
--       ])))
--     · `suc `zero
--     · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "n"
--       ·
--       ((μ "*" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ `zero |suc "m" ⇒
--           (μ "+" ⇒
--           (ƛ "m" ⇒
--             (ƛ "n" ⇒
--             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--             ])))
--           · ` "n"
--           · (` "*" · ` "m" · ` "n")
--           ])))
--       · ` "m"
--       · ` "n")
--       ]))
--     · `suc `zero
--     · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "n" ⇒
--     case `suc `zero [zero⇒ `zero |suc "m" ⇒
--     (μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "n"
--     ·
--     ((μ "*" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--           (ƛ "m" ⇒
--           (ƛ "n" ⇒
--             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--             ])))
--         · ` "n"
--         · (` "*" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     · `suc (`suc `zero))
--   —→⟨ ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   case `suc `zero [zero⇒ `zero |suc "m" ⇒
--   (μ "+" ⇒
--     (ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--   · `suc (`suc `zero)
--   ·
--   ((μ "*" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "n"
--       · (` "*" · ` "m" · ` "n")
--       ])))
--     · ` "m"
--     · `suc (`suc `zero))
--   ]
--   —→⟨ ξ-·₂ V-ƛ (β-suc V-zero) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · `suc (`suc `zero)
--     ·
--     ((μ "*" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--         · ` "n"
--         · (` "*" · ` "m" · ` "n")
--         ])))
--     · `zero
--     · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "m"
--       · ` "n")
--       ]))
--     · `suc (`suc `zero)
--     ·
--     ((μ "*" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--         · ` "n"
--         · (` "*" · ` "m" · ` "n")
--         ])))
--     · `zero
--     · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     ·
--     ((μ "*" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--         · ` "n"
--         · (` "*" · ` "m" · ` "n")
--         ])))
--     · `zero
--     · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     ·
--     ((ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "n"
--       ·
--       ((μ "*" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ `zero |suc "m" ⇒
--           (μ "+" ⇒
--             (ƛ "m" ⇒
--             (ƛ "n" ⇒
--               case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--               ])))
--           · ` "n"
--           · (` "*" · ` "m" · ` "n")
--           ])))
--         · ` "m"
--         · ` "n")
--       ]))
--     · `zero
--     · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (ξ-·₁ (β-ƛ V-zero))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     ·
--     ((ƛ "n" ⇒
--       case `zero [zero⇒ `zero |suc "m" ⇒
--       (μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "n"
--       ·
--       ((μ "*" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ `zero |suc "m" ⇒
--           (μ "+" ⇒
--           (ƛ "m" ⇒
--             (ƛ "n" ⇒
--             case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--             ])))
--           · ` "n"
--           · (` "*" · ` "m" · ` "n")
--           ])))
--       · ` "m"
--       · ` "n")
--       ])
--     · `suc (`suc `zero)))
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     ·
--     case `zero [zero⇒ `zero |suc "m" ⇒
--     (μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · `suc (`suc `zero)
--     ·
--     ((μ "*" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ `zero |suc "m" ⇒
--         (μ "+" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--         · ` "n"
--         · (` "*" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · `suc (`suc `zero))
--     ])
--   —→⟨ ξ-·₂ V-ƛ (ξ-·₂ V-ƛ β-zero) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   ((ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     · `zero)
--   —→⟨ ξ-·₂ V-ƛ (β-ƛ V-zero) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   case `suc (`suc `zero) [zero⇒ `zero |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · ` "m"
--     · `zero)
--   ]
--   —→⟨ ξ-·₂ V-ƛ (β-suc (V-suc V-zero)) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · `suc `zero
--     · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   ((ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "m"
--       · ` "n")
--       ]))
--     · `suc `zero
--     · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero)))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   ((ƛ "n" ⇒
--     case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     · `zero)
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-ƛ V-zero)) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   case `suc `zero [zero⇒ `zero |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · ` "m"
--     · `zero)
--   ]
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (β-suc V-zero)) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   (`suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · `zero
--     · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ)))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   (`suc
--     ((ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--         · ` "m"
--         · ` "n")
--       ]))
--     · `zero
--     · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero)))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   (`suc
--     ((ƛ "n" ⇒
--       case `zero [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "m"
--       · ` "n")
--       ])
--     · `zero))
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc (β-ƛ V-zero))) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   ·
--   `suc
--   (`suc
--     case `zero [zero⇒ `zero |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · `zero)
--     ])
--   —→⟨ ξ-·₂ V-ƛ (ξ-suc (ξ-suc β-zero)) ⟩
--   (ƛ "n" ⇒
--     case `suc (`suc `zero) [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · ` "n")
--     ])
--   · `suc (`suc `zero)
--   —→⟨ β-ƛ (V-suc (V-suc V-zero)) ⟩
--   case `suc (`suc `zero) [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · ` "m"
--     · `suc (`suc `zero))
--   ]
--   —→⟨ β-suc (V-suc V-zero) ⟩
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · `suc `zero
--     · `suc (`suc `zero))
--   —→⟨ ξ-suc (ξ-·₁ (ξ-·₁ β-μ)) ⟩
--   `suc
--   ((ƛ "m" ⇒
--     (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "m"
--       · ` "n")
--       ]))
--     · `suc `zero
--     · `suc (`suc `zero))
--   —→⟨ ξ-suc (ξ-·₁ (β-ƛ (V-suc V-zero))) ⟩
--   `suc
--   ((ƛ "n" ⇒
--     case `suc `zero [zero⇒ ` "n" |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--         (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--       · ` "m"
--       · ` "n")
--     ])
--     · `suc (`suc `zero))
--   —→⟨ ξ-suc (β-ƛ (V-suc (V-suc V-zero))) ⟩
--   `suc
--   case `suc `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--   `suc
--   ((μ "+" ⇒
--     (ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--       ])))
--     · ` "m"
--     · `suc (`suc `zero))
--   ]
--   —→⟨ ξ-suc (β-suc V-zero) ⟩
--   `suc
--   (`suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · `zero
--     · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (ξ-·₁ β-μ))) ⟩
--   `suc
--   (`suc
--     ((ƛ "m" ⇒
--       (ƛ "n" ⇒
--       case ` "m" [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--           (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--         · ` "m"
--         · ` "n")
--       ]))
--     · `zero
--     · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (ξ-·₁ (β-ƛ V-zero))) ⟩
--   `suc
--   (`suc
--     ((ƛ "n" ⇒
--       case `zero [zero⇒ ` "n" |suc "m" ⇒
--       `suc
--       ((μ "+" ⇒
--         (ƛ "m" ⇒
--         (ƛ "n" ⇒
--           case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--           ])))
--       · ` "m"
--       · ` "n")
--       ])
--     · `suc (`suc `zero)))
--   —→⟨ ξ-suc (ξ-suc (β-ƛ (V-suc (V-suc V-zero)))) ⟩
--   `suc
--   (`suc
--     case `zero [zero⇒ `suc (`suc `zero) |suc "m" ⇒
--     `suc
--     ((μ "+" ⇒
--       (ƛ "m" ⇒
--       (ƛ "n" ⇒
--         case ` "m" [zero⇒ ` "n" |suc "m" ⇒ `suc (` "+" · ` "m" · ` "n")
--         ])))
--     · ` "m"
--     · `suc (`suc `zero))
--     ])
--   —→⟨ ξ-suc (ξ-suc β-zero) ⟩ `suc (`suc (`suc (`suc `zero))) _—↠_.∎)
--   (done (V-suc (V-suc (V-suc (V-suc V-zero)))))
-- _ = refl

\end{code}


#### Exercise: `progress-preservation`

Without peeking at their statements above, write down the progress
and preservation theorems for the simply typed lambda-calculus.


#### Exercise `subject-expansion`

We say that `M` _reduces_ to `N` if `M —→ N`,
and conversely that `M` _expands_ to `N` if `N —→ M`.
The preservation property is sometimes called _subject reduction_.
Its opposite is _subject expansion_, which holds if
`M —→ N` and `∅ ⊢ N ⦂ A` imply `∅ ⊢ M ⦂ A`.
Find two counter-examples to subject expansion, one
with case expressions and one not involving case expressions.

```
M = case `suc V [zero⇒ P |suc x ⇒ N ]
P is a value of type A
N of type B
and type A ≠ type B
M can reduce —→ to type A
or can reduce —→ to type B
but M does not have type, because P has different type than N
```

#### Exercise `stuck`

Give an example of an ill-typed term that does get stuck.

```
s ⦂ `ℕ ⇒ `ℕ
M = s · `zero ⦂ `ℕ
M is stucked, because it can not be reduced and it is not a value
```

#### Exercise `unstuck` (recommended)

Provide proofs of the three postulates, `unstuck`, `preserves`, and `wttdgs` above.

\begin{code}
Stuck` : Term → Set
Stuck` M = ¬(¬(Normal M) ⊎ Value M)

Stuck→Stuck` : ∀ {M} → Stuck M → Stuck` M
Stuck→Stuck` ⟨ normal , _ ⟩ (inj₁ ¬normal) = ¬normal normal
Stuck→Stuck` ⟨ _ , ¬VM ⟩ (inj₂ VM) = ¬VM VM

Stuck`→Stuck : ∀ {M} → Stuck` M → Stuck M
Stuck`→Stuck stm = ⟨ (λ M→N → stm (inj₁ λ NM → NM M→N)) , (λ VM → stm (inj₂ VM)) ⟩

progress-unstuck : ∀ {M}
  → Progress M
  -----------
  → ¬ (Stuck M)
progress-unstuck (step M→N) ⟨ NM , ¬VM ⟩ = NM M→N
progress-unstuck (done VM) ⟨ NM , ¬VM ⟩ = ¬VM VM

unstuck : ∀ {M A}
  → ∅ ⊢ M ⦂ A
  -----------
  → ¬ (Stuck M)
unstuck st = progress-unstuck (progress st)

preserves : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
  ---------
  → ∅ ⊢ N ⦂ A
preserves ma (M _—↠_.∎) = ma
preserves (⊢` x₁) (.(` _) —→⟨ () ⟩ mn)
preserves (⊢ƛ ma) (.(ƛ _ ⇒ _) —→⟨ () ⟩ mn)
preserves (L⦂A₁→A · ma) (.(_ · _) —→⟨ L∘M→M₁ ⟩ M₁→N) = preserves (preserve (L⦂A₁→A · ma) L∘M→M₁) M₁→N
preserves ⊢zero (.`zero —→⟨ () ⟩ mn)
preserves (⊢suc ma) (.(`suc _) —→⟨ ξ-suc x ⟩ mn) = preserves (⊢suc (preserve ma x)) mn
preserves (⊢case LN MA xN⊢aN) (.(case _ [zero⇒ _ |suc _ ⇒ _ ]) —→⟨ L→L ⟩ case`) = 
  preserves (preserve (⊢case LN MA xN⊢aN) L→L) case`
preserves {M} {N} {A} (⊢μ ma) ((μ _ ⇒ _) —→⟨ β-μ ⟩ mn) = preserves (subst (⊢μ ma) ma) mn

wttdgs : ∀ {M N A}
  → ∅ ⊢ M ⦂ A
  → M —↠ N
  -----------
  → ¬ (Stuck N)
wttdgs MA MN = unstuck (preserves MA MN)

\end{code}







