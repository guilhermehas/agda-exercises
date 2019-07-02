Guilherme Horta Alvares da Silva
guilhermehas@hotmail.com
4/5

* Assignment 5

  + Inference
    - `bidirectional-mul` (recommended) ok
    - `bidirectional-products` (recommended) ok
    - `inference-multiplication` (recommended) [3] ok
    - `bidirectional-products` (recommended) [1] ok
    - `bidirectional-rest` (stretch)
    - `inference-products` (recommended) [2] ok
    - `inference-rest` (stretch)

  + Untyped
    - `Type≃⊤`
    - `Context≃ℕ`
    - `variant-1`
    - `variant-2`
    - `plus-eval`
    - `multiplication-untyped` (recommended) [4] ok, but wrong problem
    - `encode-more` (stretch) attempted [5] attempted

[1] You had comment 'Sums' where you should have had 'Products'
[2] inherit Γ (`let x ≡ A ⇒ B) M
    Here you use A, B to range over *types* and M to range over *terms*,
    the exact opposite of what is done elsewhere.
    You may lose points if you do this on the exam.
[3] You don't check erasure
[4] You used Church encoding, when problem asked for Scott encoding
[5] This is not what the problem requested. The idea was to translate
    these to the existing language, as was done with naturals and
    fixpoints, not to add new terms. If adding new terms, as you did,
    you must also add reductions, which you did not!
