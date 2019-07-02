Guilherme Horta Alvares da Silva
Well done. 5/5

* Assignment 3.

  + Lambda
    - `mul` (recommended) ok
    - `mulᶜ`
    - `primed` (stretch) good
    - `_[_:=_]′` (stretch) excellent
    - `—↠≲—↠′` ok
    - `plus-example` excellent
    - `Context-≃`
    - `mul-type` (recommended) ok [1]
    - `mulᶜ-type`

  + Properties
    - `Progress-≃` ok
    - `progress′` ok [2]
    - `value?` ok [3]
    - `subst′` (stretch) excellent
    - `mul-example` (recommended)
    - `progress-preservation`
    - `subject-expansion` ok
    - `stuck` ok [4]
    - `unstuck` (recommended) ok [5]

[1] Hard to read. Better to bind ⊢m, ⊢n, etc. I wouldn't bother to bind m, n, etc.
[2] The intention was to write progress′ _without_ using the isomorphism,
    then to compare with progress.
[3] More compact to use progress in the definition rather than induction.
[4] The term you give is well-typed but not closed
[5] Easier if preserves doesn't induct on term.
