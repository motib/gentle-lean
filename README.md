# A Gentle Tutorial on Lean

Moti Ben-Ari

_https://www.weizmann.ac.il/sci-tea/benari/_

Copyright 2023 by Moti Ben-Ari.

This work is licensed under a Creative Commons Attribution 4.0 International License. To view a copy of this license, visit _http://creativecommons.org/licenses/by/4.0/_.

### Overview

Lean 4 is a *proof assistant*. You enter your proof into Lean in a formal language and the system checks the correctness of the proof. It displays the current set of hypotheses and goals, and it is capable of performing many simple proofs automatically. This tutorial is, as its name states, a gentle introduction to Lean intended for students and others who have no previous experience with a proof assistant, though a basic knowledge of propositional and first-order logic is assumed.

Constructs of Lean are explained and demonstrated within complete proofs of theorems of arithmetic and logic. The source code is heavily commented and additional explanations are given. As you gain more experience with Lean, the number of comments on a proof is reduced. Proof tactics are introduced one at a time as needed. Tables of keyboard shortcuts, tactics and tips are given in the appendices. The tips include information on definitions and notations used by Lean.

The Lean source code is in directory `Projects`.

### Formatting notes

**Format the tutorial with XeLaTeX.**

The preamble of the XeLaTeX source code includes:
```
\usepackage{fontspec}
\usepackage{mathpazo}

\setromanfont{Palatino Linotype}
\setmonofont{FreeMono}

\usepackage{fancyvrb}
\fvset{frame=lines,numbers=left,xleftmargin=2em,samepage=true}
\DefineShortVerb{\!}
```
`mathpazo` is the Palatino font. `FreeMono` is used to render verbatim Unicode. `\fancyvrb` enables line numbers and frames around the code.

