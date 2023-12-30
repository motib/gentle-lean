# A Gentle Tutorial on Lean

Moti Ben-Ari

_https://www.weizmann.ac.il/sci-tea/benari/_

Copyright 2023 by Moti Ben-Ari.

This work is licensed under a Creative Commons Attribution 4.0 International License. To view a copy of this license, visit _http://creativecommons.org/licenses/by/4.0/_.

### Overview

Lean 4 is a *proof assistant*. You enter your proof into Lean in a formal language and the system checks the correctness of the proof. It displays the current set of hypotheses and goals, and it is capable of performing many simple proofs automatically. This tutorial is, as its name states, a gentle introduction to Lean intended for students and others who have no previous experience with a proof assistant.

Complete Lean proofs of six theorems of arithmetic and logic are given. The source code of the proofs (which can be found in directory `Projects`) is heavily commented and additional explanations are given. Proof tactics are introduced one at a time as needed as are tips on syntactical issues. No attempt is made to present Lean constructs in their full generality.

Tables of keyboard shortcuts, tactics and tips are given in the appendices.

### Formatting notes

Care must be taken when formatting Lean source code which uses a large set of Unicode symbols. The preamble includes
```
\usepackage{fontspec}
\usepackage{mathpazo}

\setromanfont{Palatino Linotype}
\setmonofont{FreeMono}

\usepackage{fancyvrb}
\fvset{frame=lines,numbers=left,xleftmargin=2em,samepage=true}
\DefineShortVerb{\!}
```
My favorite font is Palatino whose mathematics version is `mathpazo`. `FreeMono` is the best font I found for rendering verbatim Unicode. `\fancyvrb` enables line numbers and frames around the code.

**Important** Format the tutorial with XeLaTeX ! 
"# gentle-lean" 
