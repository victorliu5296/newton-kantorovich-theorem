# newton_kantorovich_theorem
Repository for the proof formalization of the Newton-Kantorovich theorem in Lean 4.

# Credits
I am so grateful to the following people for helping me with this project:
- All the Mathlib contributors for their development of the amazing mathlib library and the creators of the Lean language.
- Kevin Buzzard and Yury Kudryashov for helping me solve so many type errors and answering my numerous questions. Without them, I could not have gotten any far.
- Edward van de Meent, Kalle Kytölä, Michal Wallace (tangentstorm), Luigi Massacci, Yakov Pechersky, Floris van Doorn, Jireh Loreaux, Michael Stoll for helping answer my questions on the Lean zulip channel.
- Morph Labs for creating Moogle, a semantic search tool that helped me so much with finding the right lemmas.
- The LeanSearch team, who publically released their LLM-powered search engine which really streamlined searching for results in Mathlib during the later stages of this project.
- Anthropic and OpenAI for their amazing LLMs, without which this project probably take at least 3 times longer to finish (for learning Lean syntax, debugging, development in general), at which point I probably would have given up.

## References
The proof of the one constant Newton-Kantorovich theorem is based on the following paper:
```bibtex
@article{doi:10.1142/S0219530512500121,
author = {CIARLET, PHILIPPE G. and MARDARE, CRISTINEL},
title = {ON THE NEWTON–KANTOROVICH THEOREM},
journal = {Analysis and Applications},
volume = {10},
number = {03},
pages = {249-269},
year = {2012},
doi = {10.1142/S0219530512500121},

URL = {https://www.ljll.fr/mardare/recherche/pdf/NK_AA.pdf}
}
```