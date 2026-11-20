# §2 Łukasiewicz logic and continuous logic

Paper §2 (arXiv pp. 4–5) introduces Łukasiewicz propositional logic (connectives $\dot-$ and $\neg$) and continuous propositional logic (adding $\tfrac12$), with truth assignments into $[0,1]$, models, satisfiability and semantic entailment. In Lean each logic is an inductive type of formulae over an arbitrary type $I$ of propositional variables, with a recursive evaluation map.

@import "Section2.svg" {code_block=false, caption="Module dependencies within §2"}

Subsections follow Lean import order; labels are mathematical English.

- [Formulae of continuous propositional logic](Section2/CLPropForm.md)
- [Truth assignments for continuous propositional logic](Section2/CLPropFormEval.md)
- [Models, satisfiability and entailment for continuous logic](Section2/CLPropFormModels.md)
- [Formulae of Łukasiewicz propositional logic](Section2/LukPropForm.md)
- [Truth assignments for Łukasiewicz logic](Section2/LukPropFormEval.md)
- [Models, satisfiability and entailment for Łukasiewicz logic](Section2/LukPropFormModels.md)
