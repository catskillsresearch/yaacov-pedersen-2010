# §1 Introduction

Paper §1 (arXiv pp. 1–4) motivates continuous first-order logic and states the goals: completeness, approximated strong completeness and decidability. The only Lean needed from §1 is real truncated subtraction and the two closure facts for the unit interval, which every later truth-value computation uses.

@import "Section1.svg" {code_block=false, caption="Module dependencies within §1"}

Subsections follow Lean import order; labels are mathematical English.

- [Truncated subtraction on the reals](Section1/TsubR.md)
- [Closure of the unit interval under negation and halving](Section1/UnitInterval.md)
- [Shared preliminaries](Section1/Basic.md)
