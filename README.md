# refinery

`refinery` is a toolkit for building proof refinement/proof automation systems, based roughly on the [
Algebraic Foundations of Proof Refinement](https://arxiv.org/abs/1703.05215).

## Overview
The main datatype of the library is `TacticT goal extract m a`, which is a monad transformer that behaves as a tactic.
When creating your domain-specific tactics, you should use `RuleT` and `rule` to implement them.
