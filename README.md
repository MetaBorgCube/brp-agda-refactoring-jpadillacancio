# Correct-by-construction refactoring of Maybe To List terms in a Haskell Like Language

> This thesis was part of the 2022/2023 edition of the [CSE3000 (Bsc Research Project)](https://cse3000-research-project.github.io/2023/Q4) course at Delft University of Technology.


This repository contains the source code for my bachelors thesis on correct-by-construction refactoring of functional code. It defines a small Haskell-like language (as a lambda calculus), a refactoring operation swapping out `MaybeTy` terms to `ListTy` terms and formally verifies that its dynamic semantic behaviour behaves as we would expect it to.

I use intrinsically typed syntax and big step semantics in the language definition. The type system and syntax are defined in [Typesystem.agda](./src/Language/Typesystem.agda). The big step semantics are defined in [Semantics.agda](./src/Language/Semantics.agda).

The refactoring function is defined in [Refactor.agda](./src/Verification/Refactor.agda) and the semantic proof in [Proof.agda](./src/Verification/Proof.agda).
## Versions of software used

This project was edited and compiled originally on Agda version 2.6.0.1. We make use of the Agda standard library version 1.2. 

## License

This source code is licensed under the MIT license. The full license text is available in the [LICENSE.md](./LICENSE.md) file
