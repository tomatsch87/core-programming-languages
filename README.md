# Core Programming Languages

A collection of implementations from core programming languages and models of computation in Haskell.

## Overview

This project implements various programming language cores and computational models, showcasing the theoretical foundations that underlie modern programming languages. The implementations include a Turing machine, a simple imperative core language (IMP), and a functional core language (KFPT) based on lambda calculus. Additionally to these, there are implementations of the Church encoding and contextual equivalence analysis for lambda expressions.

## Implementations

### Functional Programming Models

#### Lambda Calculus (`LambdaCalculus.hs`)

The foundation of functional programming.

#### Church Encoding (`ChurchEncoding.hs`)

An implementation of the Church encoding for Lambda calculus, demonstrating its Turing completeness.

#### KFPT (`KFPT.hs`)

An extension of the Lambda calculus to a simple functional core programming language with data type representations and call-by-name evaluation.

#### Contextual Equivalence (`RefuteConEq.hs`)

Tools for analyzing and refuting contextual equivalence between lambda expressions.

### Imperative Programming Models

#### IMP (`IMP.hs`)

A simple imperative programming language implementation.

### Models of Computation

#### Turing Machine (`TM.hs`)

An implementation of the Turing machine computational model.

## Usage

Load the modules in GHCi to experiment with them:

```bash
ghci LambdaCalculus.hs
```

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.
