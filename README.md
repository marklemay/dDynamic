# dDynamic
[![Haskell CI](https://github.com/marklemay/dDynamic/actions/workflows/haskell.yml/badge.svg)](https://github.com/marklemay/dDynamic/actions/workflows/haskell.yml)

a minimal dependently typed langugage where deffintional equality can be resolved dynamically at runtime.

The project is tested in the following environments:
- GHC 9.6.1 and cabal 3.10.1.0

## REPL

To load the surface repl
```
cabal new-run repl
```
supports commands for 
* loadfiles, cast elaboration `:l`
* quit `:q`
* check type of an expression `:t`
* normalize expression `:n`
* enter an expression without a prefix with attemopt to get all information from it, typing/normalization/..

for example
```
dt-surface> :l ex/a0.dt
parsed
elaborated
cleaned
loaded
dt> :t not
not : Bool -> Bool
dt> :n not true
not true
 : Bool
~>
false
dt> not (not (true))
not (not true)
 : Bool
~>
true
```

## Conrtibute
To run the haskell project: ```cabal new-repl```

To run the test suit: ```cabal new-test```

