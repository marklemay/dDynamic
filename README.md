# dDynamic
[![Haskell CI](https://github.com/marklemay/dDynamic/actions/workflows/haskell.yml/badge.svg)](https://github.com/marklemay/dDynamic/actions/workflows/haskell.yml)

a minimal dependently typed langugage were deffintional equality can be resolved dynamically at runtime.

## REPL
To load the surface repl
```
cabal new-run repl
```
supports commands for 
* loading files, cast elaboration `:l`
* loading files, with surface typechecking `:ls`
* quiting `:q`
* checking types `:t`
* normalizing expressions `:n`
* entering an expression with attemopt to get all information from it

for example
```
dt-surface> :ls ex/ex1.dt
parsed
typechecked
loaded
dt-surface> :t not
Right (not!,boool -> boool)
dt-surface> :n not ttrue
Right flasle
dt-surface> not (not (ttrue))
Right (not! (not! ttrue),boool)
Right ttrue
```

## Conrtibute
To run the haskell project: ```cabal new-repl```

To run the test suit: ```cabal new-test```

