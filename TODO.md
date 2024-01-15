clean up the bin output
https://www.tweag.io/blog/2023-06-15-ghc-libfuzzer/


time permitting
* better motive inference / syntactic sugar for function by cases
* unseen pattern generation
  * does not specialize the cases where the type is unique
  * can extend `whnf` with info to track wich vars sould be expanded to "unstick" computations
* needs more testing
  * exampels in CH5 of thesis
  * earier examples
* nested cases need to be tested
* better warning/error messages
  * consolodate and order warnings
  * var printing bugs
* fully worked system F interperter
* clean could also rela some unions?




fix the redme (depricate the `:ls`) update the repl example
fix the repo

find or create a large bank of test cases?
* system F
* CC

move to more standard libs
* https://github.com/haskell/pretty as in https://github.com/lambdageek/unbound-generics/blob/master/examples/Nanevski.lhs#L1080
* smantic source
* check this out http://leventerkok.github.io/sbv/ (no higher order?)
