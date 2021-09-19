
currently suspect that:
* par-reduction holds, (so confulent, so type sound)
* the very lazy whfn is enough for the minimal implementation

would like:
* to have a formal notion of the extentionality availible
* a cleaner way to collect counterexamples when there is not an absolute failure
  * also a way to change the eagarness of checking
* to have some kind of typeing notion for the untyped traces
* consolidate casts and checks
* a notion of internal vs external observation.  If something uses weak typing internally it is less of an issue then if the weak typeing leaks 
for example
```
\ x. 
  let badhead ls = ...
  in badhead [x,4,5]
```
vs.
```
\ x. 
  let badhead ls = ...
  in badhead x
```



