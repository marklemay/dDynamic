

this is a compromise implementation:
* every cast has a pocket of untyped computation
* when casts disagree, (blocking term elimination) the untyped computation will have the exact trace of what went wrong

currently suspect that:
* par-reduction holds, (so confulent, so type sound)
* the very lazy whfn is enough for the minimal implementation

would like:
* have a formal notion of the extentionality availible
* a notion of internal vs external observation.  If something uses weak typing internally it is less of an issue then if the weak typeing leaks 
for example
```
\ x. 
  let badhead ls = ...
  in badhead [x,4,5]
```

```
\ x. 
  let badhead ls = ...
  in badhead x
```



