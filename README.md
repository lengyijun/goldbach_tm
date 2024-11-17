# goldbach_tm25

https://gist.github.com/anonymous/a64213f391339236c2fe31f8749a0df6
give a 27-state Turing machine which halts if, and only if, Goldbach's conjecture is false.

Actually, it's a 26-state Turing machine : 22 and 24 are same state.

Furthermore, this can be optimized to 25 states, see [How to reduce 26 states to 25 states](./26_to_25.md) for details

This repo verifies the 25-state and 31-state Turing machine formally in lean4

## Verify the proof

```
# main results at `GoldbachTm/Tm25/Content.lean`
lake build
```


## Run simulator

```
lake exe sim25
lake exe sim31
```

## Inspiration

[wiki](https://en.wikipedia.org/wiki/Busy_beaver) say 

>  A 43-state Turing machine has been constructed that halts if, and only if, Goldbach's conjecture is false, and a 27-state machine for that conjecture has been proposed **but not yet verified**.

Now it should be modified to 

>  A 43-state Turing machine has been constructed that halts if, and only if, Goldbach's conjecture is false, and a **25-state** machine for that conjecture has been proposed and **verified in lean4**.

## Note

This repo doesn't 
- solve Goldbach's conjecture
- help solve Goldbach's conjecture, because understanding 25-state turing machine is more difficult than Goldbach's conjecture

