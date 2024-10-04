# goldbach_tm27

https://gist.github.com/anonymous/a64213f391339236c2fe31f8749a0df6
give a 27-state Turing machine which halts if, and only if, Goldbach's conjecture is false,

This repo verifies the 27-state and 31-state Turing mahcine formally in lean4

## Verify the proof

```
# main results at `GoldbachTm/Tm27/Content.lean`
lake build
```


## Run simulator

```
lake exe sim27
lake exe sim31
```

## Inspiration

[wiki](https://en.wikipedia.org/wiki/Busy_beaver) say 

>  A 43-state Turing machine has been constructed that halts if, and only if, Goldbach's conjecture is false, and a 27-state machine for that conjecture has been proposed **but not yet verified**.

Now it should be modified to 

>  A 43-state Turing machine has been constructed that halts if, and only if, Goldbach's conjecture is false, and a 27-state machine for that conjecture has been proposed and **verified in lean4**.

## Note

This repo doesn't 
- solve Goldbach's conjecture
- help solve Goldbach's conjecture, because understanding 27-state turing machine is more difficult than Goldbach's conjecture

