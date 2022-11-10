# Putting Weak Memory in Order via Promising Intermediate Representation

The Coq development of the source model (vRC11) and the IR model (PSir).

## Build

- Requirement: opam (>=2.0.0), Coq 8.15.0
- Install dependencies with opam
```
./configure
```
- Build the project
```
make -j
```


## Structures

### The Source model (vRC11, Section 2)
- `src/model/TView.v`: Definition of thread views and their transitions on memory accesses
- `src/model/Memory.v`: Definition of memory and memory operations
- `src/model/Global.v`: Definition of a global state that is shared between threads
- `src/model/Local.v`: Definition of a local state and local transitions
- `src/model/Thread.v`: Definition of a thread and thread steps
- `src/model/PFConfiguration.v`: Definition of vRC11 machine steps
(consisting of thread steps except for PROMISE/RESERVE/CANCEL steps)

### The IR model (PSir, Section 3)
- `src/model/Promises.v`: Definition of promises and promise/fulfill operations
- `src/model/Reserves.v`: Definition of reservations and reserve/cancel operations
- `src/model/Configuration.v`: Definition of a machine configuration and machine steps

### Local DRF guarantees for vRC11
- `Theorem local_drf_ra` in `src/ldrfra/LocalDRFRA.v`: Local DRF-RA guarantee
- TODO: Local DRF-SC guarantee

### Adequacy of SEQ
- TODO

### Soundness of thread-local transformations on atomic accesses
- TODO
