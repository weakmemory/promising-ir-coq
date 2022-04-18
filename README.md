# Simplified Promising Semantics for Compiler IR


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

### The PS model
- `src/model/TView.v`: Definition of thread views and their transitions on memory accesses
- `src/model/Memory.v`: Definition of memory and memory operations
- `src/model/Promises.v`: Definition of promises and promise/fulfill operations
- `src/model/Reserves.v`: Definition of reservations and reserve/cancel operations
- `src/model/Global.v`: Definition of a global state that is shared between threads
- `src/model/Local.v`: Definition of a local state and local transitions
- `src/model/Thread.v`: Definition of a thread and thread steps
- `src/model/Configuration.v`: Definition of a machine configuration and machine steps
- `src/model/PFConfiguration.v`: Definition of promise-free machine steps
