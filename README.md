# Boblang

An implementation of FPC (PCF + recursive types) by value, with a encoding of by
name thanks to a computation/value modality.

Written after following a lecture of Robert "Bob" Harper in OPLSS 2019.

## Language features

Boblang comes with:

- support for modern state-of-the-art technology such as pairs and binary sum
  types
- recursive functions (fixpoint operator not included)
- a messy grammar which is a mix of Coq, OCaml and lambda-calculus
- a wonky parser with terrible error messages
- a mean typechecker and an unbounded interpreter
- source files ending in .bob
- a glorious standard library called libob

See also `examples/example.bob` for a a basic introduction.

## Usage 

Compile with `dune build boblang.exe`  
Execute with `dune exec ./boblang.exe source.bob`  

## Usefulness

As a proof that this language is very useful to do things,
`examples/brainfuck.bob` contains a Brainfuck interpreter written in Boblang.

With it, you can run the Brainfuck program contained in `examples/hello.fuck`  
`dune exec ./boblang.exe examples/brainfuck.bob < examples/hello.fuck`  
After consuming 100% of one of your CPUS for approximately one minute, it should
eventually manage to print "Hello world!".
