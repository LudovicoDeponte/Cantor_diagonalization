# Cantor's Diagonalization
Made for the Summer Semester project [Formalizing and Proving Theorems in Coq](https://msclogic.illc.uva.nl/current-students/courses/projects/project/198/2nd-Semester-2021-22-Formalizing-and-Proving-Theorems-in-Coq) by [Tobias Kappé](https://tobias.kap.pe/index.html) for the Master of Logic at ILLC, Amsterdam.

The first time I saw Cantor's diagonal argument to prove that Reals are uncountable I was stunned by the intuitiveness, simplicity and beauty of the proof.

## Contents
 - uncountability of sequences of natural numbers
 - uncountability of the power set of natural numbers

In the `short` folder, compressed proofs for the results are included.

## Usage
After downloading the repo, open a terminal in it (I used an opam switch with ocaml.4.13.1 and coq 8.18.8 installed).
Run `coq_makefile -f _CoqProject -o CoqMakefile` to generate a make file and `make -f CoqMakefile` to build the project.

## TODO
Add diagonal argument for uncountability of reals.

## Bibliography
TODO: add bibliography
