# SeCaV Prover
This is an automated theorem prover for the SeCaV system for first-order logic.

## Compilation
The prover is implemented in Isabelle and Haskell.

To compile the prover, you will need the following programs:
* A Haskell compiler (ghc)
* The Isabelle proof assistant (isabelle)
* The Cabal build system (cabal)
* The Make build system (make)

Additionally, the Archive of Formal Proof must be installed and available to Isabelle.

If all of these are available, the prover can be compiled by invoking `make`.

## Usage
The prover can be run by providing it with a formula in SeCaV Unshortener syntax, e.g.:
```
./secav-prover "Imp p p"
```
The prover will then output a proof of the formula in SeCaV Unshortener syntax on standard output.

If you would like the proof in Isabelle syntax instead, you may give a filename to write an Isabelle proof to using the `-i` switch, e.g.:
```
./secav-prover "Imp p p" -i Proof.thy
```
The generated file can then be opened in Isabelle to verify the proof.
To do so, the SeCaV theory must be available to Isabelle, e.g. by placing the theory in the same folder as the generated file.
