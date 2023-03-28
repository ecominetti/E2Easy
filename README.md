# lattice-voting-ctrsa21

Code accompannying the paper "Lattice-Based Proof of Shuffle and Applications to Electronic Voting" by Diego F. Aranha, Carsten Baum, Kristian Gjøsteen,
Tjerand Silde, and Thor Tunge accepted at CT-RSA 2021.

Depedencies are the GMP, FLINT 2.7.1, and Dilithium reference libraries. For Dilithium, some files have to be modified so it can be compiled using g++. These files are provided in the dilithiumModifiedFiles/ folder.

For building the code, run `make` inside the source directory. This sill build the binaries for `commit`, `vericrypt` and `shuffle` to test and benchmark different modules of the code.

WARNING: This is an academic proof of concept, and in particular has not received code review. This implementation is NOT ready for any type of production use.


# Modifications to original

commit_sample_short now samples uniformly in {-1,0,1}^N

voting.c shuffle run now accepts commits with different r's and uses different r's to create the intermediate commits

# Instructions to voting

run `make vote` to create voting and spoilCheck

The vote input has to be less than MODP

File voteCom is always created; openingVote is only created if vote is spoiled.
Each new vote rewrites voteCom
voteCom and the correspondent openingVote can be checked using spoilCheck.c (a vote number is used as input; if vote checks returns SUCCESS, otherwise FAIL)

Next voter input has to be 0 or 1

Maximum number of voters allowed is defined in variable VOTERS
