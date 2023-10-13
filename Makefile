CPP = g++
CFLAGS = -O3 -march=native -mtune=native -Wall -ggdb -pthread
INCLUDES = bench.h cpucycles.h
BENCH = bench.c cpucycles.c
TEST = test.c
GAUSSIAN = gaussian.o fastrandombytes.c randombytes.c
LIBS = -lflint -lgmp 
DIL_LIBS = -lpqcrystals_dilithium2_ref -lpqcrystals_dilithium3_ref -lpqcrystals_dilithium5_ref -lpqcrystals_dilithium2aes_ref \
	-lpqcrystals_dilithium3aes_ref -lpqcrystals_dilithium5aes_ref -lpqcrystals_fips202_ref -lpqcrystals_aes256ctr_ref
DILITHIUM_PATH = ./dilithium/ref/

all: commit encrypt vericrypt shuffle voting
vote: voting spoilCheck

commit: commit.c ${TEST} ${BENCH} ${INCLUDES} gaussian_ct.cpp
	${CPP} ${CFLAGS} -DSIGMA_PARAM=SIGMA_C -c gaussian_ct.cpp -o gaussian.o
	${CPP} ${CFLAGS} -DMAIN commit.c ${GAUSSIAN} ${TEST} ${BENCH} -o commit ${LIBS}

encrypt: encrypt.c ${TEST} ${BENCH} ${INCLUDES}
	${CPP} ${CFLAGS} -DMAIN encrypt.c ${TEST} ${BENCH} -o encrypt ${LIBS}

vericrypt: vericrypt.c encrypt.c ${TEST} ${BENCH} ${INCLUDES} gaussian_ct.cpp
	${CPP} ${CFLAGS} -DSIGMA_PARAM=SIGMA_E -c gaussian_ct.cpp -o gaussian.o
	${CPP} ${CFLAGS} -c encrypt.c -o encrypt.o
	${CPP} ${CFLAGS} -DMAIN vericrypt.c encrypt.o sha224-256.c ${GAUSSIAN} ${TEST} ${BENCH} -o vericrypt ${LIBS}

shuffle: shuffle.c commit.c ${TEST} ${BENCH}
	${CPP} ${CFLAGS} -DSIGMA_PARAM=SIGMA_C -c gaussian_ct.cpp -o gaussian.o
	${CPP} ${CFLAGS} shuffle.c commit.c sha224-256.c ${GAUSSIAN} ${TEST} ${BENCH} -o shuffle ${LIBS}

voting: voting.c commit.c ${TEST} ${BENCH}
	${CPP} ${CFLAGS} -DSIGMA_PARAM=SIGMA_C -c gaussian_ct.cpp -o gaussian.o
	${CPP} ${CFLAGS} -c commit.c -o commit.o ${LIBS}
	${CPP} ${CFLAGS} -DMAIN voting.c commit.o sha224-256.c sha384-512.c ${GAUSSIAN} ${TEST} ${BENCH} -o voting ${LIBS}

votingSimulator: votingSimulator.c commit.c ${TEST} ${BENCH}
	${CPP} ${CFLAGS} -DSIGMA_PARAM=SIGMA_C -c gaussian_ct.cpp -o gaussian.o
	${CPP} ${CFLAGS} -c commit.c -o commit.o ${LIBS}
	${CPP} ${CFLAGS} -DMAIN votingSimulator.c commit.o sha224-256.c sha384-512.c ${GAUSSIAN} ${TEST} ${BENCH} -o votingSimulator ${LIBS}

APISimulator: APITest.c APISimulator.c APISimulator.h commit.c
	${CPP} ${CFLAGS} -DSIGMA_PARAM=SIGMA_C -c gaussian_ct.cpp -o gaussian.o
	${CPP} ${CFLAGS} -L${DILITHIUM_PATH} -I${DILITHIUM_PATH} APITest.c APISimulator.c commit.c sha224-256.c sha384-512.c ${GAUSSIAN} ${DIL_LIBS} ${LIBS} -o APITest 

spoilCheck: spoilCheck.c commit.c ${TEST} ${BENCH}
	${CPP} ${CFLAGS} -DSIGMA_PARAM=SIGMA_C -c gaussian_ct.cpp -o gaussian.o
	${CPP} ${CFLAGS} -c commit.c -o commit.o ${LIBS}
	${CPP} ${CFLAGS} -DMAIN spoilCheck.c commit.o sha224-256.c ${GAUSSIAN} ${TEST} ${BENCH} -o spoilCheck ${LIBS}

clean:
	rm *.o commit encrypt vericrypt shuffle voting spoilCheck votingSimulator APISimulator APITest
