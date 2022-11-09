#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define _LARGE_TIME_API
#include <time.h>

#include "param.h"
#include "commit.h"
#include "test.h"
#include "bench.h"
#include "assert.h"
#include "gaussian.h"
#include "fastrandombytes.h"
#include "sha.h"

#define VOTERS 3000
#define TRUE 1
#define FALSE 0

static int voteNumber;
static uint8_t H0[SHA512HashSize];
static uint8_t Hcurrent[SHA512HashSize];
static uint32_t RDV[VOTERS];

typedef struct _VoteTable {
	commit_t commit;
	pcrt_poly_t r[WIDTH];
	nmod_poly_t vote;
	uint8_t trackingCode[SHA512HashSize];
	uint32_t timer;
} VoteTable;

void initializeVoteTable(VoteTable *vTable){
	for (int i = 0; i < 2; i++) {
		nmod_poly_init(vTable->commit.c1[i], MODP);
		nmod_poly_init(vTable->commit.c2[i], MODP);
		nmod_poly_zero(vTable->commit.c1[i]);
		nmod_poly_zero(vTable->commit.c2[i]);
		nmod_poly_fit_length(vTable->commit.c1[i],DEGCRT);
		nmod_poly_fit_length(vTable->commit.c2[i],DEGCRT);
		for (int j = 0; j < WIDTH; j++){
			nmod_poly_init(vTable->r[j][i], MODP);
			nmod_poly_zero(vTable->r[j][i]);
		}
	}
	nmod_poly_init(vTable->vote, MODP);
	nmod_poly_zero(vTable->vote);
	for (int i = 0; i < SHA512HashSize; i++) {
		vTable->trackingCode[i]=0x00;
	}
	vTable->timer=0x00;
}

/* Function to sort an array using insertion sort */
void insertionSort(uint32_t arr[], int n)
{
	int i, key, j;
	for (i = 1; i < n; i++) {
		key = arr[i];
		j = i - 1;

		/* Move elements of arr[0..i-1], that are greater than key,
		   to one position ahead of their current position */
		while (j >= 0 && arr[j] > key) {
			arr[j + 1] = arr[j];
			j = j - 1;
		}
		arr[j + 1] = key;
	}
}

void randPoly (nmod_poly_t poly, flint_rand_t rand, int size) {
	int flag;
	int lim = 50;

	do {
		flag=0;
		nmod_poly_randtest(poly,rand,size);
		for (int j = 0; j < DEGREE && flag<lim; j++) {
			if (nmod_poly_get_coeff_ui(poly,j)==0) {
				flag++;
			}
		}
	} while (flag==lim);
}

void shuffle_hash(nmod_poly_t d[2], commitkey_t *key, commit_t x, commit_t y,
		nmod_poly_t alpha, nmod_poly_t beta, nmod_poly_t u[2],
		nmod_poly_t t[2], nmod_poly_t _t[2]) {
	SHA256Context sha;
	uint8_t hash[SHA256HashSize];
	nmod_poly_t f;
	uint32_t buf;

	nmod_poly_init(f, MODP);
	SHA256Reset(&sha);

	/* Hash public key. */
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			for (int k = 0; k < 2; k++) {
				SHA256Input(&sha, (const uint8_t*)key->B1[i][j][k]->coeffs, key->B1[i][j][k]->alloc * sizeof(uint64_t));
			}
		}
	}

	/* Hash alpha, beta from linear relation. */
	SHA256Input(&sha, (const uint8_t*)alpha->coeffs, alpha->alloc * sizeof(uint64_t));
	SHA256Input(&sha, (const uint8_t*)beta->coeffs, beta->alloc * sizeof(uint64_t));

	/* Hash [x], [x'], t, t' in CRT representation. */
	for (int i = 0; i < 2; i++) {
		SHA256Input(&sha, (const uint8_t*)x.c1[i]->coeffs, x.c1[i]->alloc * sizeof(uint64_t));
		SHA256Input(&sha, (const uint8_t*)x.c2[i]->coeffs, x.c2[i]->alloc * sizeof(uint64_t));
		SHA256Input(&sha, (const uint8_t*)y.c1[i]->coeffs, y.c1[i]->alloc * sizeof(uint64_t));
		SHA256Input(&sha, (const uint8_t*)y.c2[i]->coeffs, y.c2[i]->alloc * sizeof(uint64_t));
		SHA256Input(&sha, (const uint8_t*)u[i]->coeffs, u[i]->alloc * sizeof(uint64_t));
		SHA256Input(&sha, (const uint8_t*)t[i]->coeffs, t[i]->alloc * sizeof(uint64_t));
		SHA256Input(&sha, (const uint8_t*)_t[i]->coeffs, _t[i]->alloc * sizeof(uint64_t));
	}

	SHA256Result(&sha, hash);

	/* Sample challenge from RNG seeded with hash. */
	nmod_poly_zero(f);

	fastrandombytes_setseed(hash);
	for (int i = 0; i < 2; i++) {
		nmod_poly_fit_length(d[i], DEGREE);
		for (int j = 0; j < NONZERO; j++) {
			fastrandombytes((unsigned char *)&buf, sizeof(buf));
			buf = buf % DEGREE;
			while (nmod_poly_get_coeff_ui(d[i], buf) != 0) {
				fastrandombytes((unsigned char *)&buf, sizeof(buf));
				buf = buf % DEGREE;
			}
			nmod_poly_set_coeff_ui(d[i], buf, 1);
		}
	}
	nmod_poly_sub(f, d[0], d[1]);
	nmod_poly_rem(d[0], f, *commit_irred(0));
	nmod_poly_rem(d[1], f, *commit_irred(1));
	nmod_poly_clear(f);
}

static void prover_lin(nmod_poly_t y[WIDTH][2], nmod_poly_t _y[WIDTH][2],
		nmod_poly_t t[2], nmod_poly_t _t[2], nmod_poly_t u[2],
		commit_t x, commit_t _x, commitkey_t *key,
		nmod_poly_t alpha, nmod_poly_t beta, nmod_poly_t r[WIDTH][2], nmod_poly_t _r[WIDTH][2], int l) {
	nmod_poly_t tmp, d[2];

	nmod_poly_init(tmp, MODP);
	for (int i = 0; i < 2; i++) {
		nmod_poly_init(d[i], MODP);
		nmod_poly_zero(t[i]);
		nmod_poly_zero(_t[i]);
		nmod_poly_zero(u[i]);
	}

	for (int i = 0; i < WIDTH; i++) {
		commit_sample_gauss_crt(y[i]);
		commit_sample_gauss_crt(_y[i]);
	}
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			for (int k = 0; k < 2; k++) {
				nmod_poly_mulmod(tmp, key->B1[i][j][k], y[j][k], *commit_irred(k));
				nmod_poly_add(t[k], t[k], tmp);
				nmod_poly_mulmod(tmp, key->B1[i][j][k], _y[j][k], *commit_irred(k));
				nmod_poly_add(_t[k], _t[k], tmp);
			}
		}
	}

	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_mulmod(tmp, key->b2[i][j], y[i][j], *commit_irred(j));
			nmod_poly_mulmod(tmp, tmp, alpha, *commit_irred(j));
			nmod_poly_add(u[j], u[j], tmp);
			nmod_poly_mulmod(tmp, key->b2[i][j], _y[i][j], *commit_irred(j));
			nmod_poly_sub(u[j], u[j], tmp);
		}
	}

	/* Sample challenge. */
	shuffle_hash(d, key, x, _x, alpha, beta, u, t, _t);

	/* Prover */
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_mulmod(tmp, d[j], r[i][j], *commit_irred(j));
			nmod_poly_add(y[i][j], y[i][j], tmp);
			nmod_poly_mulmod(tmp, d[j], _r[i][j], *commit_irred(j));
			nmod_poly_add(_y[i][j], _y[i][j], tmp);
		}
	}

	nmod_poly_clear(tmp);
	for (int i = 0; i < 2; i++) {
		nmod_poly_clear(d[i]);
	}
}

static int verifier_lin(commit_t com, commit_t x,
		nmod_poly_t y[WIDTH][2], nmod_poly_t _y[WIDTH][2],
		nmod_poly_t t[2], nmod_poly_t _t[2], nmod_poly_t u[2], commitkey_t *key,
		nmod_poly_t alpha, nmod_poly_t beta, int l, int MSGS) {
	nmod_poly_t tmp, _d[2], v[2], _v[2], z[WIDTH], _z[WIDTH];
	int result = 1;

	nmod_poly_init(tmp, MODP);
	for (int i = 0; i < WIDTH; i++) {
		nmod_poly_init(z[i], MODP);
		nmod_poly_init(_z[i], MODP);
	}
	for (int i = 0; i < 2; i++) {
		nmod_poly_init(_d[i], MODP);
		nmod_poly_init(v[i], MODP);
		nmod_poly_init(_v[i], MODP);
		nmod_poly_zero(v[i]);
		nmod_poly_zero(_v[i]);
	}

	/* Sample challenge. */
	shuffle_hash(_d, key, com, x, alpha, beta, u, t, _t);

	/* Verifier checks norm, reconstruct from CRT representation. */
	for (int i = 0; i < WIDTH; i++) {
		pcrt_poly_rec(z[i], y[i]);
		pcrt_poly_rec(_z[i], _y[i]);
		assert(commit_norm2_sqr(z[i]) <= (uint64_t)4 * DEGREE * SIGMA_C * SIGMA_C);
		assert(commit_norm2_sqr(_z[i]) <= (uint64_t)4 * DEGREE * SIGMA_C * SIGMA_C);
	}
	/* Verifier computes B1z and B1z'. */
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			for (int k = 0; k < 2; k++) {
				nmod_poly_mulmod(tmp, key->B1[i][j][k], y[j][k], *commit_irred(k));
				nmod_poly_add(v[k], v[k], tmp);
				nmod_poly_mulmod(tmp, key->B1[i][j][k], _y[j][k], *commit_irred(k));
				nmod_poly_add(_v[k], _v[k], tmp);
			}
		}
	}
	/* Verifier checks that B_1z = t + dc1, B_1z' = t' + dc1'. */
	for (int j = 0; j < 2; j++) {
		nmod_poly_mulmod(tmp, _d[j], com.c1[j], *commit_irred(j));
		nmod_poly_add(t[j], t[j], tmp);
		nmod_poly_mulmod(tmp, _d[j], x.c1[j], *commit_irred(j));
		nmod_poly_add(_t[j], _t[j], tmp);
		result &= nmod_poly_equal(t[j], v[j]);
		result &= nmod_poly_equal(_t[j], _v[j]);
	}

	if (l == 0) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_mulmod(t[j], alpha, com.c2[j], *commit_irred(j));
			nmod_poly_add(t[j], t[j], beta);
			nmod_poly_sub(t[j], t[j], x.c2[j]);
			nmod_poly_mulmod(t[j], t[j], _d[j], *commit_irred(j));
			nmod_poly_add(t[j], t[j], u[j]);
			nmod_poly_rem(t[j], t[j], *commit_irred(j));
		}
	}
	if (l > 0 && l < MSGS - 1) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_mulmod(t[j], alpha, com.c2[j], *commit_irred(j));
			nmod_poly_add(t[j], t[j], beta);
			nmod_poly_sub(t[j], t[j], x.c2[j]);
			nmod_poly_mulmod(t[j], t[j], _d[j], *commit_irred(j));
			nmod_poly_add(t[j], t[j], u[j]);
		}
	}
	if (l == MSGS - 1) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_mulmod(t[j], alpha, com.c2[j], *commit_irred(j));
			if (MSGS & 1) {
				nmod_poly_sub(t[j], t[j], beta);
			} else {
				nmod_poly_add(t[j], t[j], beta);
			}
			nmod_poly_sub(t[j], t[j], x.c2[j]);
			nmod_poly_mulmod(t[j], t[j], _d[j], *commit_irred(j));
			nmod_poly_add(t[j], t[j], u[j]);
		}
	}

	nmod_poly_zero(v[0]);
	nmod_poly_zero(v[1]);
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_mulmod(tmp, key->b2[i][j], y[i][j], *commit_irred(j));
			nmod_poly_mulmod(tmp, alpha, tmp, *commit_irred(j));
			nmod_poly_add(v[j], v[j], tmp);
			nmod_poly_mulmod(tmp, key->b2[i][j], _y[i][j], *commit_irred(j));
			nmod_poly_sub(v[j], v[j], tmp);
		}
	}
	for (int j = 0; j < 2; j++) {
		result &= nmod_poly_equal(t[j], v[j]);
	}

	nmod_poly_clear(tmp);
	for (int i = 0; i < WIDTH; i++) {
		nmod_poly_clear(z[i]);
		nmod_poly_clear(_z[i]);
	}
	for (int i = 0; i < 2; i++) {
		nmod_poly_clear(_d[i]);
		nmod_poly_clear(v[i]);
		nmod_poly_clear(_v[i]);
	}
	return result;
}

static int run(commit_t com[VOTERS], nmod_poly_t m[VOTERS], nmod_poly_t _m[VOTERS],
		nmod_poly_t r[VOTERS][WIDTH][2], commitkey_t *key, flint_rand_t rng, int MSGS) {
	FILE *zkpOutput;
	int flag, result = 1;
	commit_t d[VOTERS];
	nmod_poly_t t0, t1, rho, beta, theta[VOTERS], s[VOTERS];
	nmod_poly_t y[WIDTH][2], _y[WIDTH][2], t[2], _t[2], u[2], _r[VOTERS][WIDTH][2];
	flint_rand_t rand2;
	uint64_t buf1,buf2;

	// flint_randinit(rand2);
	// getrandom(&buf1, sizeof(buf1), 0);
	// getrandom(&buf2, sizeof(buf2), 0);
	// flint_randseed(rand2, buf1, buf2);

	nmod_poly_init(t0, MODP);
	nmod_poly_init(t1, MODP);
	nmod_poly_init(rho, MODP);
	nmod_poly_init(beta, MODP);
	for (int i = 0; i < VOTERS; i++) {
		nmod_poly_init(theta[i], MODP);
		nmod_poly_init(s[i], MODP);
	}
	for (int i = 0; i < 2; i++) {
		nmod_poly_init(t[i], MODP);
		nmod_poly_init(_t[i], MODP);
		nmod_poly_init(u[i], MODP);
	}
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_init(y[i][j], MODP);
			nmod_poly_init(_y[i][j], MODP);
		}
	}
	for (int w = 0; w < VOTERS; w++) {
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_init(_r[w][i][j], MODP);
			}
		}
	}

	zkpOutput = fopen("ZKPOutput", "w");
	if (zkpOutput == NULL) {
		printf("Error\n");
	}

	/* Verifier samples \rho that is different from the messages, and \beta. */
	do {
		flag = 1;
		commit_sample_rand(rho, rng);
		for (int i = 0; i < MSGS; i++) {
			if (nmod_poly_equal(rho, _m[i]) == 1) {
				flag = 0;
			}
		}
	} while (flag == 0);

	fwrite(rho->coeffs, sizeof(uint32_t), rho->length,zkpOutput);
	// for (int coeff = 0; coeff < rho->length; coeff++) {
	// 	fprintf(zkpOutput, "%08llx\n", rho->coeffs[coeff]);
	// }
	// fprintf(zkpOutput, "rho\n");
	// nmod_poly_fprint(zkpOutput,rho);
	// fprintf(zkpOutput, "\n");



	/* Prover shifts the messages by rho and shuffles them. */
	for (int i = 0; i < MSGS; i++) {
		nmod_poly_sub(m[i], m[i], rho);
		nmod_poly_sub(_m[i], _m[i], rho);
	}


	/* Verifier shifts the commitment by rho. */
	for (int i = 0; i < MSGS; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_rem(t0, rho, *commit_irred(j));
			nmod_poly_sub(com[i].c2[j], com[i].c2[j], t0);
		}
	}


	/* Prover samples theta_i and computes commitments D_i. */
	commit_sample_rand(theta[0], rng);
	nmod_poly_mulmod(t0, theta[0], _m[0], *commit_poly());
	for (int j = 0; j < WIDTH; j++) {
		commit_sample_short_crt(_r[0][j]);
	}
	commit_doit(&d[0], t0, key, _r[0]);

	for (int i = 1; i < MSGS - 1; i++) {
		commit_sample_rand(theta[i], rng);
		nmod_poly_mulmod(t0, theta[i - 1], m[i], *commit_poly());
		nmod_poly_mulmod(t1, theta[i], _m[i], *commit_poly());
		nmod_poly_add(t0, t0, t1);
		for (int j = 0; j < WIDTH; j++) {
  		commit_sample_short_crt(_r[i][j]);
  	}
		commit_doit(&d[i], t0, key, _r[i]);
	}


	nmod_poly_mulmod(t0, theta[MSGS - 2], m[MSGS - 1], *commit_poly());
	for (int j = 0; j < WIDTH; j++) {
		commit_sample_short_crt(_r[MSGS - 1][j]);
	}
	commit_doit(&d[MSGS - 1], t0, key, _r[MSGS - 1]);

	// for (int a = 0; a < MSGS - 1; a++){
	// 	printf("\nTheta[%d]\n", a);
	// 	nmod_poly_print(theta[a]);
	// 	printf("\n\n");
	// }


	commit_sample_rand(beta, rng);

	// nmod_poly_print(beta);
	// printf("\n");
	// commit_sample_rand(beta, rand2);
	// nmod_poly_print(beta);
	// nmod_poly_randtest(beta, rand2, 1024);
	// printf("\n");
	// nmod_poly_print(beta);
	// nmod_poly_randtest(beta, rand2, 1024);
	// printf("\n");
	// nmod_poly_print(beta);
	// nmod_poly_randtest(beta, rand2, 1024);
	// printf("\n");
	// nmod_poly_print(beta);
	// printf("\n\n");

	fwrite(beta->coeffs, sizeof(uint32_t), beta->length,zkpOutput);
	// fprintf(zkpOutput, "alfa\n");
	// nmod_poly_fprint(zkpOutput,beta);
	// // nmod_poly_print(beta);
	// fprintf(zkpOutput, "\n");
	// fprintf(zkpOutput, "s_i, i < %d\n", MSGS);

	nmod_poly_mulmod(s[0], theta[0], _m[0], *commit_poly());
	nmod_poly_mulmod(t0, beta, m[0], *commit_poly());
	nmod_poly_sub(s[0], s[0], t0);
	nmod_poly_invmod(t0, _m[0], *commit_poly());
	nmod_poly_mulmod(s[0], s[0], t0, *commit_poly());
	fwrite(s[0]->coeffs, sizeof(uint32_t), s[0]->length,zkpOutput);
	// nmod_poly_fprint(zkpOutput,s[0]);
	for (int i = 1; i < MSGS - 1; i++) {
		nmod_poly_mulmod(s[i], theta[i - 1], m[i], *commit_poly());
		nmod_poly_mulmod(t0, theta[i], _m[i], *commit_poly());
		nmod_poly_add(s[i], s[i], t0);
		nmod_poly_mulmod(t0, s[i - 1], m[i], *commit_poly());
		nmod_poly_sub(s[i], s[i], t0);
		nmod_poly_invmod(t0, _m[i], *commit_poly());
		nmod_poly_mulmod(s[i], s[i], t0, *commit_poly());
		fwrite(s[i]->coeffs, sizeof(uint32_t), s[i]->length,zkpOutput);
		// nmod_poly_fprint(zkpOutput,s[i]);
	}
	if (MSGS > 2) {
		nmod_poly_mulmod(s[MSGS - 1], theta[MSGS - 2], m[MSGS - 1], *commit_poly());
		nmod_poly_mulmod(t0, beta, _m[MSGS - 1], *commit_poly());
		if (MSGS & 1) {
			nmod_poly_sub(s[MSGS - 1], s[0], t0);
		} else {
			nmod_poly_add(s[MSGS - 1], s[0], t0);
		}
		nmod_poly_invmod(t0, m[MSGS - 1], *commit_poly());
		nmod_poly_mulmod(s[MSGS - 1], s[MSGS - 1], t0, *commit_poly());
		fwrite(s[MSGS - 1]->coeffs, sizeof(uint32_t), s[MSGS - 1]->length,zkpOutput);
		// nmod_poly_fprint(zkpOutput,s[MSGS - 1]);
	}
	// fprintf(zkpOutput, "\n");
	// fprintf(zkpOutput, "D_i, t, t', u, z, z' (d not required - FiatShamir)\n");

	/* Now run \Prod_LIN instances, one for each commitment. */
	for (int l = 0; l < MSGS; l++) {
		if (l < MSGS - 1) {
			nmod_poly_mulmod(t0, s[l], _m[l], *commit_poly());
		} else {
			nmod_poly_mulmod(t0, beta, _m[l], *commit_poly());
		}

		if (l == 0) {
			prover_lin(y, _y, t, _t, u, com[0], d[0], key, beta, t0, r[0], _r[0], l);
			result &= verifier_lin(com[0], d[0], y, _y, t, _t, u, key, beta, t0, l, MSGS);

			for (int i = 0; i < 2; i++) {
				fwrite(d[0].c1[i]->coeffs, sizeof(uint32_t), d[0].c1[i]->length,zkpOutput);
				fwrite(d[0].c2[i]->coeffs, sizeof(uint32_t), d[0].c2[i]->length,zkpOutput);
				fwrite(t[i]->coeffs, sizeof(uint32_t), t[i]->length,zkpOutput);
				fwrite(_t[i]->coeffs, sizeof(uint32_t), _t[i]->length,zkpOutput);
				fwrite(u[i]->coeffs, sizeof(uint32_t), u[i]->length,zkpOutput);
			// 	nmod_poly_fprint(zkpOutput,d[0].c1[i]);
			// 	nmod_poly_fprint(zkpOutput,d[0].c2[i]);
			// 	nmod_poly_fprint(zkpOutput,t[i]);
			// 	nmod_poly_fprint(zkpOutput,_t[i]);
			// 	nmod_poly_fprint(zkpOutput,u[i]);
				for (int j = 0; j < WIDTH; j++) {
					fwrite(y[j][i]->coeffs, sizeof(uint32_t), y[j][i]->length,zkpOutput);
					fwrite(_y[j][i]->coeffs, sizeof(uint32_t), _y[j][i]->length,zkpOutput);
			// 		nmod_poly_fprint(zkpOutput,y[j][i]);
			// 		nmod_poly_fprint(zkpOutput,_y[j][i]);
				}
			}
		} else {
			prover_lin(y, _y, t, _t, u, com[l], d[l], key, s[l - 1], t0, r[l], _r[l], l);
			result &= verifier_lin(com[l], d[l], y, _y, t, _t, u, key, s[l - 1], t0, l, MSGS);
			for (int i = 0; i < 2; i++) {
				fwrite(d[l].c1[i]->coeffs, sizeof(uint32_t), d[l].c1[i]->length,zkpOutput);
				fwrite(d[l].c2[i]->coeffs, sizeof(uint32_t), d[l].c2[i]->length,zkpOutput);
				fwrite(t[i]->coeffs, sizeof(uint32_t), t[i]->length,zkpOutput);
				fwrite(_t[i]->coeffs, sizeof(uint32_t), _t[i]->length,zkpOutput);
				fwrite(u[i]->coeffs, sizeof(uint32_t), u[i]->length,zkpOutput);
			// 	nmod_poly_fprint(zkpOutput,d[l].c1[i]);
			// 	nmod_poly_fprint(zkpOutput,d[l].c2[i]);
			// 	nmod_poly_fprint(zkpOutput,t[i]);
			// 	nmod_poly_fprint(zkpOutput,_t[i]);
			// 	nmod_poly_fprint(zkpOutput,u[i]);
				for (int j = 0; j < WIDTH; j++) {
					fwrite(y[j][i]->coeffs, sizeof(uint32_t), y[j][i]->length,zkpOutput);
					fwrite(_y[j][i]->coeffs, sizeof(uint32_t), _y[j][i]->length,zkpOutput);
			// 		nmod_poly_fprint(zkpOutput,y[j][i]);
			// 		nmod_poly_fprint(zkpOutput,_y[j][i]);
				}
			}
		}
	}

	fclose(zkpOutput);


	nmod_poly_clear(t0);
	nmod_poly_clear(t1);
	nmod_poly_clear(rho);
	nmod_poly_clear(beta);
	for (int i = 0; i < VOTERS; i++) {
		nmod_poly_clear(theta[i]);
		nmod_poly_clear(s[i]);
		for (int w = 0; w < WIDTH; w++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_clear(_r[i][w][j]);
			}
		}
	}
	for (int i = 0; i < 2; i++) {
		nmod_poly_clear(t[i]);
		nmod_poly_clear(_t[i]);
		nmod_poly_clear(u[i]);
	}
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_clear(y[i][j]);
			nmod_poly_clear(_y[i][j]);
		}
	}

	return result;
}


static void Setup(commitkey_t *key) {
	flint_rand_t rand;

	flint_randinit(rand);
  commit_setup();

	commit_keygen(key, rand);

	commit_finish();
	flint_randclear(rand);
	flint_cleanup();
}

static void onStart (commitkey_t *key, char *infoContest, VoteTable vTable[VOTERS]) {
	uint8_t Q[] = "Teste\0";
	SHA512Context sha;
	uint8_t overlineQ[SHA512HashSize];

	/* Start commitment alg */
	commit_setup();

	/*TODO: CREATE SIGNATURE KEY PAIR*/

	/*Hash overlineQ=Hash(A,Q,PublicSignKey)*/
	SHA512Reset(&sha);

	SHA512Input(&sha, Q, strlen((char *)Q));

	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			for (int k = 0; k < 2; k++) {
				SHA512Input(&sha, (const uint8_t*)key->B1[i][j][k]->coeffs, key->B1[i][j][k]->alloc * sizeof(uint64_t));
			}
		}
	}

	for (int j = 0; j < WIDTH; j++) {
		for (int k = 0; k < 2; k++) {
			SHA512Input(&sha, (const uint8_t*)key->b2[j][k]->coeffs, key->b2[j][k]->alloc * sizeof(uint64_t));
		}
	}

	/*TODO: ADD Public Sign Key to Hash*/

	SHA512Result(&sha, overlineQ);

	/*TODO: Process infoContest*/

	/* Creat H0 for table */
	SHA512Reset(&sha);

	SHA512Input(&sha, overlineQ, SHA512HashSize);

	SHA512Input(&sha, 0x00, 1);//Simulating X

	SHA512Result(&sha, H0);

	for (int i  = 0; i < SHA512HashSize; i++) {
		Hcurrent[i]=H0[i];
	}

	/* Initialize voting table and RDV*/
	for (int i  = 0; i < VOTERS; i++) {
		initializeVoteTable(&vTable[i]);
		RDV[i]=0x00;
	}

	/* Initialize number of voters as 0 */
	voteNumber=0;

	/*TODO: Output Sign public key and H0 */
}

static void onVoterActive(uint32_t vote, commit_t *com, nmod_poly_t m, commitkey_t *key, pcrt_poly_t r[WIDTH], time_t *timer, uint8_t trackingCode[SHA512HashSize]) {
	SHA512Context sha;
	uint32_t timerInt;
	uint64_t *coeffs;
	int aux;

	/* Initialize polinomial m,r to receive the vote and random to create the commitment */
	nmod_poly_init(m, MODP);
	nmod_poly_zero(m);
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_init(r[i][j], MODP);
			nmod_poly_zero(r[i][j]);
		}
	}

	/* Set the coefficient 0 of m as the vote value */
	nmod_poly_set_coeff_ui(m, 0, vote);

	/* Draw r randomly and create the commitment */
	for (int i = 0; i < WIDTH; i++) {
		commit_sample_short_crt(r[i]);
	}
	commit_doit(com, m, key, r);


	/* Set timer as current time */
	time(timer);

	timerInt=(uint32_t)*timer;

	/* Parse the commitment to coeffs variable */
	aux = 0;
	coeffs = (uint64_t*)malloc(sizeof(uint64_t)*(nmod_poly_length(com->c1[0])+
																						   nmod_poly_length(com->c1[1])+
																						   nmod_poly_length(com->c2[0])+
																					     nmod_poly_length(com->c2[1])));

	for (int i = 0; i < nmod_poly_length(com->c1[0]); i++){
		coeffs[i] = nmod_poly_get_coeff_ui(com->c1[0],i);
	}
	aux = nmod_poly_length(com->c1[0]);

	for (int i = 0; i < nmod_poly_length(com->c1[1]); i++){
		coeffs[i+aux] = nmod_poly_get_coeff_ui(com->c1[1],i);
	}
	aux+=nmod_poly_length(com->c1[1]);

	for (int i = 0; i < nmod_poly_length(com->c2[0]); i++){
		coeffs[i+aux] = nmod_poly_get_coeff_ui(com->c2[0],i);
	}
	aux+=nmod_poly_length(com->c2[0]);

	for (int i = 0; i < nmod_poly_length(com->c2[1]); i++){
		coeffs[i+aux] = nmod_poly_get_coeff_ui(com->c2[1],i);
	}
	aux+=nmod_poly_length(com->c2[1]);


	/* Compute tracking code */
	SHA512Reset(&sha);

	SHA512Input(&sha, Hcurrent, SHA512HashSize);

	SHA512Input(&sha, (const uint8_t*)&timerInt, 4);

	SHA512Input(&sha, (const uint8_t*)coeffs, aux * sizeof(uint64_t));

	SHA512Result(&sha, trackingCode);

	/* TODO: output tracking code and timer */
}

static void onChallenge (bool cast, VoteTable *vTable, commit_t *com, nmod_poly_t m, commitkey_t *key, pcrt_poly_t r[WIDTH], time_t *timer, uint8_t trackingCode[SHA512HashSize]) {

	/* If vote is cast, store it on table */
	if (cast){
		for (int i = 0; i < 2; i++) {
			nmod_poly_set(vTable->commit.c1[i], com->c1[i]);
			nmod_poly_set(vTable->commit.c2[i], com->c2[i]);
			for (int j = 0; j < WIDTH; j++){
				nmod_poly_set(vTable->r[j][i],r[j][i]);
			}
		}
		nmod_poly_set(vTable->vote,m);
		vTable->timer=(uint32_t)*timer;
		/* Also set Hcurrent as the tracking code */
		for (int i = 0; i < SHA512HashSize; i++) {
			vTable->trackingCode[i]=trackingCode[i];
			Hcurrent[i]=trackingCode[i];
		}
		/* Add vote to RDV and sort RDV */
		RDV[voteNumber]=(uint32_t)nmod_poly_get_coeff_ui(m, 0);
		insertionSort(RDV,voteNumber+1);

		/* Increment vote number as a vote has been registered */
		voteNumber++;


		/* TODO: Sign tracking code and output*/


	} else {
		/* Benaloh Challenge: output  Hcurrent, r and vote. Discard everything*/
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_print(r[i][j]);
				nmod_poly_zero(r[i][j]);
			}
		}
		for (int i = 0; i < SHA512HashSize; i++) {
			printf("%02x ",Hcurrent[i]);
			trackingCode[i]=0x00;
		}
		printf("\n%lld\n", nmod_poly_get_coeff_ui(m, 0));
	}
	/* free commitment and clear message poly */
	nmod_poly_zero(m);
	commit_free(com);

}

static void onFinish (VoteTable *vTable, commitkey_t *key) {
	FILE *voteOutput;
	SHA512Context sha;
	flint_rand_t rand;
	int res;
	commit_t com[VOTERS];
	nmod_poly_t m[VOTERS], _m[VOTERS];
	pcrt_poly_t r[VOTERS][WIDTH];
	uint8_t closeSignal[] = "CLOSE\0";


	/* Initialize auxiliary variables */
	flint_randinit(rand);
	for (int i = 0; i < voteNumber; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_init(com[i].c1[j], MODP);
			nmod_poly_init(com[i].c2[j], MODP);
			nmod_poly_zero(com[i].c1[j]);
			nmod_poly_zero(com[i].c2[j]);
			for (int w = 0; w < WIDTH; w++){
				nmod_poly_init(r[i][w][j], MODP);
				nmod_poly_zero(r[i][w][j]);
			}
		}

		nmod_poly_init(m[i], MODP);
		nmod_poly_zero(m[i]);
		nmod_poly_init(_m[i], MODP);
		nmod_poly_zero(_m[i]);
	}

	/* Compute Hlast */
	SHA512Reset(&sha);

	SHA512Input(&sha, Hcurrent, SHA512HashSize);

	SHA512Input(&sha, (const uint8_t*)closeSignal, strlen((char *)closeSignal));

	SHA512Result(&sha, Hcurrent);

	/* Parse vTable variables to auxiliary variables */
	for (int i = 0; i < voteNumber; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_set(com[i].c1[j], vTable[i].commit.c1[j]);
			nmod_poly_set(com[i].c2[j], vTable[i].commit.c2[j]);
			for (int w = 0; w < WIDTH; w++){
				nmod_poly_set(r[i][w][j], vTable[i].r[w][j]);
			}
		}
		nmod_poly_set(m[i], vTable[i].vote);
		nmod_poly_set_coeff_ui(_m[i], 0, RDV[i]);
	}

	res=run(com, m, _m, r, key, rand, voteNumber);

	/* Clear auxiliary variables and commit-vote-opening association*/
	if (res) {
		printf("ZKP Successful\n" );
		voteOutput = fopen("voteOutput", "w");
		fwrite(H0, sizeof(uint8_t), SHA512HashSize,voteOutput);
		fwrite(Hcurrent, sizeof(uint8_t), SHA512HashSize,voteOutput);
		for (int i = 0; i < voteNumber; i++) {
			nmod_poly_clear(vTable[i].vote);
			nmod_poly_clear(m[i]);
			nmod_poly_clear(_m[i]);
			fwrite(&RDV[i], sizeof(uint32_t), 1,voteOutput);
			fwrite(vTable[i].trackingCode, sizeof(uint8_t), SHA512HashSize,voteOutput);
			fwrite(&vTable[i].timer, sizeof(uint32_t), 1,voteOutput);
			for (int j = 0; j < 2; j++) {
				fwrite(vTable[i].commit.c1[j]->coeffs, sizeof(uint32_t), vTable[i].commit.c1[j]->length,voteOutput);
				fwrite(vTable[i].commit.c2[j]->coeffs, sizeof(uint32_t), vTable[i].commit.c2[j]->length,voteOutput);
				nmod_poly_clear(com[i].c1[j]);
				nmod_poly_clear(com[i].c2[j]);
				for (int w = 0; w < WIDTH; w++){
					nmod_poly_clear(vTable[i].r[w][j]);
					nmod_poly_clear(r[i][w][j]);
				}
			}
		}
		fclose(voteOutput);
	}

	/* TODO: Sign ZKP result and final tracking code */

	commit_finish();
	flint_randclear(rand);
	flint_cleanup();

}



static void verifyVote (uint32_t vote, commitkey_t *key, pcrt_poly_t r[WIDTH], time_t *timer, uint8_t trackingCode[SHA512HashSize]) {
	SHA512Context sha;
	commit_t tmpCom;
	nmod_poly_t m;
	uint32_t timerInt;
	uint64_t *coeffs;
	uint8_t newTrCode[SHA512HashSize];
	int aux;

	nmod_poly_init(m, MODP);
	nmod_poly_zero(m);

	nmod_poly_set_coeff_ui(m, 0, vote);

	/* Compute commit from the vote and the received r */
	commit_doit(&tmpCom, m, key, r);


	/* Parse the commitment to coeffs variable */
	aux = 0;
	coeffs = (uint64_t*)malloc(sizeof(uint64_t)*(nmod_poly_length(tmpCom.c1[0])+
																						   nmod_poly_length(tmpCom.c1[1])+
																						   nmod_poly_length(tmpCom.c2[0])+
																					     nmod_poly_length(tmpCom.c2[1])));

	for (int i = 0; i < nmod_poly_length(tmpCom.c1[0]); i++){
		coeffs[i] = nmod_poly_get_coeff_ui(tmpCom.c1[0],i);
	}
	aux = nmod_poly_length(tmpCom.c1[0]);

	for (int i = 0; i < nmod_poly_length(tmpCom.c1[1]); i++){
		coeffs[i+aux] = nmod_poly_get_coeff_ui(tmpCom.c1[1],i);
	}
	aux+=nmod_poly_length(tmpCom.c1[1]);

	for (int i = 0; i < nmod_poly_length(tmpCom.c2[0]); i++){
		coeffs[i+aux] = nmod_poly_get_coeff_ui(tmpCom.c2[0],i);
	}
	aux+=nmod_poly_length(tmpCom.c2[0]);

	for (int i = 0; i < nmod_poly_length(tmpCom.c2[1]); i++){
		coeffs[i+aux] = nmod_poly_get_coeff_ui(tmpCom.c2[1],i);
	}
	aux+=nmod_poly_length(tmpCom.c2[1]);

	timerInt=(uint32_t)*timer;


	/* Compute new tracking code */
	SHA512Reset(&sha);

	SHA512Input(&sha, Hcurrent, SHA512HashSize);

	SHA512Input(&sha, (const uint8_t*)&timerInt, 4);

	SHA512Input(&sha, (const uint8_t*)coeffs, aux * sizeof(uint64_t));

	SHA512Result(&sha, newTrCode);

	/* Check if computed tracking code matches the received tracking code */
	for(int j=0;j<SHA512HashSize;j++){
		if(trackingCode[j]!=newTrCode[j]){
			printf("ERROR\n");
		}
	}
}


#ifdef MAIN
int main(int argc, char *arg[]) {
	FILE *resultadoCycles;
  flint_rand_t rand;
  commitkey_t key;
	unsigned long long onVoterActiveCycles, onChallengeCycles;
	commit_t com;
	nmod_poly_t m,_m[VOTERS];
	pcrt_poly_t r[WIDTH];
  uint32_t vote;
	uint8_t nextVoter;
  int a=0;
	char infoContest[]="Teste";
	VoteTable vTable[VOTERS];
	// uint8_t Q[] = "abc\0";
	SHA512Context sha;
	uint8_t trackingCode[SHA512HashSize];
	uint8_t Teste[SHA512HashSize];
	time_t timer;
	int numVotos, numTest=2;
	int flag=0;

  // flint_randinit(rand);
	// for (int i = 0; i < VOTERS; i++) {
	// 	nmod_poly_init(_m[i], MODP);
	// }
	// nmod_poly_init(m,MODP);
  // commit_setup();
	// commit_sample_rand(m,rand);
	// printf("%lld\n", m->alloc);
	// printf("%lld\n", m->length);
	// printf("%lld\n", m->mod.n);
	//
	//
	// for (int i = 0; i < 100; i++) {
	// 	printf("%2d %08llx\n", i, m->coeffs[i]);
	// }
	resultadoCycles = fopen("resultadoCiclos","a");
	if (resultadoCycles==NULL) {
		printf("Erro arquivo\n");
		return 0;
	}

	for (numVotos = 500; numVotos <= 800; numVotos+=500) {
		fprintf(resultadoCycles, "Numero Votos = %d, %d testes\n", numVotos, numTest);
		fprintf(resultadoCycles, "    Setup;  onStart;onVoterActive;  onChallenge;    onFinish\n");
		fflush(resultadoCycles);
		for (int i = 0; i < numTest; i ++) {

			bench_reset();
			bench_before();
			Setup(&key);
			bench_after();
			fprintf(resultadoCycles, "%9lld;", bench_total());

			bench_reset();
			bench_before();
			onStart (&key, infoContest, vTable);
			bench_after();
			fprintf(resultadoCycles, "%9lld;", bench_total());

			onVoterActiveCycles = 0;
			onChallengeCycles = 0;
			for(int j = 0; j < numVotos; j ++) {
				getrandom(&vote, sizeof(vote), 0);
				vote&=0x8FFFFFFF;

				bench_reset();
				bench_before();
				onVoterActive(vote, &com, m, &key, r, &timer, trackingCode);
				bench_after();
				onVoterActiveCycles+=bench_total();

				//verifyVote (vote, &key, r, &timer, trackingCode);

				bench_reset();
				bench_before();
				onChallenge (TRUE, &vTable[voteNumber], &com, m, &key, r, &timer, trackingCode);
				bench_after();
				onChallengeCycles+=bench_total();
			}

			fprintf(resultadoCycles, "%13lld;%13lld;", onVoterActiveCycles,onChallengeCycles);

			bench_reset();
			bench_before();
			onFinish(vTable, &key);
			bench_after();
			fprintf(resultadoCycles, "%12lld\n", bench_total());
			fflush(resultadoCycles);
		}
	}
	fclose (resultadoCycles);

	// for (int i = 0; i < 20; i++){
	// 	bench_reset();
	// 	bench_before();
	// 	do {
	// 		flag=50;
	// 		nmod_poly_randtest_not_zero(_m[i],rand,DEGREE);
	// 		for (int j = 0; j < DEGREE; j++) {
	// 			if (nmod_poly_get_coeff_ui(_m[i],j)==0) {
	// 				flag--;
	// 			}
	// 		}
	// 	} while (flag<0);
	// 	bench_after();
	// 	bench_print();
	// 	printf("\n");
	// 	printf("i = %d\n", i);
	// 	nmod_poly_print(_m[i]);
	// 	printf("\n\n");
	// }
	// bench_reset();
	// bench_before();
	// commit_sample_rand(_m[2],rand);
	// bench_after();
	// bench_print();
	// printf("\n");
	// nmod_poly_print(_m[2]);
	// printf("\n");
	// printf("\nRDV ordenado: \n");
	// for (int i = voteNumber-10; i < voteNumber; i++) {
	// 	printf("%u\n", RDV[i]);
	// }
	// printf("%u\n", RDV[voteNumber]);

// printf("Total time = %lld cycles\n\n", cpuCycles);
// printf("Avg time = %lld cycles\n\n", cpuCycles/numTest);
//
// for (int i = 0; i<2;i++){
// 	// nmod_poly_print(vTable[i].vote);
// 	printf("Hash ");
// 	for (int j = 0; j < SHA512HashSize; j++) {
// 		printf("%02x ", vTable[i].trackingCode[j]);
// 	}
// 	printf("\nTime %d\n", vTable[i].timer);
//
// }
// printf("%d\n", voteNumber);


	// for (int i = 0; i < HEIGHT; i++) {
	// 	for (int j = 0; j < WIDTH; j++) {
	// 		for (int k = 0; k < 2; k++) {
	// 			nmod_poly_print(key.B1[i][j][k]);
	// 		}
	// 		printf("\n\n");
	// 	}
	// }
	//
	// for (int i = 0; i < WIDTH; i++) {
	// 	for (int j = 0; j < 2; j++) {
	// 		nmod_poly_print(key.b2[i][j]);
	// 	}
	// }

	// SHA512Reset(&sha);
	//
	// SHA512Input(&sha, Q, strlen((char *)Q));
	//
	// SHA512Result(&sha, overlineQ);
	//
	// printf("\n\n\n");
	// for(int i=0;i<SHA512HashSize;i++){
	// 	printf("%02x", overlineQ[i]);
	// 	if((i+1)%4==0){
	// 		printf(" ");
	// 	}
	// }
	// printf("\n\n");

  // for(int i = 0; i < VOTERS; i++) {
  //   nmod_poly_init(m[i], MODP);
  //   nmod_poly_init(_m[i], MODP);
  // }
	//
	//
	// for (int i = 0; i < VOTERS; i++) {
	// 	for (int w = 0; w < WIDTH; w++) {
	//     for (int j = 0; j < 2; j++) {
	//       nmod_poly_init(r[i][w][j], MODP);
	//     }
	//   }
	// }
	//
	// voteNumber = 0;
	//
	//
  // commit_keygen(&key, rand);
	//
	// // Unnecessary as flint_randinit always initializes to the same value. Remember to add again when truly randomly Initializing
	// // chave = fopen("CommomKey","w");
	// // for (int i = 0; i < HEIGHT; i++) {
	// // 	for (int j = 0; j < WIDTH; j++) {
	// // 		for (int k = 0; k < 2; k++) {
	// // 			nmod_poly_fprint(chave, key.B1[i][j][k]);
	// // 			fprintf(chave, "\n");
	// // 		}
	// // 	}
	// // }
	// // for (int i = 0; i < WIDTH; i++) {
	// // 	for (int j = 0; j < 2; j++) {
	// // 		nmod_poly_fprint(chave, key.b2[i][j]);
	// // 		fprintf(chave, "\n");
	// // 	}
	// // }
	// // fclose(chave);
	//
	//
	// do {
	// 	voteCasting(&com[voteNumber], m[voteNumber], &key, r[voteNumber]);
	// 	// printf("\nVerificar voto? (0 - nao, 1 - sim)?: ");
	// 	// scanf("%hhd", &nextVoter);
	// 	// if (nextVoter) {
	// 	// 	checkSpoil(&key);
	// 	// }
	// 	printf("\n\nProximo eleitor (0 - nao, 1 - sim)?: ");
	// 	scanf("%hhd", &nextVoter);
	// } while(nextVoter && voteNumber < VOTERS);
	//
	//
	// // Shuffle Function
  // for (int i = 0; i < voteNumber; i++) {
	// 	nmod_poly_set(_m[i], m[(i + 10) % voteNumber]);
	// }
	//
  // bench_reset();
  // bench_before();
  // a=run(com, m, _m, r, &key, rand, voteNumber);
  // bench_after();
  // printf("\n\n\nTime for shuffle: ");
  // bench_print();
  // if (a) {
	// 	printf("ZKP de Shuffle - Sucesso\n");
	// }
	// else {
	// 	printf("ZKP de Shuffle - Fracassp\n");
	// }
	//
  // commit_keyfree(&key);
  // for (int i = 0; i < VOTERS; i++) {
  //   commit_free(&com[i]);
  // 	nmod_poly_clear(m[i]);
	// 	nmod_poly_clear(_m[i]);
  // }
	//
	// for (int i = 0; i < VOTERS; i++){
	// 	for (int w = 0; w < WIDTH; w++) {
	// 		for (int j = 0; j < 2; j++) {
	// 			nmod_poly_clear(r[i][w][j]);
	// 		}
	// 	}
	// }
	//commit_finish();
	//flint_randclear(rand);
	//flint_cleanup();

  return 0;
}
#endif
