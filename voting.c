#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#include "param.h"
#include "commit.h"
#include "test.h"
#include "bench.h"
#include "assert.h"
#include "gaussian.h"
#include "fastrandombytes.h"
#include "sha.h"

#define VOTERS 3000

static int voteNumber;

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
	int flag, result = 1;
	commit_t d[MSGS];
	nmod_poly_t t0, t1, rho, beta, theta[MSGS], s[MSGS];
	nmod_poly_t y[WIDTH][2], _y[WIDTH][2], t[2], _t[2], u[2], _r[MSGS][WIDTH][2];

	nmod_poly_init(t0, MODP);
	nmod_poly_init(t1, MODP);
	nmod_poly_init(rho, MODP);
	nmod_poly_init(beta, MODP);
	for (int i = 0; i < MSGS; i++) {
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
	for (int w = 0; w < MSGS; w++) {
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_init(_r[w][i][j], MODP);
			}
		}
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

	commit_sample_rand(beta, rng);
	nmod_poly_mulmod(s[0], theta[0], _m[0], *commit_poly());
	nmod_poly_mulmod(t0, beta, m[0], *commit_poly());
	nmod_poly_sub(s[0], s[0], t0);
	nmod_poly_invmod(t0, _m[0], *commit_poly());
	nmod_poly_mulmod(s[0], s[0], t0, *commit_poly());
	for (int i = 1; i < MSGS - 1; i++) {
		nmod_poly_mulmod(s[i], theta[i - 1], m[i], *commit_poly());
		nmod_poly_mulmod(t0, theta[i], _m[i], *commit_poly());
		nmod_poly_add(s[i], s[i], t0);
		nmod_poly_mulmod(t0, s[i - 1], m[i], *commit_poly());
		nmod_poly_sub(s[i], s[i], t0);
		nmod_poly_invmod(t0, _m[i], *commit_poly());
		nmod_poly_mulmod(s[i], s[i], t0, *commit_poly());
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
	}

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
		} else {
			prover_lin(y, _y, t, _t, u, com[l], d[l], key, s[l - 1], t0, r[l], _r[l], l);
			result &= verifier_lin(com[l], d[l], y, _y, t, _t, u, key, s[l - 1], t0, l, MSGS);
		}
	}

	nmod_poly_clear(t0);
	nmod_poly_clear(t1);
	nmod_poly_clear(rho);
	nmod_poly_clear(beta);
	for (int i = 0; i < MSGS; i++) {
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

static void voteCasting(commit_t *com, nmod_poly_t m, commitkey_t *key, pcrt_poly_t r[WIDTH]) {
	FILE *voteFile, *openingFile;
	commit_t tmpCom;
	nmod_poly_t tmpMsg;
	pcrt_poly_t tmpR[WIDTH];
	uint32_t vote;
	uint8_t spoilChoice;

	nmod_poly_init(tmpMsg, MODP);
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_init(tmpR[i][j], MODP);
		}
	}

	printf("Numero candidato: ");
  scanf("%d", &vote);
	nmod_poly_set_coeff_ui(tmpMsg, 0, vote);

	for (int i = 0; i < WIDTH; i++) {
		commit_sample_short_crt(tmpR[i]);
	}
	commit_doit(&tmpCom, tmpMsg, key, tmpR);

	voteFile = fopen("voteCom","w");
	nmod_poly_fprint(voteFile,tmpCom.c1[0]);
	fprintf(voteFile, "\n");
	nmod_poly_fprint(voteFile,tmpCom.c1[1]);
	fprintf(voteFile, "\n");
	nmod_poly_fprint(voteFile,tmpCom.c2[0]);
	fprintf(voteFile, "\n");
	nmod_poly_fprint(voteFile,tmpCom.c2[1]);
	fclose(voteFile);

	printf("Depositar (0) ou Cancelar e Auditar (1)?: ");
	scanf("%hhd", &spoilChoice);

	if (spoilChoice) {
		openingFile = fopen("openingVote","w");
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_fprint(openingFile,tmpR[i][j]);
				fprintf(voteFile, "\n");
			}
		}
		fclose(openingFile);
	}
	else {
		for (int i = 0; i < 2; i++) {
			nmod_poly_init(com->c1[i], MODP);
			nmod_poly_init(com->c2[i], MODP);
			nmod_poly_set(com->c1[i],tmpCom.c1[i]);
			nmod_poly_set(com->c2[i],tmpCom.c2[i]);
			for (int j = 0; j < WIDTH; j++){
				nmod_poly_init(r[j][i], MODP);
				nmod_poly_set(r[j][i],tmpR[j][i]);
			}
			nmod_poly_set(m,tmpMsg);
		}

		voteNumber++;
	}

	commit_free(&tmpCom);
  nmod_poly_clear(tmpMsg);
  for (int w = 0; w < WIDTH; w++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_clear(tmpR[w][j]);
		}
	}
}

static void checkSpoil(commitkey_t *key) {
	FILE *voteFile, *openingFile;
	commit_t com,_com;
	nmod_poly_t m;
	pcrt_poly_t r[WIDTH];
	uint32_t vote;
	uint8_t result=1;

	for (int i = 0; i < 2; i++) {
		nmod_poly_init(com.c1[i], MODP);
		nmod_poly_init(com.c2[i], MODP);
		nmod_poly_zero(com.c1[i]);
		nmod_poly_zero(com.c2[i]);
	}
	nmod_poly_init(m, MODP);
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_init(r[i][j], MODP);
		}
	}

	printf("Candidato a checar: ");
  scanf("%d", &vote);
	nmod_poly_set_coeff_ui(m, 0, vote);

	voteFile = fopen("voteCom","r");
	nmod_poly_fread(voteFile,com.c1[0]);
	nmod_poly_fread(voteFile,com.c1[1]);
	nmod_poly_fread(voteFile,com.c2[0]);
	nmod_poly_fread(voteFile,com.c2[1]);
	fclose(voteFile);

	openingFile = fopen("openingVote","r");
	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_fread(openingFile,r[i][j]);
		}
	}
	fclose(openingFile);

	commit_doit(&_com, m, key, r);

	for (int i = 0; i < 2; i++) {
		result &= nmod_poly_equal(com.c1[i], _com.c1[i]);
		result &= nmod_poly_equal(com.c2[i], _com.c2[i]);
	}

	if (result) {
		printf("\nSUCESSO\n");
	}
	else {
		printf("\nFALHA\n");
	}

	commit_free(&com);
	commit_free(&_com);
  nmod_poly_clear(m);
  for (int w = 0; w < WIDTH; w++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_clear(r[w][j]);
		}
	}
}


#ifdef MAIN
int main(int argc, char *arg[]) {
	// FILE *chave;
  flint_rand_t rand;
  commitkey_t key;
	commit_t com[VOTERS];
	nmod_poly_t m[VOTERS],_m[VOTERS];
	pcrt_poly_t r[VOTERS][WIDTH];
  uint64_t vote;
	uint8_t nextVoter;
  int a=0;

  flint_randinit(rand);
  commit_setup();

  for(int i = 0; i < VOTERS; i++) {
    nmod_poly_init(m[i], MODP);
    nmod_poly_init(_m[i], MODP);
  }


	for (int i = 0; i < VOTERS; i++) {
		for (int w = 0; w < WIDTH; w++) {
	    for (int j = 0; j < 2; j++) {
	      nmod_poly_init(r[i][w][j], MODP);
	    }
	  }
	}

	voteNumber = 0;


  commit_keygen(&key, rand);

	// Unnecessary as flint_randinit always initializes to the same value. Remember to add again when truly randomly Initializing
	// chave = fopen("CommomKey","w");
	// for (int i = 0; i < HEIGHT; i++) {
	// 	for (int j = 0; j < WIDTH; j++) {
	// 		for (int k = 0; k < 2; k++) {
	// 			nmod_poly_fprint(chave, key.B1[i][j][k]);
	// 			fprintf(chave, "\n");
	// 		}
	// 	}
	// }
	// for (int i = 0; i < WIDTH; i++) {
	// 	for (int j = 0; j < 2; j++) {
	// 		nmod_poly_fprint(chave, key.b2[i][j]);
	// 		fprintf(chave, "\n");
	// 	}
	// }
	// fclose(chave);


	do {
		voteCasting(&com[voteNumber], m[voteNumber], &key, r[voteNumber]);
		// printf("\nVerificar voto? (0 - nao, 1 - sim)?: ");
		// scanf("%hhd", &nextVoter);
		// if (nextVoter) {
		// 	checkSpoil(&key);
		// }
		printf("\n\nProximo eleitor (0 - nao, 1 - sim)?: ");
		scanf("%hhd", &nextVoter);
	} while(nextVoter && voteNumber < VOTERS);


	// Shuffle Function
  for (int i = 0; i < voteNumber; i++) {
		nmod_poly_set(_m[i], m[(i + 10) % voteNumber]);
	}

  bench_reset();
  bench_before();
  a=run(com, m, _m, r, &key, rand, voteNumber);
  bench_after();
  printf("\n\n\nTime for shuffle: ");
  bench_print();
  if (a) {
		printf("ZKP de Shuffle - Sucesso\n");
	}
	else {
		printf("ZKP de Shuffle - Fracassp\n");
	}

  commit_keyfree(&key);
  for (int i = 0; i < VOTERS; i++) {
    commit_free(&com[i]);
  	nmod_poly_clear(m[i]);
		nmod_poly_clear(_m[i]);
  }

	for (int i = 0; i < VOTERS; i++){
		for (int w = 0; w < WIDTH; w++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_clear(r[i][w][j]);
			}
		}
	}
	commit_finish();
	flint_randclear(rand);
	flint_cleanup();

  return 0;
}
#endif
