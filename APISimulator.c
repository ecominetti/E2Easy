#include "APISimulator.h"

typedef struct _VoteTable {
	commit_t commit;
	pcrt_poly_t r[WIDTH];
	nmod_poly_t vote;
	uint8_t trackingCode[SHA512HashSize];
	uint32_t timer;
} VoteTable;

static int voteNumber;
static uint8_t H0[CONTESTS][SHA512HashSize];
static uint8_t Hcurrent[CONTESTS][SHA512HashSize];
static uint32_t RDV[CONTESTS][VOTERS];
static VoteTable vTable[CONTESTS][VOTERS];
static commitkey_t key;
static commit_t com[CONTESTS];
static nmod_poly_t m[CONTESTS];
static pcrt_poly_t r[CONTESTS][WIDTH];
static time_t timer[CONTESTS];
static uint8_t trackingCode[CONTESTS][SHA512HashSize];
static uint8_t voteContestCasted;
static uint8_t numberContests;
uint8_t QRCodeTrackingCode[CONTESTS*(SHA512HashSize+sizeof(uint32_t))];
uint8_t QRCodeSpoilTrackingCode[CONTESTS*SHA512HashSize];
uint8_t QRCodeSpoilNonce[CONTESTS*WIDTH*(DEGREE/4)]; // Degree*2/8
uint32_t QRCodeSpoilVotes[CONTESTS];
int sizeQRCodeSpoil[3];

static void initializeVoteTable(VoteTable *vTable){
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

static void finalizeVoteTable(VoteTable *vTable){
	for (int i = 0; i < 2; i++) {
		nmod_poly_zero(vTable->commit.c1[i]);
		nmod_poly_zero(vTable->commit.c2[i]);
		nmod_poly_clear(vTable->commit.c1[i]);
		nmod_poly_clear(vTable->commit.c2[i]);
		for (int j = 0; j < WIDTH; j++){
			nmod_poly_zero(vTable->r[j][i]);
			nmod_poly_clear(vTable->r[j][i]);
		}
	}
	nmod_poly_zero(vTable->vote);
	nmod_poly_clear(vTable->vote);
	for (int i = 0; i < SHA512HashSize; i++) {
		vTable->trackingCode[i]=0x00;
	}
	vTable->timer=0x00;
}

/* Function to sort an array using insertion sort */
static void insertionSort(uint32_t arr[], int n)
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

static void shuffle_hash(nmod_poly_t d[2], commitkey_t *key, commit_t x, commit_t y,
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
		nmod_poly_t r[VOTERS][WIDTH][2], commitkey_t *key, flint_rand_t rng, int MSGS, char *outputFileName) {
	FILE *zkpOutput;
	int flag, result = 1;
	commit_t d[VOTERS];
	nmod_poly_t t0, t1, rho, beta, theta[VOTERS], s[VOTERS];
	nmod_poly_t y[WIDTH][2], _y[WIDTH][2], t[2], _t[2], u[2], _r[VOTERS][WIDTH][2];


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

	zkpOutput = fopen(outputFileName, "w");
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

	fwrite(beta->coeffs, sizeof(uint32_t), beta->length,zkpOutput);

	nmod_poly_mulmod(s[0], theta[0], _m[0], *commit_poly());
	nmod_poly_mulmod(t0, beta, m[0], *commit_poly());
	nmod_poly_sub(s[0], s[0], t0);
	nmod_poly_invmod(t0, _m[0], *commit_poly());
	nmod_poly_mulmod(s[0], s[0], t0, *commit_poly());
	fwrite(s[0]->coeffs, sizeof(uint32_t), s[0]->length,zkpOutput);
	for (int i = 1; i < MSGS - 1; i++) {
		nmod_poly_mulmod(s[i], theta[i - 1], m[i], *commit_poly());
		nmod_poly_mulmod(t0, theta[i], _m[i], *commit_poly());
		nmod_poly_add(s[i], s[i], t0);
		nmod_poly_mulmod(t0, s[i - 1], m[i], *commit_poly());
		nmod_poly_sub(s[i], s[i], t0);
		nmod_poly_invmod(t0, _m[i], *commit_poly());
		nmod_poly_mulmod(s[i], s[i], t0, *commit_poly());
		fwrite(s[i]->coeffs, sizeof(uint32_t), s[i]->length,zkpOutput);
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

			for (int i = 0; i < 2; i++) {
				fwrite(d[0].c1[i]->coeffs, sizeof(uint32_t), d[0].c1[i]->length,zkpOutput);
				fwrite(d[0].c2[i]->coeffs, sizeof(uint32_t), d[0].c2[i]->length,zkpOutput);
				fwrite(t[i]->coeffs, sizeof(uint32_t), t[i]->length,zkpOutput);
				fwrite(_t[i]->coeffs, sizeof(uint32_t), _t[i]->length,zkpOutput);
				fwrite(u[i]->coeffs, sizeof(uint32_t), u[i]->length,zkpOutput);
				for (int j = 0; j < WIDTH; j++) {
					fwrite(y[j][i]->coeffs, sizeof(uint32_t), y[j][i]->length,zkpOutput);
					fwrite(_y[j][i]->coeffs, sizeof(uint32_t), _y[j][i]->length,zkpOutput);
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
				for (int j = 0; j < WIDTH; j++) {
					fwrite(y[j][i]->coeffs, sizeof(uint32_t), y[j][i]->length,zkpOutput);
					fwrite(_y[j][i]->coeffs, sizeof(uint32_t), _y[j][i]->length,zkpOutput);
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
		commit_free(&d[i]);
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


void Setup() {
	flint_rand_t rand;

	flint_randinit(rand);
    commit_setup();

	commit_keygen(&key, rand);

	commit_finish();
	flint_randclear(rand);
	flint_cleanup();
}

void onStart (uint8_t infoContest) {
	uint8_t Q[] = "Teste\0";
	SHA512Context sha;
	commitkey_t *keyP = &key;
	uint8_t overlineQ[SHA512HashSize];

	numberContests = 0;

	/* Start commitment alg */
	commit_setup();

	/*TODO: CREATE SIGNATURE KEY PAIR*/

	/*Hash overlineQ=Hash(A,Q,PublicSignKey)*/
	SHA512Reset(&sha);

	SHA512Input(&sha, Q, strlen((char *)Q));

	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			for (int k = 0; k < 2; k++) {
				SHA512Input(&sha, (const uint8_t*)keyP->B1[i][j][k]->coeffs, keyP->B1[i][j][k]->alloc * sizeof(uint64_t));
			}
		}
	}

	for (int j = 0; j < WIDTH; j++) {
		for (int k = 0; k < 2; k++) {
			SHA512Input(&sha, (const uint8_t*)keyP->b2[j][k]->coeffs, keyP->b2[j][k]->alloc * sizeof(uint64_t));
		}
	}

	/*TODO: ADD Public Sign Key to Hash*/

	SHA512Result(&sha, overlineQ);

	/*TODO: Process infoContest*/
	numberContests = infoContest;
	

	/* Create H0 for each contest table */
	for (uint8_t i = 0; i < CONTESTS; i++)
	{
		SHA512Reset(&sha);

		SHA512Input(&sha, overlineQ, SHA512HashSize);

		SHA512Input(&sha, &i, 1);

		SHA512Result(&sha, H0[i]);
	}

	for (int j = 0; j < CONTESTS; j++) {
		for (int i  = 0; i < SHA512HashSize; i++) {
			Hcurrent[j][i]=H0[j][i];
		}
	}

	/* Initialize voting table and RDV*/
	for (int i  = 0; i < VOTERS; i++) {
		for (int j = 0; j < CONTESTS; j++) {
			initializeVoteTable(&vTable[j][i]);
			RDV[j][i]=0x00;
		}
	}

	/* Initialize number of voters as 0 */
	voteNumber = 0;

	/* Initialize vote timestamp as 0 */
	for (int i = 0; i < CONTESTS; i++) {
		timer[i] = 0x00;
	}

	/* Initialize if a vote was casted for a contest as 0 */
	voteContestCasted = 0;

	/*TODO: Output Sign public key and H0 */
}

void onVoterActive(uint32_t vote, uint8_t cont) {
	SHA512Context sha;
	uint32_t timerInt;
	uint64_t *coeffs;
	int aux;

	/* Check if the contest provided is within range and enabled*/
	if (((numberContests >> cont) & 1) != 1) {
		printf("Error: contest not enabled\n");
	}
	else {

		/* Initialize polinomial m,r to receive the vote and random to create the commitment */
		nmod_poly_init(m[cont], MODP);
		nmod_poly_zero(m[cont]);
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_init(r[cont][i][j], MODP);
				nmod_poly_zero(r[cont][i][j]);
			}
		}

		/* Set the coefficient 0 of m as the vote value */
		nmod_poly_set_coeff_ui(m[cont], 0, vote);

		/* Draw r randomly and create the commitment */
		for (int i = 0; i < WIDTH; i++) {
			commit_sample_short_crt(r[cont][i]);
		}
		commit_doit(&com[cont], m[cont], &key, r[cont]);


		/* Set timer as current time */
		time(&timer[cont]);

		timerInt=(uint32_t)timer[cont];

		/* Parse the commitment to coeffs variable */
		aux = 0;
		coeffs = (uint64_t*)malloc(sizeof(uint64_t)*(nmod_poly_length(com[cont].c1[0])+
														nmod_poly_length(com[cont].c1[1])+
														nmod_poly_length(com[cont].c2[0])+
															nmod_poly_length(com[cont].c2[1])));

		for (int i = 0; i < nmod_poly_length(com[cont].c1[0]); i++){
			coeffs[i] = nmod_poly_get_coeff_ui(com[cont].c1[0],i);
		}
		aux = nmod_poly_length(com[cont].c1[0]);

		for (int i = 0; i < nmod_poly_length(com[cont].c1[1]); i++){
			coeffs[i+aux] = nmod_poly_get_coeff_ui(com[cont].c1[1],i);
		}
		aux+=nmod_poly_length(com[cont].c1[1]);

		for (int i = 0; i < nmod_poly_length(com[cont].c2[0]); i++){
			coeffs[i+aux] = nmod_poly_get_coeff_ui(com[cont].c2[0],i);
		}
		aux+=nmod_poly_length(com[cont].c2[0]);

		for (int i = 0; i < nmod_poly_length(com[cont].c2[1]); i++){
			coeffs[i+aux] = nmod_poly_get_coeff_ui(com[cont].c2[1],i);
		}
		aux+=nmod_poly_length(com[cont].c2[1]);


		/* Compute tracking code */
		SHA512Reset(&sha);

		SHA512Input(&sha, Hcurrent[cont], SHA512HashSize);

		SHA512Input(&sha, (const uint8_t*)&timerInt, 4);

		SHA512Input(&sha, (const uint8_t*)coeffs, aux * sizeof(uint64_t));

		SHA512Result(&sha, trackingCode[cont]);

		free(coeffs);

		/* Inform that a vote was casted for this contest */
		voteContestCasted += (0x01 << cont);

		/* TODO: output tracking code and timer */
	}
}

void onChallenge (bool cast) {
	nmod_poly_t rnd;
	uint32_t coeffValue;
	uint8_t coeffSeq[DEGREE*2/8];
	uint16_t index;
	uint8_t numberActiveContests=0;

	/* If vote is cast, store it on table */
	if (cast){
		for (uint8_t cont = 0; cont < CONTESTS; cont++) {
			if (((voteContestCasted >> cont) & 1) == 1) {
				for (int i = 0; i < 2; i++) {
					nmod_poly_set(vTable[cont][voteNumber].commit.c1[i], com[cont].c1[i]);
					nmod_poly_set(vTable[cont][voteNumber].commit.c2[i], com[cont].c2[i]);
					for (int j = 0; j < WIDTH; j++){
						nmod_poly_set(vTable[cont][voteNumber].r[j][i],r[cont][j][i]);
					}
				}
				nmod_poly_set(vTable[cont][voteNumber].vote,m[cont]);
				vTable[cont][voteNumber].timer=(uint32_t)timer[cont];
				/* Also set Hcurrent as the tracking code */
				for (int i = 0; i < SHA512HashSize; i++) {
					vTable[cont][voteNumber].trackingCode[i]=trackingCode[cont][i];
					Hcurrent[cont][i]=trackingCode[cont][i];
				}
				/* Add vote to RDV and sort RDV */
				RDV[cont][voteNumber]=(uint32_t)nmod_poly_get_coeff_ui(m[cont], 0);
				insertionSort(RDV[cont],voteNumber+1);
			}
		}

		/* Increment vote number as a vote has been registered */
		voteNumber++;


		/* TODO: Sign tracking code and output*/

	} else {
		/* Benaloh Challenge: output  Hcurrent, r and vote. Discard everything*/

		/* Initilize QRCodeVectors*/
		for (int i = 0; i < CONTESTS*WIDTH*(DEGREE/4); i++) {
			QRCodeSpoilNonce[i]=0x00;
		}
		for (int i = 0; i < CONTESTS; i++) {
			QRCodeSpoilVotes[i]=0x00;
		}
		for (int i = 0; i < CONTESTS*SHA512HashSize; i++) {
			QRCodeSpoilTrackingCode[i]=0x00;
		}

		for (uint8_t cont = 0; cont < CONTESTS; cont++) {
			if (((voteContestCasted >> cont) & 1) == 1) {
				for (int i = 0; i < WIDTH; i++) {
					for (index = 0; index < (DEGREE*2/8); index++) {
						coeffSeq[index]=0x00;
					}
					index = 0;
					nmod_poly_init(rnd, MODP);
					nmod_poly_zero(rnd);
					pcrt_poly_rec(rnd, r[cont][i]);

					for (int coeff = 0; coeff < DEGREE; coeff++) {
						coeffValue = nmod_poly_get_coeff_ui(rnd,coeff);
						coeffValue++;
						coeffValue %= MODP;
						coeffValue &= 0xFF;
						index=floor(coeff/4);
						coeffSeq[index]|=((uint8_t)coeffValue << (2*(coeff%4)));
						QRCodeSpoilNonce[numberActiveContests*(WIDTH*(DEGREE*2/8))+i*(DEGREE*2/8)+index] |= 
																		((uint8_t)coeffValue << (2*(coeff%4)));
					}
				
					for (int j = 0; j < 2; j++) {
						nmod_poly_zero(r[cont][i][j]);
					}
					nmod_poly_clear(rnd);

				}
				for (int i = 0; i < SHA512HashSize; i++) {
					QRCodeSpoilTrackingCode[numberActiveContests*SHA512HashSize+i] =
													Hcurrent[cont][i];
					trackingCode[cont][i]=0x00;
				}
				QRCodeSpoilVotes[numberActiveContests]=nmod_poly_get_coeff_ui(m[cont], 0);
				numberActiveContests++;
			}
		}
		sizeQRCodeSpoil[0]=numberActiveContests*SHA512HashSize;
		sizeQRCodeSpoil[1]=numberActiveContests*(WIDTH*(DEGREE*2/8));
		sizeQRCodeSpoil[2]=numberActiveContests;
	}
	/* free commitment and clear message poly */
	for (uint8_t cont = 0; cont < CONTESTS; cont++) {
		nmod_poly_zero(m[cont]);
		nmod_poly_clear(m[cont]);
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_zero(r[cont][i][j]);
				nmod_poly_clear(r[cont][i][j]);
			}
		}
		commit_free(&com[cont]);
	}
	voteContestCasted = 0x00;

}

void onFinish () {
	FILE *voteOutput;
	SHA512Context sha;
	flint_rand_t rand;
	int res;
	commit_t com_aux[VOTERS];
	nmod_poly_t m_aux[VOTERS], _m[VOTERS];
	pcrt_poly_t r_aux[VOTERS][WIDTH];
	uint8_t closeSignal[] = "CLOSE\0";
	char outputFileName[20];

	flint_randinit(rand);
	for (uint8_t cont = 0; cont < CONTESTS; cont++) {
		if (((numberContests >> cont) & 1) == 1) {
			/* Initialize auxiliary variables */
			for (int i = 0; i < voteNumber; i++) {
				for (int j = 0; j < 2; j++) {
					nmod_poly_init(com_aux[i].c1[j], MODP);
					nmod_poly_init(com_aux[i].c2[j], MODP);
					nmod_poly_zero(com_aux[i].c1[j]);
					nmod_poly_zero(com_aux[i].c2[j]);
					for (int w = 0; w < WIDTH; w++){
						nmod_poly_init(r_aux[i][w][j], MODP);
						nmod_poly_zero(r_aux[i][w][j]);
					}
				}

				nmod_poly_init(m_aux[i], MODP);
				nmod_poly_zero(m_aux[i]);
				nmod_poly_init(_m[i], MODP);
				nmod_poly_zero(_m[i]);
			}

			/* Compute Hlast */
			SHA512Reset(&sha);

			SHA512Input(&sha, Hcurrent[cont], SHA512HashSize);

			SHA512Input(&sha, (const uint8_t*)closeSignal, strlen((char *)closeSignal));

			SHA512Result(&sha, Hcurrent[cont]);

			/* Parse vTable variables to auxiliary variables */
			for (int i = 0; i < voteNumber; i++) {
				for (int j = 0; j < 2; j++) {
					nmod_poly_set(com_aux[i].c1[j], vTable[cont][i].commit.c1[j]);
					nmod_poly_set(com_aux[i].c2[j], vTable[cont][i].commit.c2[j]);
					for (int w = 0; w < WIDTH; w++){
						nmod_poly_set(r_aux[i][w][j], vTable[cont][i].r[w][j]);
					}
				}
				nmod_poly_set(m_aux[i], vTable[cont][i].vote);
				nmod_poly_set_coeff_ui(_m[i], 0, RDV[cont][i]);
			}

			snprintf(outputFileName,20,"ZKPOutput_Cont%d", cont);

			res=run(com_aux, m_aux, _m, r_aux, &key, rand, voteNumber, outputFileName);

			/* Clear auxiliary variables and commit-vote-opening association*/
			if (res) {
				snprintf(outputFileName,20,"voteOutput_Cont%d", cont);
				voteOutput = fopen(outputFileName, "w");
				fwrite(H0[cont], sizeof(uint8_t), SHA512HashSize,voteOutput);
				fwrite(Hcurrent[cont], sizeof(uint8_t), SHA512HashSize,voteOutput);
				for (int i = 0; i < voteNumber; i++) {
					nmod_poly_clear(m_aux[i]);
					nmod_poly_clear(_m[i]);
					fwrite(&RDV[cont][i], sizeof(uint32_t), 1,voteOutput);
					fwrite(vTable[cont][i].trackingCode, sizeof(uint8_t), SHA512HashSize,voteOutput);
					fwrite(&vTable[cont][i].timer, sizeof(uint32_t), 1,voteOutput);
					for (int j = 0; j < 2; j++) {
						fwrite(vTable[cont][i].commit.c1[j]->coeffs, sizeof(uint32_t), vTable[cont][i].commit.c1[j]->length,voteOutput);
						fwrite(vTable[cont][i].commit.c2[j]->coeffs, sizeof(uint32_t), vTable[cont][i].commit.c2[j]->length,voteOutput);
						nmod_poly_clear(com_aux[i].c1[j]);
						nmod_poly_clear(com_aux[i].c2[j]);
						for (int w = 0; w < WIDTH; w++){
							nmod_poly_clear(r_aux[i][w][j]);
						}
					}
				}
				fclose(voteOutput);
			} else {
				printf("ERRO ZKP\n");
			}
		}
	}

	/* TODO: Sign ZKP result and final tracking code */

	for (int cont = 0; cont < CONTESTS; cont++) {
		for (int i = 0; i < VOTERS; i++) {
			finalizeVoteTable(&vTable[cont][i]);
		}
	}
	commit_keyfree(&key);
	commit_finish();
	flint_randclear(rand);
	flint_cleanup();

}

int createQRTrackingCode() {
	uint8_t numberActiveContests = 0;

	for (uint8_t cont = 0; cont < CONTESTS; cont++) {
			if (((numberContests >> cont) & 1) == 1) {
				for (int i = 0; i < SHA512HashSize; i++) {
					QRCodeTrackingCode[numberActiveContests*(SHA512HashSize+sizeof(uint32_t))+i] =
								trackingCode[cont][i];
				}
				for (int j = 0; j < 4; j++){
					QRCodeTrackingCode[SHA512HashSize+numberActiveContests*(SHA512HashSize+sizeof(uint32_t))+j] = 
								(timer[cont]>>(j*8))&0xFF;
				}
				numberActiveContests++;
			}
	}
	return numberActiveContests*(SHA512HashSize+sizeof(uint32_t));
}



void verifyVote (uint8_t *QRTrack, uint8_t *QRSpoilTrack, uint8_t *QRSpoilNon, uint32_t *QRSpoilVot) {
	SHA512Context sha;
	commit_t tmpCom[CONTESTS];
	nmod_poly_t _m[CONTESTS];
	nmod_poly_t aux;
	uint32_t timerInt[CONTESTS];
	uint32_t coeffValue;
	uint64_t *coeffs;
	uint8_t newTrCode[CONTESTS][SHA512HashSize];
	pcrt_poly_t rnd[CONTESTS][WIDTH];
	int index;
	int verified=TRUE;

	uint8_t QRTrackingCode[CONTESTS*(SHA512HashSize+sizeof(uint32_t))];
	uint8_t QRSpoilTrackingCode[CONTESTS*SHA512HashSize];
	uint8_t QRSpoilNonce[CONTESTS*WIDTH*(DEGREE/4)]; // Degree*2/8
	uint32_t QRSpoilVotes[CONTESTS];
	uint8_t numberActiveContests=0;

	/* Initialize internal vectors with external vectors*/
	for (uint8_t cont = 0; cont < CONTESTS; cont++) {
			if (((numberContests >> cont) & 1) == 1) {
				numberActiveContests++;
			}
	}
	memmove(QRTrackingCode,QRTrack,numberActiveContests*(SHA512HashSize+sizeof(uint32_t)));
	memmove(QRSpoilTrackingCode,QRSpoilTrack,numberActiveContests*SHA512HashSize);
	memmove(QRSpoilNonce, QRSpoilNon, numberActiveContests*WIDTH*(DEGREE/4));
	memmove(QRSpoilVotes, QRSpoilVot, numberActiveContests*4);

	for (uint8_t cont = 0; cont < numberActiveContests; cont++) {
		nmod_poly_init(_m[cont], MODP);
		nmod_poly_zero(_m[cont]);
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_init(rnd[cont][i][j], MODP);
				nmod_poly_zero(rnd[cont][i][j]);
			}
		}
		for (int i = 0; i < WIDTH; i++) {
			nmod_poly_init(aux, MODP);
			nmod_poly_zero(aux);
			for (int coeff = 0; coeff < DEGREE; coeff++) {
				index=floor(coeff/4);
				coeffValue = QRSpoilNonce[cont*(WIDTH*(DEGREE*2/8))+i*(DEGREE*2/8)+index] >> (2*(coeff%4));
				coeffValue &= 0x03; //only the two first bits
				coeffValue += (MODP-1);
				nmod_poly_set_coeff_ui(aux,coeff,coeffValue);
			}
			pcrt_poly_convert(rnd[cont][i], aux);
			nmod_poly_zero(aux);
			nmod_poly_clear(aux);
		}

		timerInt[cont] = QRTrackingCode[SHA512HashSize+cont*(SHA512HashSize+sizeof(uint32_t))] |
					QRTrackingCode[SHA512HashSize+cont*(SHA512HashSize+sizeof(uint32_t))+1]<<8 |
						QRTrackingCode[SHA512HashSize+cont*(SHA512HashSize+sizeof(uint32_t))+2]<<16 |
							QRTrackingCode[SHA512HashSize+cont*(SHA512HashSize+sizeof(uint32_t))+3]<<24;
		nmod_poly_set_coeff_ui(_m[cont], 0, QRSpoilVotes[cont]);

		commit_doit(&tmpCom[cont], _m[cont], &key, rnd[cont]);

		/* Parse the commitment to coeffs variable */
		index = 0;
		coeffs = (uint64_t*)malloc(sizeof(uint64_t)*(nmod_poly_length(tmpCom[cont].c1[0])+
														nmod_poly_length(tmpCom[cont].c1[1])+
														nmod_poly_length(tmpCom[cont].c2[0])+
															nmod_poly_length(tmpCom[cont].c2[1])));

		for (int i = 0; i < nmod_poly_length(tmpCom[cont].c1[0]); i++){
			coeffs[i] = nmod_poly_get_coeff_ui(tmpCom[cont].c1[0],i);
		}
		index = nmod_poly_length(tmpCom[cont].c1[0]);

		for (int i = 0; i < nmod_poly_length(tmpCom[cont].c1[1]); i++){
			coeffs[i+index] = nmod_poly_get_coeff_ui(tmpCom[cont].c1[1],i);
		}
		index+=nmod_poly_length(tmpCom[cont].c1[1]);

		for (int i = 0; i < nmod_poly_length(tmpCom[cont].c2[0]); i++){
			coeffs[i+index] = nmod_poly_get_coeff_ui(tmpCom[cont].c2[0],i);
		}
		index+=nmod_poly_length(tmpCom[cont].c2[0]);

		for (int i = 0; i < nmod_poly_length(tmpCom[cont].c2[1]); i++){
			coeffs[i+index] = nmod_poly_get_coeff_ui(tmpCom[cont].c2[1],i);
		}
		index+=nmod_poly_length(tmpCom[cont].c2[1]);


		/* Compute tracking code */
		SHA512Reset(&sha);

		SHA512Input(&sha, &QRSpoilTrackingCode[cont*SHA512HashSize], SHA512HashSize);

		SHA512Input(&sha, (const uint8_t*)&timerInt[cont], 4);

		SHA512Input(&sha, (const uint8_t*)coeffs, index * sizeof(uint64_t));

		SHA512Result(&sha, newTrCode[cont]);

		free(coeffs);
		for (int a = 0; a < SHA512HashSize; a++){
			if(newTrCode[cont][a]!=QRTrackingCode[cont*(SHA512HashSize+sizeof(uint32_t))+a]) {
				verified=FALSE;
			}
		}
	}
	if (verified==TRUE){
		printf("(SUCESSO) Tracking Code corresponde aos votos\n");
	} else {
		printf("(ERRO) Tracking Code nao corresponde aos votos\n");
	}

	for (uint8_t cont = 0; cont < numberActiveContests; cont++) {
		commit_free(&tmpCom[cont]);
		nmod_poly_zero(_m[cont]);
		nmod_poly_clear(_m[cont]);
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_zero(rnd[cont][i][j]);
				nmod_poly_clear(rnd[cont][i][j]);
			}
		}
	}
	
}

int numberTotalvoters() {
	return voteNumber;
}