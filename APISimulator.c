#include "APISimulator.h"



typedef struct _VoteTable {
	commit_t commit;
	pcrt_poly_t r[WIDTH];
	nmod_poly_t vote;
	uint8_t trackingCode[SHA512HashSize];
	uint32_t timer;
} VoteTable;

static int voteNumber;
uint8_t pubSignKey[pqcrystals_dilithium2_PUBLICKEYBYTES];
static uint8_t privSignKey[pqcrystals_dilithium2_SECRETKEYBYTES];
uint8_t QRCodeSign[pqcrystals_dilithium2_BYTES];
size_t tamSig;
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
static int tamQRCodeTrackingCode;
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
static void printCommitKey(commitkey_t *key){
	for(int w = 0; w < WIDTH; w++){
		for(int h = 0; h < HEIGHT; h++){
			for (int k = 0; k < 2; k++){
				printf("\n\n");
				nmod_poly_print(key->B1[h][w][k]);
			}
		}
		for (int k = 0; k < 2; k++){
			printf("\n\n");
			nmod_poly_print(key->b2[w][k]);
		}
	}
	
}


static void escreverArquivoMp_ptr (SHA512Context *sha, mp_ptr ptr, size_t typ, size_t len, FILE *nomeArquivo) {
	uint64_t filler = 0x00;
	int fullLen=DEGREE;

	if(len<=DEGCRT){
		fullLen = DEGCRT;
	}
	for (int i = 0; i < fullLen; i++) {
		if(i<len){
			fwrite(ptr+i, typ, 1,nomeArquivo);
			SHA512Input(sha,(const uint8_t*)ptr+i,typ);
		} else {
			fwrite(&filler, typ, 1,nomeArquivo);
			SHA512Input(sha,(const uint8_t*)&filler, typ);
		}
		
	}
}

static void lerArquivoVoteOutput (char voteOutputName[20], uint8_t HTail[SHA512HashSize], uint8_t HHead[SHA512HashSize], 
							uint8_t HTrackCode[VOTERS][SHA512HashSize], time_t vTime[VOTERS], commit_t com[VOTERS], int numVoters) {
	FILE *voteOutput;

	for (int i = 0; i < numVoters; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_init(com[i].c1[j], MODP);
			nmod_poly_init(com[i].c2[j], MODP);
			nmod_poly_fit_length(com[i].c1[j], DEGCRT);
			nmod_poly_fit_length(com[i].c2[j], DEGCRT);
			nmod_poly_zero(com[i].c1[j]);
			nmod_poly_zero(com[i].c2[j]);
		}
	}

	voteOutput = fopen(voteOutputName,"r");
	if (voteOutput != NULL) {
		fread(HTail,sizeof(uint8_t),SHA512HashSize,voteOutput);
		fread(HHead,sizeof(uint8_t),SHA512HashSize,voteOutput);
		for (int i = 0; i < numVoters; i++) {
			fread(HTrackCode[i],sizeof(uint8_t),SHA512HashSize,voteOutput);
			fread(&vTime[i],sizeof(uint32_t),1,voteOutput);
			for (int j = 0; j < 2; j++) {
				com[i].c1[j]->length = DEGCRT;
				com[i].c2[j]->length = DEGCRT;

				for (int coeff = 0; coeff < DEGCRT; coeff++) {
					fread(com[i].c1[j]->coeffs+coeff, sizeof(uint32_t), 1, voteOutput);
					*(com[i].c1[j]->coeffs+coeff)&=0xFFFFFFFF;
				}
				
				for (int coeff = 0; coeff < DEGCRT; coeff++) {
					fread(com[i].c2[j]->coeffs+coeff, sizeof(uint32_t), 1, voteOutput);
					*(com[i].c2[j]->coeffs+coeff)&=0xFFFFFFFF;
				}
			}
		}
		
	}
	fclose(voteOutput);
}

static void lerArquivoRDV (char RDVOutputName[20], nmod_poly_t _m[VOTERS], int numVoters) {
	FILE *RDVOutput;
	uint32_t vote;

	for (int i = 0; i < numVoters; i++) {
		nmod_poly_init(_m[i], MODP);
		nmod_poly_zero(_m[i]);
	}

	RDVOutput = fopen(RDVOutputName,"r");
	if (RDVOutput != NULL) {
		for (int i = 0; i < numVoters; i++) {
			if (fscanf(RDVOutput,"%u",&vote) != EOF) {
				nmod_poly_set_coeff_ui(_m[i],0,vote);
			}
		}
	}
	fclose(RDVOutput);
}

static void lerArquivoZKP (char ZKPOutputName[20], nmod_poly_t rho, nmod_poly_t beta,
					nmod_poly_t s[VOTERS], commit_t d[VOTERS],
					nmod_poly_t t[VOTERS][2], nmod_poly_t _t[VOTERS][2],
					nmod_poly_t u[VOTERS][2], nmod_poly_t y[VOTERS][WIDTH][2], 
					nmod_poly_t _y[VOTERS][WIDTH][2], int numVoters) {
	FILE *ZKPOutput;

	nmod_poly_init(rho, MODP);
	nmod_poly_init(beta, MODP);

	nmod_poly_fit_length(rho, DEGREE);
	nmod_poly_fit_length(beta, DEGREE);

	nmod_poly_zero(rho);
	nmod_poly_zero(beta);
	

	for (int i = 0; i < numVoters; i++) {
		nmod_poly_init(s[i], MODP);

		nmod_poly_fit_length(s[i],DEGREE);

		nmod_poly_zero(s[i]);

		for (int j = 0; j < 2; j++) {
			nmod_poly_init(d[i].c1[j], MODP);
			nmod_poly_init(d[i].c2[j], MODP);
			nmod_poly_init(t[i][j], MODP);
			nmod_poly_init(_t[i][j], MODP);
			nmod_poly_init(u[i][j], MODP);
			for (int w = 0; w < WIDTH; w++) {
				nmod_poly_init(y[i][w][j], MODP);
				nmod_poly_init(_y[i][w][j], MODP);
			}


			nmod_poly_fit_length(d[i].c1[j], DEGCRT);
			nmod_poly_fit_length(d[i].c2[j], DEGCRT);
			nmod_poly_fit_length(t[i][j], DEGCRT);
			nmod_poly_fit_length(_t[i][j], DEGCRT);
			nmod_poly_fit_length(u[i][j], DEGCRT);
			for (int w = 0; w < WIDTH; w++) {
				nmod_poly_fit_length(y[i][w][j], DEGCRT);
				nmod_poly_fit_length(_y[i][w][j], DEGCRT);
			}

			nmod_poly_zero(d[i].c1[j]);
			nmod_poly_zero(d[i].c2[j]);
			nmod_poly_zero(t[i][j]);
			nmod_poly_zero(_t[i][j]);
			nmod_poly_zero(u[i][j]);
			for (int w = 0; w < WIDTH; w++) {
				nmod_poly_zero(y[i][w][j]);
				nmod_poly_zero(_y[i][w][j]);
			}

		}
	}

	ZKPOutput = fopen(ZKPOutputName,"r");
	if (ZKPOutput != NULL) {
		rho->length = DEGREE;
		beta->length = DEGREE;

		for (int coeff = 0; coeff < DEGREE; coeff++) {
			fread(rho->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
			*(rho->coeffs+coeff)&=0xFFFFFFFF;
		}

		for (int coeff = 0; coeff < DEGREE; coeff++) {
			fread(beta->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
			*(beta->coeffs+coeff)&=0xFFFFFFFF;
		}

		s[0]->length = DEGREE;
		for (int coeff = 0; coeff < DEGREE; coeff++) {
			fread(s[0]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
			*(s[0]->coeffs+coeff)&=0xFFFFFFFF;
		}

		for (int i = 1; i < numVoters-1; i++) {
			s[i]->length = DEGREE;

			for (int coeff = 0; coeff < DEGREE; coeff++) {
			fread(s[i]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
			*(s[i]->coeffs+coeff)&=0xFFFFFFFF;
			}
		}

		for (int i = 0; i < numVoters; i++){
			for (int j = 0; j < 2; j++) {
				d[i].c1[j]->length = DEGCRT;
				d[i].c2[j]->length = DEGCRT;
				t[i][j]->length = DEGCRT;
				_t[i][j]->length = DEGCRT;
				u[i][j]->length = DEGCRT;

				for (int coeff = 0; coeff < DEGCRT; coeff++) {
					fread(d[i].c1[j]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
					*(d[i].c1[j]->coeffs+coeff)&=0xFFFFFFFF;
				}

				for (int coeff = 0; coeff < DEGCRT; coeff++) {
					fread(d[i].c2[j]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
					*(d[i].c2[j]->coeffs+coeff)&=0xFFFFFFFF;
				}

				for (int coeff = 0; coeff < DEGCRT; coeff++) {
					fread(t[i][j]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
					*(t[i][j]->coeffs+coeff)&=0xFFFFFFFF;
				}

				for (int coeff = 0; coeff < DEGCRT; coeff++) {
					fread(_t[i][j]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
					*(_t[i][j]->coeffs+coeff)&=0xFFFFFFFF;
				}

				for (int coeff = 0; coeff < DEGCRT; coeff++) {
					fread(u[i][j]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
					*(u[i][j]->coeffs+coeff)&=0xFFFFFFFF;
				}

				for (int w = 0; w < WIDTH; w++) {
					y[i][w][j]->length = DEGCRT;
					_y[i][w][j]->length = DEGCRT;

					for (int coeff = 0; coeff < DEGCRT; coeff++) {
						fread(y[i][w][j]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
						*(y[i][w][j]->coeffs+coeff)&=0xFFFFFFFF;
					}

					for (int coeff = 0; coeff < DEGCRT; coeff++) {
						fread(_y[i][w][j]->coeffs+coeff, sizeof(uint32_t), 1, ZKPOutput);
						*(_y[i][w][j]->coeffs+coeff)&=0xFFFFFFFF;
					}
				}
			}
		}
	}
	fclose(ZKPOutput);

}

static void HashMp_ptr(SHA512Context *sha, mp_ptr ptr, size_t typ, size_t len) {
	uint64_t filler = 0x00;
	int fullLen=DEGREE;


	if(len<=DEGCRT){
		fullLen = DEGCRT;
	}
	
	for (int i = 0; i < fullLen; i++) {
		if(i<len){
			
			SHA512Input(sha,(const uint8_t*)ptr+i,typ);
		} else {
			
			SHA512Input(sha,(const uint8_t*)&filler, typ);
		}
		
	}
}

static void Hash256Mp_ptr(SHA256Context *sha, mp_ptr ptr, size_t typ, size_t len) {
	uint64_t filler = 0x00;
	int fullLen=DEGREE;


	if(len<=DEGCRT){
		fullLen = DEGCRT;
	}
	
	for (int i = 0; i < fullLen; i++) {
		if(i<len){
			
			SHA256Input(sha,(const uint8_t*)ptr+i,typ);
		} else {
			
			SHA256Input(sha,(const uint8_t*)&filler, typ);
		}
		
	}
}


int rej_sampling(nmod_poly_t z[WIDTH][2], nmod_poly_t v[WIDTH][2], uint64_t s2) {
	double r, M = 1.75;
	int64_t seed, dot, norm;
	mpf_t u;
	int64_t c0, c1;
	nmod_poly_t t0, t1;
	uint8_t buf[8];
	gmp_randstate_t state;
	int result;

	mpf_init(u);
	nmod_poly_init(t0, MODP);
	nmod_poly_init(t1, MODP);
	gmp_randinit_mt(state);

	getrandom(buf, sizeof(buf), 0);
	memcpy(&seed, buf, sizeof(buf));
	gmp_randseed_ui(state, seed);
	mpf_urandomb(u, state, mpf_get_default_prec());

	norm = dot = 0;
	for (int i = 0; i < WIDTH; i++) {
		pcrt_poly_rec(t0, z[i]);
		pcrt_poly_rec(t1, v[i]);
		for (int j = 0; j < DEGREE; j++) {
			c0 = nmod_poly_get_coeff_ui(t0, j);
			c1 = nmod_poly_get_coeff_ui(t1, j);
			if (c0 > MODP / 2)
				c0 -= MODP;
			if (c1 > MODP / 2)
				c1 -= MODP;
			dot += c0 * c1;
			norm += c1 * c1;
		}
	}

	r = -2.0 * dot + norm;
	r = r / (2.0 * s2);
	r = exp(r) / M;

	result = mpf_get_d(u) > r;

	mpf_clear(u);
	nmod_poly_clear(t0);
	nmod_poly_clear(t1);
	return result;
}

void lin_hash(nmod_poly_t d[2], commitkey_t *key, commit_t x, commit_t y,
		nmod_poly_t alpha, nmod_poly_t beta, nmod_poly_t u[2],
		nmod_poly_t t[2], nmod_poly_t _t[2]) {
	SHA256Context sha;
	uint8_t hash[SHA256HashSize];
	uint32_t buf;

	SHA256Reset(&sha);

	/* Hash public key. */
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			for (int k = 0; k < 2; k++) {
				Hash256Mp_ptr(&sha,key->B1[i][j][k]->coeffs,sizeof(uint32_t),key->B1[i][j][k]->length);
				if (i == 0) {
					Hash256Mp_ptr(&sha,key->b2[j][k]->coeffs,sizeof(uint32_t),key->b2[j][k]->length);
				}
			}
		}
	}

	/* Hash alpha, beta from linear relation. */

	Hash256Mp_ptr(&sha,alpha->coeffs,sizeof(uint32_t),alpha->length);
	Hash256Mp_ptr(&sha,beta->coeffs,sizeof(uint32_t),beta->length);

	/* Hash [x], [x'], t, t' in CRT representation. */
	for (int i = 0; i < 2; i++) {
		Hash256Mp_ptr(&sha,x.c1[i]->coeffs,sizeof(uint32_t),x.c1[i]->length);
		Hash256Mp_ptr(&sha,x.c2[i]->coeffs,sizeof(uint32_t),x.c2[i]->length);
		Hash256Mp_ptr(&sha,y.c1[i]->coeffs,sizeof(uint32_t),y.c1[i]->length);
		Hash256Mp_ptr(&sha,y.c2[i]->coeffs,sizeof(uint32_t),y.c2[i]->length);
		Hash256Mp_ptr(&sha,u[i]->coeffs,sizeof(uint32_t),u[i]->length);
		Hash256Mp_ptr(&sha,t[i]->coeffs,sizeof(uint32_t),t[i]->length);
		Hash256Mp_ptr(&sha,_t[i]->coeffs,sizeof(uint32_t),_t[i]->length);
	}

	SHA256Result(&sha, hash);

	/* Sample challenge from RNG seeded with hash. */
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
	nmod_poly_sub(d[1], d[0], d[1]);
	nmod_poly_rem(d[0], d[1], *commit_irred(0));
	nmod_poly_rem(d[1], d[1], *commit_irred(1));
}

static void lin_prover(nmod_poly_t y[WIDTH][2], nmod_poly_t _y[WIDTH][2],
		nmod_poly_t t[2], nmod_poly_t _t[2], nmod_poly_t u[2],
		commit_t x, commit_t _x, commitkey_t *key, nmod_poly_t alpha,
		nmod_poly_t beta, nmod_poly_t r[WIDTH][2], nmod_poly_t _r[WIDTH][2],
		int l) {
	nmod_poly_t tmp, d[2], dr[WIDTH][2], _dr[WIDTH][2];
	int rej0, rej1;
	// Compute sigma^2 = (11 * v * beta * sqrt(k * N))^2.
	uint64_t sigma_sqr = 11 * NONZERO * BETA;
	sigma_sqr *= sigma_sqr * DEGREE * WIDTH;

	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_init(dr[i][j], MODP);
			nmod_poly_init(_dr[i][j], MODP);
		}
	}
	nmod_poly_init(tmp, MODP);
	nmod_poly_init(d[0], MODP);
	nmod_poly_init(d[1], MODP);

	do {
		for (int i = 0; i < 2; i++) {
			nmod_poly_zero(t[i]);
			nmod_poly_zero(_t[i]);
			nmod_poly_zero(u[i]);
			nmod_poly_zero(d[i]);
		}

		for (int i = 0; i < WIDTH; i++) {
			commit_sample_gauss_crt(y[i]);
			commit_sample_gauss_crt(_y[i]);
		}
		for (int i = 0; i < HEIGHT; i++) {
			for (int j = 0; j < WIDTH; j++) {
				for (int k = 0; k < 2; k++) {
					nmod_poly_mulmod(tmp, key->B1[i][j][k], y[j][k],
							*commit_irred(k));
					nmod_poly_add(t[k], t[k], tmp);
					nmod_poly_mulmod(tmp, key->B1[i][j][k], _y[j][k],
							*commit_irred(k));
					nmod_poly_add(_t[k], _t[k], tmp);
				}
			}
		}

		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_mulmod(tmp, key->b2[i][j], y[i][j], *commit_irred(j));
				nmod_poly_mulmod(tmp, tmp, alpha, *commit_irred(j));
				nmod_poly_add(u[j], u[j], tmp);
				nmod_poly_mulmod(tmp, key->b2[i][j], _y[i][j],
						*commit_irred(j));
				nmod_poly_sub(u[j], u[j], tmp);
			}
		}

		/* Sample challenge. */
		lin_hash(d, key, x, _x, alpha, beta, u, t, _t);

		/* Prover */
		for (int i = 0; i < WIDTH; i++) {
			for (int j = 0; j < 2; j++) {
				nmod_poly_mulmod(dr[i][j], d[j], r[i][j], *commit_irred(j));
				nmod_poly_add(y[i][j], y[i][j], dr[i][j]);
				nmod_poly_mulmod(_dr[i][j], d[j], _r[i][j], *commit_irred(j));
				nmod_poly_add(_y[i][j], _y[i][j], _dr[i][j]);
			}
		}
		rej0 = rej_sampling(y, dr, sigma_sqr);
		rej1 = rej_sampling(_y, _dr, sigma_sqr);
	} while (rej0 || rej1);

	for (int i = 0; i < WIDTH; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_clear(dr[i][j]);
			nmod_poly_clear(_dr[i][j]);
		}
	}
	nmod_poly_clear(tmp);
	for (int i = 0; i < 2; i++) {
		nmod_poly_clear(d[i]);
	}
}

static int lin_verifier(nmod_poly_t y[WIDTH][2], nmod_poly_t _y[WIDTH][2],
		nmod_poly_t t[2], nmod_poly_t _t[2], nmod_poly_t u[2],
		commit_t com, commit_t x, commitkey_t *key,
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
	lin_hash(_d, key, com, x, alpha, beta, u, t, _t);

	/* Verifier checks norm, reconstruct from CRT representation. */
	for (int i = 0; i < WIDTH; i++) {
		pcrt_poly_rec(z[i], y[i]);
		pcrt_poly_rec(_z[i], _y[i]);
		assert(commit_norm2_sqr(z[i]) <=
				(uint64_t) 4 * DEGREE * SIGMA_C * SIGMA_C);
		assert(commit_norm2_sqr(_z[i]) <=
				(uint64_t) 4 * DEGREE * SIGMA_C * SIGMA_C);
	}
	/* Verifier computes B1z and B1z'. */
	for (int i = 0; i < HEIGHT; i++) {
		for (int j = 0; j < WIDTH; j++) {
			for (int k = 0; k < 2; k++) {
				nmod_poly_mulmod(tmp, key->B1[i][j][k], y[j][k],
						*commit_irred(k));
				nmod_poly_add(v[k], v[k], tmp);
				nmod_poly_mulmod(tmp, key->B1[i][j][k], _y[j][k],
						*commit_irred(k));
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

void shuffle_hash(nmod_poly_t beta, commit_t c[VOTERS], commit_t d[VOTERS],
		nmod_poly_t _m[VOTERS], nmod_poly_t rho, int MSGS) {
	flint_rand_t rand;
	SHA256Context sha;
	uint8_t hash[SHA256HashSize];
	uint64_t seed0, seed1, seed2, seed3;

	SHA256Reset(&sha);

	for (int i = 0; i < MSGS; i++) {
		Hash256Mp_ptr(&sha,_m[i]->coeffs,sizeof(uint32_t),_m[i]->length);
		for (int j = 0; j < 2; j++) {
			Hash256Mp_ptr(&sha,c[i].c1[j]->coeffs,sizeof(uint32_t),c[i].c1[j]->length);
			Hash256Mp_ptr(&sha,c[i].c2[j]->coeffs,sizeof(uint32_t),c[i].c2[j]->length);
			Hash256Mp_ptr(&sha,d[i].c1[j]->coeffs,sizeof(uint32_t),d[i].c1[j]->length);
			Hash256Mp_ptr(&sha,d[i].c2[j]->coeffs,sizeof(uint32_t),d[i].c2[j]->length);
		}
	}
	Hash256Mp_ptr(&sha,rho->coeffs,sizeof(uint32_t),rho->length);
	
	SHA256Result(&sha, hash);

	flint_randinit(rand);
	memcpy(&seed0, hash, sizeof(uint64_t));
	memcpy(&seed1, hash + sizeof(uint64_t), sizeof(uint64_t));
	memcpy(&seed2, hash + 2 * sizeof(uint64_t), sizeof(uint64_t));
	memcpy(&seed3, hash + 3 * sizeof(uint64_t), sizeof(uint64_t));
	seed0 ^= seed2;
	seed1 ^= seed3;
	flint_randseed(rand, seed0, seed1);
	commit_sample_rand(beta, rand, DEGREE);
	flint_randclear(rand);
}

static void shuffle_prover(nmod_poly_t y[VOTERS][WIDTH][2],
		nmod_poly_t _y[VOTERS][WIDTH][2], nmod_poly_t t[VOTERS][2],
		nmod_poly_t _t[VOTERS][2], nmod_poly_t u[VOTERS][2], commit_t d[VOTERS],
		nmod_poly_t s[VOTERS], commit_t com[VOTERS], nmod_poly_t m[VOTERS],
		nmod_poly_t _m[VOTERS], nmod_poly_t r[VOTERS][WIDTH][2], nmod_poly_t rho,
		commitkey_t *key, flint_rand_t rng,
		int MSGS, char *outputFileName) {
	FILE *zkpOutput;
	SHA512Context sha;
	uint8_t HashToSign[SHA512HashSize];
	uint8_t Signature[pqcrystals_dilithium2_BYTES];
	size_t tamSig=0;
	char SignatureFileName[20];

	nmod_poly_t beta, t0, t1, theta[VOTERS], _r[VOTERS][WIDTH][2];

	nmod_poly_init(t0, MODP);
	nmod_poly_init(t1, MODP);
	nmod_poly_init(beta, MODP);
	for (int i = 0; i < VOTERS; i++) {
		nmod_poly_init(theta[i], MODP);
		for (int k = 0; k < 2; k++) {
			for (int j = 0; j < WIDTH; j++) {
				nmod_poly_init(_r[i][j][k], MODP);
			}
		}
	}

	SHA512Reset(&sha);

	zkpOutput = fopen(outputFileName, "w");
	if (zkpOutput == NULL) {
		printf("Error\n");
	}

	escreverArquivoMp_ptr(&sha,rho->coeffs, sizeof(uint32_t), rho->length, zkpOutput);

	/* Prover shifts the messages by rho. */
	for (int i = 0; i < MSGS; i++) {
		nmod_poly_sub(m[i], m[i], rho);
		nmod_poly_sub(_m[i], _m[i], rho);
	}

	/* Prover samples theta_i and computes commitments D_i. */
	commit_sample_rand(theta[0], rng, DEGREE);
	nmod_poly_mulmod(t0, theta[0], _m[0], *commit_poly());
	for (int j = 0; j < WIDTH; j++) {
		commit_sample_short_crt(_r[0][j]);
	}
	commit_doit(&d[0], t0, key, _r[0]);
	for (int i = 1; i < MSGS - 1; i++) {
		commit_sample_rand(theta[i], rng, DEGREE);
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

	shuffle_hash(beta, com, d, _m, rho, MSGS);
	escreverArquivoMp_ptr(&sha,beta->coeffs, sizeof(uint32_t), beta->length, zkpOutput);

	nmod_poly_mulmod(s[0], theta[0], _m[0], *commit_poly());
	nmod_poly_mulmod(t0, beta, m[0], *commit_poly());
	nmod_poly_sub(s[0], s[0], t0);
	nmod_poly_invmod(t0, _m[0], *commit_poly());
	nmod_poly_mulmod(s[0], s[0], t0, *commit_poly());
	escreverArquivoMp_ptr(&sha,s[0]->coeffs, sizeof(uint32_t), s[0]->length, zkpOutput);
	for (int i = 1; i < MSGS - 1; i++) {
		nmod_poly_mulmod(s[i], theta[i - 1], m[i], *commit_poly());
		nmod_poly_mulmod(t0, theta[i], _m[i], *commit_poly());
		nmod_poly_add(s[i], s[i], t0);
		nmod_poly_mulmod(t0, s[i - 1], m[i], *commit_poly());
		nmod_poly_sub(s[i], s[i], t0);
		nmod_poly_invmod(t0, _m[i], *commit_poly());
		nmod_poly_mulmod(s[i], s[i], t0, *commit_poly());
	}
	for (int i = 1; i < MSGS-1; i++) {
		escreverArquivoMp_ptr(&sha,s[i]->coeffs, sizeof(uint32_t), s[i]->length,zkpOutput);
	}

	for (int l = 0; l < MSGS; l++) {
		if (l < MSGS - 1) {
			nmod_poly_mulmod(t0, s[l], _m[l], *commit_poly());
		} else {
			nmod_poly_mulmod(t0, beta, _m[l], *commit_poly());
		}

		if (l == 0) {
			lin_prover(y[l], _y[l], t[l], _t[l], u[l], com[l], d[l], key, beta,
					t0, r[l], _r[l], l);
		} else {
			lin_prover(y[l], _y[l], t[l], _t[l], u[l], com[l], d[l], key,
					s[l - 1], t0, r[l], _r[l], l);
		}

		for (int i = 0; i < 2; i++) {
			escreverArquivoMp_ptr(&sha,d[l].c1[i]->coeffs, sizeof(uint32_t), d[l].c1[i]->length,zkpOutput);
			escreverArquivoMp_ptr(&sha,d[l].c2[i]->coeffs, sizeof(uint32_t), d[l].c2[i]->length,zkpOutput);
			escreverArquivoMp_ptr(&sha,t[l][i]->coeffs, sizeof(uint32_t), t[l][i]->length,zkpOutput);
			escreverArquivoMp_ptr(&sha,_t[l][i]->coeffs, sizeof(uint32_t), _t[l][i]->length,zkpOutput);
			escreverArquivoMp_ptr(&sha,u[l][i]->coeffs, sizeof(uint32_t), u[l][i]->length,zkpOutput);

			for (int j = 0; j < WIDTH; j++) {
				escreverArquivoMp_ptr(&sha,y[l][j][i]->coeffs, sizeof(uint32_t), y[l][j][i]->length,zkpOutput);
				escreverArquivoMp_ptr(&sha,_y[l][j][i]->coeffs, sizeof(uint32_t), _y[l][j][i]->length,zkpOutput);
			}
		}
	}

	fclose(zkpOutput);

	snprintf(SignatureFileName,20,"Sig%s", outputFileName);
	zkpOutput = fopen(SignatureFileName, "w");

	SHA512Result(&sha, HashToSign);
	
	pqcrystals_dilithium2aes_ref_signature(Signature, &tamSig,
                                           HashToSign, SHA512HashSize,
                                           privSignKey);
	fwrite(Signature, sizeof(uint8_t), tamSig,zkpOutput);
	fclose(zkpOutput);

	nmod_poly_clear(t0);
	nmod_poly_clear(t1);
	nmod_poly_clear(beta);
	for (int i = 0; i < VOTERS; i++) {
		nmod_poly_clear(theta[i]);
		for (int k = 0; k < 2; k++) {
			for (int j = 0; j < WIDTH; j++) {
				nmod_poly_clear(_r[i][j][k]);
			}
		}
	}
}

static int shuffle_verifier(nmod_poly_t y[VOTERS][WIDTH][2],
		nmod_poly_t _y[VOTERS][WIDTH][2], nmod_poly_t t[VOTERS][2],
		nmod_poly_t _t[VOTERS][2], nmod_poly_t u[VOTERS][2], commit_t d[VOTERS],
		nmod_poly_t s[VOTERS], commit_t com[VOTERS], nmod_poly_t _m[VOTERS],
		nmod_poly_t rho, commitkey_t *key, int MSGS) {
	int result = 1;
	nmod_poly_t beta, t0;

	nmod_poly_init(t0, MODP);
	nmod_poly_init(beta, MODP);

	shuffle_hash(beta, com, d, _m, rho, MSGS);
	
	/* Now verify each \Prod_LIN instance, one for each commitment. */
	for (int l = 0; l < MSGS; l++) {
		if (l < MSGS - 1) {
			nmod_poly_mulmod(t0, s[l], _m[l], *commit_poly());
		} else {
			nmod_poly_mulmod(t0, beta, _m[l], *commit_poly());
		}

		if (l == 0) {
			result &=
					lin_verifier(y[l], _y[l], t[l], _t[l], u[l], com[l], d[l],
					key, beta, t0, l, MSGS);
		} else {
			result &=
					lin_verifier(y[l], _y[l], t[l], _t[l], u[l], com[l], d[l],
					key, s[l - 1], t0, l, MSGS);
		}
	}

	nmod_poly_clear(t0);
	nmod_poly_clear(beta);
	return result;
}

static int run(commit_t com[VOTERS], nmod_poly_t m[VOTERS], nmod_poly_t _m[VOTERS],
		nmod_poly_t r[VOTERS][WIDTH][2], commitkey_t *key, flint_rand_t rng,
		int MSGS, char *outputFileName) {
	int flag, result = 1;
	commit_t d[VOTERS];
	nmod_poly_t t0, t1, rho, s[VOTERS], u[VOTERS][2];
	nmod_poly_t y[VOTERS][WIDTH][2], _y[VOTERS][WIDTH][2], t[VOTERS][2], _t[VOTERS][2];

	nmod_poly_init(t0, MODP);
	nmod_poly_init(t1, MODP);
	nmod_poly_init(rho, MODP);
	for (int i = 0; i < VOTERS; i++) {
		nmod_poly_init(s[i], MODP);
		for (int k = 0; k < 2; k++) {
			nmod_poly_init(t[i][k], MODP);
			nmod_poly_init(_t[i][k], MODP);
			nmod_poly_init(u[i][k], MODP);
			for (int j = 0; j < WIDTH; j++) {
				nmod_poly_init(y[i][j][k], MODP);
				nmod_poly_init(_y[i][j][k], MODP);
			}
		}
	}

	/* Verifier samples \rho that is different from the messages, and \beta. */
	do {
		flag = 1;
		commit_sample_rand(rho, rng, DEGREE);
		for (int i = 0; i < MSGS; i++) {
			if (nmod_poly_equal(rho, _m[i]) == 1) {
				flag = 0;
			}
		}
	} while (flag == 0);


	/* Verifier shifts the commitments by rho. */
	nmod_poly_rem(t0, rho, *commit_irred(0));
	nmod_poly_rem(t1, rho, *commit_irred(1));
	for (int i = 0; i < MSGS; i++) {
		nmod_poly_sub(com[i].c2[0], com[i].c2[0], t0);
		nmod_poly_sub(com[i].c2[1], com[i].c2[1], t1);
	}

	shuffle_prover(y, _y, t, _t, u, d, s, com, m, _m, r, rho, key, rng, MSGS, outputFileName);

	//result = shuffle_verifier(y, _y, t, _t, u, d, s, com, _m, rho, key, MSGS);

	nmod_poly_clear(t0);
	nmod_poly_clear(t1);
	nmod_poly_clear(rho);
	for (int i = 0; i < MSGS; i++) {
		for (int j = 0; j < 2; j++){
			nmod_poly_clear(d[i].c1[j]);
			nmod_poly_clear(d[i].c2[j]);
		}
	}
	for (int i = 0; i < VOTERS; i++) {
		nmod_poly_clear(s[i]);
		for (int k = 0; k < 2; k++) {
			nmod_poly_clear(t[i][k]);
			nmod_poly_clear(_t[i][k]);
			nmod_poly_clear(u[i][k]);
			for (int j = 0; j < WIDTH; j++) {
				nmod_poly_clear(y[i][j][k]);
				nmod_poly_clear(_y[i][j][k]);
			}
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

	/* Create Signature Key pair */
	pqcrystals_dilithium2aes_ref_keypair(pubSignKey, privSignKey);

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
		pqcrystals_dilithium2aes_ref_signature(QRCodeSign, &tamSig,
                                           QRCodeTrackingCode, tamQRCodeTrackingCode,
                                           privSignKey);
		

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
	FILE *voteOutput, *RDVOutput;
	SHA512Context sha, shaRDV;
	flint_rand_t rand;
	int res;
	commit_t com_aux[VOTERS];
	nmod_poly_t m_aux[VOTERS], _m[VOTERS];
	pcrt_poly_t r_aux[VOTERS][WIDTH];
	uint8_t closeSignal[] = "CLOSE\0";
	uint8_t HashToSign[SHA512HashSize];
	uint8_t Signature[pqcrystals_dilithium2_BYTES];
	size_t tamSig=0;
	char outputFileName[20], RDVFileName[20];

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
				SHA512Reset(&sha);
				SHA512Reset(&shaRDV);

				snprintf(outputFileName,20,"voteOutput_Cont%d", cont);
				snprintf(RDVFileName,20,"RDVOutput_Cont%d", cont);

				voteOutput = fopen(outputFileName, "w");
				RDVOutput = fopen(RDVFileName, "w");

				fwrite(H0[cont], sizeof(uint8_t), SHA512HashSize,voteOutput);
				SHA512Input(&sha, H0[cont], SHA512HashSize);

				fwrite(Hcurrent[cont], sizeof(uint8_t), SHA512HashSize,voteOutput);
				SHA512Input(&sha, Hcurrent[cont], SHA512HashSize);

				for (int i = 0; i < voteNumber; i++) {
					nmod_poly_clear(m_aux[i]);
					nmod_poly_clear(_m[i]);

					fprintf(RDVOutput, "%u",RDV[cont][i]);
					SHA512Input(&shaRDV, (const uint8_t*)&RDV[cont][i], 4);
					fprintf(RDVOutput, "\n");
					SHA512Input(&shaRDV, (const uint8_t*)"\n", 2);
					
					fwrite(vTable[cont][i].trackingCode, sizeof(uint8_t), SHA512HashSize,voteOutput);
					SHA512Input(&sha, vTable[cont][i].trackingCode, SHA512HashSize);
					fwrite(&vTable[cont][i].timer, sizeof(uint32_t), 1,voteOutput);
					SHA512Input(&sha, (const uint8_t*)&vTable[cont][i].timer, 4);

					for (int j = 0; j < 2; j++) {
						escreverArquivoMp_ptr(&sha,vTable[cont][i].commit.c1[j]->coeffs, sizeof(uint32_t), vTable[cont][i].commit.c1[j]->length,voteOutput);
						escreverArquivoMp_ptr(&sha,vTable[cont][i].commit.c2[j]->coeffs, sizeof(uint32_t), vTable[cont][i].commit.c2[j]->length,voteOutput);

						nmod_poly_clear(com_aux[i].c1[j]);
						nmod_poly_clear(com_aux[i].c2[j]);
						for (int w = 0; w < WIDTH; w++){
							nmod_poly_clear(r_aux[i][w][j]);
						}
					}
				}
				fclose(voteOutput);
				fclose(RDVOutput);

				/* Sign both files (from each hashed entry included)*/

				snprintf(outputFileName,20,"voteOutputSig_Cont%d", cont);
				snprintf(RDVFileName,20,"RDVOutputSig_Cont%d", cont);

				voteOutput = fopen(outputFileName, "w");
				RDVOutput = fopen(RDVFileName, "w");				

				SHA512Result(&sha, HashToSign);
				pqcrystals_dilithium2aes_ref_signature(Signature, &tamSig,
                                           HashToSign, SHA512HashSize,
                                           privSignKey);
				fwrite(Signature, sizeof(uint8_t), tamSig,voteOutput);

				SHA512Result(&shaRDV, HashToSign);
				pqcrystals_dilithium2aes_ref_signature(Signature, &tamSig,
                                           HashToSign, SHA512HashSize,
                                           privSignKey);
				fwrite(Signature, sizeof(uint8_t), tamSig,RDVOutput);

				fclose(voteOutput);
				fclose(RDVOutput);

			} else {
				printf("ERRO ZKP\n");
			}
		}
	}

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
	tamQRCodeTrackingCode = numberActiveContests*(SHA512HashSize+sizeof(uint32_t));
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

void validateRDV (char RDVOutputName[20], char RDVSigOutputName[20], int numVoters){
	FILE *SigFile;
	SHA512Context sha;
	uint8_t hash[SHA512HashSize];
	nmod_poly_t _m[VOTERS];
	uint32_t vote;
	uint8_t Signature[pqcrystals_dilithium2_BYTES];
	int Success = -1;

	SHA512Reset(&sha);
	lerArquivoRDV(RDVOutputName,_m,numVoters);
	for (int i = 0; i < numVoters; i++) {
		vote = nmod_poly_get_coeff_ui(_m[i],0);
		SHA512Input(&sha, (const uint8_t*)&vote, 4);
		SHA512Input(&sha, (const uint8_t*)"\n", 2);
	}
	SHA512Result(&sha, hash);

	SigFile = fopen(RDVSigOutputName, "r");
	if(SigFile != NULL){
		fread(Signature, sizeof(uint8_t), pqcrystals_dilithium2_BYTES, SigFile);
	}
	fclose(SigFile);

	Success = pqcrystals_dilithium2aes_ref_verify(Signature, pqcrystals_dilithium2_BYTES,
                                        		 hash, SHA512HashSize,
                                        		 pubSignKey);

	if (Success == 0){
		printf("\nASSINATURA DO ARQUIVO RDV VERIFICADA COM SUCESSO!\n");
	} else {
		printf("\n\nERRO! -- ASSINATURA DO ARQUIVO RDV NAO VERIFICADA -- ERRO!\n\n");
	}

	for(int i = 0; i < numVoters; i++) {
		nmod_poly_clear(_m[i]);
	}
}

void validateVoteOutput (char voteOutputName[20], char voteSigOutputName[20], int numVoters){
	FILE *SigFile;
	SHA512Context sha;
	uint8_t hash[SHA512HashSize];
	uint32_t vote;
	uint8_t Signature[pqcrystals_dilithium2_BYTES];
	uint8_t HTail[SHA512HashSize];
	uint8_t HHead[SHA512HashSize];
	uint8_t HTrackCode[VOTERS][SHA512HashSize];
	time_t vTime[VOTERS];
	commit_t com[VOTERS];
	int Success = -1;
	uint64_t *coeffs;
	int aux, result=1;
	uint8_t HCurrent[SHA512HashSize];
	uint8_t HNext[SHA512HashSize];
	uint8_t closeSignal[] = "CLOSE\0";

	SHA512Reset(&sha);

	lerArquivoVoteOutput(voteOutputName, HTail, HHead, HTrackCode, vTime, com, numVoters);

	SHA512Input(&sha, HTail, SHA512HashSize);
	SHA512Input(&sha, HHead, SHA512HashSize);

	/* Normalise polys to avoid leading zeros */
	for (int i = 0; i < numVoters; i++) {
		for (int j = 0; j < 2; j++) {
			_nmod_poly_normalise(com[i].c1[j]);
			_nmod_poly_normalise(com[i].c2[j]);
		}
	}	

	for (int i = 0; i < numVoters; i++) {
		SHA512Input(&sha, HTrackCode[i], SHA512HashSize);
		SHA512Input(&sha, (const uint8_t*)&vTime[i], 4);
		for (int j = 0; j < 2; j++) {
			HashMp_ptr(&sha, com[i].c1[j]->coeffs, sizeof(uint32_t), com[i].c1[j]->length);
			HashMp_ptr(&sha, com[i].c2[j]->coeffs, sizeof(uint32_t), com[i].c2[j]->length);
		}
	}
	SHA512Result(&sha, hash);

	SigFile = fopen(voteSigOutputName, "r");
	if(SigFile != NULL){
		fread(Signature, sizeof(uint8_t), pqcrystals_dilithium2_BYTES, SigFile);
	}
	fclose(SigFile);

	Success = pqcrystals_dilithium2aes_ref_verify(Signature, pqcrystals_dilithium2_BYTES,
                                        		 hash, SHA512HashSize,
                                        		 pubSignKey);

	if (Success == 0){
		printf("\nASSINATURA DO ARQUIVO DE COMMITS VERIFICADA COM SUCESSO!\n");
	} else {
		printf("\n\nERRO! -- ASSINATURA DO ARQUIVO DE COMMITS NAO VERIFICADA -- ERRO!\n\n");
	}

	/* Check Commitment Chain*/

	for (int j = 0; j < SHA512HashSize; j++){
		HCurrent[j]=HTail[j];
	}

	for(int i = 0; i < numVoters; i++){
		
		/* Parse the commitment to coeffs variable */
		aux = 0;
		coeffs = (uint64_t*)malloc(sizeof(uint64_t)*(nmod_poly_length(com[i].c1[0])+
														nmod_poly_length(com[i].c1[1])+
														nmod_poly_length(com[i].c2[0])+
															nmod_poly_length(com[i].c2[1])));

		for (int w = 0; w < nmod_poly_length(com[i].c1[0]); w++){
			coeffs[w] = nmod_poly_get_coeff_ui(com[i].c1[0],w);
		}
		aux = nmod_poly_length(com[i].c1[0]);

		for (int w = 0; w < nmod_poly_length(com[i].c1[1]); w++){
			coeffs[w+aux] = nmod_poly_get_coeff_ui(com[i].c1[1],w);
		}
		aux+=nmod_poly_length(com[i].c1[1]);

		for (int w = 0; w < nmod_poly_length(com[i].c2[0]); w++){
			coeffs[w+aux] = nmod_poly_get_coeff_ui(com[i].c2[0],w);
		}
		aux+=nmod_poly_length(com[i].c2[0]);

		for (int w = 0; w < nmod_poly_length(com[i].c2[1]); w++){
			coeffs[w+aux] = nmod_poly_get_coeff_ui(com[i].c2[1],w);
		}
		aux+=nmod_poly_length(com[i].c2[1]);


		/* Compute next tracking code */
		SHA512Reset(&sha);

		SHA512Input(&sha, HCurrent, SHA512HashSize);

		SHA512Input(&sha, (const uint8_t*)&vTime[i], 4);

		SHA512Input(&sha, (const uint8_t*)coeffs, aux * sizeof(uint64_t));

		SHA512Result(&sha, HNext);

		free(coeffs);

		for (int j = 0; j < SHA512HashSize; j++){
			if(HNext[j]!=HTrackCode[i][j]){
				result = 0;
			}
		}

		for (int j = 0; j < SHA512HashSize; j++){
			HCurrent[j]=HNext[j];
		}

	}
	/* Compute HHead */
	SHA512Reset(&sha);

	SHA512Input(&sha, HCurrent, SHA512HashSize);

	SHA512Input(&sha, (const uint8_t*)closeSignal, strlen((char *)closeSignal));

	SHA512Result(&sha, HNext);

	for (int j = 0; j < SHA512HashSize; j++){
		if(HNext[j]!=HHead[j]){
			result = 0;
		}
	}

	if(result == 1) {
		printf("\nHASH CHAIN DOS COMMITS VERIFICADA COM SUCESSO!\n");
	} else {
		printf("\n\nERRO! -- HASH CHAIN DOS COMMITS NAO VERIFICADA -- ERRO!\n\n");
	}

	for(int i = 0; i < numVoters; i++) {
		commit_free(&com[i]);
	}

}


void validateZKPOutput (char ZKPOutputName[20], char ZKPSigOutputName[20], 
						char RDVOutputName[20],	char voteOutputName[20], 
						int numVoters) {
	nmod_poly_t rho, beta;
	nmod_poly_t s[VOTERS];
	commit_t d[VOTERS];
	nmod_poly_t t[VOTERS][2], _t[VOTERS][2];
	nmod_poly_t u[VOTERS][2];
	nmod_poly_t y[VOTERS][WIDTH][2], _y[VOTERS][WIDTH][2];
	nmod_poly_t t0;
	uint8_t HTail[SHA512HashSize];
	uint8_t HHead[SHA512HashSize];
	uint8_t HTrackCode[VOTERS][SHA512HashSize];
	time_t vTime[VOTERS];
	commit_t com[VOTERS];
	nmod_poly_t _m[VOTERS];
	int flag, result = 1;
	flint_rand_t rand;
	commitkey_t keyTemp;
	FILE *SigFile;
	SHA512Context sha;
	uint8_t hash[SHA512HashSize];
	uint8_t Signature[pqcrystals_dilithium2_BYTES];
	int Success = -1;

	flint_randinit(rand);
    commit_setup();

	commit_keygen(&keyTemp, rand);
	
	nmod_poly_init(t0, MODP);

	lerArquivoRDV(RDVOutputName,_m,numVoters);
	lerArquivoVoteOutput(voteOutputName, HTail, HHead, HTrackCode, vTime, com, numVoters);
	lerArquivoZKP (ZKPOutputName, rho, beta,
				   s, d, t, _t,
				   u, y, _y, numVoters);

	/* Normalise polys to avoid leading zeros */
	_nmod_poly_normalise(rho);
	_nmod_poly_normalise(beta);
	for (int i = 0; i < numVoters; i++) {
		_nmod_poly_normalise(s[i]);
		for (int j = 0; j < 2; j++) {
			_nmod_poly_normalise(d[i].c1[j]);
			_nmod_poly_normalise(d[i].c2[j]);
			_nmod_poly_normalise(com[i].c1[j]);
			_nmod_poly_normalise(com[i].c2[j]);
			_nmod_poly_normalise(t[i][j]);
			_nmod_poly_normalise(_t[i][j]);
			_nmod_poly_normalise(u[i][j]);
			for (int w = 0; w < WIDTH; w++){
				_nmod_poly_normalise(y[i][w][j]);
				_nmod_poly_normalise(_y[i][w][j]);
			}
		}
	}

	SHA512Reset(&sha);

	HashMp_ptr(&sha,rho->coeffs, sizeof(uint32_t), rho->length);
	HashMp_ptr(&sha,beta->coeffs, sizeof(uint32_t), beta->length);

	HashMp_ptr(&sha,s[0]->coeffs, sizeof(uint32_t), s[0]->length);

	for (int i = 1; i < numVoters-1; i++) {
		HashMp_ptr(&sha,s[i]->coeffs, sizeof(uint32_t), s[i]->length);
	}


	for (int l = 0; l < numVoters; l++) {
		for (int i = 0; i < 2; i++) {
			HashMp_ptr(&sha,d[l].c1[i]->coeffs, sizeof(uint32_t), d[0].c1[i]->length);
			HashMp_ptr(&sha,d[l].c2[i]->coeffs, sizeof(uint32_t), d[0].c2[i]->length);
			HashMp_ptr(&sha,t[l][i]->coeffs, sizeof(uint32_t), t[l][i]->length);
			HashMp_ptr(&sha,_t[l][i]->coeffs, sizeof(uint32_t), _t[l][i]->length);
			HashMp_ptr(&sha,u[l][i]->coeffs, sizeof(uint32_t), u[l][i]->length);

			for (int j = 0; j < WIDTH; j++) {
				HashMp_ptr(&sha,y[l][j][i]->coeffs, sizeof(uint32_t), y[l][j][i]->length);
				HashMp_ptr(&sha,_y[l][j][i]->coeffs, sizeof(uint32_t), _y[l][j][i]->length);
			}
		}
	}

	SHA512Result(&sha, hash);

	SigFile = fopen(ZKPSigOutputName, "r");
	if(SigFile != NULL){
		fread(Signature, sizeof(uint8_t), pqcrystals_dilithium2_BYTES, SigFile);
	}
	fclose(SigFile);

	Success = pqcrystals_dilithium2aes_ref_verify(Signature, pqcrystals_dilithium2_BYTES,
                                        		 hash, SHA512HashSize,
                                        		 pubSignKey);

	if (Success == 0){
		printf("\nASSINATURA DO ARQUIVO DE ZKP VERIFICADA COM SUCESSO!\n");
	} else {
		printf("\n\nERRO! -- ASSINATURA DO ARQUIVO DE ZKP NAO VERIFICADA -- ERRO!\n\n");
	}

	/* Prover shifts the messages by rho */
	for (int i = 0; i < numVoters; i++) {
		nmod_poly_sub(_m[i], _m[i], rho);
	}

	/* Verifier shifts the commitment by rho. */
	for (int i = 0; i < numVoters; i++) {
		for (int j = 0; j < 2; j++) {
			nmod_poly_rem(t0, rho, *commit_irred(j));
			nmod_poly_sub(com[i].c2[j], com[i].c2[j], t0);
		}
	}

	result = shuffle_verifier(y, _y, t, _t, u, d, s, com, _m, rho, &keyTemp, numVoters);

	if (result == 1) {
		printf("\nPROVA ZKP DE SHUFFLE VERIFICADA COM SUCESSO!\n");
	} else {
		printf("\n\nERRO! -- PROVA ZKP DE SHUFFLE NAO VERIFICADA -- ERRO!\n\n");
	}

	nmod_poly_clear(t0);
	nmod_poly_clear(rho);
	nmod_poly_clear(beta);
	for(int i = 0; i < numVoters; i++) {
		commit_free(&com[i]);
		commit_free(&d[i]);
		nmod_poly_clear(_m[i]);
		nmod_poly_clear(s[i]);
		for (int j = 0; j < 2; j++){
			nmod_poly_clear(t[i][j]);
			nmod_poly_clear(_t[i][j]);
			nmod_poly_clear(u[i][j]);
			for (int w = 0; w < WIDTH; w++){
				nmod_poly_clear(y[i][w][j]);
				nmod_poly_clear(_y[i][w][j]);
			}
		}
	}
	commit_keyfree(&keyTemp);
	commit_finish();
	flint_randclear(rand);
	flint_cleanup();

}

int numberTotalvoters() {
	return voteNumber;
}