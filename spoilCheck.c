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
	uint8_t nextVoter;


  flint_randinit(rand);

  commit_setup();

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
		printf("\nVerificar voto? (0 - nao, 1 - sim)?: ");
		scanf("%hhd", &nextVoter);
		if (nextVoter) {
			checkSpoil(&key);
		}
	} while(nextVoter);


  commit_keyfree(&key);
  
	commit_finish();
	flint_randclear(rand);
	flint_cleanup();

  return 0;
}
#endif
