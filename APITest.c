#include "APISimulator.h"

int main(int argc, char *arg[]) {
  	uint32_t vote;
	uint8_t infoContest=0x3f;
	uint8_t HTail[SHA512HashSize], HHead[SHA512HashSize], HTrack[VOTERS][SHA512HashSize];
	time_t vTime[VOTERS];
	int totalVoters, tamQR;
	int chal;
	int proxEleitor;
	int eleitoresHabilitados;
	commit_t com[VOTERS],d[VOTERS];
	nmod_poly_t _m[VOTERS],res,m1,m2,mod,rho,beta;
	nmod_poly_t s[VOTERS],t[VOTERS][2],_t[VOTERS][2],u[VOTERS][2];
	nmod_poly_t y[VOTERS][WIDTH][2], _y[VOTERS][WIDTH][2];

	printf("Demonstracao do sistema de votacao E2Easy\n\n");

	Setup();

	onStart (infoContest);

	do {
		printf("\nSelecionar modo: Automatico(1) ou interativo(0): ");
		scanf("%u", &vote);
	} while (vote != 0 && vote != 1);

	if(vote == 1) {
		do {
		printf("\nSelecionar a quantidade de eleitores: ");
		scanf("%d", &eleitoresHabilitados);
		} while (eleitoresHabilitados < 0);
		for (int i = 0; i < eleitoresHabilitados; i++) {
			getrandom(&vote, sizeof(vote), 0);
			vote%=100000;
			if (vote < 10000){
				vote+=10000;
			}
			onVoterActive(vote, 0);

			getrandom(&vote, sizeof(vote), 0);
			vote%=10000;
			if (vote < 1000){
				vote+=1000;
			}
			onVoterActive(vote, 1);

			getrandom(&vote, sizeof(vote), 0);
			vote%=1000;
			if (vote < 100){
				vote+=100;
			}
			onVoterActive(vote, 2);

			getrandom(&vote, sizeof(vote), 0);
			vote%=1000;
			if (vote < 100){
				vote+=100;
			}
			onVoterActive(vote, 3);

			getrandom(&vote, sizeof(vote), 0);
			vote%=100;
			if (vote < 10){
				vote+=10;
			}
			onVoterActive(vote, 4);

			getrandom(&vote, sizeof(vote), 0);
			vote%=100;
			if (vote < 10){
				vote+=10;
			}
			onVoterActive(vote, 5);

			onChallenge (1);
		}
	} else {

		do {

			do {
				printf("\nDigite o voto para deputado estadual: ");
				scanf("%u", &vote);
			} while (vote > 99999 || vote < 10000);
			onVoterActive(vote, 0);

			do {
				printf("\nDigite o voto para deputado federal: ");
				scanf("%u", &vote);
			} while (vote > 9999 || vote < 1000);
			onVoterActive(vote, 1);

			do {
				printf("\nDigite o voto para senador 1: ");
				scanf("%u", &vote);
			} while (vote > 999 || vote < 100);
			onVoterActive(vote, 2);

			do {
				printf("\nDigite o voto para senador 2: ");
				scanf("%u", &vote);
			} while (vote > 999 || vote < 100);
			onVoterActive(vote, 3);

			do {
				printf("\nDigite o voto para governador: ");
				scanf("%u", &vote);
			} while (vote > 99 || vote < 10);
			onVoterActive(vote, 4);

			do {
				printf("\nDigite o voto para presidente: ");
				scanf("%u", &vote);
			} while (vote > 99 || vote < 10);
			onVoterActive(vote, 5);

			//check tracking code
			tamQR = createQRTrackingCode();

			printf("\n\n");
			for (int i = 0; i < tamQR; i++) {
				if (i%(SHA512HashSize+sizeof(uint32_t))==0) {
					printf("\n\n");
				}
				printf("%02X ", QRCodeTrackingCode[i]);
			}

			printf("\nDepositar (1) ou desafiar (0): ");
			scanf("%1u", &chal);
			onChallenge (chal);

			if (!chal) {
				printf("\n\n");
				for (int i = 0; i < sizeQRCodeSpoil[0]; i++) {
					printf("%02X ", QRCodeSpoilTrackingCode[i]);
				}

				printf("\n\n");
				for (int i = 0; i < sizeQRCodeSpoil[1]; i++) {
					printf("%02X ", QRCodeSpoilNonce[i]);
				}

				printf("\n\n");
				for (int i = 0; i < sizeQRCodeSpoil[2]; i++) {
					printf("%lld ", QRCodeSpoilVotes[i]);
				}
			} else {
				printf("\n\nSignature Dilithium 2 (%d)\n",tamSig);
				for (int i = 0; i < tamSig; i++) {
					printf("%02X ", QRCodeSign[i]);
				}
				printf("\n");
			}
			
			printf("\nProximo eleitor (1) ou finalizar (0): ");
			scanf("%1u", &proxEleitor);
			
		} while (proxEleitor==1);
	}
	totalVoters=numberTotalvoters();

	onFinish();

	// lerArquivoVoteOutput("voteOutput_Cont0", HTail, HHead, HTrack, vTime, com, totalVoters);

	// lerArquivoRDV("RDVOutput_Cont0", _m, totalVoters);

	// lerArquivoZKP ("ZKPOutput_Cont0", rho, beta,
	// 				s, d, t, _t, u, y, _y, totalVoters);

	if(totalVoters > 0) {
		if ((infoContest & 0x1) != 0) {
			printf("\n\n\nPara cargo Deputado Federal");
			validateRDV("RDVOutput_Cont0", "RDVOutputSig_Cont0", totalVoters);

			validateVoteOutput ("voteOutput_Cont0", "voteOutputSig_Cont0", totalVoters);

			validateZKPOutput ("ZKPOutput_Cont0", "SigZKPOutput_Cont0", 
							"RDVOutput_Cont0", "voteOutput_Cont0",  
							totalVoters);
		}

		if ((infoContest & 0x2) != 0) {
			printf("\n\n\nPara cargo Deputado Estadual");
			validateRDV("RDVOutput_Cont1", "RDVOutputSig_Cont1", totalVoters);

			validateVoteOutput ("voteOutput_Cont1", "voteOutputSig_Cont1", totalVoters);

			validateZKPOutput ("ZKPOutput_Cont1", "SigZKPOutput_Cont1", 
							"RDVOutput_Cont1", "voteOutput_Cont1", 
							totalVoters);
		}

		if ((infoContest & 0x4) != 0) {
			printf("\n\n\nPara cargo Senador 1");
			validateRDV("RDVOutput_Cont2", "RDVOutputSig_Cont2", totalVoters);

			validateVoteOutput ("voteOutput_Cont2", "voteOutputSig_Cont2", totalVoters);

			validateZKPOutput ("ZKPOutput_Cont2", "SigZKPOutput_Cont2", 
							"RDVOutput_Cont2", "voteOutput_Cont2", 
							totalVoters);
		}

		if ((infoContest & 0x8) != 0) {
			printf("\n\n\nPara cargo Senador 2");
			validateRDV("RDVOutput_Cont3", "RDVOutputSig_Cont3", totalVoters);

			validateVoteOutput ("voteOutput_Cont3", "voteOutputSig_Cont3", totalVoters);

			validateZKPOutput ("ZKPOutput_Cont3", "SigZKPOutput_Cont3", 
							"RDVOutput_Cont3", "voteOutput_Cont3",  
							totalVoters);
		}

		if ((infoContest & 0x10) != 0) {
			printf("\n\n\nPara cargo Governador");
			validateRDV("RDVOutput_Cont4", "RDVOutputSig_Cont4", totalVoters);

			validateVoteOutput ("voteOutput_Cont4", "voteOutputSig_Cont4", totalVoters);

			validateZKPOutput ("ZKPOutput_Cont4", "SigZKPOutput_Cont4", 
							"RDVOutput_Cont4", "voteOutput_Cont4",
							totalVoters);
		}

		if ((infoContest & 0x20) != 0) {
			printf("\n\n\nPara cargo Presidente");
			validateRDV("RDVOutput_Cont5", "RDVOutputSig_Cont5", totalVoters);

			validateVoteOutput ("voteOutput_Cont5", "voteOutputSig_Cont5", totalVoters);

			validateZKPOutput ("ZKPOutput_Cont5", "SigZKPOutput_Cont5", 
							"RDVOutput_Cont5", "voteOutput_Cont5", 
							totalVoters);
		}
	}
	
	// printf("\n\n\n\n\n");
	// for (int z = 0; z < totalVoters; z++){
	// 	nmod_poly_print(_y[z][1][1]);
	// 	printf("\n");
	// }
	

	// printf("\n\n");
	// for (int i=0; i < SHA512HashSize; i++) {
	// 	printf("%02x ", HTail[i]);
	// }

	// printf("\n\n");
	// for (int i=0; i < SHA512HashSize; i++) {
	// 	printf("%02x ", HHead[i]);
	// }

	// for (int j = 0; j <totalVoters; j++) {
	// 	printf("\n\n");
	// 	for (int i=0; i < SHA512HashSize; i++) {
	// 		printf("%02x ", HTrack[j][i]);
	// 	}
	// 	printf("\n");
	// 	printf("%lx", vTime[j]);
	// }

	// nmod_poly_init(res, MODP);
	// nmod_poly_init(m1, MODP);
	// nmod_poly_init(m2, MODP);
	// nmod_poly_init(mod, MODP);

	// nmod_poly_zero(res);
	// nmod_poly_zero(m1);
	// nmod_poly_zero(m2);
	// nmod_poly_zero(mod);

	// nmod_poly_set_coeff_ui(m1,4,1);
	// for(int i = 0; i < DEGREE; i++){
	// 	nmod_poly_set_coeff_ui(m2,i,1);
	// }
	// nmod_poly_set_coeff_ui(mod,DEGREE,1);
	// nmod_poly_set_coeff_ui(mod,0,1);

	// printf("\nm1 = ");
	// nmod_poly_print(m1);
	// printf("\nm2 = ");
	// nmod_poly_print(m2);
	// printf("\nmod = ");
	// nmod_poly_print(mod);

	// nmod_poly_mulmod(res,m1,m2,mod);

	// printf("\nres = ");
	// nmod_poly_print(res);

	// for(int i = 0; i < DEGREE; i++) {
	// 	res->coeffs[i]*=res->coeffs[i];
	// 	res->coeffs[i]%=MODP;
	// }
	// printf("\nres hadamard = ");
	// nmod_poly_print(res);


	printf("\n\nO numero total de eleitores foi %d\n\n", totalVoters);

  return 0;
}