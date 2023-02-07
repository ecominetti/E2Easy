#include "APISimulator.h"

int main(int argc, char *arg[]) {
  	uint32_t vote;
	uint8_t infoContest=0x3f;
	int tamQR, numVotos, numTest=1;
	int chal = 1;

	for (numVotos = 10; numVotos <= 100; numVotos+=100) {
		printf("Votos = %d\n",numVotos);
		for (int i = 0; i < numTest; i ++) {

			if (i%100==0) {
				printf("Teste = %d\n",i);
			}

			Setup();
		
			onStart (infoContest);

			for(int j = 0; j < numVotos; j ++) {
				printf("VOTO %d\n\n",numberTotalvoters());
				getrandom(&vote, sizeof(vote), 0);
				vote&=0x8FFFFFFF;
				onVoterActive(vote, 0);

				getrandom(&vote, sizeof(vote), 0);
				vote&=0x8FFFFFFF;
				onVoterActive(vote, 1);

				getrandom(&vote, sizeof(vote), 0);
				vote&=0x8FFFFFFF;
				onVoterActive(vote, 2);

				getrandom(&vote, sizeof(vote), 0);
				vote&=0x8FFFFFFF;
				onVoterActive(vote, 3);

				getrandom(&vote, sizeof(vote), 0);
				vote&=0x8FFFFFFF;
				onVoterActive(vote, 4);

				getrandom(&vote, sizeof(vote), 0);
				vote&=0x8FFFFFFF;
				onVoterActive(vote, 5);

				//check tracking code
				tamQR = createQRTrackingCode();

				printf("\n%d\n",tamQR);
				for(int idx = 0; idx < tamQR; idx++) {
					printf("%02x ", QRCodeTrackingCode[idx]);
				}
				printf("\n");

		
				if (j == 7 && chal == 1){

					onChallenge (FALSE);

					printf("\n%d %d %d\n", sizeQRCodeSpoil[0],sizeQRCodeSpoil[1],sizeQRCodeSpoil[2]);

					for(int idx = 0; idx < sizeQRCodeSpoil[0]; idx++) {
						printf("%02x ", QRCodeSpoilTrackingCode[idx]);
					}
					printf("\n\n");

					for(int idx = 0; idx < sizeQRCodeSpoil[1]; idx++) {
						printf("%02x ", QRCodeSpoilNonce[idx]);
					}
					printf("\n\n");

					for(int idx = 0; idx < sizeQRCodeSpoil[2]; idx++) {
						printf("%02x ", QRCodeSpoilVotes[idx]);
					}
					printf("\n\n");

					verifyVote(QRCodeTrackingCode,QRCodeSpoilTrackingCode,QRCodeSpoilNonce,QRCodeSpoilVotes);
					chal = 0;
				} else {
					onChallenge (TRUE);
				}
				
			}

			onFinish();
		}
	}

  return 0;
}