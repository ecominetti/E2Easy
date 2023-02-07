#include "APISimulator.h"

int main(int argc, char *arg[]) {
  	uint32_t vote;
	uint8_t infoContest=0x3f;
	int totalVoters, tamQR, numVotos, numTest=1;
	int chal = 1;

	for (numVotos = 600; numVotos <= 600; numVotos+=100) {
		printf("Votos = %d\n",numVotos);
		for (int i = 0; i < numTest; i ++) {

			if (i%100==0) {
				printf("Teste = %d\n",i);
			}

			Setup();
		
			onStart (infoContest);

			for(int j = 0; j < numVotos; j ++) {
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

				onChallenge (TRUE);
				
				
			}
			totalVoters=numberTotalvoters();
			onFinish();
		}
		printf("\n\nO numero total de eleitores foi %d\n\n", totalVoters);
	}

  return 0;
}