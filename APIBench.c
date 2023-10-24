#include "APISimulator.h"
#include "bench.h"
#include "test.h"

int main(int argc, char *arg[]) {
	FILE *resultadoCycles;
	unsigned long long onVoterActiveCycles, onChallengeCycles;
  	int numTests=3;
	uint32_t vote;
	uint8_t infoContest=0x3f;
	int eleitoresHabilitados;

	printf("Benchmark do sistema de votacao E2Easy\n\n");

	resultadoCycles = fopen("BenchSim","a");
	if (resultadoCycles==NULL) {
		printf("Erro arquivo\n");
		return 0;
	}

	for (eleitoresHabilitados = 10; eleitoresHabilitados <= 15; eleitoresHabilitados+=1) {

		fprintf(resultadoCycles, "Numero eleitores = %d (%d votos), %d testes\n", eleitoresHabilitados, eleitoresHabilitados*6, numTests);
		fprintf(resultadoCycles, "    Setup;  onStart;onVoterActive;  onChallenge;    onFinish\n");
		fflush(resultadoCycles);
		printf("Eleitores = %d\n",eleitoresHabilitados);

		for (int bm = 0; bm < numTests; bm++) {

			if (bm%100==0) {
				printf("Test = %d\n",bm);
			}

			bench_reset();
			bench_before();
			Setup();
			bench_after();
			fprintf(resultadoCycles, "%9lld;", bench_total());

			bench_reset();
			bench_before();
			onStart (infoContest);
			bench_after();
			fprintf(resultadoCycles, "%9lld;", bench_total());

			onVoterActiveCycles = 0;
			onChallengeCycles = 0;
			
			for (int i = 0; i < eleitoresHabilitados; i++) {
				getrandom(&vote, sizeof(vote), 0);
				vote%=100000;
				if (vote < 10000){
					vote+=10000;
				}
				bench_reset();
				bench_before();
				onVoterActive(vote, 0);
				bench_after();
				onVoterActiveCycles+=bench_total();

				getrandom(&vote, sizeof(vote), 0);
				vote%=10000;
				if (vote < 1000){
					vote+=1000;
				}
				bench_reset();
				bench_before();
				onVoterActive(vote, 1);
				bench_after();
				onVoterActiveCycles+=bench_total();

				getrandom(&vote, sizeof(vote), 0);
				vote%=1000;
				if (vote < 100){
					vote+=100;
				}
				bench_reset();
				bench_before();
				onVoterActive(vote, 2);
				bench_after();
				onVoterActiveCycles+=bench_total();

				getrandom(&vote, sizeof(vote), 0);
				vote%=1000;
				if (vote < 100){
					vote+=100;
				}
				bench_reset();
				bench_before();
				onVoterActive(vote, 3);
				bench_after();
				onVoterActiveCycles+=bench_total();

				getrandom(&vote, sizeof(vote), 0);
				vote%=100;
				if (vote < 10){
					vote+=10;
				}
				bench_reset();
				bench_before();
				onVoterActive(vote, 4);
				bench_after();
				onVoterActiveCycles+=bench_total();

				getrandom(&vote, sizeof(vote), 0);
				vote%=100;
				if (vote < 10){
					vote+=10;
				}
				bench_reset();
				bench_before();
				onVoterActive(vote, 5);
				bench_after();
				onVoterActiveCycles+=bench_total();

				bench_reset();
				bench_before();
				onChallenge (1);
				bench_after();
				onChallengeCycles+=bench_total();
			}

			fprintf(resultadoCycles, "%13lld;%13lld;", onVoterActiveCycles,onChallengeCycles);

			bench_reset();
			bench_before();
			onFinish();
			bench_after();
			fprintf(resultadoCycles, "%12lld\n", bench_total());
			fflush(resultadoCycles);

		}
	}

	fclose (resultadoCycles);

  	return 0;
}