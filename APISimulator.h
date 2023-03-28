#include <stdio.h>
#include <stdlib.h>
#include <math.h>

#define _LARGE_TIME_API
#include <time.h>

#include "./dilithium/ref/api.h"

#include "param.h"
#include "commit.h"
#include "gaussian.h"
#include "fastrandombytes.h"
#include "assert.h"
#include "sha.h"

/*============================================================================*/
/* Constant definitions                                                       */
/*============================================================================*/

/* Maximum number of contests in an election */
#define CONTESTS 6
/* Maximum number of voter in an election */
#define VOTERS 600
/* Define TRUE and FALSE as integers */
#define TRUE 1
#define FALSE 0
/* Define Dilithium Parameters */
#define DILITHIUM_MODE 2
#define DILITHIUM_USE_AES

/*============================================================================*/
/* External variables definitions                                             */
/*============================================================================*/

extern uint8_t pubSignKey[pqcrystals_dilithium2_PUBLICKEYBYTES];
extern uint8_t QRCodeTrackingCode[CONTESTS*(SHA512HashSize+sizeof(uint32_t))];
extern uint8_t QRCodeSign[pqcrystals_dilithium2_BYTES];
extern size_t tamSig;
extern uint8_t QRCodeSpoilTrackingCode[CONTESTS*SHA512HashSize];
extern uint8_t QRCodeSpoilNonce[CONTESTS*WIDTH*(DEGREE/4)]; // Degree*2/8
extern uint32_t QRCodeSpoilVotes[CONTESTS];
extern int sizeQRCodeSpoil[3];

/*============================================================================*/
/* Function prototypes                                                        */
/*============================================================================*/

/**
 * Create commitment key for use in the simulator.
*/
void Setup();


/**
 * Start the voting machine simulator for use
 * @param[in] infoContest   - 6 less significant bits: set if contest is held, clear otherwise.
 */
void onStart (uint8_t infoContest);


/**
 * Cast vote for a contest
 * @param[in] vote          - Candidate number.
 * @param[in] cont          - Contest, represented as a 8 bit string, where a single bit is set.
 */
void onVoterActive(uint32_t vote, uint8_t cont);


/**
 * Create final Tracking Code from all available contests.
 * Tracking Code is output in QRCodeTrackingCode variable.
 * @return number of bytes written in the Tracking Code.
 */
int createQRTrackingCode();


/**
 * Benaloh Challenge: Deposit or challenge Tracking code.
 * @param[in] cast          -Deposit vote (TRUE) or challenge vote (FALSE).
 * For challenge, output the required Challenge QR codes using variables:
 *              QRCodeSpoilTrackingCode
 *              QRCodeSpoilNonce
 *              QRCodeSpoilVotes
 * The size of the QR codes for the spoil are output, respectively, in sizeQRCodeSpoil[3].
 */
void onChallenge (bool cast);


/**
 * Close the voting machine and create results.
 * Results are output in files voteOutput_contX for election public data for contest X.
 *                             ZKPOutput_contX for ZKP data of contest X.
 */
void onFinish ();


/**
 * Return the number of voters who deposited their votes.
 * @return the total number of voters.
 */
int numberTotalvoters();


/**
 * Verify function for the Benaloh Challenge.
 * Print the result on screen.
 * @param[in] QRTrack       - Tracking Code provided before the challenge.
 * @param[in] QRSpoilTrack      - Tracking Code of the previous voter, provided by the challenge.
 * @param[in] QRSpoilNon 		- Nonce used to create the commitment, provided by the challenge.
 * @param[in] QRSpoilVot 		- Votes used to create the commitment, provided by the challenge.
 */
void verifyVote (uint8_t *QRTrack, uint8_t *QRSpoilTrack, uint8_t *QRSpoilNon, uint32_t *QRSpoilVot);


/**
 * Validate the signature of the RDV file.
 * Print the result on screen.
 * @param[in] RDVOutputName 		- Name of the RDV file.
 * @param[in] RDVSigOutputName 		- Name of the file that contains the signature for the RDV file.
 * @param[in] numVoters 			- Number of voters.
 */
void validateRDV (char RDVOutputName[20], char RDVSigOutputName[20], int numVoters);


/**
 * Validate the signature of the voteOutput file and the Tracking Code chain.
 * Print the result on the screeen.
 * @param[in] voteOutputName 		- Name of the voteOutput file.
 * @param[in] voteSigOutputName 	- Name of the file that contains the signature for the voteOutput file.
 * @param[in] numVoters 			- Number of voters.
 */
void validateVoteOutput (char voteOutputName[20], char voteSigOutputName[20], int numVoters);


/**
 * Validate the signature of the ZKP file and the ZKPs.
 * Print the result on the screen.
 * @param[in] ZKPOutputName 		- Name of the ZKP file.
 * @param[in] ZKPSigOutputName 		- Name of the file that contains the signature for the ZKP file.
 * @param[in] RDVOutputName 		- Name of the RDV file.
 * @param[in] voteOutputName 		- Name of the voteOutput file.
 * @param numVoters 				- Number of voters.
 */
void validateZKPOutput (char ZKPOutputName[20], char ZKPSigOutputName[20], 
						char RDVOutputName[20], char voteOutputName[20],
						int numVoters);
