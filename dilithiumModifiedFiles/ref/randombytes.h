#ifndef rng_h
#define rng_h

#ifdef __cplusplus
extern "C" {
#endif

int
randombytes(unsigned char *x, unsigned long long xlen);

#ifdef __cplusplus
}
#endif

#endif /* rng_h */
