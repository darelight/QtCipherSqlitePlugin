/*
** 2017-03-08
**
** The author disclaims copyright to this source code.  In place of
** a legal notice, here is a blessing:
**
**    May you do good and not evil.
**    May you find forgiveness for yourself and forgive others.
**    May you share freely, never taking more than you give.
**
******************************************************************************
**
** This SQLite extension implements a functions that compute SHA1 hashes.
** Two SQL functions are implemented:
**
**     sha3(X,SIZE)
**     sha3_query(Y,SIZE)
**
** The sha3(X) function computes the SHA3 hash of the input X, or NULL if
** X is NULL.
**
** The sha3_query(Y) function evalutes all queries in the SQL statements of Y
** and returns a hash of their results.
**
** The SIZE argument is optional.  If omitted, the SHA3-256 hash algorithm
** is used.  If SIZE is included it must be one of the integers 224, 256,
** 384, or 512, to determine SHA3 hash variant that is computed.
*/
#include "sqlite3ext.h"
SQLITE_EXTENSION_INIT1
#include <assert.h>
#include <string.h>
#include <stdarg.h>
#if 0
typedef sqlite3_uint64 u64;
#endif

/******************************************************************************
** The Hash Engine
*/
/*
** Macros to determine whether the machine is big or little endian,
** and whether or not that determination is run-time or compile-time.
**
** For best performance, an attempt is made to guess at the byte-order
** using C-preprocessor macros.  If that is unsuccessful, or if
** -DSHA3_BYTEORDER=0 is set, then byte-order is determined
** at run-time.
*/
#ifndef SHA3_BYTEORDER
# if defined(i386)     || defined(__i386__)   || defined(_M_IX86) ||    \
     defined(__x86_64) || defined(__x86_64__) || defined(_M_X64)  ||    \
     defined(_M_AMD64) || defined(_M_ARM)     || defined(__x86)   ||    \
     defined(__arm__)
#   define SHA3_BYTEORDER    1234
# elif defined(sparc)    || defined(__ppc__)
#   define SHA3_BYTEORDER    4321
# else
#   define SHA3_BYTEORDER 0
# endif
#endif


/*
** State structure for a SHA3 hash in progress
*/
typedef struct SHA3Context SHA3Context;
struct SHA3Context {
  union {
    u64 s[25];                /* Keccak state. 5x5 lines of 64 bits each */
    unsigned char x[1600];    /* ... or 1600 bytes */
  } u;
  unsigned nRate;        /* Bytes of input accepted per Keccak iteration */
  unsigned nLoaded;      /* Input bytes loaded into u.x[] so far this cycle */
  unsigned ixMask;       /* Insert next input into u.x[nLoaded^ixMask]. */
};

/*
** A single step of the Keccak mixing function for a 1600-bit state
*/
static void KeccakF1600Step(SHA3Context *p){
  int i;
  u64 DTB0, DTB1, DTB2, DTB3, DTB4;
  u64 DTC0, DTC1, DTC2, DTC3, DTC4;
  u64 DTD0, DTD1, DTD2, DTD3, DTD4;
  static const u64 RC[] = {
    0x0000000000000001ULL,  0x0000000000008082ULL,
    0x800000000000808aULL,  0x8000000080008000ULL,
    0x000000000000808bULL,  0x0000000080000001ULL,
    0x8000000080008081ULL,  0x8000000000008009ULL,
    0x000000000000008aULL,  0x0000000000000088ULL,
    0x0000000080008009ULL,  0x000000008000000aULL,
    0x000000008000808bULL,  0x800000000000008bULL,
    0x8000000000008089ULL,  0x8000000000008003ULL,
    0x8000000000008002ULL,  0x8000000000000080ULL,
    0x000000000000800aULL,  0x800000008000000aULL,
    0x8000000080008081ULL,  0x8000000000008080ULL,
    0x0000000080000001ULL,  0x8000000080008008ULL
  };
# define DTA00 (p->u.s[0])
# define DTA01 (p->u.s[1])
# define DTA02 (p->u.s[2])
# define DTA03 (p->u.s[3])
# define DTA04 (p->u.s[4])
# define DTA10 (p->u.s[5])
# define DTA11 (p->u.s[6])
# define DTA12 (p->u.s[7])
# define DTA13 (p->u.s[8])
# define DTA14 (p->u.s[9])
# define DTA20 (p->u.s[10])
# define DTA21 (p->u.s[11])
# define DTA22 (p->u.s[12])
# define DTA23 (p->u.s[13])
# define DTA24 (p->u.s[14])
# define DTA30 (p->u.s[15])
# define DTA31 (p->u.s[16])
# define DTA32 (p->u.s[17])
# define DTA33 (p->u.s[18])
# define DTA34 (p->u.s[19])
# define DTA40 (p->u.s[20])
# define DTA41 (p->u.s[21])
# define DTA42 (p->u.s[22])
# define DTA43 (p->u.s[23])
# define DTA44 (p->u.s[24])
# define ROL64(a,x) ((a<<x)|(a>>(64-x)))

  for(i=0; i<24; i+=4){
    DTC0 = DTA00^DTA10^DTA20^DTA30^DTA40;
    DTC1 = DTA01^DTA11^DTA21^DTA31^DTA41;
    DTC2 = DTA02^DTA12^DTA22^DTA32^DTA42;
    DTC3 = DTA03^DTA13^DTA23^DTA33^DTA43;
    DTC4 = DTA04^DTA14^DTA24^DTA34^DTA44;
    DTD0 = DTC4^ROL64(DTC1, 1);
    DTD1 = DTC0^ROL64(DTC2, 1);
    DTD2 = DTC1^ROL64(DTC3, 1);
    DTD3 = DTC2^ROL64(DTC4, 1);
    DTD4 = DTC3^ROL64(DTC0, 1);

    DTB0 = (DTA00^DTD0);
    DTB1 = ROL64((DTA11^DTD1), 44);
    DTB2 = ROL64((DTA22^DTD2), 43);
    DTB3 = ROL64((DTA33^DTD3), 21);
    DTB4 = ROL64((DTA44^DTD4), 14);
    DTA00 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA00 ^= RC[i];
    DTA11 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA22 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA33 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA44 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB2 = ROL64((DTA20^DTD0), 3);
    DTB3 = ROL64((DTA31^DTD1), 45);
    DTB4 = ROL64((DTA42^DTD2), 61);
    DTB0 = ROL64((DTA03^DTD3), 28);
    DTB1 = ROL64((DTA14^DTD4), 20);
    DTA20 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA31 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA42 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA03 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA14 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB4 = ROL64((DTA40^DTD0), 18);
    DTB0 = ROL64((DTA01^DTD1), 1);
    DTB1 = ROL64((DTA12^DTD2), 6);
    DTB2 = ROL64((DTA23^DTD3), 25);
    DTB3 = ROL64((DTA34^DTD4), 8);
    DTA40 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA01 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA12 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA23 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA34 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB1 = ROL64((DTA10^DTD0), 36);
    DTB2 = ROL64((DTA21^DTD1), 10);
    DTB3 = ROL64((DTA32^DTD2), 15);
    DTB4 = ROL64((DTA43^DTD3), 56);
    DTB0 = ROL64((DTA04^DTD4), 27);
    DTA10 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA21 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA32 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA43 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA04 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB3 = ROL64((DTA30^DTD0), 41);
    DTB4 = ROL64((DTA41^DTD1), 2);
    DTB0 = ROL64((DTA02^DTD2), 62);
    DTB1 = ROL64((DTA13^DTD3), 55);
    DTB2 = ROL64((DTA24^DTD4), 39);
    DTA30 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA41 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA02 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA13 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA24 =   DTB4 ^((~DTB0)&  DTB1 );

    DTC0 = DTA00^DTA20^DTA40^DTA10^DTA30;
    DTC1 = DTA11^DTA31^DTA01^DTA21^DTA41;
    DTC2 = DTA22^DTA42^DTA12^DTA32^DTA02;
    DTC3 = DTA33^DTA03^DTA23^DTA43^DTA13;
    DTC4 = DTA44^DTA14^DTA34^DTA04^DTA24;
    DTD0 = DTC4^ROL64(DTC1, 1);
    DTD1 = DTC0^ROL64(DTC2, 1);
    DTD2 = DTC1^ROL64(DTC3, 1);
    DTD3 = DTC2^ROL64(DTC4, 1);
    DTD4 = DTC3^ROL64(DTC0, 1);

    DTB0 = (DTA00^DTD0);
    DTB1 = ROL64((DTA31^DTD1), 44);
    DTB2 = ROL64((DTA12^DTD2), 43);
    DTB3 = ROL64((DTA43^DTD3), 21);
    DTB4 = ROL64((DTA24^DTD4), 14);
    DTA00 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA00 ^= RC[i+1];
    DTA31 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA12 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA43 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA24 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB2 = ROL64((DTA40^DTD0), 3);
    DTB3 = ROL64((DTA21^DTD1), 45);
    DTB4 = ROL64((DTA02^DTD2), 61);
    DTB0 = ROL64((DTA33^DTD3), 28);
    DTB1 = ROL64((DTA14^DTD4), 20);
    DTA40 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA21 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA02 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA33 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA14 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB4 = ROL64((DTA30^DTD0), 18);
    DTB0 = ROL64((DTA11^DTD1), 1);
    DTB1 = ROL64((DTA42^DTD2), 6);
    DTB2 = ROL64((DTA23^DTD3), 25);
    DTB3 = ROL64((DTA04^DTD4), 8);
    DTA30 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA11 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA42 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA23 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA04 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB1 = ROL64((DTA20^DTD0), 36);
    DTB2 = ROL64((DTA01^DTD1), 10);
    DTB3 = ROL64((DTA32^DTD2), 15);
    DTB4 = ROL64((DTA13^DTD3), 56);
    DTB0 = ROL64((DTA44^DTD4), 27);
    DTA20 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA01 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA32 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA13 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA44 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB3 = ROL64((DTA10^DTD0), 41);
    DTB4 = ROL64((DTA41^DTD1), 2);
    DTB0 = ROL64((DTA22^DTD2), 62);
    DTB1 = ROL64((DTA03^DTD3), 55);
    DTB2 = ROL64((DTA34^DTD4), 39);
    DTA10 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA41 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA22 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA03 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA34 =   DTB4 ^((~DTB0)&  DTB1 );

    DTC0 = DTA00^DTA40^DTA30^DTA20^DTA10;
    DTC1 = DTA31^DTA21^DTA11^DTA01^DTA41;
    DTC2 = DTA12^DTA02^DTA42^DTA32^DTA22;
    DTC3 = DTA43^DTA33^DTA23^DTA13^DTA03;
    DTC4 = DTA24^DTA14^DTA04^DTA44^DTA34;
    DTD0 = DTC4^ROL64(DTC1, 1);
    DTD1 = DTC0^ROL64(DTC2, 1);
    DTD2 = DTC1^ROL64(DTC3, 1);
    DTD3 = DTC2^ROL64(DTC4, 1);
    DTD4 = DTC3^ROL64(DTC0, 1);

    DTB0 = (DTA00^DTD0);
    DTB1 = ROL64((DTA21^DTD1), 44);
    DTB2 = ROL64((DTA42^DTD2), 43);
    DTB3 = ROL64((DTA13^DTD3), 21);
    DTB4 = ROL64((DTA34^DTD4), 14);
    DTA00 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA00 ^= RC[i+2];
    DTA21 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA42 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA13 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA34 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB2 = ROL64((DTA30^DTD0), 3);
    DTB3 = ROL64((DTA01^DTD1), 45);
    DTB4 = ROL64((DTA22^DTD2), 61);
    DTB0 = ROL64((DTA43^DTD3), 28);
    DTB1 = ROL64((DTA14^DTD4), 20);
    DTA30 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA01 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA22 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA43 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA14 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB4 = ROL64((DTA10^DTD0), 18);
    DTB0 = ROL64((DTA31^DTD1), 1);
    DTB1 = ROL64((DTA02^DTD2), 6);
    DTB2 = ROL64((DTA23^DTD3), 25);
    DTB3 = ROL64((DTA44^DTD4), 8);
    DTA10 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA31 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA02 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA23 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA44 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB1 = ROL64((DTA40^DTD0), 36);
    DTB2 = ROL64((DTA11^DTD1), 10);
    DTB3 = ROL64((DTA32^DTD2), 15);
    DTB4 = ROL64((DTA03^DTD3), 56);
    DTB0 = ROL64((DTA24^DTD4), 27);
    DTA40 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA11 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA32 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA03 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA24 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB3 = ROL64((DTA20^DTD0), 41);
    DTB4 = ROL64((DTA41^DTD1), 2);
    DTB0 = ROL64((DTA12^DTD2), 62);
    DTB1 = ROL64((DTA33^DTD3), 55);
    DTB2 = ROL64((DTA04^DTD4), 39);
    DTA20 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA41 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA12 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA33 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA04 =   DTB4 ^((~DTB0)&  DTB1 );

    DTC0 = DTA00^DTA30^DTA10^DTA40^DTA20;
    DTC1 = DTA21^DTA01^DTA31^DTA11^DTA41;
    DTC2 = DTA42^DTA22^DTA02^DTA32^DTA12;
    DTC3 = DTA13^DTA43^DTA23^DTA03^DTA33;
    DTC4 = DTA34^DTA14^DTA44^DTA24^DTA04;
    DTD0 = DTC4^ROL64(DTC1, 1);
    DTD1 = DTC0^ROL64(DTC2, 1);
    DTD2 = DTC1^ROL64(DTC3, 1);
    DTD3 = DTC2^ROL64(DTC4, 1);
    DTD4 = DTC3^ROL64(DTC0, 1);

    DTB0 = (DTA00^DTD0);
    DTB1 = ROL64((DTA01^DTD1), 44);
    DTB2 = ROL64((DTA02^DTD2), 43);
    DTB3 = ROL64((DTA03^DTD3), 21);
    DTB4 = ROL64((DTA04^DTD4), 14);
    DTA00 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA00 ^= RC[i+3];
    DTA01 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA02 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA03 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA04 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB2 = ROL64((DTA10^DTD0), 3);
    DTB3 = ROL64((DTA11^DTD1), 45);
    DTB4 = ROL64((DTA12^DTD2), 61);
    DTB0 = ROL64((DTA13^DTD3), 28);
    DTB1 = ROL64((DTA14^DTD4), 20);
    DTA10 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA11 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA12 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA13 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA14 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB4 = ROL64((DTA20^DTD0), 18);
    DTB0 = ROL64((DTA21^DTD1), 1);
    DTB1 = ROL64((DTA22^DTD2), 6);
    DTB2 = ROL64((DTA23^DTD3), 25);
    DTB3 = ROL64((DTA24^DTD4), 8);
    DTA20 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA21 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA22 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA23 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA24 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB1 = ROL64((DTA30^DTD0), 36);
    DTB2 = ROL64((DTA31^DTD1), 10);
    DTB3 = ROL64((DTA32^DTD2), 15);
    DTB4 = ROL64((DTA33^DTD3), 56);
    DTB0 = ROL64((DTA34^DTD4), 27);
    DTA30 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA31 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA32 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA33 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA34 =   DTB4 ^((~DTB0)&  DTB1 );

    DTB3 = ROL64((DTA40^DTD0), 41);
    DTB4 = ROL64((DTA41^DTD1), 2);
    DTB0 = ROL64((DTA42^DTD2), 62);
    DTB1 = ROL64((DTA43^DTD3), 55);
    DTB2 = ROL64((DTA44^DTD4), 39);
    DTA40 =   DTB0 ^((~DTB1)&  DTB2 );
    DTA41 =   DTB1 ^((~DTB2)&  DTB3 );
    DTA42 =   DTB2 ^((~DTB3)&  DTB4 );
    DTA43 =   DTB3 ^((~DTB4)&  DTB0 );
    DTA44 =   DTB4 ^((~DTB0)&  DTB1 );
  }
}

/*
** Initialize a new hash.  iSize determines the size of the hash
** in bits and should be one of 224, 256, 384, or 512.  Or iSize
** can be zero to use the default hash size of 256 bits.
*/
static void SHA3Init(SHA3Context *p, int iSize){
  memset(p, 0, sizeof(*p));
  if( iSize>=128 && iSize<=512 ){
    p->nRate = (1600 - ((iSize + 31)&~31)*2)/8;
  }else{
    p->nRate = (1600 - 2*256)/8;
  }
#if SHA3_BYTEORDER==1234
  /* Known to be little-endian at compile-time. No-op */
#elif SHA3_BYTEORDER==4321
  p->ixMask = 7;  /* Big-endian */
#else
  {
    static unsigned int one = 1;
    if( 1==*(unsigned char*)&one ){
      /* Little endian.  No byte swapping. */
      p->ixMask = 0;
    }else{
      /* Big endian.  Byte swap. */
      p->ixMask = 7;
    }
  }
#endif
}

/*
** Make consecutive calls to the SHA3Update function to add new content
** to the hash
*/
static void SHA3Update(
  SHA3Context *p,
  const unsigned char *aData,
  unsigned int nData
){
  unsigned int i = 0;
#if SHA3_BYTEORDER==1234
  if( (p->nLoaded % 8)==0 && ((aData - (const unsigned char*)0)&7)==0 ){
    for(; i+7<nData; i+=8){
      p->u.s[p->nLoaded/8] ^= *(u64*)&aData[i];
      p->nLoaded += 8;
      if( p->nLoaded>=p->nRate ){
        KeccakF1600Step(p);
        p->nLoaded = 0;
      }
    }
  }
#endif
  for(; i<nData; i++){
#if SHA3_BYTEORDER==1234
    p->u.x[p->nLoaded] ^= aData[i];
#elif SHA3_BYTEORDER==4321
    p->u.x[p->nLoaded^0x07] ^= aData[i];
#else
    p->u.x[p->nLoaded^p->ixMask] ^= aData[i];
#endif
    p->nLoaded++;
    if( p->nLoaded==p->nRate ){
      KeccakF1600Step(p);
      p->nLoaded = 0;
    }
  }
}

/*
** After all content has been added, invoke SHA3Final() to compute
** the final hash.  The function returns a pointer to the binary
** hash value.
*/
static unsigned char *SHA3Final(SHA3Context *p){
  unsigned int i;
  if( p->nLoaded==p->nRate-1 ){
    const unsigned char c1 = 0x86;
    SHA3Update(p, &c1, 1);
  }else{
    const unsigned char c2 = 0x06;
    const unsigned char c3 = 0x80;
    SHA3Update(p, &c2, 1);
    p->nLoaded = p->nRate - 1;
    SHA3Update(p, &c3, 1);
  }
  for(i=0; i<p->nRate; i++){
    p->u.x[i+p->nRate] = p->u.x[i^p->ixMask];
  }
  return &p->u.x[p->nRate];
}
/* End of the hashing logic
*****************************************************************************/

/*
** Implementation of the sha3(X,SIZE) function.
**
** Return a BLOB which is the SIZE-bit SHA3 hash of X.  The default
** size is 256.  If X is a BLOB, it is hashed as is.  
** For all other non-NULL types of input, X is converted into a UTF-8 string
** and the string is hashed without the trailing 0x00 terminator.  The hash
** of a NULL value is NULL.
*/
static void sha3Func(
  sqlite3_context *context,
  int argc,
  sqlite3_value **argv
){
  SHA3Context cx;
  int eType = sqlite3_value_type(argv[0]);
  int nByte = sqlite3_value_bytes(argv[0]);
  int iSize;
  if( argc==1 ){
    iSize = 256;
  }else{
    iSize = sqlite3_value_int(argv[1]);
    if( iSize!=224 && iSize!=256 && iSize!=384 && iSize!=512 ){
      sqlite3_result_error(context, "SHA3 size should be one of: 224 256 "
                                    "384 512", -1);
      return;
    }
  }
  if( eType==SQLITE_NULL ) return;
  SHA3Init(&cx, iSize);
  if( eType==SQLITE_BLOB ){
    SHA3Update(&cx, sqlite3_value_blob(argv[0]), nByte);
  }else{
    SHA3Update(&cx, sqlite3_value_text(argv[0]), nByte);
  }
  sqlite3_result_blob(context, SHA3Final(&cx), iSize/8, SQLITE_TRANSIENT);
}

/* Compute a string using sqlite3_vsnprintf() with a maximum length
** of 50 bytes and add it to the hash.
*/
static void hash_step_vformat(
  SHA3Context *p,                 /* Add content to this context */
  const char *zFormat,
  ...
){
  va_list ap;
  int n;
  char zBuf[50];
  va_start(ap, zFormat);
  sqlite3_vsnprintf(sizeof(zBuf),zBuf,zFormat,ap);
  va_end(ap);
  n = (int)strlen(zBuf);
  SHA3Update(p, (unsigned char*)zBuf, n);
}

/*
** Implementation of the sha3_query(SQL,SIZE) function.
**
** This function compiles and runs the SQL statement(s) given in the
** argument. The results are hashed using a SIZE-bit SHA3.  The default
** size is 256.
**
** The format of the byte stream that is hashed is summarized as follows:
**
**       S<n>:<sql>
**       R
**       N
**       I<int>
**       F<ieee-float>
**       B<size>:<bytes>
**       T<size>:<text>
**
** <sql> is the original SQL text for each statement run and <n> is
** the size of that text.  The SQL text is UTF-8.  A single R character
** occurs before the start of each row.  N means a NULL value.
** I mean an 8-byte little-endian integer <int>.  F is a floating point
** number with an 8-byte little-endian IEEE floating point value <ieee-float>.
** B means blobs of <size> bytes.  T means text rendered as <size>
** bytes of UTF-8.  The <n> and <size> values are expressed as an ASCII
** text integers.
**
** For each SQL statement in the X input, there is one S segment.  Each
** S segment is followed by zero or more R segments, one for each row in the
** result set.  After each R, there are one or more N, I, F, B, or T segments,
** one for each column in the result set.  Segments are concatentated directly
** with no delimiters of any kind.
*/
static void sha3QueryFunc(
  sqlite3_context *context,
  int argc,
  sqlite3_value **argv
){
  sqlite3 *db = sqlite3_context_db_handle(context);
  const char *zSql = (const char*)sqlite3_value_text(argv[0]);
  sqlite3_stmt *pStmt = 0;
  int nCol;                   /* Number of columns in the result set */
  int i;                      /* Loop counter */
  int rc;
  int n;
  const char *z;
  SHA3Context cx;
  int iSize;

  if( argc==1 ){
    iSize = 256;
  }else{
    iSize = sqlite3_value_int(argv[1]);
    if( iSize!=224 && iSize!=256 && iSize!=384 && iSize!=512 ){
      sqlite3_result_error(context, "SHA3 size should be one of: 224 256 "
                                    "384 512", -1);
      return;
    }
  }
  if( zSql==0 ) return;
  SHA3Init(&cx, iSize);
  while( zSql[0] ){
    rc = sqlite3_prepare_v2(db, zSql, -1, &pStmt, &zSql);
    if( rc ){
      char *zMsg = sqlite3_mprintf("error SQL statement [%s]: %s",
                                   zSql, sqlite3_errmsg(db));
      sqlite3_finalize(pStmt);
      sqlite3_result_error(context, zMsg, -1);
      sqlite3_free(zMsg);
      return;
    }
    if( !sqlite3_stmt_readonly(pStmt) ){
      char *zMsg = sqlite3_mprintf("non-query: [%s]", sqlite3_sql(pStmt));
      sqlite3_finalize(pStmt);
      sqlite3_result_error(context, zMsg, -1);
      sqlite3_free(zMsg);
      return;
    }
    nCol = sqlite3_column_count(pStmt);
    z = sqlite3_sql(pStmt);
    n = (int)strlen(z);
    hash_step_vformat(&cx,"S%d:",n);
    SHA3Update(&cx,(unsigned char*)z,n);

    /* Compute a hash over the result of the query */
    while( SQLITE_ROW==sqlite3_step(pStmt) ){
      SHA3Update(&cx,(const unsigned char*)"R",1);
      for(i=0; i<nCol; i++){
        switch( sqlite3_column_type(pStmt,i) ){
          case SQLITE_NULL: {
            SHA3Update(&cx, (const unsigned char*)"N",1);
            break;
          }
          case SQLITE_INTEGER: {
            sqlite3_uint64 u;
            int j;
            unsigned char x[9];
            sqlite3_int64 v = sqlite3_column_int64(pStmt,i);
            memcpy(&u, &v, 8);
            for(j=8; j>=1; j--){
              x[j] = u & 0xff;
              u >>= 8;
            }
            x[0] = 'I';
            SHA3Update(&cx, x, 9);
            break;
          }
          case SQLITE_FLOAT: {
            sqlite3_uint64 u;
            int j;
            unsigned char x[9];
            double r = sqlite3_column_double(pStmt,i);
            memcpy(&u, &r, 8);
            for(j=8; j>=1; j--){
              x[j] = u & 0xff;
              u >>= 8;
            }
            x[0] = 'F';
            SHA3Update(&cx,x,9);
            break;
          }
          case SQLITE_TEXT: {
            int n2 = sqlite3_column_bytes(pStmt, i);
            const unsigned char *z2 = sqlite3_column_text(pStmt, i);
            hash_step_vformat(&cx,"T%d:",n2);
            SHA3Update(&cx, z2, n2);
            break;
          }
          case SQLITE_BLOB: {
            int n2 = sqlite3_column_bytes(pStmt, i);
            const unsigned char *z2 = sqlite3_column_blob(pStmt, i);
            hash_step_vformat(&cx,"B%d:",n2);
            SHA3Update(&cx, z2, n2);
            break;
          }
        }
      }
    }
    sqlite3_finalize(pStmt);
  }
  sqlite3_result_blob(context, SHA3Final(&cx), iSize/8, SQLITE_TRANSIENT);
}


#ifdef _WIN32
__declspec(dllexport)
#endif
int sqlite3_shathree_init(
  sqlite3 *db,
  char **pzErrMsg,
  const sqlite3_api_routines *pApi
){
  int rc = SQLITE_OK;
  SQLITE_EXTENSION_INIT2(pApi);
  (void)pzErrMsg;  /* Unused parameter */
  rc = sqlite3_create_function(db, "sha3", 1, SQLITE_UTF8, 0,
                               sha3Func, 0, 0);
  if( rc==SQLITE_OK ){
    rc = sqlite3_create_function(db, "sha3", 2, SQLITE_UTF8, 0,
                                 sha3Func, 0, 0);
  }
  if( rc==SQLITE_OK ){
    rc = sqlite3_create_function(db, "sha3_query", 1, SQLITE_UTF8, 0,
                                 sha3QueryFunc, 0, 0);
  }
  if( rc==SQLITE_OK ){
    rc = sqlite3_create_function(db, "sha3_query", 2, SQLITE_UTF8, 0,
                                 sha3QueryFunc, 0, 0);
  }
  return rc;
}
