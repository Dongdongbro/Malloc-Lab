// /*
//  * mm-naive.c - The fastest, least memory-efficient malloc package.
//  *
//  * In this naive approach, a block is allocated by simply incrementing
//  * the brk pointer.  A block is pure payload. There are no headers or
//  * footers.  Blocks are never coalesced or reused. Realloc is
//  * implemented directly using mm_malloc and mm_free.
//  *
//  * NOTE TO STUDENTS: Replace this header comment with your own header
//  * comment that gives a high level description of your solution.
//  */
// #include <stdio.h>
// #include <stdlib.h>
// #include <assert.h>
// #include <unistd.h>
// #include <string.h>

// #include "mm.h"
// #include "memlib.h"

// /*********************************************************
//  * NOTE TO STUDENTS: Before you do anything else, please
//  * provide your team information in the following struct.
//  ********************************************************/
// team_t team = {
//     /* Team name */
//     "Jungle",
//     /* First member's full name */
//     "Dongdongbro",
//     /* First member's email address */
//     "ehdtm93@gmail.com",
//     /* Second member's full name (leave blank if none) */
//     "",
//     /* Second member's email address (leave blank if none) */
//     ""
// };

// /* single word (4) or double word (8) alignment */
// // #define ALIGNMENT 8

// // /* rounds up to the nearest multiple of ALIGNMENT */
// // #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// // #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

// #define WSIZE 4                 /*Word and header/footer size(bytes) */
// #define DSIZE 8                 /*Double word size(bytes) */
// #define CHUNKSIZE (1<<12)       /*Extend heap by this amount(bytes) */

// #define MAX(x, y) ((x) > (y)? (x) : (y))

// /* Pack a size and allocated bit into a word */
// #define PACK(size, alloc) ((size) | (alloc))

// /* Read and write a word at adress p */
// #define GET(p) (*(unsigned int *)(p))
// #define PUT(p, val) (*(unsigned int *)(p) = (val))

// /* Read the size and allocated fields from address p */
// #define GET_SIZE(p) (GET(p) & ~0x7)
// #define GET_ALLOC(p) (GET(p) & 0x1)

// /* Given block ptr bp, compute address of its header and footer */
// #define HDRP(bp) ((char *)(bp) - WSIZE)
// #define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

// /* Given block ptr bp, compute address of next and previous blocks */
// #define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
// #define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))
// /*
//  * mm_init - initialize the malloc package.
//  */
// static void *heap_listp = NULL;
// int mm_init(void);
// static void *extend_heap(size_t words);
// void *mm_malloc(size_t size);
// void mm_free(void *bp);
// static void *coalesce(void *bp);
// static void *find_fit(size_t asize);
// static void place(void *bp, size_t asize);
// void *mm_realloc(void *bp, size_t size);


// int mm_init(void)
// {
//     /* create : 초기의 빈 heap 할당(mem_sbrk) */
//     // heap_listp가 힙의 최댓값 이상을 요청한다면 fail
//     if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
//         return -1;

//     PUT(heap_listp, 0); // Alignment padding 생성
//     PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // prologue header 생성
//     PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // prologue footer 생성
//     PUT(heap_listp + (3*WSIZE), PACK(0,1)); // epilogue block header 생성
//     heap_listp += (2*WSIZE); // prologue header와 footer 사이로 포인터를 옮김.

//     // 빈 Heap을 CHUNKSIZE byte로 확장하고, 초기 가용 블록을 생성해줌
//     if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
//         return -1;
//     }
//     return 0;
// }

// // 새 가용 블록으로 힙을 확장
// static void *extend_heap(size_t words){
//     char *bp;
//     size_t size;

//     /* alignment 유지를 위해 짝수 개수의 words를 할당*/
//     size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 홀수면 앞, 짝수면 뒤가 나옴
//     if ((long)(bp = mem_sbrk(size)) == -1)
//         return NULL;

//     // free block header와 footer를 init하고 epilogue header를 init
//     PUT(HDRP(bp), PACK(size, 0)); // free block header 생성 / regular block의 총합의 첫번째 부분. 현재 bp위치의 한 칸 앞에 헤더를 생성
//     PUT(FTRP(bp), PACK(size, 0)); // free block footer 생성 / regular block의 마지막 부분
//     PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // block을 추가했으니 epilogue header를 새롭게 위치 조정해줌
//     // HDRP : 1word 뒤에 있는 것을 지칭.
//     // bp를 header에서 읽은 사이즈만큼 이동하고, 앞으로 한칸 간다. 그 위치가 결국 늘린 블록 끝에서 한칸 간것이기 때문에, epilogue header 위치가 됨

//     // 만약 previous block이 free 상태라면 병합(coalesce)
//     return coalesce(bp);

// }


// /*
//  * mm_malloc - Allocate a block by incrementing the brk pointer.
//  *     Always allocate a block whose size is a multiple of the alignment.
//  */
// void *mm_malloc(size_t size)
// {
//     size_t asize; // block 사이즈 조정
//     size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
//     char *bp;

//     /* 거짓된 요청 무시 */
//     if (size == 0) return NULL;

//     // 2words 이하의 사이즈는 4워드로 할당을 요청함 (header-1word, footer-1word)
//     if (size <= DSIZE){
//         asize = 2*DSIZE;
//     }
//     else{ // 요청된 용량이 2words 초과 시, 충분한 8byte 배수의 용량을 할당
//         asize = DSIZE * ((size + (DSIZE)+(DSIZE-1)) / DSIZE);
//     }
//     // fit에 맞는 free 리스트를 찾는다.
//     if ((bp = find_fit(asize)) != NULL){ // 적당한 크기의 가용 블록 검색
//         place(bp,asize); // 초과 부분을 분할하고 새롭게 할당한 블록의 포인터 반환
//         return bp;
//     }
//     /* fit에 맞는게 없는 경우, 메모리를 더 가져와 block을 위치시킴 */
//     extendsize = MAX(asize, CHUNKSIZE);
//     if((bp=extend_heap(extendsize/WSIZE)) == NULL){ // 추가가 안되었을 경우
//         return NULL;
//     }
//     place(bp, asize);
//     return bp;
// }
// /*
//  * mm_free - Freeing a block does nothing.
//  */
// void mm_free(void *bp)
// {
//     // 어느 시점에 있는 bp를 인자로 받음
//     size_t size = GET_SIZE(HDRP(bp)); // bp의 주소를 가지고 헤더에 접근하여(HDRP) -> block의 사이즈를 얻음(GET_SIZE)
//     PUT(HDRP(bp), PACK(size,0)); // header free -> 가용상태로 만들기
//     PUT(FTRP(bp), PACK(size,0)); // footer free -> 가용상태로 만들기
//     coalesce(bp);
// }
// /*
//     coalesce : 블록을 연결하는 함수
// */
// static void *coalesce(void *bp){
//     size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록이 할당되었는지 확인 : bp의 포인터를 통해 이전 블록을 찾고, 이 이전블록의 footer를 통해 할당 여부를 확인한다.
//     size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록이 할당되었는지 확인 : bp의 포인터를 통해 다음 블록을 찾고, 이 다음블록의 header를 통해 할당 여부를 확인한다.
//     size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈 확인

//     // case 1 : 이전 블록과 다음 블록이 모두 할당된 케이스 -> 합칠 수 없음
//     if (prev_alloc && next_alloc){
//         return bp;
//     }
//     // case 2 : 이전 블록 : 할당 상태, 다음 블록 : 가용 상태 -> 다음 블록과 합침
//     else if (prev_alloc && !next_alloc){
//         size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기를 현재 size에 더해줘요.
//         PUT(HDRP(bp), PACK(size, 0)); // header 갱신 (더 큰 크기로 PUT)
//         PUT(FTRP(bp), PACK(size,0)); // footer 갱신
//     }
//     // case 3 : 이전 블록 : 가용 상태, 다음 블록 : 할당 상태 -> 이전 블록과 합침
//     else if (!prev_alloc && next_alloc){
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 크기를 현재 size에 더해줘요.
//         PUT(FTRP(bp), PACK(size,0)); // 현재 위치의 footer에 block size를 갱신해줌
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
//         bp = PREV_BLKP(bp);
//     }
//     // case 4 : 이전 블록과 다음 블록이 모두 가용 블록인 상태 -> 이전 및 다음 블록 모두 합칠 수 있다.
//     else{
//         size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 및 다음 블록의 크기를 현재 size에 더해줘요.
//         PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
//         PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
//         bp = PREV_BLKP(bp);
//     }
//     return bp;
// }

// static void *find_fit(size_t asize){
//     void *bp;
//     for (bp = (char *)heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)){
//         // for문이 계속 돌면 epliogue header까지 간다. epliogue header는 0이므로 끝까지 가면 종료됨
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))){ // 이 블록이 가용상태이고, 내가 갖고있는 asize를 담을 수 있다면
//             return bp; // 내가 넣을 수 있는 블록만 찾으면 되기 때문에, 바로 리턴
//         }
//     }
//     return NULL; // NULL 리턴 시, fit에 맞는 block이 없는 것
// }

// static void place(void *bp, size_t asize){
//     // 요청한 블록을 가용 블록의 시작 부분에 배치한다.
//     // 나머지 부분의 크기가 최소 블록의 크기와 같거나 큰 경우에만 분할하는 함수
//     size_t csize = GET_SIZE(HDRP(bp));
//     if ((csize-asize) >= (2*DSIZE)){
//         PUT(HDRP(bp), PACK(asize,1));
//         PUT(FTRP(bp), PACK(asize,1));
//         bp = NEXT_BLKP(bp);
//         PUT(HDRP(bp), PACK(csize-asize, 0));
//         PUT(FTRP(bp), PACK(csize-asize, 0));
//     }
//     else{
//         PUT(HDRP(bp), PACK(csize,1));
//         PUT(FTRP(bp), PACK(csize,1));
//     }
// }
// /*
//  * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
//  */
// void *mm_realloc(void *bp, size_t size) // bp : 크기를 조정할 블록의 위치, size : 요청 사이즈
// {
//     // 요청 사이즈가 0보다 작거나 같다면 free 상태로 만들고 0을 리턴해줌
//     if (size <= 0){
//         mm_free(bp);
//         return 0;
//     }
//     // 위치(bp)가 없다면 malloc을 통해 새로 생성해줌 (예외처리의 일종)
//     if (bp == NULL){
//         return mm_malloc(size);
//     }
//     void *newp = mm_malloc(size);
//     if(newp == NULL){
//         return 0;
//     }
//     // 요청 사이즈가 기존 사이즈보다 작으면 요청 사이즈만큼 데이터를 잘라서 옮겨준다.
//     size_t oldsize = GET_SIZE(HDRP(bp));
//     if (size < oldsize){
//         oldsize = size;
//     }
//     // 블록 내의 데이터를 옮기기 위한 함수
//     memcpy(newp, bp, oldsize);
//     // 기존 블록 반환
//     mm_free(bp);
//     return newp;
// }




//-------------------------------------------------------------------------------------------------------------------------------------------------------------------------//



/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"
/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "week06-03",
    /* First member's full name */
    "Dongdongbro",
    /* First member's email address */
    "hdl93@naver.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

// Next fit 방식 malloc

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4 // word and header footer 사이즈를 byte로
#define DSIZE 8 // double word size를 byte로
#define CHUNKSIZE (1<<12) // heap을 늘릴 때 4kb 분량으로 늘림.

#define MAX(x,y) ((x)>(y) ? (x) : (y)) // x,y 중 큰 값을 가진다.

// size를 pack하고 개별 word 안의 bit를 할당 (size와 alloc을 비트연산), 헤더에서 써야하기 때문에 생성.
#define PACK(size,alloc) ((size)|(alloc)) // alloc : 가용여부 (ex.000) / size : block size를 의미 -> 이를 통합해서 header와 footer에 저장할 수 있는 값 리턴

/* address p위치에 words를 read와 write 한다.*/
#define GET(p) (*(unsigned int*)(p)) // 인자 p가 참조하는 워드를 읽어서 리턴. 즉, 헤더에 담긴 정보를 꺼낼 수 있음
#define PUT(p,val) (*(unsigned int*)(p)=(val)) // 인자 p가 가리키는 워드에 val을 저장

/* address p위치로부터 size를 읽고 field를 할당 */
#define GET_SIZE(p) (GET(p) & ~0x7) // 0x7를 2진수에서 역수를 취하면 11111000이 됨. 이것을 GET(p)를 통해 가져온 헤더 정보에 and 연산을 하면 block size만 가져올 수 있음
#define GET_ALLOC(p) (GET(p) & 0x1) // 위의 케이스와 반대로 00000001을 and해주면 헤더에서 가용여부만 가져올 수 있음

/* given block ptr bp, header와 footer의 주소를 계산 */
#define HDRP(bp) ((char*)(bp) - WSIZE) // bp의 현재 주소에서 4byte(1워드)만큼 빼주면 헤더의 위치가 됨 (char*)인 이유는 (int*)일 경우에는 WSIZE로 인해 16이 반환되기 때문?
#define FTRP(bp) ((char*)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 헤더의 끝 지점부터 GET SIZE(블록의 사이즈)만큼 더한 다음 word를 2번빼는게(그 뒤 블록의 헤드에서 앞으로 2번) footer의 시작 위치가 된다.


/* GIVEN block ptr bp, 이전 블록과 다음 블록의 주소를 계산 */
#define NEXT_BLKP(bp) ((char*)(bp) + GET_SIZE(((char*)(bp) - WSIZE))) // 그 다음 블록의 bp 위치로 이동한다.(bp에서 해당 블록의 크기만큼 이동 -> 그 다음 블록의 헤더 뒤로 감.)
#define PREV_BLKP(bp) ((char*)(bp) - GET_SIZE(((char*)(bp) - DSIZE))) // 그 전 블록의 bp위치로 이동.(이전 블록 footer로 이동하면 그 전 블록의 사이즈를 알 수 있으니 그만큼 그 전으로 이동.)

static void *heap_listp;
static char *last_bp;

int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void mm_free(void *bp);
static void *coalesce(void *bp);
static void *next_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *bp, size_t size);
/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void)
{
    /* create : 초기의 빈 heap 할당(mem_sbrk) */
    if ((heap_listp = mem_sbrk(4*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0); // Alignment padding 생성
    PUT(heap_listp + (1*WSIZE), PACK(DSIZE,1)); // prologue header 생성
    PUT(heap_listp + (2*WSIZE), PACK(DSIZE,1)); // prologue footer 생성
    PUT(heap_listp + (3*WSIZE), PACK(0,1)); // epilogue block header 생성
    heap_listp += (2*WSIZE); // prologue header와 footer 사이로 포인터를 옮김.

    // 빈 Heap을 CHUNKSIZE byte로 확장하고, 초기 가용 블록을 생성해줌
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
    last_bp = (char *)heap_listp;
    return 0;
}

// 새 가용 블록으로 힙을 확장
static void *extend_heap(size_t words){
    char *bp;
    size_t size;

    /* alignment 유지를 위해 짝수 개수의 words를 할당*/
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE; // 홀수면 앞, 짝수면 뒤가 나옴
    if ((long)(bp = mem_sbrk(size)) == -1)
        return NULL;

    // free block header와 footer를 init하고 epilogue header를 init
    PUT(HDRP(bp), PACK(size, 0)); // free block header 생성 / regular block의 총합의 첫번째 부분. 현재 bp위치의 한 칸 앞에 헤더를 생성
    PUT(FTRP(bp), PACK(size, 0)); // free block footer 생성 / regular block의 마지막 부분
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0,1)); // block을 추가했으니 epilogue header를 새롭게 위치 조정해줌
    // HDRP : 1word 뒤에 있는 것을 지칭.
    // bp를 header에서 읽은 사이즈만큼 이동하고, 앞으로 한칸 간다. 그 위치가 결국 늘린 블록 끝에서 한칸 간것이기 때문에, epilogue header 위치가 됨

    // 만약 previous block이 free 상태라면 병합(coalesce)
    return coalesce(bp);

}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; // block 사이즈 조정
    size_t extendsize; // heap에 맞는 fit이 없으면 확장하기 위한 사이즈
    char *bp;

    /* 거짓된 요청 무시 */
    if (size == 0) return NULL;

    /* overhead, alignment 요청 포함해서 블록 사이즈 조정 */
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{
        // size보다 클 때, 블록이 가질 수 있는 크기 중, 최적회된 크기로 재조정
        asize = DSIZE * ((size + (DSIZE)+(DSIZE-1)) / DSIZE);
    }
    // fit에 맞는 free 리스트를 찾는다.
    if ((bp = next_fit(asize)) != NULL){
        place(bp,asize);
        return bp;
    }
    /* fit에 맞는게 없는 경우, 메모리를 더 가져와 block을 위치시킴 */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE)) == NULL){
        return NULL;
    }
    place(bp, asize);
    last_bp = bp;
    return bp;
}
/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    // 어느 시점에 있는 bp를 인자로 받음
    size_t size = GET_SIZE(HDRP(bp)); // bp의 주소를 가지고 헤더에 접근하여(HDRP) -> block의 사이즈를 얻음(GET_SIZE)
    PUT(HDRP(bp), PACK(size,0)); // header free -> 가용상태로 만들기
    PUT(FTRP(bp), PACK(size,0)); // footer free -> 가용상태로 만들기
    coalesce(bp);
}
/*
    coalesce : 블록을 연결하는 함수
*/
static void *coalesce(void *bp){
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp))); // 이전 블록이 할당되었는지 확인 : bp의 포인터를 통해 이전 블록을 찾고, 이 이전블록의 footer를 통해 할당 여부를 확인한다.
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp))); // 다음 블록이 할당되었는지 확인 : bp의 포인터를 통해 다음 블록을 찾고, 이 다음블록의 header를 통해 할당 여부를 확인한다.
    size_t size = GET_SIZE(HDRP(bp)); // 현재 블록의 사이즈 확인

    // case 1 : 이전 블록과 다음 블록이 모두 할당된 케이스 -> 합칠 수 없음
    if (prev_alloc && next_alloc){
        last_bp = bp;
        return bp;
    }
    // case 2 : 이전 블록 : 할당 상태, 다음 블록 : 가용 상태 -> 다음 블록과 합침
    else if (prev_alloc && !next_alloc){
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기를 현재 size에 더해줘요.
        PUT(HDRP(bp), PACK(size, 0)); // header 갱신 (더 큰 크기로 PUT)
        PUT(FTRP(bp), PACK(size,0)); // footer 갱신
    }
    // case 3 : 이전 블록 : 가용 상태, 다음 블록 : 할당 상태 -> 이전 블록과 합침
    else if (!prev_alloc && next_alloc){
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 크기를 현재 size에 더해줘요.
        PUT(FTRP(bp), PACK(size,0)); // 현재 위치의 footer에 block size를 갱신해줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // case 4 : 이전 블록과 다음 블록이 모두 가용 블록인 상태 -> 이전 및 다음 블록 모두 합칠 수 있다.
    else{
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 및 다음 블록의 크기를 현재 size에 더해줘요.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    last_bp = bp;
    return bp;
}

/*
    - 적당한 크기의 가용블록을 검색
    - 최근(마지막)에 할당된 블록을 기준으로 다음 블록 검색
*/
static void *next_fit(size_t asize){
    char *bp = last_bp;

    for (bp=NEXT_BLKP(bp); GET_SIZE(HDRP(bp)) != 0; bp = NEXT_BLKP(bp)){
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize){
            last_bp = bp;
            return bp;
        }
    }
    bp = heap_listp;
    while (bp < last_bp) {
        bp = NEXT_BLKP(bp);
        if (!GET_ALLOC(HDRP(bp)) && GET_SIZE(HDRP(bp)) >= asize){
            last_bp = bp;
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    /*
    요청한 블록을 가용 블록의 시작 부분에 배치한다.
    나머지 부분의 크기가 최소 블록의 크기와 같거나 큰 경우에만 분할하는 함수
    */
    // csize : current size, asize : adjust size
    size_t csize = GET_SIZE(HDRP(bp));
    if ((csize-asize) >= (2*DSIZE)){
        // 요청 용량만큼 블록 배치
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        // 남은 블록에 header, footer 배치
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
    }
    else{
        // csize와 asize 차이가 4word(16byte)보다 작다면 해당 블록을 통째로 사용
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}
/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) // bp : 크기를 조정할 블록의 위치, size : 요청 사이즈
{
    size_t old_size = GET_SIZE(HDRP(bp));
    size_t new_size = size + (2 * WSIZE); // 2 * WSIZE는 header와 footer

    // new_size가 old_size보다 작거나 같으면 기존 bp 그대로 사용
    if (new_size <= old_size){
        return bp;
    }
    // new_size가 old_size보다 크면 사이즈 변경
    else {
        size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
        size_t current_size = old_size + GET_SIZE(HDRP(NEXT_BLKP(bp)));

        // next block이 가용상태이고 old, next block의 사이즈 합이 new_size보다 크면 바로 합쳐서 쓰기
        if (!next_alloc && current_size >= new_size){
            PUT(HDRP(bp), PACK(current_size, 1));
            PUT(FTRP(bp), PACK(current_size, 1));
            return bp;
        }
        else {
            void *new_bp = mm_malloc(new_size);
            place(new_bp, new_size);
            memcpy(new_bp, bp, new_size);
            mm_free(bp);
            return new_bp;
        }
    }
}





