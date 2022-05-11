
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
    "Jungle",
    /* First member's full name */
    "Dongdongbro",
    /* First member's email address */
    "ehdtm93@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""
};

/* single word (4) or double word (8) alignment */
// #define ALIGNMENT 8

// /* rounds up to the nearest multiple of ALIGNMENT */
// #define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)


// #define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4                 /*Word and header/footer size(bytes) */
#define DSIZE 8                 /*Double word size(bytes) */
#define CHUNKSIZE (1<<12)       /*Extend heap by this amount(bytes) */

#define MAX(x, y) ((x) > (y)? (x) : (y))

/* Pack a size and allocated bit into a word */
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at adress p */
#define GET(p) (*(unsigned int *)(p))
#define PUT(p, val) (*(unsigned int *)(p) = (val))

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7)
#define GET_ALLOC(p) (GET(p) & 0x1)

/* Given block ptr bp, compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)

/* Given block ptr bp, compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE)))
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp)-DSIZE)))

#define PRED_BLKP(bp) (*(void **)(bp))
#define SUCC_BLKP(bp) (*(void **)((bp)+WSIZE))
/*
 * mm_init - initialize the malloc package.
 */
static void *heap_listp = NULL;
int mm_init(void);
static void *extend_heap(size_t words);
void *mm_malloc(size_t size);
void mm_free(void *bp);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);
void *mm_realloc(void *bp, size_t size);
static void list_add(void *bp);
static void list_remove(void *bp);


int mm_init(void)
{
    /* create : 초기의 빈 heap 할당(mem_sbrk) */
    // heap_listp가 힙의 최댓값 이상을 요청한다면 fail
    // explicit은 next prev가 가르키는 블록을 지정해주어야 하므로 Padding 1워드 + Prologue 4워드 + eplilog 1워드 크기만큼 할당해준다.
    if ((heap_listp = mem_sbrk(6*WSIZE)) == (void *)-1)
        return -1;

    PUT(heap_listp, 0); // Alignment padding 생성
    PUT(heap_listp + (1*WSIZE), PACK(2*DSIZE,1)); // prologue header 생성
    PUT(heap_listp + (2*WSIZE), heap_listp+(3*WSIZE));
    PUT(heap_listp + (3*WSIZE), heap_listp+(2*WSIZE));
    PUT(heap_listp + (4*WSIZE), PACK(2*DSIZE,1));
    PUT(heap_listp + (5*WSIZE), PACK(0,1));
    heap_listp += (2*WSIZE); // 초기 bp 값을 설정
    // 빈 Heap을 CHUNKSIZE byte로 확장하고, 초기 가용 블록을 생성해줌
    if (extend_heap(CHUNKSIZE/WSIZE) == NULL){
        return -1;
    }
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

    // 2words 이하의 사이즈는 4워드로 할당을 요청함 (header-1word, footer-1word)
    if (size <= DSIZE){
        asize = 2*DSIZE;
    }
    else{ // 요청된 용량이 2words 초과 시, 충분한 8byte 배수의 용량을 할당
        asize = DSIZE * ((size + (DSIZE)+(DSIZE-1)) / DSIZE);
    }
    // fit에 맞는 free 리스트를 찾는다.
    if ((bp = find_fit(asize)) != NULL){ // 적당한 크기의 가용 블록 검색
        place(bp,asize); // 초과 부분을 분할하고 새롭게 할당한 블록의 포인터 반환
        return bp;
    }
    /* fit에 맞는게 없는 경우, 메모리를 더 가져와 block을 위치시킴 */
    extendsize = MAX(asize, CHUNKSIZE);
    if((bp=extend_heap(extendsize/WSIZE)) == NULL){ // 추가가 안되었을 경우
        return NULL;
    }
    place(bp, asize);
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
        list_add(bp);
        return bp;
    }
    // case 2 : 이전 블록 : 할당 상태, 다음 블록 : 가용 상태 -> 다음 블록과 합침
    else if (prev_alloc && !next_alloc){
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 다음 블록의 크기를 현재 size에 더해줘요.
        PUT(HDRP(bp), PACK(size, 0)); // header 갱신 (더 큰 크기로 PUT)
        PUT(FTRP(bp), PACK(size,0)); // footer 갱신
    }
    // case 3 : 이전 블록 : 가용 상태, 다음 블록 : 할당 상태 -> 이전 블록과 합침
    else if (!prev_alloc && next_alloc){
        list_remove(PREV_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 이전 블록의 크기를 현재 size에 더해줘요.
        PUT(FTRP(bp), PACK(size,0)); // 현재 위치의 footer에 block size를 갱신해줌
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    // case 4 : 이전 블록과 다음 블록이 모두 가용 블록인 상태 -> 이전 및 다음 블록 모두 합칠 수 있다.
    else{
        list_remove(PREV_BLKP(bp));
        list_remove(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 이전 블록 및 다음 블록의 크기를 현재 size에 더해줘요.
        PUT(HDRP(PREV_BLKP(bp)), PACK(size,0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size,0));
        bp = PREV_BLKP(bp);
    }
    list_add(bp);
    return bp;
}

static void *find_fit(size_t asize){
    void *bp;
    // 시작은 1
    for (bp = SUCC_BLKP(heap_listp); !GET_ALLOC(HDRP(bp)); bp = SUCC_BLKP(bp)){
        if (asize <= GET_SIZE(HDRP(bp))){
            return bp;
        }
    }
    return NULL;
}

static void place(void *bp, size_t asize){
    size_t csize = GET_SIZE(HDRP(bp));
    list_remove(bp);
    if ((csize-asize) >= (2*DSIZE)){
        PUT(HDRP(bp), PACK(asize,1));
        PUT(FTRP(bp), PACK(asize,1));
        bp = NEXT_BLKP(bp);
        PUT(HDRP(bp), PACK(csize-asize, 0));
        PUT(FTRP(bp), PACK(csize-asize, 0));
        list_add(bp);
    }
    else{
        PUT(HDRP(bp), PACK(csize,1));
        PUT(FTRP(bp), PACK(csize,1));
    }
}

static void list_add(void *bp){
    SUCC_BLKP(bp) = SUCC_BLKP(heap_listp);  // 추가하는 bp의 SUCC는 root가 가르키고 있던 SUCC로 받아와준다.
    PRED_BLKP(bp) = heap_listp;             // 추가하는 bp의 PRED는 root를 가르키게 한다.
    PRED_BLKP(SUCC_BLKP(heap_listp)) = bp;  // 원래 root가 갖고 있던 SUCC 블록포인터의 PRED를 bp로 만들어준다.
    SUCC_BLKP(heap_listp) = bp;             // root의 SUCC를 bp로 업데이트 시킨다.
}

static void list_remove(void *bp){
    SUCC_BLKP(PRED_BLKP(bp)) = SUCC_BLKP(bp);   // bp의 PRED의 SUCC를 bp의 SUCC로 설정.
    PRED_BLKP(SUCC_BLKP(bp)) = PRED_BLKP(bp);   // bp의 SUCC의 PRED를 bp의 PRED로 설정.
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) // bp : 크기를 조정할 블록의 위치, size : 요청 사이즈
{
    // 요청 사이즈가 0보다 작거나 같다면 free 상태로 만들고 0을 리턴해줌
    if (size <= 0){
        mm_free(bp);
        return 0;
    }
    // 위치(bp)가 없다면 malloc을 통해 새로 생성해줌 (예외처리의 일종)
    if (bp == NULL){
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if(newp == NULL){
        return 0;
    }
    // 요청 사이즈가 기존 사이즈보다 작으면 요청 사이즈만큼 데이터를 잘라서 옮겨준다.
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize){
        oldsize = size;
    }
    // 블록 내의 데이터를 옮기기 위한 함수
    memcpy(newp, bp, oldsize);
    // 기존 블록 반환
    mm_free(bp);
    return newp;
}

