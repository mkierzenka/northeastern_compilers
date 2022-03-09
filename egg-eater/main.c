#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t* HEAP, int size) asm("our_code_starts_here");
//extern void error(uint64_t code, SNAKEVAL val) asm("error");
//TODO this should be uncommented
extern SNAKEVAL print(SNAKEVAL val) asm("print");
extern SNAKEVAL input() asm("input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t* esp, uint64_t* ebp, int args) asm("print_stack");
extern uint64_t* STACK_BOTTOM asm("STACK_BOTTOM");

uint64_t* HEAP;



const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t BOOL_TAG = 0x0000000000000007L;
const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t NUM_TAG = 0x0000000000000000L;
const uint64_t FIRST_BIT_MASK = 0x8000000000000000L;

const uint64_t err_COMP_NOT_NUM   = 1L;
const uint64_t err_ARITH_NOT_NUM  = 2L;
const uint64_t err_LOGIC_NOT_BOOL = 3L;
const uint64_t err_IF_NOT_BOOL    = 4L;
const uint64_t err_OVERFLOW       = 5L;



void printAsBoolean(FILE *out, SNAKEVAL val) {
  if (val & FIRST_BIT_MASK) {
    fprintf(out, "true");
  } else {
    fprintf(out, "false");
  }
}

void printAsNumber(FILE *out, SNAKEVAL val) {
  int64_t signed_num = 0;
  if (val & FIRST_BIT_MASK) {
    signed_num = (val >> 1) | FIRST_BIT_MASK;
  } else {
    signed_num = (val >> 1);
  }
  fprintf(out, "%ld", signed_num);
}


void printHelp(FILE *out, SNAKEVAL val) {
  // COPY YOUR IMPLEMENTATION FROM DIAMONDBACK
  // and enhance it to handle tuples (TODO)
  if ((val & BOOL_TAG_MASK) == BOOL_TAG) {
    printAsBoolean(out, val);
  } else if ((val & NUM_TAG_MASK) == NUM_TAG) {
    printAsNumber(out, val);
  } else {
    fprintf(out, "Unknown value: %#018lx", val);
  }
}

SNAKEVAL print(SNAKEVAL val) {
  printHelp(stdout, val);
  printf("\n");
  fflush(stdout);
  return val;
}

/*

COPY YOUR IMPLEMENTATION FROM DIAMONDBACK

*/


void error(uint64_t errCode) {
  switch (errCode) {
    case err_COMP_NOT_NUM:
      fprintf(stderr, "comparison expected a number");
      break;
    case err_ARITH_NOT_NUM:
      fprintf(stderr, "arithmetic expected a number");
      break;
    case err_LOGIC_NOT_BOOL:
      fprintf(stderr, "logic expected a boolean");
      break;
    case err_IF_NOT_BOOL:
      fprintf(stderr, "if expected a boolean");
      break;
    case err_OVERFLOW:
      fprintf(stderr, "overflow");
      break;
    default:
      fprintf(stderr, "unknown error code");  //exit() will print the errCode
  }
  exit(errCode);
}



// main should remain unchanged
// You can pass in a numeric argument to your program when you run it,
// to specify the size of the available heap.  You may find this useful
// for debugging...
int main(int argc, char** argv) {
  int size = 100000;
  if (argc > 1) { size = atoi(argv[1]); }
  if (size < 0 || size > 1000000) { size = 0; }
  HEAP = calloc(size, sizeof (int));

  SNAKEVAL result = our_code_starts_here(HEAP, size);
  print(result);
  free(HEAP);
  return 0;
}
