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
const uint64_t TUPLE_TAG_MASK = 0x0000000000000007L;
const uint64_t TUPLE_TAG = 0x0000000000000001L;

const uint64_t err_COMP_NOT_NUM   = 1L;
const uint64_t err_ARITH_NOT_NUM  = 2L;
const uint64_t err_LOGIC_NOT_BOOL = 3L;
const uint64_t err_IF_NOT_BOOL    = 4L;
const uint64_t err_OVERFLOW       = 5L;
const uint64_t err_GET_NOT_TUPLE  = 6L;
const uint64_t err_GET_LOW_INDEX  = 7L;
const uint64_t err_GET_HIGH_INDEX = 8L;
const uint64_t err_NIL_DEREF      = 9L;

void printHelp(FILE *out, SNAKEVAL val);


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

void printAsTuple(FILE* out, SNAKEVAL val) {
  int64_t* heap_address = val - 1L;
  int64_t tup_size = heap_address[0];
  int64_t* elems = heap_address + 1;
  //fprintf(out, "tuple @ %p. size: %ld. value: (", heap_address, tup_size);
  fprintf(out, "(", heap_address, tup_size);
  for (int i = 0; i < tup_size; ++i) {
    printHelp(out, elems[i]);
    if (i+1 < tup_size) {
      fprintf(out, ",");
    }
  }
  if (tup_size == 1) {
    fprintf(out, ",");
  }
  fprintf(out, ")");
}


void printHelp(FILE *out, SNAKEVAL val) {
  if ((val & BOOL_TAG_MASK) == BOOL_TAG) {
    printAsBoolean(out, val);
  } else if ((val & NUM_TAG_MASK) == NUM_TAG) {
    printAsNumber(out, val);
  } else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG) {
    printAsTuple(out, val);
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
    case err_GET_NOT_TUPLE:
      fprintf(stderr, "expected tuple");
      break;
    case err_GET_LOW_INDEX:
    case err_GET_HIGH_INDEX:
    case err_NIL_DEREF:
      fprintf(stderr, "todo finish implementing error handling");
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
