#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here() asm("our_code_starts_here");
extern SNAKEVAL print(SNAKEVAL val) asm("print");

extern void error(uint64_t errCode) asm("error");


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


void printAsBoolean(SNAKEVAL val) {
  if (val & FIRST_BIT_MASK) {
    printf("true\n");
  } else {
    printf("false\n");
  }
}

void printAsNumber(SNAKEVAL val) {
  int64_t signed_num = 0;
  if (val & FIRST_BIT_MASK) {
    signed_num = (val >> 1) | FIRST_BIT_MASK;
  } else {
    signed_num = (val >> 1);
  }
  printf("%ld\n", signed_num);
}

uint64_t print(SNAKEVAL val) {
  if ((val & BOOL_TAG_MASK) == BOOL_TAG) {
    printAsBoolean(val);
  } else if ((val & NUM_TAG_MASK) == NUM_TAG) {
    printAsNumber(val);
  } else {
    printf("Unknown value: %#018lx\n", val);
  }
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
    default:
      fprintf(stderr, "unknown error code");  //exit() will print the errCode
  }
  exit(errCode);
}


// main should remain unchanged
int main(int argc, char** argv) {
  SNAKEVAL result = our_code_starts_here();
  print(result);
  return 0;
}
