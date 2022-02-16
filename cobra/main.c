#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(SNAKEVAL val) asm("print");

const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t BOOL_TAG = 0x0000000000000007L;
const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t NUM_TAG = 0x0000000000000000L;
const uint64_t FIRST_BIT_MASK = 0x8000000000000000L;


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
  //todo, does this print negative SNAKEVAL numbers correctly?
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

int main(int argc, char** argv) {
  SNAKEVAL result = our_code_starts_here();
  print(result);
  return 0;
}
