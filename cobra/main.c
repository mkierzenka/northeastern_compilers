#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

extern uint64_t our_code_starts_here() asm("our_code_starts_here");
extern uint64_t print(SNAKEVAL val) asm("print");

typedef uint64_t SNAKEVAL;

const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t BOOL_TAG = 0x0000000000000007L;
const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t NUM_TAG = 0x0000000000000000L;


void printAsBoolean(SNAKEVAL val) {
  const uint64_t BOOL_MASK = 0x8000000000000000L;
  if (val & BOOL_MASK) {
    printf("Boolean value: true\n");
  } else {
    printf("Boolean value: false\n");
  }
}

void printAsNumber(SNAKEVAL val) {
  printf("Numerical value: %ul\n", (val >> 1);
  //todo, does this print negative SNAKEVAL numbers correctly?
}

uint64_t print(SNAKEVAL val) {
  if (val & BOOL_TAG_MASK == BOOL_TAG) {
    printAsBoolean(val);
  } else if (val & NUM_TAG_MASK == NUM_TAG) {
    printAsNum(val);
  } else {
    printf("Unknown value: %#018x\n", val);
  }
  return val;
}

int main(int argc, char** argv) {
  SNAKEVAL result = our_code_starts_here();
  print(result);
  return 0;
}
