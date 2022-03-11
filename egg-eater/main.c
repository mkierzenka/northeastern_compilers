#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t* HEAP, int size) asm("our_code_starts_here");
//extern void error(uint64_t code, SNAKEVAL val) asm("error");
//TODO this should be uncommented
extern SNAKEVAL print(SNAKEVAL val) asm("print");
//extern SNAKEVAL input() asm("input"); //TODO delete
extern SNAKEVAL input() asm("cinput");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t* esp, uint64_t* ebp, int args) asm("print_stack");
extern SNAKEVAL equal(SNAKEVAL e1, SNAKEVAL e2) asm("cequal");
extern uint64_t* STACK_BOTTOM asm("STACK_BOTTOM");

uint64_t* HEAP;


const uint64_t const_true = 0xFFFFFFFFFFFFFFFFL;
const uint64_t const_false = 0x7FFFFFFFFFFFFFFFL;

const uint64_t BOOL_TAG_MASK = 0x0000000000000007L;
const uint64_t BOOL_TAG = 0x0000000000000007L;
const uint64_t NUM_TAG_MASK = 0x0000000000000001L;
const uint64_t NUM_TAG = 0x0000000000000000L;
const uint64_t FIRST_BIT_MASK = 0x8000000000000000L;
const uint64_t TUPLE_TAG_MASK = 0x0000000000000007L;
const uint64_t TUPLE_TAG = 0x0000000000000001L;

const uint64_t err_COMP_NOT_NUM    = 1L;
const uint64_t err_ARITH_NOT_NUM   = 2L;
const uint64_t err_LOGIC_NOT_BOOL  = 3L;
const uint64_t err_IF_NOT_BOOL     = 4L;
const uint64_t err_OVERFLOW        = 5L;
const uint64_t err_GET_NOT_TUPLE   = 6L;
const uint64_t err_GET_LOW_INDEX   = 7L;
const uint64_t err_GET_HIGH_INDEX  = 8L;
const uint64_t err_NIL_DEREF       = 9L;
const uint64_t err_BAD_INPUT       = 10L;
const uint64_t err_TUP_IDX_NOT_NUM = 11L;

void printHelp(FILE *out, SNAKEVAL val);
bool cequalToBoolean(SNAKEVAL e1, SNAKEVAL e2);
bool cequalToNumber(SNAKEVAL e1, SNAKEVAL e2);
bool cequalToTuple(SNAKEVAL e1, SNAKEVAL e2);
bool cequalInner(SNAKEVAL e1, SNAKEVAL e2);



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
  int64_t* heap_address = (int64_t*) (val - 1L);

  // handle the nil case
  if (heap_address == 0L) {
    fprintf(out, "nil");
    return;
  }

  int64_t tup_size = heap_address[0];
  int64_t* elems = heap_address + 1;
  //fprintf(out, "tuple @ %p. size: %ld. value: (", heap_address, tup_size);
  fprintf(out, "(");
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
      // todo maybe print idx
      fprintf(stderr, "index too small");
      break;
    case err_GET_HIGH_INDEX:
      // todo maybe print idx and tup length
      fprintf(stderr, "index too big");
      break;
    case err_BAD_INPUT:
      fprintf(stderr, "bad input: input must be a number or a bool");
      break;
    case err_NIL_DEREF:
      fprintf(stderr, "attempted to dereference a nil tuple");
      break;
    case err_TUP_IDX_NOT_NUM:
      fprintf(stderr, "tuple indices must be numeric");
      break;
    default:
      fprintf(stderr, "unknown error code");  //exit() will print the errCode
  }
  exit(errCode);
}

SNAKEVAL cinput() {
  // todo maybe make case insensitive
  static const int buf_max = 21;
  static const char* str_true = "true";
  static const char* str_false = "false";
  char inp[buf_max];
  fgets(inp, buf_max, stdin);

  if (strcmp(inp, str_true) == 0) {
    return const_true;
  }
  if (strcmp(inp, str_false) == 0) {
    return const_false;
  }

  const uint64_t as_uint = strtoull(inp, NULL, 10);
  if (as_uint == 0L) {
    // check '0' first
    if (strcmp(inp, "0") == 0) {
      return 0L;
    }
    else {
      // error exits
      error(err_BAD_INPUT);
      return 0L; // defensive coding
    }
  }
  else {
    // TODO check for overflow
    return 2L * as_uint;
  }
}


// ASSUME: e1 is a snake boolean
bool cequalToBoolean(SNAKEVAL e1, SNAKEVAL e2) {
  if ((e2 & BOOL_TAG_MASK) != BOOL_TAG) {
    // TODO- This will trigger for garbage inputs too, is that ok? Should we throw error?
    return false;
  }

  // e2 is a snake boolean
  return (e1 == e2);
}

// ASSUME: e1 is a snake number
bool cequalToNumber(SNAKEVAL e1, SNAKEVAL e2) {
  if ((e2 & NUM_TAG_MASK) != NUM_TAG) {
    // TODO- This will trigger for garbage inputs too, is that ok? Should we throw error?
    return false;
  }

  // e2 is a snake number
  return (e1 == e2);
}

// ASSUME: e1 is a snake tuple and that we have already checked e1 != e2
bool cequalToTuple(SNAKEVAL e1, SNAKEVAL e2) {
  if ((e2 & TUPLE_TAG_MASK) != TUPLE_TAG) {
    // TODO- This will trigger for garbage inputs too, is that ok? Should we throw error?
    return false;
  }
  // e2 is a snake tuple
  // Convert to machine addresses
  e1 = e1 - 1L;
  e2 = e2 - 1L;

  // Handle nil cases
  if (e1 == 0L && e2 == 0L) {
    // both nil
    return true;
  } else if (e1 == 0L || e2 == 0L) {
    // exactly 1 is nil
    return false;
  }

  // e1 and e2 are tuples (with dif mem locations) and neither are nil
  // Now need to check structural equality
  int64_t* e1_heap_address = (int64_t*) e1;
  int64_t* e2_heap_address = (int64_t*) e2;

  int64_t e1_tup_size = e1_heap_address[0];
  int64_t* e1_elems = e1_heap_address + 1;
  int64_t e2_tup_size = e2_heap_address[0];
  int64_t* e2_elems = e2_heap_address + 1;

  // Different sizes means unequal for sure
  if (e1_tup_size != e2_tup_size) {
    return false;
  }

  // e1 and e2 have same size
  for (int i = 0; i < e1_tup_size; ++i) {
    if (!cequalInner(e1_elems[i], e2_elems[i])) {
      return false;
    }
  }
  return true;
}

bool cequalInner(SNAKEVAL e1, SNAKEVAL e2) {
  if (e1 == e2) {
    // shortcircuit
    // TODO, this will pass for garbage inputs -> should we move into the helpers?
    return true;
  }

  if ((e1 & BOOL_TAG_MASK) == BOOL_TAG) {
    return cequalToBoolean(e1, e2);
  } else if ((e1 & NUM_TAG_MASK) == NUM_TAG) {
    return cequalToNumber(e1, e2);
  } else if ((e1 & TUPLE_TAG_MASK) == TUPLE_TAG) {
    return cequalToTuple(e1, e2);
  } else {
    // e1 is an unknown type
    error(err_BAD_INPUT);  // should exit
    return false;  // defensive coding
  }
}

SNAKEVAL cequal(SNAKEVAL e1, SNAKEVAL e2) {
  if (cequalInner(e1, e2)) {
    return const_true;
  } else {
    return const_false;
  }
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
