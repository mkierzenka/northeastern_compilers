#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t *HEAP, int size) asm("our_code_starts_here");
extern void error(uint64_t err_code, SNAKEVAL val) asm("error");
extern SNAKEVAL print(SNAKEVAL val) asm("print");
extern SNAKEVAL input() asm("input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t* esp, uint64_t* ebp, int args) asm("print_stack");
extern SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) asm("equal");
extern SNAKEVAL printRaw(SNAKEVAL val) asm("print_raw");
extern uint64_t* STACK_BOTTOM asm("STACK_BOTTOM");


uint64_t* HEAP;

//extern uint64_t* HEAP_TOP asm("HEAP_TOP");

const uint64_t NUM_TAG_MASK     = 0x0000000000000001;
const uint64_t BOOL_TAG_MASK    = 0x0000000000000007;
const uint64_t TUPLE_TAG_MASK   = 0x0000000000000007;
const uint64_t CLOSURE_TAG_MASK = 0x0000000000000007;
const uint64_t NUM_TAG          = 0x0000000000000000;
const uint64_t BOOL_TAG         = 0x0000000000000007;
const uint64_t TUPLE_TAG        = 0x0000000000000001;
const uint64_t CLOSURE_TAG      = 0x0000000000000005;
const uint64_t BOOL_TRUE        = 0xFFFFFFFFFFFFFFFF;
const uint64_t BOOL_FALSE       = 0x7FFFFFFFFFFFFFFF;
const uint64_t NIL              = ((uint64_t)NULL | TUPLE_TAG);

const uint64_t ERR_COMP_NOT_NUM     = 1;
const uint64_t ERR_ARITH_NOT_NUM    = 2;
const uint64_t ERR_LOGIC_NOT_BOOL   = 3;
const uint64_t ERR_IF_NOT_BOOL      = 4;
const uint64_t ERR_OVERFLOW         = 5;
const uint64_t ERR_GET_NOT_TUPLE    = 6;
const uint64_t ERR_GET_LOW_INDEX    = 7;
const uint64_t ERR_GET_HIGH_INDEX   = 8;
const uint64_t ERR_GET_NOT_NUM      = 9;
const uint64_t ERR_NIL_DEREF        = 10;
const uint64_t ERR_OUT_OF_MEMORY    = 11;
const uint64_t ERR_SET_NOT_TUPLE    = 12;
const uint64_t ERR_SET_LOW_INDEX    = 13;
const uint64_t ERR_SET_NOT_NUM      = 14;
const uint64_t ERR_SET_HIGH_INDEX   = 15;
const uint64_t ERR_CALL_NOT_CLOSURE = 16;
const uint64_t ERR_CALL_ARITY_ERR   = 17;
const uint64_t ERR_BAD_INPUT        = 18;
const uint64_t ERR_TUP_IDX_NOT_NUM  = 19;

uint64_t* STACK_BOTTOM;

SNAKEVAL printRaw(SNAKEVAL val) {
  printf("%#018lx ==> %ld\n", val, val);
  return val;
}

typedef struct equal_cache {
  SNAKEVAL left;
  SNAKEVAL right;
} equal_cache;

int ensure_cache(equal_cache** p_cache, int last, int size, int needed) {
  int minneeded = last + needed;
  if (minneeded >= size) {
    int doubled = size * 2;
    int newsize = (doubled > minneeded) ? doubled : minneeded;
    equal_cache* newcache = (equal_cache*)realloc(*p_cache, size * 2 * sizeof(equal_cache));
    if (newcache != NULL) {
      *p_cache = newcache;
      return newsize;
    } else {
      fprintf(stderr, "Internal error while trying to compute equality\n");
      return 0;
    }
  }
  return size;
}

SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) {
  int size = 100;
  equal_cache* cache = (equal_cache*)calloc(size, sizeof(equal_cache));
  int cur = 0;
  int last = 1;
  SNAKEVAL ans = BOOL_TRUE;
  cache[cur].left = val1;
  cache[cur].right = val2;
  while (cur < last) {
    val1 = cache[cur].left;
    val2 = cache[cur].right;
    cur++;
    if (val1 == val2) { continue; }
    if (val1 == NIL || val2 == NIL) { ans = BOOL_FALSE; break; }
    int found_cached = -1;
    for (int i = 0; i < cur - 1; i++) {
      if (cache[i].left == val1 && cache[i].right == val2) {
        found_cached = i;
        break;
      }
    }
    if (found_cached > -1) { continue; }
    if ((val1 & TUPLE_TAG_MASK) == TUPLE_TAG && (val2 & TUPLE_TAG_MASK) == TUPLE_TAG) {
      uint64_t *tup1 = (uint64_t*)(val1 - TUPLE_TAG);
      uint64_t *tup2 = (uint64_t*)(val2 - TUPLE_TAG);
      if (tup1[0] != tup2[0]) { ans = BOOL_FALSE; break; }
      size = ensure_cache(&cache, last, size, tup1[0]);
      if (size == 0) {
        free(cache);
        return BOOL_FALSE;
      }
      for (int i = 1; i <= tup1[0]; i++) {
        cache[last].left = tup1[i];
        cache[last].right = tup2[i];
        last++;
      }
      continue;
    }
    ans = BOOL_FALSE;
    break;
  }
  free(cache);
  return ans;
}

int tupleCounter = 0;
void printHelp(FILE *out, SNAKEVAL val) {
  if (val == NIL) {
    fprintf(out, "nil");
  }
  else if((val & NUM_TAG_MASK) == NUM_TAG) {
    fprintf(out, "%ld", ((int64_t)val) >> 1);
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
    fprintf(out, "<function>");
    uint64_t* addr = (uint64_t*)(val - CLOSURE_TAG);
    uint64_t arity = addr[0];
    fprintf(out, "(%lu, ", arity);
    uint64_t code_ptr = addr[1];
    fprintf(out, "%#018lx, ", code_ptr);
    int num_free_vars = (int)addr[2];
    fprintf(out, "%d, ", num_free_vars);
    for (int i = 0; i < num_free_vars - 1; i++) {
      printHelp(out, addr[3 + i]);
      fprintf(out, ", ");
    }
    if (num_free_vars > 0) {
      printHelp(out, addr[3 + num_free_vars - 1]);
    }
    fprintf(out, ")");
  }
  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG) {
    uint64_t* addr = (uint64_t*)(val - TUPLE_TAG);
    if ((*addr & 0x8000000000000000) != 0) {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFFFFFFFFFF));
      return;
    }
    int len = (int)addr[0];
    *(addr) = 0x8000000000000000 | (++tupleCounter);
    fprintf(out, "(");
    for (int i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i]);
    }
    if (len == 1) fprintf(out, ", ");
    fprintf(out, ")");
    // Unmark this tuple: restore its length
    *(addr) = len; // length is encoded
  }
  else {
    fprintf(out, "Unknown value: %#018lx", val);
  }
}


SNAKEVAL printStack(SNAKEVAL val, uint64_t* esp, uint64_t* ebp, int args) {
  printf("ESP: %#018lx\t==>  ", (uint64_t)esp); fflush(stdout);
  printHelp(stdout, *esp); fflush(stdout);
  printf("\nEBP: %#018lx\t==>  ", (uint64_t)ebp); fflush(stdout);
  printHelp(stdout, *ebp); fflush(stdout);
  printf("\n(difference: %ld)\n", (uint64_t)(esp - ebp)); fflush(stdout);
  printf("Requested return val: %#018lx\t==> ", (uint64_t)val); fflush(stdout);
  printHelp(stdout, val); fflush(stdout);
  printf("\n"); fflush(stdout);
  printf("Num args: %d\n", args);

  uint64_t* origEsp = esp;

  if (esp > ebp) {
    printf("Error: ESP and EBP are not properly oriented\n"); fflush(stdout);
  } else {
    for (uint64_t* cur = esp; cur < STACK_BOTTOM + 3; cur++) {
      if (cur == STACK_BOTTOM) {
        printf("BOT %#018lx: %#018lx\t==>  old ebp\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == ebp) {
        printf("EBP %#018lx: %#018lx\t==>  old ebp\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == origEsp) {
        printf("    %#018lx: %#018lx\t==>  old ebp\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == ebp + 1) {
        printf("    %#018lx: %#018lx\t==>  saved ret\n", (uint64_t)cur, *cur); fflush(stdout);
        esp = ebp + 2;
        ebp = (uint64_t*)(*ebp);
      } else if (cur == STACK_BOTTOM + 2) {
        printf("    %#018lx: %#018lx\t==>  heap\n", (uint64_t)cur, *cur); fflush(stdout);
      } else {
        printf("    %#018lx: %#018lx\t==>  ", (uint64_t)cur, *cur); fflush(stdout);
        printHelp(stdout, *cur); fflush(stdout);
        printf("\n"); fflush(stdout);
      }
    }
  }
  return val;
}

SNAKEVAL input() {
  uint64_t ans;
  scanf("%ld", &ans);
  return ans << 1;
}

SNAKEVAL print(SNAKEVAL val) {
  printHelp(stdout, val);
  printf("\n");
  fflush(stdout);
  return val;
}


void error(uint64_t code, SNAKEVAL val) {
  switch (code) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number, got "); printHelp(stderr, val);
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number, got "); printHelp(stderr, val);
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error: logic expected a boolean, got "); printHelp(stderr, val);
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean, got "); printHelp(stderr, val);
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow, got "); printHelp(stderr, val);
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple, got "); printHelp(stderr, val);
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get, got %ld\n", (uint64_t)val);
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get, got %ld\n", (uint64_t)val);
    break;
  case ERR_GET_NOT_NUM:
    fprintf(stderr, "Error: get expected numeric index, got "); printHelp(stderr, val);
    break;
  case ERR_NIL_DEREF:
    fprintf(stderr, "Error: tried to access component of nil\n");
    break;
  case ERR_OUT_OF_MEMORY:
    fprintf(stderr, "Error: out of memory\n");
    break;
  case ERR_SET_NOT_TUPLE:
    fprintf(stderr, "Error: set expected tuple\n");
    break;
  case ERR_SET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to set\n");
    break;
  case ERR_SET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to set\n");
    break;
  case ERR_SET_NOT_NUM:
    fprintf(stderr, "Error: set expected numeric index, got "); printHelp(stderr, val);
    break;
  case ERR_CALL_NOT_CLOSURE:
    fprintf(stderr, "Error: tried to call a non-closure value: "); printHelp(stderr, val);
    break;
  case ERR_CALL_ARITY_ERR:
    fprintf(stderr, "Error: arity mismatch in call\n");
    break;
  case ERR_BAD_INPUT:
    fprintf(stderr, "Error: bad input, input must be a number or a bool");
    break;
  case ERR_TUP_IDX_NOT_NUM:
    fprintf(stderr, "Error: tuple indices must be numeric");
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %ld, val: ", code); printHelp(stderr, val);
  }
  free(HEAP);
  exit(code);
}

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
