#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>
#include "gc.h"

typedef uint64_t SNAKEVAL;

extern SNAKEVAL our_code_starts_here(uint64_t* HEAP, uint64_t size) asm("?our_code_starts_here");
extern void error() asm("?error");
extern SNAKEVAL set_stack_bottom(uint64_t* stack_bottom) asm("?set_stack_bottom");
extern SNAKEVAL print(SNAKEVAL val) asm("?print");
extern SNAKEVAL input() asm("?input");
extern SNAKEVAL printStack(SNAKEVAL val, uint64_t* rsp, uint64_t* rbp, uint64_t args) asm("?print_stack");
extern SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) asm("?equal");
extern uint64_t* try_gc(uint64_t* alloc_ptr, uint64_t amount_needed, uint64_t* first_frame, uint64_t* stack_top) asm("?try_gc");
extern uint64_t* HEAP_END asm("?HEAP_END");
extern uint64_t* HEAP asm("?HEAP");
extern char *FIELDS_CONCAT asm("?fields");
extern int NUM_FIELDS asm("?num_fields");
extern bool checkFields(SNAKEVAL first, SNAKEVAL second) asm("?check_fields");

const uint64_t NUM_TAG_MASK     = 0x0000000000000001;
const uint64_t BOOL_TAG_MASK    = 0x000000000000000F;
const uint64_t TUPLE_TAG_MASK   = 0x000000000000000F;
const uint64_t CLOSURE_TAG_MASK = 0x000000000000000F;
const uint64_t RECORD_TAG_MASK  = 0x000000000000000F;
const uint64_t TABLE_TAG_MASK   = 0x000000000000000F;
const uint64_t NUM_TAG          = 0x0000000000000000;
const uint64_t BOOL_TAG         = 0x0000000000000007;
const uint64_t TUPLE_TAG        = 0x0000000000000001;
const uint64_t CLOSURE_TAG      = 0x0000000000000005;
const uint64_t RECORD_TAG       = 0x0000000000000003;
const uint64_t TABLE_TAG        = 0x0000000000000009;
const uint64_t BOOL_TRUE        = 0xFFFFFFFFFFFFFFFF;
const uint64_t BOOL_FALSE       = 0x7FFFFFFFFFFFFFFF;
const uint64_t NIL              = ((uint64_t)NULL | TUPLE_TAG);

const uint64_t ERR_COMP_NOT_NUM         = 1;
const uint64_t ERR_ARITH_NOT_NUM        = 2;
const uint64_t ERR_LOGIC_NOT_BOOL       = 3;
const uint64_t ERR_IF_NOT_BOOL          = 4;
const uint64_t ERR_OVERFLOW             = 5;
const uint64_t ERR_GET_NOT_TUPLE        = 6;
const uint64_t ERR_GET_LOW_INDEX        = 7;
const uint64_t ERR_GET_HIGH_INDEX       = 8;
const uint64_t ERR_NIL_DEREF            = 9;
const uint64_t ERR_OUT_OF_MEMORY        = 10;
const uint64_t ERR_SET_NOT_TUPLE        = 11;
const uint64_t ERR_SET_LOW_INDEX        = 12;
const uint64_t ERR_SET_HIGH_INDEX       = 13;
const uint64_t ERR_CALL_NOT_CLOSURE     = 14;
const uint64_t ERR_CALL_ARITY_ERR       = 15;
const uint64_t ERR_GET_NOT_NUM          = 16;
const uint64_t ERR_SET_NOT_NUM          = 17;
const uint64_t ERR_BAD_INPUT            = 18;
const uint64_t ERR_GET_FIELD_NOT_RECORD = 19;
const uint64_t ERR_GET_FIELD_NOT_FOUND  = 20;
const uint64_t ERR_TABLE_OF_NOT_RECORD  = 21;
const uint64_t ERR_TABLE_OF_HET_RECORDS = 22;
// TODO- Add error checking to input() for ERR_BAD_INPUT

size_t HEAP_SIZE;
uint64_t* STACK_BOTTOM;
uint64_t* HEAP;
uint64_t* HEAP_END;

SNAKEVAL set_stack_bottom(uint64_t* stack_bottom) {
  STACK_BOTTOM = stack_bottom;
  return 0;
}

uint64_t* FROM_S;
uint64_t* FROM_E;
uint64_t* TO_S;
uint64_t* TO_E;

char **FIELDS;

SNAKEVAL equal(SNAKEVAL val1, SNAKEVAL val2) {
  if (val1 == val2) { return BOOL_TRUE; }
  if (val1 == NIL || val2 == NIL) { return BOOL_FALSE; }
  if ((val1 & TUPLE_TAG_MASK) == TUPLE_TAG && (val2 & TUPLE_TAG_MASK) == TUPLE_TAG) {
    uint64_t *tup1 = (uint64_t*)(val1 - TUPLE_TAG);
    uint64_t *tup2 = (uint64_t*)(val2 - TUPLE_TAG);
    if (tup1[0] != tup2[0]) { return BOOL_FALSE; }
    for (uint64_t i = 1; i <= tup1[0] / 2; i++) {
      if (equal(tup1[i], tup2[i]) == BOOL_FALSE)
        return BOOL_FALSE;
    }
    return BOOL_TRUE;
  }
  if ((val1 & RECORD_TAG_MASK) == RECORD_TAG && (val2 & RECORD_TAG_MASK) == RECORD_TAG) {
    uint64_t *rec1 = (uint64_t*)(val1 - RECORD_TAG);
    uint64_t *rec2 = (uint64_t*)(val2 - RECORD_TAG);
    if (rec1[0] != rec2[0]) { return BOOL_FALSE; }
    // Multiply by 2 to go through all fieldId-value pairs
    for (uint64_t i = 1; i <= rec1[0] * 2; i++) {
      if (equal(rec1[i], rec2[i]) == BOOL_FALSE)
        return BOOL_FALSE;
    }
    return BOOL_TRUE;
  }
  if ((val1 & TABLE_TAG_MASK) == TABLE_TAG && (val2 & TABLE_TAG_MASK) == TABLE_TAG) {
    uint64_t *table1 = (uint64_t*)(val1 - TABLE_TAG);
    uint64_t *table2 = (uint64_t*)(val2 - TABLE_TAG);
    if (table1[0] != table2[0]) { return BOOL_FALSE; }
    for (uint64_t i = 1; i <= table1[0]; i++) {
      if (equal(table1[i], table2[i]) == BOOL_FALSE)
        return BOOL_FALSE;
    }
    return BOOL_TRUE;
  }
  return BOOL_FALSE;
}

bool checkFields(SNAKEVAL first, SNAKEVAL second) {
  // Assume that both have been tag-checked already
  uint64_t *first_ptr = (uint64_t *) (first & (~RECORD_TAG_MASK));
  uint64_t *second_ptr = (uint64_t *) (second & (~RECORD_TAG_MASK));
  if (first_ptr[0] != second_ptr[0]) {
    // Diff number of fields
    return false;
  }
  uint64_t num_fields = first_ptr[0];
  for (uint64_t i = 0; i < num_fields; ++i) {
    if (first_ptr[2 * i + 1] != second_ptr[2 * i + 1]) {
      return false;
    }
  }
  return true;
}

void printHelp(FILE *out, SNAKEVAL val, bool in_row);

void printRecordFieldsAsRow(FILE *out, SNAKEVAL record_snakeval) {
  uint64_t *record_ptr = (uint64_t *) (record_snakeval & (~RECORD_TAG_MASK));
  int num_fields = record_ptr[0];
  if (num_fields == 0) {
    fprintf(out, "(no fields)");
    return;
  }
  for (int i = 0; i < num_fields; ++i) {
    // [field name 1]\t[field name 2]\t...\t[field name n]
    uint64_t field_num = record_ptr[(i * 2) + 1]; // "+ 1" for size
    fprintf(out, "%s", FIELDS[field_num]);
    if (i < num_fields - 1) {
      fprintf(out, "\t");
    }
  }
}

void printRecordValuesAsRow(FILE *out, SNAKEVAL record_snakeval) {
  uint64_t *record_ptr = (uint64_t *) (record_snakeval & (~RECORD_TAG_MASK));
  int num_fields = record_ptr[0];
  for (int i = 0; i < num_fields; ++i) {
    // [field 1]\t[field 2]\t...\t[field n]
    uint64_t field_val = record_ptr[(i * 2) + 2]; // "+ 2" for size and fieldId
    printHelp(out, field_val, true);
    if (i < num_fields - 1) {
      fprintf(out, "\t");
    }
  }
}

uint64_t tupleCounter = 0;

// in_row = whether or not we are printing within a row. If we are, should summarize some
// SNAKEVALs (e.g., tables) to return simplified outputs like "(table)"
void printHelp(FILE *out, SNAKEVAL val, bool in_row) {
  // printf("(printed %p): ", (void *) val);
  if (val == NIL) {
    fprintf(out, "nil");
  }
  else if((val & NUM_TAG_MASK) == NUM_TAG) {
    fprintf(out, "%ld", ((int64_t)val) >> 1); // deliberately int64, so that it's signed
  }
  else if(val == BOOL_TRUE) {
    fprintf(out, "true");
  }
  else if(val == BOOL_FALSE) {
    fprintf(out, "false");
  }
  else if ((val & CLOSURE_TAG_MASK) == CLOSURE_TAG) {
    uint64_t* addr = (uint64_t*)(val - CLOSURE_TAG);
    fprintf(out, "[%p - 5] ==> <function arity %ld, fn-ptr %p, closed %ld>",
            (uint64_t*)val, addr[0], (uint64_t*)addr[1], addr[2]);
    // TODO- If we switch to encoding the lengths as SNAKEVALs, need to divide by 2 above (and for tuples)
    /* fprintf(out, "\nClosed-over values:\n"); */
    /* for (uint64_t i = 0; i < addr[1] / 2; i++) { */
    /*   if (i > 0) { fprintf(out, "\n"); } */
    /*   if ((addr[3 + i] & TUPLE_TAG_MASK) == 5) { */
    /*     fprintf(out, "<closure %p>", (uint64_t*)addr[3 + i]); */
    /*   } else { */
    /*     printHelp(out, addr[3 + i]); */
    /*   } */
    /* } */
  }
  /* else if ((val & TUPLE_TAG_MASK) == 3) { */
  /*   fprintf(out, "forwarding to "); */
  /*   fflush(out); */
  /*   fprintf(out, "%p", (int*)(val - 3)); */
  /*   fflush(out); */
  /*   return; */
  /* } */
  else if ((val & TUPLE_TAG_MASK) == TUPLE_TAG) {
    uint64_t* addr = (uint64_t*)(val - TUPLE_TAG);
    // Check whether we've visited this tuple already
    if ((*addr & 0x8000000000000000) != 0) {
      fprintf(out, "<cyclic tuple %d>", (int)(*addr & 0x7FFFFFFFFFFFFFFF));
      return;
    }
    /* if (!(addr >= FROM_S && addr < FROM_E) && !(addr >= TO_S && addr < TO_E)) { */
    /*   fprintf(out, "DANGLING POINTER %p", addr); */
    /*   return; */
    /* } */
    // Mark this tuple: save its length locally, then mark it
    uint64_t len = addr[0];
    if (len & 0x1) { // actually, it's a forwarding pointer
      fprintf(out, "forwarding to %p", (uint64_t*)(len - 1));
      return;
    } else {
      len /= 2; // length is encoded, also see below/end of this func
    }
    /* fprintf(out, "Heap is:\n"); */
    /* naive_print_heap(HEAP, HEAP_END); */
    /* fprintf(out, "%p-->(len=%d)", (int*)(val - 1), len / 2); */
    /* fflush(out); */
    *(addr) = 0x8000000000000000 | (++tupleCounter);
    fprintf(out, "(");
    for (uint64_t i = 1; i <= len; i++) {
      if (i > 1) fprintf(out, ", ");
      printHelp(out, addr[i], in_row);
    }
    if (len == 1) fprintf(out, ",");
    fprintf(out, ")");
    // Unmark this tuple: restore its length to the SNAKEVAL
    *(addr) = len * 2;
  }
  else if ((val & RECORD_TAG_MASK) == RECORD_TAG) {
    // [ num fields | field 1 num | field 1 data | field 2 num | field 2 data | ... | field n num | field n data | padding ]
    // addr [0]            [1]           [2]            [3]           [4]       ...
    uint64_t* addr = (uint64_t*)(val - RECORD_TAG);
    uint64_t len = addr[0];
    if (len == 0) {
      fprintf(out, "{}");
      return;
    }
    fprintf(out, "{ ");
    for (uint64_t i = 0; i < len; i++) {
      if (i > 0) fprintf(out, ", ");
      uint64_t field_num = addr[(i * 2) + 1];
      fprintf(out, "%s = ", FIELDS[field_num]);
      printHelp(out, addr[(i * 2) + 2], true);
    }
    fprintf(out, " }");
  }
  else if ((val & TABLE_TAG_MASK) == TABLE_TAG) {
    // [ num recs | rec 1 | rec 2 | ... | rec n ]
    // addr [0]      [1]     [2]    ...
    uint64_t* addr = (uint64_t*)(val - TABLE_TAG);
    uint64_t num_records = addr[0];
    // example/template of table printing behavior:
    // table:
    // \t   f1 \t f2   \t f3
    // 1 \t 17 \t 103  \t 86
    // 2 \t 2  \t 1337 \t 0
    if (num_records == 0) {
      fprintf(out, "(empty table)");
    } else if (in_row) {
      fprintf(out, "(non-empty table)");
    } else {
      SNAKEVAL first_record_snakeval = addr[1];

      fprintf(out, "table:\n\t");
      printRecordFieldsAsRow(out, first_record_snakeval);

      for (uint64_t i = 0; i < num_records; i++) {
        fprintf(out, "\n%lu\t", i);
        SNAKEVAL this_record_snakeval = addr[i + 1]; // + 1 because num_records
        printRecordValuesAsRow(out, this_record_snakeval);
      }
    }
  }
  else {
    fprintf(out, "Unknown value: %#018lx", val);
  }
}


SNAKEVAL printStack(SNAKEVAL val, uint64_t* rsp, uint64_t* rbp, uint64_t args) {
  printf("RSP: %#018lx\t==>  ", (uint64_t)rsp); fflush(stdout);
  printHelp(stdout, *rsp, false); fflush(stdout);
  printf("\nRBP: %#018lx\t==>  ", (uint64_t)rbp); fflush(stdout);
  printHelp(stdout, *rbp, false); fflush(stdout);
  printf("\n(difference: %ld)\n", (uint64_t)(rsp - rbp)); fflush(stdout);
  printf("Requested return val: %#018lx\t==> ", (uint64_t)val); fflush(stdout);
  printHelp(stdout, val, false); fflush(stdout);
  printf("\n"); fflush(stdout);
  printf("Num args: %ld\n", args);

  uint64_t* origRsp = rsp;
  
  if (rsp > rbp) {
    printf("Error: RSP and RBP are not properly oriented\n"); fflush(stdout);
  } else {
    for (uint64_t* cur = rsp; cur < STACK_BOTTOM + 3; cur++) {
      if (cur == STACK_BOTTOM) {
        printf("BOT %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == rbp) {
        printf("RBP %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == origRsp) {
        printf("    %#018lx: %#018lx\t==>  old rbp\n", (uint64_t)cur, *cur); fflush(stdout);
      } else if (cur == rbp + 1) {
        printf("    %#018lx: %#018lx\t==>  saved ret\n", (uint64_t)cur, *cur); fflush(stdout);
        rsp = rbp + 2;
        rbp = (uint64_t*)(*rbp);
      } else if (cur == STACK_BOTTOM + 2) {
        printf("    %#018lx: %#018lx\t==>  heap\n", (uint64_t)cur, *cur); fflush(stdout);
      } else {
        printf("    %#018lx: %#018lx\t==>  ", (uint64_t)cur, *cur); fflush(stdout);
        printHelp(stdout, *cur, false); fflush(stdout);
        printf("\n"); fflush(stdout);
      }
    }
  }
  return val;
}

SNAKEVAL input() {
  int64_t int_input;
  char str_input[6] = { '\0' };
  if (scanf("%ld", &int_input) == 1) {
    return int_input << 1;
  }
  if (scanf("%5s", str_input) == 1) {
    if (strcmp(str_input, "true") == 0) {
      return BOOL_TRUE;
    } else if (strcmp(str_input, "false") == 0) {
      return BOOL_FALSE;
    } else {
      error(ERR_BAD_INPUT);
    }
  }
  error(ERR_BAD_INPUT);
}

SNAKEVAL print(SNAKEVAL val) {
  printHelp(stdout, val, false);
  printf("\n");
  fflush(stdout);
  return val;
}

void error(uint64_t code, SNAKEVAL val) {
  switch (code) {
  case ERR_COMP_NOT_NUM:
    fprintf(stderr, "Error: comparison expected a number, got "); printHelp(stderr, val, false);
    break;
  case ERR_ARITH_NOT_NUM:
    fprintf(stderr, "Error: arithmetic expected a number, got "); printHelp(stderr, val, false);
    break;
  case ERR_LOGIC_NOT_BOOL:
    fprintf(stderr, "Error: logic expected a boolean, got "); printHelp(stderr, val, false);
    break;
  case ERR_IF_NOT_BOOL:
    fprintf(stderr, "Error: if expected a boolean, got "); printHelp(stderr, val, false);
    break;
  case ERR_OVERFLOW:
    fprintf(stderr, "Error: Integer overflow, got "); printHelp(stderr, val, false);
    break;
  case ERR_GET_NOT_TUPLE:
    fprintf(stderr, "Error: get expected tuple, got "); printHelp(stderr, val, false);
    break;
  case ERR_GET_LOW_INDEX:
    fprintf(stderr, "Error: index too small to get, got %ld\n", (uint64_t)val);
    break;
  case ERR_GET_HIGH_INDEX:
    fprintf(stderr, "Error: index too large to get, got %ld\n", (uint64_t)val);
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
  case ERR_CALL_NOT_CLOSURE:
    fprintf(stderr, "Error: tried to call a non-closure value: "); printHelp(stderr, val, false);
    break;
  case ERR_CALL_ARITY_ERR:
    fprintf(stderr, "Error: arity mismatch in call\n");
    break;
  case ERR_GET_NOT_NUM:
    fprintf(stderr, "Error: tuple-get index not numeric\n");
    break;
  case ERR_SET_NOT_NUM:
    fprintf(stderr, "Error: tuple-set index not numeric\n");
    break;
  case ERR_BAD_INPUT:
    fprintf(stderr, "Error: bad input, input must be a number or a bool\n");
    break;
  case ERR_GET_FIELD_NOT_RECORD:
    fprintf(stderr, "Error: record-get expected record, got "); printHelp(stderr, val, false);
    break;
  case ERR_GET_FIELD_NOT_FOUND:
    fprintf(stderr, "Error: record-get failed to find field of name %s\n", FIELDS[(uint64_t) val]);
    break;
  case ERR_TABLE_OF_NOT_RECORD:
    fprintf(stderr, "Error: table-create expected record, got "); printHelp(stderr, val, false);
    break;
  case ERR_TABLE_OF_HET_RECORDS:
    fprintf(stderr, "Error: table-create expected homogeneous records. Inconsistent record was "); printHelp(stderr, val, false);
    break;
  default:
    fprintf(stderr, "Error: Unknown error code: %ld, val: \n", code); printHelp(stderr, val, false);
  }
  // fprintf(stderr, "\n%p ==> ", (uint64_t*)val);
  // printHelp(stderr, val, false);
  fprintf(stderr, "\n");
  fflush(stderr);
  // naive_print_heap(HEAP, HEAP_END);
  fflush(stdout);
  free(HEAP);
  exit(code);
}


/*
  Try to reserve the desired number of bytes of memory, and free garbage if
  needed.  Fail (and exit the program) if there is insufficient memory.  Does 
  not actually allocate the desired number of bytes of memory; the caller 
  will do that.

  Arguments:

    uint64_t* alloc_ptr - the current top of the heap (which we store in R15), where
                          the next allocation should occur, if possible
    uint64_t bytes_needed - the number of bytes of memory we want to allocate
                            (including padding)
    uint64_t* cur_frame - the base pointer of the topmost stack frame of our code
                          (i.e., RBP)
    uint64_t* cur_stack_top - the stack pointer of the topmost stack frame of our
                              code (i.e., RSP)

  Returns:
    The new top of the heap (i.e. the new value of R15) after garbage collection.  
    Does not actually allocate bytes_needed space.

  Side effect:
    Also updates HEAP_END to point to the new end of the heap, if it's changed
*/
uint64_t* try_gc(uint64_t* alloc_ptr, uint64_t bytes_needed, uint64_t* cur_frame, uint64_t* cur_stack_top) {
  uint64_t* new_heap = (uint64_t*)calloc(HEAP_SIZE + 15, sizeof(uint64_t));
  uint64_t* old_heap = HEAP;
  uint64_t* old_heap_end = HEAP_END;

  uint64_t* new_r15 = (uint64_t*)(((uint64_t)new_heap + 15) & ~0xF);
  uint64_t* new_heap_end = new_r15 + HEAP_SIZE;

  FROM_S = (uint64_t*)(((uint64_t)HEAP + 15) & ~0xF);
  FROM_E = HEAP_END;
  TO_S = new_r15;
  TO_E = new_heap_end;

  /* printf("FROM_S = %p, FROM_E = %p, TO_S = %p, TO_E = %p\n", FROM_S, FROM_E, TO_S, TO_E); */
  /* naive_print_heap(FROM_S, FROM_E); */
  /* printStack(BOOL_TRUE, cur_stack_top, cur_frame, 0); */

  // Abort early, if we can't allocate a new to-space
  if (new_heap == NULL) {
    fprintf(stderr, "Out of memory: could not allocate a new semispace for garbage collection\n");
    fflush(stderr);
    if (old_heap != NULL) free(old_heap);
    exit(ERR_OUT_OF_MEMORY);
  }
  
  new_r15 = gc(STACK_BOTTOM, cur_frame, cur_stack_top, FROM_S, HEAP_END, new_r15);
  HEAP = new_heap;
  HEAP_END = new_heap_end;
  free(old_heap);

  // Note: strict greater-than is correct here: if new_r15 + (bytes_needed / 8) == HEAP_END,
  // that does not mean we're *using* the byte at HEAP_END, but rather that it would be the
  // next free byte, which is still ok and not a heap-overflow.
  if (bytes_needed / sizeof(uint64_t) > HEAP_SIZE) {
    fprintf(stderr, "Allocation error: needed %ld words, but the heap is only %ld words\n",
            bytes_needed / sizeof(uint64_t), HEAP_SIZE);
    fflush(stderr);
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else if((new_r15 + (bytes_needed / sizeof(uint64_t))) > HEAP_END) {
    fprintf(stderr, "Out of memory: needed %ld words, but only %ld remain after collection\n",
            bytes_needed / sizeof(uint64_t), (HEAP_END - new_r15));
    fflush(stderr);
    if (new_heap != NULL) free(new_heap);
    exit(ERR_OUT_OF_MEMORY);
  } else {
    /* fprintf(stderr, "new_r15 = %p\n", new_r15); */
    /* naive_print_heap(HEAP, HEAP_END); */
    return new_r15;
  }
}

int main(int argc, char** argv) {
  // Generate malloc'd FIELDS array of field names
  FIELDS = malloc(NUM_FIELDS * sizeof(char *));
  char *ptr = FIELDS_CONCAT;
  for (int i = 0; i < NUM_FIELDS; ++i) {
    FIELDS[i] = ptr;
    ptr += strlen(FIELDS[i]) + 1;
  }

  // // Print out FIELDS array
  // printf("Fields:\n");
  // if (NUM_FIELDS != 0) {
  //   for (int i = 0; i < NUM_FIELDS; ++i) {
  //     printf("%s\n", FIELDS[i]);
  //   }
  // } else {
  //   printf("No fields");
  // }
  // printf("\n");

  HEAP_SIZE = 100000;
  if (argc > 1) { HEAP_SIZE = atoi(argv[1]); }
  if (HEAP_SIZE < 0 || HEAP_SIZE > 1000000) { HEAP_SIZE = 0; }
  HEAP = (uint64_t*)calloc(HEAP_SIZE + 15, sizeof(uint64_t));

  uint64_t* aligned = (uint64_t*)(((uint64_t)HEAP + 15) & ~0xF);
  HEAP_END = aligned + HEAP_SIZE;
  /* printf("HEAP = %p, aligned = %p, HEAP_END = %p\n", HEAP, aligned, HEAP_END); */
  SNAKEVAL result = our_code_starts_here(aligned, HEAP_SIZE);
  /* smarter_print_heap(aligned, HEAP_END, TO_S, TO_E); */
  print(result);

  free(HEAP);
  return 0;
}

