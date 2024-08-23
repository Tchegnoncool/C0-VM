/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2023                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
#include <assert.h>
#include <stdio.h>
#include <limits.h>
#include <stdlib.h>

#include "lib/xalloc.h"
#include "lib/stack.h"
#include "lib/contracts.h"
#include "lib/c0v_stack.h"
#include "lib/c0vm.h"
#include "lib/c0vm_c0ffi.h"
#include "lib/c0vm_abort.h"

/* call stack frames */
typedef struct frame_info frame;
struct frame_info {
  c0v_stack_t  S;   /* Operand stack of C0 values */
  ubyte       *P;   /* Function body */
  size_t       pc;  /* Program counter */
  c0_value    *V;   /* The local variables */
};

int execute(struct bc0_file *bc0) {
  REQUIRES(bc0 != NULL);

  /* Variables */
  c0v_stack_t S = c0v_stack_new(); /* Operand stack of C0 values */
  ubyte *P = bc0->function_pool[0].code;      /* Array of bytes that make up the current function */
  size_t pc = 0;     /* Current location within the current byte array P */
  c0_value *V = xcalloc(sizeof(c0_value), bc0->function_pool[0].num_vars);
  // bc0->native_pool.;   /* Local variables (you won't need this till Task 2) */
  // (void) V;      // silences compilation errors about V being currently unused

  /* The call stack, a generic stack that should contain pointers to frames */
  /* You won't need this until you implement functions. */
  gstack_t callStack = stack_new();
  // (void) callStack; // silences compilation errors about callStack being currently unused

  while (true) {

#ifdef DEBUG
    /* You can add extra debugging information here */
    fprintf(stderr, "Opcode %x -- Stack size: %zu -- PC: %zu\n",
            P[pc], c0v_stack_size(S), pc);
#endif

    switch (P[pc]) {

    /* Additional stack operation: */

    case POP: {
      pc++;
      c0v_pop(S);
      break;
    }

    case DUP: {
      pc++;
      c0_value v = c0v_pop(S);
      c0v_push(S,v);
      c0v_push(S,v);
      break;
    }

    case SWAP: {
      pc++;
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      c0v_push(S,v2);
      c0v_push(S,v1);
      break;
    }


    /* Returning from a function.
     * This currently has a memory leak! You will need to make a slight
     * change for the initial tasks to avoid leaking memory.  You will
     * need to revise it further when you write INVOKESTATIC. */

    case RETURN: {
      c0_value retval = c0v_pop(S);
      ASSERT(c0v_stack_empty(S));
      c0v_stack_free(S);
      free(V);
      if(stack_empty(callStack))
      {
        stack_free(callStack, NULL);
        IF_DEBUG(fprintf(stderr, "Returning %d from execute()\n", val2int(retval)));
        return val2int(retval);
      }
      else
      {
        frame *current_frame = (frame*)pop(callStack);
        
        S = current_frame->S;
        P = current_frame->P;
        pc = current_frame->pc;
        V = current_frame->V;
        // free(current_frame->V);
        free(current_frame);
        c0v_push(S, retval);
      }
      break;
    }


    /* Arithmetic and Logical operations */

    case IADD:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1+i2));
      c0v_push(S, r);
      break;
    }

    case ISUB:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1-i2));
      c0v_push(S, r);
      break;
    }

    case IMUL:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1*i2));
      c0v_push(S, r);
      break;
    }

    case IDIV:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      if(i2 == 0)
      {
        char* error = "Division by 0";
        c0_arith_error(error);
      }
      int32_t i1 = val2int(c0v_pop(S));
      if(i1 == (int)0x80000000 && i2 == -1)
      {
        char* error = "Dividing int_min by -1";
        c0_arith_error(error);
      }
      c0_value r = int2val((i1/i2));
      c0v_push(S, r);
      break;
    }

    case IREM:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      if(i2 == 0)
      {
        char* error = "Division by 0";
        c0_arith_error(error);
      }
      int32_t i1 = val2int(c0v_pop(S));
      if(i1 == (int)0x80000000 && i2 == -1)
      {
        char* error = "Dividing int_min by -1";
        c0_arith_error(error);
      }
      c0_value r = int2val((i1%i2));
      c0v_push(S, r);
      break;
    }

    case IAND:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1&i2));
      c0v_push(S, r);
      break;
    }

    case IOR:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1|i2));
      c0v_push(S, r);
      break;
    }

    case IXOR:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1^i2));
      c0v_push(S, r);
      break;
    }

    case ISHR:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      if(i2 < 0 || 32 <= i2)
      {
        char* error = "Shifting right by over 32 bits";
        c0_arith_error(error);
      }
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1 >> i2));
      c0v_push(S, r);
      break;
    }

    case ISHL:{
      pc++;
      int32_t i2 = val2int(c0v_pop(S));
      if(i2 < 0 || 32 <= i2)
      {
        char* error = "Shifting left by over 32 bits";
        c0_arith_error(error);
      }
      int32_t i1 = val2int(c0v_pop(S));
      c0_value r = int2val((i1 << i2));
      c0v_push(S, r);
      break;
    }


    /* Pushing constants */

    case BIPUSH:{
      pc++;
      ubyte b = P[pc]; // CHECK types!!!!! This should be unit then convert
      signed char sc = (signed char)b;
      int32_t i = (int32_t)sc;
      c0v_push(S,int2val(i));
      pc++;
      break;
    }

    case ILDC:{
      pc++;
      ubyte b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      int32_t i = bc0->int_pool[((b1 << 8) | b2)];
      c0v_push(S, int2val(i));
      pc++;
      break;
    }

    case ALDC:{
      pc++;
      ubyte b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      char* c = &bc0->string_pool[((b1 << 8) | b2)];
      c0v_push(S, ptr2val(c));
      pc++;
      break;
    }

    case ACONST_NULL:{
      pc++;
      c0v_push(S, ptr2val(NULL));
      break;
    }


    /* Operations on local variables */

    case VLOAD:{
      pc++;
      ubyte b = P[pc];
      c0_value v = V[b];
      c0v_push(S, v);
      pc++;
      break;
    }

    case VSTORE:{
      pc++;
      ubyte b = P[pc];
      c0_value v = c0v_pop(S);
      V[b] = v;
      pc++;
      break;
    }


    /* Assertions and errors */

    case ATHROW:{
      pc++;
      char* a = val2ptr(c0v_pop(S));
      c0_user_error(a);
      break;
    }

    case ASSERT:{
      pc++;
      char* a = val2ptr(c0v_pop(S));
      int32_t i = val2int(c0v_pop(S));
      if(i == 0) c0_assertion_failure(a);
      break;
    }


    /* Control flow operations */

    case NOP:
    {
      pc++;
      break;
    }

    case IF_CMPEQ:{
      pc++;
      int32_t b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if(val_equal(v1, v2)) pc = pc + (int32_t)(((b1 << 8) | b2) - (int32_t)2);
      else pc++;
      break;
    }

    case IF_CMPNE:{
      pc++;
      int32_t b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      c0_value v2 = c0v_pop(S);
      c0_value v1 = c0v_pop(S);
      if(!val_equal(v1, v2)) pc = pc + (int32_t)(((b1 << 8) | b2) - (int32_t)2);
      else pc++;
      break;
    }

    case IF_ICMPLT:{
      pc++;
      int32_t b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      if(i1 < i2) pc = pc + (int32_t)(((b1 << 8) | b2) - (int32_t)2);
      else pc++;
      break;
    }

    case IF_ICMPGE:{
      pc++;
      int32_t b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      if(i1 >= i2) pc = pc + (int32_t)(((b1 << 8) | b2) - (int32_t)2);
      else pc++;
      break;
    }

    case IF_ICMPGT:{
      pc++;
      int32_t b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      if(i1 > i2) pc = pc + (int32_t)(((b1 << 8) | b2) - (int32_t)2);
      else pc++;
      break;
    }

    case IF_ICMPLE:{
      pc++;
      int32_t b1 = P[pc];
      pc++;
      ubyte b2 = P[pc];
      int32_t i2 = val2int(c0v_pop(S));
      int32_t i1 = val2int(c0v_pop(S));
      if(i1 <= i2) pc = pc + (int32_t)(((b1 << 8) | b2) - (int32_t)2);
      else pc++;
      break;
    }

    case GOTO:{
      ubyte b1 = P[pc+1];
      ubyte b2 = P[pc+2];
      pc = pc + (int16_t)(((b1 << 8) | b2));
      break;
    }


    /* Function call operations: */

    case INVOKESTATIC:{
      ubyte b1 = P[pc+1];
      ubyte b2 = P[pc+2];
      int ind = (int16_t)(((uint16_t)(b1 << 8) | b2));
      frame *new_frame = xmalloc(sizeof(frame));

      new_frame->P = P;
      new_frame->pc = pc+3;
      new_frame->V = V;
      new_frame->S = S;

      struct function_info g = bc0->function_pool[ind];
      int num_vars = g.num_vars;

      P = g.code;
      pc = 0;
      V = xcalloc(sizeof(c0_value), num_vars);

      for(int i = g.num_args-1; i >= 0; i--)
      {
        V[i] = c0v_pop(S);
      }
      push(callStack, (stack_elem)new_frame);
      S = c0v_stack_new();
      break;
    }

    case INVOKENATIVE:{
      ubyte b1 = P[pc+1];
      ubyte b2 = P[pc+2];
      int ind = (int16_t)(((b1 << 8) | b2));

      struct native_info g = bc0->native_pool[ind];
      int num_args = g.num_args;
      c0_value *ARGS = xcalloc(sizeof(c0_value), num_args);

      for(int i = num_args-1; i >= 0; i--)
      {
        ARGS[i] = c0v_pop(S);
      }

      native_fn *native_func = native_function_table[g.function_table_index];
      c0_value v = (*native_func)(ARGS);
      c0v_push(S, v);
      free(ARGS);
      pc = pc + 3;

      break;
    }


    /* Memory allocation and access operations: */

    case NEW:{
      pc++;
      char* C = xcalloc(sizeof(char), (int32_t)P[pc]);
      char *error = "Can't store NULL pointer";
      if(C == NULL) c0_memory_error(error);
      c0v_push(S, ptr2val(C));
      pc++;
      break;
    }

    case IMLOAD:{
      pc++;
      c0_value v = c0v_pop(S);
      int32_t *adress = (int*)val2ptr(v);
      char *error = "Can't store NULL pointer";
      if(adress == NULL) c0_memory_error(error);
      c0v_push(S, int2val(*adress));
      break;
    }

    case IMSTORE:{
      pc++;
      c0_value v = c0v_pop(S);
      int32_t *adress = val2ptr(v);
      char *error = "Can't store NULL pointer";
      if(adress == NULL) c0_memory_error(error);
      int32_t i = val2int(c0v_pop(S));
      *adress = i;
      break;
    }

    case AMLOAD:{
      pc++;
      c0_value v = c0v_pop(S);
      void **adress = val2ptr(v);
      char *error = "Can't store NULL pointer";
      if(adress == NULL) c0_memory_error(error);
      c0v_push(S, ptr2val(adress));
      break;
    }

    case AMSTORE:{
      pc++;
      c0_value v = c0v_pop(S);
      void **adress1 = val2ptr(v);
      char *error = "Can't store NULL pointer";
      if(adress1 == NULL) c0_memory_error(error);
      void *adress2 = val2ptr(c0v_pop(S));
      *adress1 = adress2;
      break;
    }

    case CMLOAD:{
      pc++;
      c0_value v = c0v_pop(S);
      int32_t *adress = val2ptr(v);
      char *error = "Can't store NULL pointer";
      if(adress == NULL) c0_memory_error(error);
      int32_t x = (int32_t) (*adress);
      c0v_push(S, int2val(x));
      break;
    }

    case CMSTORE:{
      pc++;
      c0_value v = c0v_pop(S);
      int32_t *adress = val2ptr(v);
      char *error = "Can't store NULL pointer";
      if(adress == NULL) c0_memory_error(error);
      int32_t i = val2int(c0v_pop(S));
      *adress = i & 0x7f;
      break;
    }

    case AADDF:{
      pc++;
      c0_value v = c0v_pop(S);
      int32_t *adress = val2ptr(v);
      char *error = "Can't store NULL pointer";
      if(adress == NULL) c0_memory_error(error);
      c0v_push(S, ptr2val(adress+P[pc]));
      pc++;
      break;
    }


    // /* Array operations: */

    case NEWARRAY:{ // 0 length array is a NULL struct; Construvt a new struct and fiil out the fields look at the c0vm.h array struct definition.
      pc++;
      int32_t i = val2int(c0v_pop(S));
      char *error = "Can't allocate array of negative size.";
      if(i < 0) c0_memory_error(error);
      else if (i == 0)
      {
        c0v_push(S, ptr2val(NULL));
        pc++;
        break;
      }
      c0_array *arr = xmalloc(sizeof(c0_array));
      arr->count = i;
      arr->elt_size = P[pc];
      arr->elems = xcalloc(i, P[pc]);
      c0v_push(S, ptr2val(arr));
      pc++;
      break;
    }

    case ARRAYLENGTH:{
      pc++;
      c0_array *arr = val2ptr(c0v_pop(S));
      if(arr == NULL) c0v_push(S, int2val(0));
      else c0v_push(S, int2val(arr->count));
      break;
    }

    case AADDS:{
    pc++;
    int32_t i = val2int(c0v_pop(S));
    c0_array *arr = val2ptr(c0v_pop(S));
    char *error1 = "Can't acess a NULL pointer";
    char *error2 = "Index out of bounds";
    if(arr == NULL) c0_memory_error(error1);
    if(i < 0 || arr->count < (uint32_t)i) c0_memory_error(error2);
    int32_t size = arr->elt_size;
    c0v_push(S, ptr2val((void*)((char*)(arr->elems)+(size * i))));
    break;
    }


    /* BONUS -- C1 operations */

    case CHECKTAG:

    case HASTAG:

    case ADDTAG:

    case ADDROF_STATIC:

    case ADDROF_NATIVE:

    case INVOKEDYNAMIC:

    default:
      fprintf(stderr, "invalid opcode: 0x%02x\n", P[pc]);
      abort();
    }
  }

  /* cannot get here from infinite loop */
  assert(false);
}
