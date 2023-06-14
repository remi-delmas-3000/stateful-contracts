#include <assert.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdlib.h>

// oracle that tells us if we are in an initial state or not
static bool __initial_state;
uint32_t nondet_uint32_t();

// the original function to be checked
uint32_t get_time()
// __CPROVER_static(uint32_t count = 0)
// __CPROVER_requires(count < UINT32_MAX)
// __CPROVER_ensures(
//   count == __CPROVER_old(count) + 1 && __CPROVER_return_value == count)
{
#ifdef FAIL_BASE
  static uint32_t count = UINT32_MAX;
#else
  static uint32_t count = 0;
#endif
#ifdef FAIL_STEP
  /* violates the contract and the glue lemma by returning the value
  pre-increment and not incrementing */
  if (count == 32) {
    return count;
  }
#else
  return ++count;
#endif
}

// contract-derived abstraction
uint32_t get_time_contract() {
  static uint32_t count = 0;

  // check preconditions
  assert(count < UINT32_MAX);

  // history vars
  uint32_t count_old = count;

  // havoc state
  count = nondet_uint32_t();
  uint32_t __return_value = nondet_uint32_t();

  // assume post
  __CPROVER_assume(count == count_old + 1 && __return_value == count);

  // return value
  return __return_value;
}

#define GET_TIME_COUNT __CPROVER_ID "get_time::1::count"
#define GET_TIME_CONTRACT_COUNT __CPROVER_ID "get_time_contract::1::count"

// verification wrapper encoding sequential equivalence checking
// invoke with
// cbmc --function check_get_time stateful.c
int check_get_time() {
  // base case

  // check glue clause and preconditions
  assert(GET_TIME_CONTRACT_COUNT == GET_TIME_COUNT);
  assert(GET_TIME_CONTRACT_COUNT < UINT32_MAX);

  // step case

  // havoc statics
  GET_TIME_COUNT = nondet_uint32_t();
  GET_TIME_CONTRACT_COUNT = nondet_uint32_t();

  // assume glue clause and preconditions
  __CPROVER_assume(GET_TIME_CONTRACT_COUNT == GET_TIME_COUNT);
  __CPROVER_assume(GET_TIME_CONTRACT_COUNT < UINT32_MAX);

  // history variable
  uint32_t __contract_count_old = GET_TIME_CONTRACT_COUNT;

  // call the function
  uint32_t __return_value = get_time();

  // call the contract
  uint32_t __contract_return_value = get_time_contract();

  // check glue clause and postconditions
  assert(GET_TIME_CONTRACT_COUNT == GET_TIME_COUNT);
  assert(GET_TIME_CONTRACT_COUNT == __contract_count_old + 1);
  assert(__return_value == GET_TIME_CONTRACT_COUNT);

  // return
  return 0;
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

typedef enum { SUCCESS, FAILURE } status_t;

#define TEN_CALLS_COUNT __CPROVER_ID "ten_calls::1::count"

// function under verification
status_t ten_calls()
// __CPROVER_static(uint32_t count = TEN_CALLS_COUNT_INIT)
// __CPROVER_requires(count <= 10)
// __CPROVER_ensures(count <= 10)
// __CPROVER_ensures(
//     __CPROVER_old(count) < 10 ?
//         count == __CPROVER_old(count) + 1 :
//         count == __CPROVER_old(count))
// __CPROVER_ensures(__CPROVER_return_value == (__CPROVER_old(count) < 10 ?
// SUCCESS : FAILURE))
{
#ifdef FAIL_BASE
  static uint32_t count = 11;
#else
  static uint32_t count = 0;
#endif

#ifdef FAIL_STEP
  if (count <= 10)
#else
  if (count < 10)
#endif
  {
    count++;
    return SUCCESS;
  } else {
    return FAILURE;
  }
}

// contract-derived abstraction
status_t ten_calls_contract() {
  static uint32_t count = 0;

  // preconditions
  assert(count <= 10);
  uint32_t count_old = count;

  // havoc
  count = nondet_uint32_t();
  status_t __return_value = nondet_uint32_t() ? SUCCESS : FAILURE;

  // postconditions
  __CPROVER_assume(count <= 10);
  __CPROVER_assume(count_old < 10 ? count == count_old + 1
                                  : count == count_old);
  __CPROVER_assume(__return_value == (count_old < 10 ? SUCCESS : FAILURE));
  return __return_value;
}

#define TEN_CALLS_COUNT __CPROVER_ID "ten_calls::1::count"
#define TEN_CALLS_CONTRACT_COUNT __CPROVER_ID "ten_calls_contract::1::count"

// the contract checking harness function
// invoke with
// cbmc --function check_ten_calls stateful.c
int check_ten_calls() {

  // base case

  // check glue clause and preconditions in base case
  assert(TEN_CALLS_CONTRACT_COUNT == TEN_CALLS_COUNT);
  assert(TEN_CALLS_CONTRACT_COUNT <= 10);

  // step case
  // havoc statics
  TEN_CALLS_COUNT = nondet_uint32_t();
  TEN_CALLS_CONTRACT_COUNT = nondet_uint32_t();

  // step case
  // assume glue clause and preconditions
  __CPROVER_assume(TEN_CALLS_CONTRACT_COUNT == TEN_CALLS_COUNT);
  __CPROVER_assume(TEN_CALLS_CONTRACT_COUNT <= 10);

  uint32_t __contract_count_old = TEN_CALLS_CONTRACT_COUNT;

  // call the function
  status_t __return_value = ten_calls();

  // call the contract
  status_t __contract_return_value = ten_calls_contract();

  // check glue clause and postconditions
  assert(TEN_CALLS_CONTRACT_COUNT == TEN_CALLS_COUNT);
  assert(TEN_CALLS_CONTRACT_COUNT <= 10);
  assert(__contract_count_old < 10
             ? TEN_CALLS_CONTRACT_COUNT == __contract_count_old + 1
             : TEN_CALLS_CONTRACT_COUNT == __contract_count_old);
  assert(__return_value == (__contract_count_old < 10 ? SUCCESS : FAILURE));

  return 0;
}

////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////
////////////////////////////////////////////////////////////

// invoke with
// cbmc --function ten_calls_replace stateful.c
void ten_calls_replace() {

  for (size_t i = 0; i < 10; i++) {
    status_t status = ten_calls_contract();
    assert(SUCCESS == status); // SUCCESS
  }

  assert(FAILURE == ten_calls_contract()); // SUCCESS
}

// invoke with
// cbmc --function ten_calls_replace_nondet --nondet-static stateful.c
void ten_calls_replace_nondet() {
  __CPROVER_assume(TEN_CALLS_CONTRACT_COUNT <= 10);

  for (size_t i = 0; i < 10; i++) {
    status_t status = ten_calls_contract();
    assert(SUCCESS == status); // this can now fail at any iteration
    assert(!(i == 9 && SUCCESS == status)); // but this is reachable too
  }

  assert(FAILURE == ten_calls_contract()); // passes
}
