#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lang.h"

struct expr * new_expr_ptr() {
  struct expr * res = (struct expr *) malloc(sizeof(struct expr));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  return res;
}

struct expr * TConst(unsigned int value) {
  struct expr * res = new_expr_ptr();
  res -> t = T_CONST;
  res -> d.CONST.value = value;
  return res;
}

struct expr * TVar(char * name) {
  struct expr * res = new_expr_ptr();
  res -> t = T_VAR;
  res -> d.VAR.name = name;
  return res;
}

struct expr * TPlus(struct expr * left, struct expr * right) {
  struct expr * res = new_expr_ptr();
  res -> t = T_PLUS;
  res -> d.PLUS.left = left;
  res -> d.PLUS.right = right;
  return res;
}

struct expr * TMult(struct expr * left, struct expr * right) {
  struct expr * res = new_expr_ptr();
  res -> t = T_MULT;
  res -> d.MULT.left = left;
  res -> d.MULT.right = right;
  return res;
}

void print_expr(struct expr * e) {
  switch (e -> t) {
  case T_CONST:
    printf("CONST(%d)", e -> d.CONST.value);
    break;
  case T_VAR:
    printf("VAR(%s)", e -> d.VAR.name);
    break;
  case T_PLUS:
    printf("PLUS(");
    print_expr(e -> d.PLUS.left);
    printf(",");
    print_expr(e -> d.PLUS.right);
    printf(")");
    break;
  case T_MULT:
    printf("MULT(");
    print_expr(e -> d.MULT.left);
    printf(",");
    print_expr(e -> d.MULT.right);
    printf(")");
    break;
  }
}

int build_nat(char * c, int len) {
  int s = 0, i = 0;
  for (i = 0; i < len; ++i) {
    if (s > 1000000) {
      printf("We cannot handle very large natural numbers.\n");
      exit(0);
    }
    s = s * 10 + (c[i] - '0');
  }
  return s;
}

char * new_str(char * str, int len) {
  char * res = (char *) malloc(sizeof(char) * (len + 1));
  if (res == NULL) {
    printf("Failure in malloc.\n");
    exit(0);
  }
  strcpy(res, str);
  return res;
}

