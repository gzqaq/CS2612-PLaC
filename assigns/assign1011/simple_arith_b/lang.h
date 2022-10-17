#ifndef LANG_H_INCLUDED
#define LANG_H_INCLUDED

#include <stdio.h>
#include <stdlib.h>

enum ExprType {
  T_CONST,
  T_VAR,
  T_PLUS,
  T_MULT
};

struct expr {
  enum ExprType t;
  union {
    struct {unsigned int value; } CONST;
    struct {char * name; } VAR;
    struct {struct expr * left; struct expr * right; } PLUS;
    struct {struct expr * left; struct expr * right; } MULT;
  } d;
};

struct expr * TConst(unsigned int value);
struct expr * TVar(char * name);
struct expr * TPlus(struct expr * left, struct expr * right);
struct expr * TMult(struct expr * left, struct expr * right);
void print_expr(struct expr * e);

int build_nat(char * c, int len);
char * new_str(char * str, int len);

#endif // LANG_H_INCLUDED
