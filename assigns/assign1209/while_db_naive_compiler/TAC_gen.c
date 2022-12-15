#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lib.h"
#include "lang.h"
#include "L1.h"

unsigned int get_next_var_name(unsigned int * p_vcnt) {
  unsigned int vcnt = * p_vcnt;
  (* p_vcnt) ++;
  return vcnt;
}

struct L1_const_or_var * optional_add_asgn_cv(struct L1_expr * val,
                                              unsigned int * p_vcnt,
                                              struct L1_cmd_listbox * cs) {
  if (val -> t == L1_T_CONST_OR_VAR) {
    return L1_ConstOrVar_from_Expr(val);
  }
  else {
    unsigned int vcnt = get_next_var_name(p_vcnt);
    L1_CmdListBox_Add1(cs, L1_TAsgnVar(vcnt, val));
    return L1_TVar(vcnt);
  }
}

unsigned int optional_add_asgn_var(struct L1_expr * val,
                                   unsigned int * p_vcnt,
                                   struct L1_cmd_listbox * cs) {
  struct L1_const_or_var * cv =
    optional_add_asgn_cv(val, p_vcnt, cs);
  if (cv -> t == L1_T_CONST) {
    unsigned int vcnt = get_next_var_name(p_vcnt);
    L1_CmdListBox_Add1(cs, L1_TAsgnVar(vcnt, L1_TConstOrVar(cv)));
    return vcnt;
  }
  else {
    unsigned res = cv -> d.VAR.name;
    free(cv);
    return res;
  }
}

struct L1_expr * TAC_gen_expr(struct expr * e,
                                    struct SU_hash_table * var_idents,
                                    unsigned int * p_vcnt,
                                    struct L1_cmd_listbox * cs) {
  // 测试时可以使用上一个作业中的代码
}

struct L1_cmd_listbox * TAC_gen_cmd(struct cmd * c,
                                    struct SU_hash_table * var_idents,
                                    unsigned int * p_vcnt) {
  // 测试时可以使用上一个作业中的代码
}

struct L1_cmd_listbox * TAC_gen(struct cmd * c) {
  struct SU_hash_table * var_idents = init_SU_hash();
  unsigned int vcnt = 0;
  return TAC_gen_cmd(c, var_idents, & vcnt);
}

