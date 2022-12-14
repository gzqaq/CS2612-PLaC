#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "L1.h"
#include "lang.h"
#include "lib.h"

unsigned int get_next_var_name(unsigned int * p_vcnt) {
  unsigned int vcnt = *p_vcnt;
  (*p_vcnt)++;
  return vcnt;
}

// 该函数表示要返回val这个表达式，
// 如果val内部包含计算，那么就需要在cs这个cmd_list中增加必要的赋值语句
struct L1_const_or_var * optional_add_asgn_cv(struct L1_expr * val,
                                              unsigned int * p_vcnt,
                                              struct L1_cmd_listbox * cs) {
  if (val->t == L1_T_CONST_OR_VAR) {
    return L1_ConstOrVar_from_Expr(val);
  } else {
    unsigned int vcnt = get_next_var_name(p_vcnt);
    L1_CmdListBox_Add1(cs, L1_TAsgnVar(vcnt, val));
    return L1_TVar(vcnt);
  }
}

// 该函数的功能与上面类似，但是要求表达式的结果要用变量表示
unsigned int optional_add_asgn_var(struct L1_expr * val, unsigned int * p_vcnt,
                                   struct L1_cmd_listbox * cs) {
  struct L1_const_or_var * cv = optional_add_asgn_cv(val, p_vcnt, cs);
  if (cv->t == L1_T_CONST) {
    unsigned int vcnt = get_next_var_name(p_vcnt);
    L1_CmdListBox_Add1(cs, L1_TAsgnVar(vcnt, L1_TConstOrVar(cv)));
    return vcnt;
  } else {
    unsigned res = cv->d.VAR.name;
    free(cv);
    return res;
  }
}

struct L1_expr * TAC_gen_expr(struct expr * e,
                              struct SU_hash_table * var_idents,
                              unsigned int * p_vcnt,
                              struct L1_cmd_listbox * cs) {
  switch (e->t) {
    case T_CONST:
      return L1_TConstOrVar(L1_TConst(e->d.CONST.value));
    case T_VAR: {
      unsigned int id = SU_hash_get(var_idents, e->d.VAR.name);
      if (id == NONE) {
        printf("Undefined var %s is used.\n", e->d.VAR.name);
        exit(0);
      }
      return L1_TConstOrVar(L1_TVar(id));
    }
    case T_BINOP: {
      if (e->d.BINOP.op == T_AND || e->d.BINOP.op == T_OR) {
        struct L1_expr * res_right1 =
            TAC_gen_expr(e->d.BINOP.left, var_idents, p_vcnt, cs);
        struct L1_cmd_listbox * cs0 = L1_CmdListBox_Empty();
        struct L1_expr * res_right2 =
            TAC_gen_expr(e->d.BINOP.right, var_idents, p_vcnt, cs0);
        unsigned int vcnt = get_next_var_name(p_vcnt);
        L1_CmdListBox_Add1(cs0, L1_TAsgnVar(vcnt, res_right2));
        if (e->d.BINOP.op == T_AND) {
          L1_CmdListBox_Add1(
              cs, L1_TIf(res_right1, cs0,
                         L1_CmdListBox_Single(
                             L1_TAsgnVar(vcnt, L1_TConstOrVar(L1_TConst(0))))));
        } else {
          // TODO：请在此处实现二元运算符为T_OR的情况
          L1_CmdListBox_Add1(
              cs, L1_TIf(res_right1,
                         L1_CmdListBox_Single(
                             L1_TAsgnVar(vcnt, L1_TConstOrVar(L1_TConst(1)))),
                         cs0));
        }
        return L1_TConstOrVar(L1_TVar(vcnt));
      } else {
        struct L1_expr * res_left =
            TAC_gen_expr(e->d.BINOP.left, var_idents, p_vcnt, cs);
        struct L1_const_or_var * cv_left =
            optional_add_asgn_cv(res_left, p_vcnt, cs);
        struct L1_expr * res_right =
            TAC_gen_expr(e->d.BINOP.right, var_idents, p_vcnt, cs);
        struct L1_const_or_var * cv_right =
            optional_add_asgn_cv(res_right, p_vcnt, cs);
        return L1_TBinop(e->d.BINOP.op, cv_left, cv_right);
      }
    }
    case T_UNOP: {
      // TODO：请在此处实现一元运算符的情况
      struct L1_expr * arg =
          TAC_gen_expr(e->d.UNOP.arg, var_idents, p_vcnt, cs);
      struct L1_const_or_var * cv = optional_add_asgn_cv(arg, p_vcnt, cs);
      return L1_TUnop(e->d.UNOP.op, cv);
    }
    case T_DEREF: {
      struct L1_expr * arg =
          TAC_gen_expr(e->d.DEREF.arg, var_idents, p_vcnt, cs);
      struct L1_const_or_var * cv = optional_add_asgn_cv(arg, p_vcnt, cs);
      return L1_TDeref(cv);
    }
    case T_MALLOC: {
      struct L1_expr * arg =
          TAC_gen_expr(e->d.MALLOC.arg, var_idents, p_vcnt, cs);
      struct L1_const_or_var * cv = optional_add_asgn_cv(arg, p_vcnt, cs);
      return L1_TMalloc(cv);
    }
    case T_RI: {
      return L1_TReadInt();
    }
    case T_RC: {
      return L1_TReadChar();
    }
  }
}

struct L1_cmd_listbox * TAC_gen_cmd(struct cmd * c,
                                    struct SU_hash_table * var_idents,
                                    unsigned int * p_vcnt) {
  switch (c->t) {
    case T_DECL: {
      printf("Ilegal position of variable declaration.\n");
      exit(0);
    }
    case T_ASGN: {
      switch (c->d.ASGN.left->t) {
        case T_VAR: {
          char * name = c->d.ASGN.left->d.VAR.name;
          unsigned int id = SU_hash_get(var_idents, name);
          struct L1_cmd_listbox * cs = L1_CmdListBox_Empty();
          struct L1_expr * res_right =
              TAC_gen_expr(c->d.ASGN.right, var_idents, p_vcnt, cs);
          L1_CmdListBox_Add1(cs, L1_TAsgnVar(id, res_right));
          return cs;
        }
        case T_DEREF: {
          // TODO：请在此处实现向地址赋值的情况
          struct expr * arg = c->d.ASGN.left->d.DEREF.arg;
          struct L1_cmd_listbox * cs = L1_CmdListBox_Empty();
          struct L1_expr * res_left = TAC_gen_expr(arg, var_idents, p_vcnt, cs);
          unsigned int name = optional_add_asgn_var(res_left, p_vcnt, cs);
          struct L1_expr * res_right =
              TAC_gen_expr(c->d.ASGN.right, var_idents, p_vcnt, cs);
          struct L1_const_or_var * cv =
              optional_add_asgn_cv(res_right, p_vcnt, cs);
          L1_CmdListBox_Add1(cs, L1_TAsgnMem(name, cv));

          return cs;
        }
        default: {
          printf("Ilegal assignment command.\n");
          exit(0);
        }
      }
    }
    case T_SEQ: {
      if (c->d.SEQ.left->t == T_DECL) {
        char * name = c->d.SEQ.left->d.DECL.name;
        unsigned int old_id = SU_hash_get(var_idents, name);
        unsigned int new_id = get_next_var_name(p_vcnt);
        SU_hash_set(var_idents, name, new_id);
        struct L1_cmd_listbox * cs =
            TAC_gen_cmd(c->d.SEQ.right, var_idents, p_vcnt);
        if (old_id == NONE) {
          SU_hash_delete(var_idents, name);
        } else {
          SU_hash_set(var_idents, name, old_id);
        }
        return cs;
      } else {
        struct L1_cmd_listbox * cs_left =
            TAC_gen_cmd(c->d.SEQ.left, var_idents, p_vcnt);
        struct L1_cmd_listbox * cs_right =
            TAC_gen_cmd(c->d.SEQ.right, var_idents, p_vcnt);
        L1_CmdListBox_Append(cs_left, cs_right);
        return cs_left;
      }
    }
    case T_IF: {
      struct L1_cmd_listbox * cs = L1_CmdListBox_Empty();
      struct L1_expr * res_cond =
          TAC_gen_expr(c->d.IF.cond, var_idents, p_vcnt, cs);
      struct L1_cmd_listbox * res_left =
          TAC_gen_cmd(c->d.IF.left, var_idents, p_vcnt);
      struct L1_cmd_listbox * res_right =
          TAC_gen_cmd(c->d.IF.right, var_idents, p_vcnt);
      L1_CmdListBox_Add1(cs, L1_TIf(res_cond, res_left, res_right));
      return cs;
    }
    case T_WHILE: {
      // TODO：请在此处实现while循环语句的转换方案
      struct L1_cmd_listbox * cs = L1_CmdListBox_Empty();
      struct L1_cmd_listbox * pre = L1_CmdListBox_Empty();
      struct L1_expr * res_cond =
          TAC_gen_expr(c->d.WHILE.cond, var_idents, p_vcnt, pre);
      struct L1_cmd_listbox * body =
          TAC_gen_cmd(c->d.WHILE.body, var_idents, p_vcnt);
      L1_CmdListBox_Add1(cs, L1_TWhile(pre, res_cond, body));

      return cs;
    }
    case T_WI: {
      struct L1_cmd_listbox * cs = L1_CmdListBox_Empty();
      struct L1_expr * arg = TAC_gen_expr(c->d.WI.arg, var_idents, p_vcnt, cs);
      struct L1_const_or_var * vcnt = optional_add_asgn_cv(arg, p_vcnt, cs);
      L1_CmdListBox_Add1(cs, L1_TWriteInt(vcnt));
      return cs;
    }
    case T_WC: {
      struct L1_cmd_listbox * cs = L1_CmdListBox_Empty();
      struct L1_expr * arg = TAC_gen_expr(c->d.WC.arg, var_idents, p_vcnt, cs);
      struct L1_const_or_var * vcnt = optional_add_asgn_cv(arg, p_vcnt, cs);
      L1_CmdListBox_Add1(cs, L1_TWriteChar(vcnt));
      return cs;
    }
  }
}

struct L1_cmd_listbox * TAC_gen(struct cmd * c) {
  struct SU_hash_table * var_idents = init_SU_hash();
  unsigned int vcnt = 0;
  return TAC_gen_cmd(c, var_idents, &vcnt);
}
