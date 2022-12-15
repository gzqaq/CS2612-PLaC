#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lib.h"
#include "lang.h"
#include "L1.h"

unsigned int get_next_block_id(unsigned int * p_bbcnt) {  
  unsigned int bbcnt = * p_bbcnt;
  (* p_bbcnt) ++;
  return bbcnt;
}

void basic_block_gen(struct L1_cmd_list * p,
		     unsigned int id,
		     struct L1_basic_block_end * end_info,
		     struct L1_basic_blocks * bbs,
		     unsigned int * p_bbcnt,
		     unsigned int * p_ocnt) {
  int flag = 1;
  struct L1_basic_block * bb = (bbs -> l) + id;
  struct L1_cmd_list * * ptr_p = & (bb -> head);
  // TODO：可以在此处添加代码
  * ptr_p = p;
  while (p) {
    switch (p -> head -> t) {
    case L1_T_IF:
      if (p -> tail || end_info -> t == L1_T_CJMP) {
	// TODO：请在此处实现if语句的处理
	return;
      }
      else {
	// TODO：请在此处实现if语句的处理
	return;
      }
    case L1_T_WHILE:
      if (p -> tail || end_info -> t == L1_T_CJMP) {
	// TODO：请在此处实现while语句的处理
	return;
      }
      else {
	// TODO：请在此处实现while语句的处理
	return;
      }
    default:
      ptr_p = & (p -> tail);
      p = * ptr_p;
      flag = 0;
    }
  }
  L1_set_BBEnd(bb, end_info);
}

struct L1_basic_blocks * BB_gen(struct L1_cmd_listbox * cs) {
  // TODO：请在此处添加代码调用 basic_block_gen 生成基本块
}
