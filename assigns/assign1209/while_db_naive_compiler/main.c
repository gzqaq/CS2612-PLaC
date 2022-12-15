#include <stdio.h>
#include "lang.h"
#include "L1.h"
#include "lexer.h"
#include "parser.h"

extern struct cmd * root;
int yyparse();
struct L1_cmd_listbox * TAC_gen(struct cmd * c);
struct L1_basic_blocks * BB_gen(struct L1_cmd_listbox * l);

int main(int argc, char **argv) {
    yyin = stdin;
    yyparse();
    fclose(stdin);
    print_cmd(root);
    printf("\n");
    struct L1_cmd_listbox * l = TAC_gen(root);
    struct L1_basic_blocks * bbs = BB_gen(l);
    print_L1_basic_blocks(bbs);
}
