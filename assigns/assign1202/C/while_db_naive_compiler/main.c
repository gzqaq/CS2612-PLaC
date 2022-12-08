#include <stdio.h>
#include "lang.h"
#include "L1.h"
#include "lexer.h"
#include "parser.h"

extern struct cmd * root;
int yyparse();
struct L1_cmd_listbox * TAC_gen(struct cmd * c);

int main(int argc, char **argv) {
    yyin = stdin;
    yyparse();
    fclose(stdin);
    print_cmd(root);
    printf("\n");
    struct L1_cmd_listbox * l = TAC_gen(root);
    print_L1_cmd_listbox(l);
}
