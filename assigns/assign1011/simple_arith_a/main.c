#include <stdio.h>
#include "lang.h"
#include "lexer.h"
#include "parser.h"

extern struct expr * root;
int yyparse(void);

int main(int argc, char **argv) {
    yyin = stdin;
    yyparse();
    fclose(stdin);
    print_expr(root);
    printf("\n");
}
