#include <stdlib.h>
#include <stdio.h>

const unsigned int int_literal[4] = {1,2,3,4};
float float_literal = 3.1415;
const char *string_literal = "This is a string literal.";

int main(int argc, char **argv)
{
    printf("int literal: %d\n", int_literal[0]);
    printf("float literal: %f\n", float_literal);
    printf("string literal: %s\n", string_literal);
    return 0;
}