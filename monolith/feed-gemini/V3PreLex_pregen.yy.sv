module DirectiveTest (input logic [7:0] in_data, output logic [7:0] out_data);
  parameter int TEST_VAL = 10;
  `define MY_DEFINE_A
  `undef MY_DEFINE_B
  always_comb begin
    logic [7:0] temp_data;
    temp_data = in_data + TEST_VAL;
    `ifdef MY_DEFINE_A
      temp_data = temp_data + 1;
    `else
      temp_data = temp_data - 1; /*
                                 * Multi-line
                                 * comment block
                                 */
    `endif
    `line 100 "generated_file_1.sv" 0
    temp_data = temp_data * 2;
    `ifndef ANOTHER_DEFINE
      temp_data = temp_data / 2;
    `endif
    `undefineall
    `ifdef MY_DEFINE_A_AFTER_UNDEFINEALL
      temp_data = temp_data + 100;
    `else
      temp_data = temp_data - 100;
    `endif
    out_data = temp_data;
  end
endmodule
module StringTest (input logic [15:0] in_val, output logic [15:0] out_val);
  localparam string STR1 = "Hello, World!\nThis is a new line.";
  localparam string STR2 = "Escaped double quote here: \"";
  localparam string STR3 = "Backslash continuation: \\\nNext part.";
  localparam string STR4 = """This is a
 triple-quoted
 string.""";
  `define MY_STRING_MACRO(text) \`text
  localparam string STRINGIFIED_TEXT = `MY_STRING_MACRO(This_is_my_text_to_stringify);
  always_comb begin
    logic [15:0] temp_val;
    temp_val = in_val;
    if (STR1.len() > 0) temp_val = temp_val + 1;
    if (STR2.len() > 0) temp_val = temp_val + 2;
    if (STR3.len() > 0) temp_val = temp_val + 3;
    if (STR4.len() > 0) temp_val = temp_val + 4;
    if (STRINGIFIED_TEXT.len() > 0) temp_val = temp_val + 5;
    out_val = temp_val;
  end
  `define BACKSLASH_SPACE_DEFINE \
  `define BACKSLASH_SPACE_WARN \       \n
  localparam int BS_TEST = 1;
endmodule
module ComplexDefineTest (input logic [3:0] in_cdef, output logic [3:0] out_cdef);
  `define ADD_ONE(val) (val + 1)
  `define SUBTRACT(a, b) (a - b)
  `define CONCAT(x, y) x``y
  `define EMPTY_ARGS_NO_PARENS 1
  `define VALUE_WITH_COMMENT 10 /* This is an embedded comment in value */
  `define VALUE_MULTILINE 20 + 30
  `define VALUE_WITH_STRING "hello"
  `define VALUE_WITH_TRIPLE_QUOTE """world"""
  `define NO_BACKSLASH_SPACE_WARNING \
  `define BACKSLASH_SPACE_WARN \    \n
  `define PART_A first
  `define PART_B second
  `define UNDERSCORE_LITERAL _
  `define JOINED_TEXT_MACRO_STRINGIFIED(x, y, z) \`x``y``z
  `define JOINED_TEXT_MACRO_IDENTIFIER(x, y, z) x``y``z
  localparam string s_val_str = `VALUE_WITH_STRING;
  localparam string s_val_qqq = `VALUE_WITH_TRIPLE_QUOTE;
  `define INNER_MACRO(z) (z * 2)
  `define OUTER_MACRO(v, w) (v + `INNER_MACRO(w))
  `define MULT_ARGS(a,b,c) (a*b*c)
  `define LONG_ARG_LIST_DEF(p,q,r,s) (p+q+r+s)
  localparam string COMPOSITE_JOIN_ID = `JOINED_TEXT_MACRO_STRINGIFIED(PART_A, UNDERSCORE_LITERAL, PART_B);
  always_comb begin
    logic [3:0] temp_cdef;
    temp_cdef = in_cdef;
    temp_cdef = `ADD_ONE(temp_cdef);
    temp_cdef = `SUBTRACT(temp_cdef, 2);
    `ifdef EMPTY_ARGS_NO_PARENS
      temp_cdef = temp_cdef + 1;
    `endif
    temp_cdef = temp_cdef + `VALUE_WITH_COMMENT;
    temp_cdef = temp_cdef + `VALUE_MULTILINE;
    if (s_val_str.len() > 0) temp_cdef = temp_cdef + 1;
    if (s_val_qqq.len() > 0) temp_cdef = temp_cdef + 1;
    temp_cdef = `OUTER_MACRO(temp_cdef, 3);
    temp_cdef = `MULT_ARGS(temp_cdef, 2, 1);
    temp_cdef = `LONG_ARG_LIST_DEF(temp_cdef, 1, 2, 3);
    if (COMPOSITE_JOIN_ID.len() > 0) temp_cdef = temp_cdef + 1;
    out_cdef = temp_cdef;
  end
endmodule
module PragmaTest (input logic [1:0] in_p, output logic [1:0] out_p);
  always_comb begin
    logic [1:0] temp_p;
    temp_p = in_p;
    `pragma verilator_protected_encoding = (enctype = "BASE64", line_length = 76, bytes = 0)
    `pragma verilator_protected_data_block
    "AAECAwQFBgcICQoLDA0ODxAREhMUFRYXGBkaGxwdHh8gISIjJCUmJygpKissLS4vMDEyMzQ1Njc4OTo7PD0+P0"
    `pragma verilator_protected_end
    `pragma verilator_protected_key_block
    "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
    `pragma verilator_protected_decrypt
    `pragma verilator_protected_end
    `pragma some_other_pragma_type (arg1, arg2)
    `pragma verilator_empty_pragma
    `pragma verilator_protected_unknown_protect_syntax_test
    `pragma verilator_protected_verilator_unknown_subdirective_test
    out_p = temp_p;
  end
endmodule
module JoinExprTest (input logic [2:0] in_je, output logic [2:0] out_je);
  `define MY_SYM_A sym
  `define MY_SYM_B bol
  `define JOINED_SYMA_B_STR \`MY_SYM_A``MY_SYM_B
  `define JOINED_WORD_LITERAL_P A_LITERAL
  `define JOINED_WORD_LITERAL_Q B_LITERAL
  `define JOINED_WORD_LITERAL_STR \`JOINED_WORD_LITERAL_P``JOINED_WORD_LITERAL_Q
  always_comb begin
    localparam string SYMBOL_TEST_A = `JOINED_SYMA_B_STR;
    localparam string SYMBOL_TEST_B_FIXED = "sym_back_join_placeholder";
    localparam string TEXT_JOIN = `JOINED_WORD_LITERAL_STR;
    logic [2:0] temp_je;
    temp_je = in_je;
    if (SYMBOL_TEST_A.len() > 0) temp_je = temp_je + 1;
    if (SYMBOL_TEST_B_FIXED.len() > 0) temp_je = temp_je + 1;
    if (TEXT_JOIN.len() > 0) temp_je = temp_je + 1;
    `define EXPR_VAL 1
    `if (`EXPR_VAL && 1)
      temp_je = temp_je * 2;
    `elsif (`EXPR_VAL || 0)
      temp_je = temp_je / 2;
    `else
      temp_je = temp_je + 0;
    `endif
    `define IS_DEFINED_FOO_VALUE defined(FOO)
    `if (`IS_DEFINED_FOO_VALUE) temp_je = temp_je + 1;
    `endif
    out_je = temp_je;
  end
endmodule
module ExtensiveTest (input logic [6:0] in_ext, output logic [6:0] out_ext);
  logic [6:0] internal_array [0:3];
  `define SYM_A_PART_VAL A_
  `define SYM_B_PART_VAL B_
  `define END_LITERAL_COMPLETE complete
  `define CONCAT_SYM_PARTS_STRINGIFIED \`SYM_A_PART_VAL``SYM_B_PART_VAL``END_LITERAL_COMPLETE
  always_comb begin
    localparam string COMPOSITE_ID = `CONCAT_SYM_PARTS_STRINGIFIED;
    logic [6:0] temp_ext;
    `ifdef FEATURE_A
      localparam string CONFIG_STR = "Configured for feature A";
    `elsif FEATURE_B
      localparam string CONFIG_STR = "Configured for\nfeature B";
    `else
      localparam string CONFIG_STR = "Default config";
    `endif
    temp_ext = in_ext;
    `ifdef FEATURE_A
      `define FEATURE_A_ENABLED
      temp_ext = temp_ext + 1;
      `define COMPLEX_CONFIG(param1, param2) \
        begin \
          temp_ext = temp_ext + param1; \
          temp_ext = temp_ext - param2; \
        end
      `COMPLEX_CONFIG(5, 2);
      `pragma verilator_lint_on
      `line 200 "extended_test_file.sv" 1
    `elsif FEATURE_B
      temp_ext = temp_ext + 2;
    `else
      temp_ext = temp_ext + 3;
    `endif
    `define GET_VALUE(idx) internal_array[idx]
    internal_array[0] = 7'd10;
    internal_array[1] = 7'd20;
    internal_array[2] = 7'd30;
    internal_array[3] = 7'd40;
    temp_ext = temp_ext + `GET_VALUE(1);
    if (COMPOSITE_ID.len() > 0) temp_ext = temp_ext + 1;
    `pragma some_other_valid_pragma
    `line 1 "dummy_file.sv" 0
    out_ext = temp_ext;
  end
endmodule
