module snippet #(
    parameter bit GEN = 1
) (
    input wire clk,
    input wire [7:0] inj_in_a_1755004213162_427,
    input wire [7:0] inj_in_b_1755004213162_642,
    input wire [7:0] inj_in_c_1755004213162_885,
    input wire [7:0] inj_in_const1_1755004213162_767,
    input wire [7:0] inj_in_const2_1755004213162_81,
    input logic inj_sig_in_1755004213160_419,
    input logic [1:0] inj_test_case_mode_1755004213160_3,
    input wire reset,
    output logic [31:0] inj_out1_1755004213169_9,
    output logic [7:0] inj_out_add_assoc_1755004213162_539,
    output logic [7:0] inj_out_and_assoc_1755004213162_528,
    output logic [7:0] inj_out_and_swap_const_1755004213162_419,
    output logic [7:0] inj_out_arith_1755004213162_519,
    output logic [7:0] inj_out_bitwise_1755004213162_246,
    output logic inj_out_logical_1755004213162_559,
    output logic [7:0] inj_out_mul_assoc_1755004213162_295,
    output logic [7:0] inj_out_negate_1755004213162_626,
    output logic [7:0] inj_out_or_assoc_1755004213162_34,
    output logic [7:0] inj_out_or_swap_not_1755004213162_72,
    output logic [7:0] inj_out_unary_not_1755004213162_157,
    output logic [7:0] inj_out_xor_assoc_1755004213162_585,
    output logic [7:0] inj_out_xor_swap_var_1755004213162_806,
    output logic inj_sig_out_1755004213160_646,
    output logic [3:0] inj_test_case_result_1755004213160_392
);
    // BEGIN: GenerateIfParam_ts1755004213160
    // BEGIN: PragmaSyntaxVariety_ts1755004213161
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
    // BEGIN: Mod_BasicOps_ts1755004213168
    logic [7:0] intermediate_arith_ts1755004213166;
    logic [7:0] intermediate_bitwise_ts1755004213166;
    logic [0:0] intermediate_logical_ts1755004213166;
    logic [7:0] intermediate_add_assoc_ts1755004213166;
    logic [7:0] intermediate_mul_assoc_ts1755004213166;
    logic [7:0] intermediate_and_assoc_ts1755004213166;
    logic [7:0] intermediate_or_assoc_ts1755004213166;
    logic [7:0] intermediate_xor_assoc_ts1755004213166;
        // BEGIN: simple_macro_user_ts1755004213169
        `define SIMPLE_VALUE 32'd12345
        `define ANOTHER_SIMPLE (1 + 2)
        assign inj_out1_1755004213169_9 = inj_sig_in_1755004213160_419 ? (`SIMPLE_VALUE + `ANOTHER_SIMPLE) : 32'd0;
        // END: simple_macro_user_ts1755004213169

    parameter [7:0] CONST_ZERO = 8'h00;
    always_comb begin
        intermediate_arith_ts1755004213166 = inj_in_a_1755004213162_427;
        intermediate_arith_ts1755004213166 = intermediate_arith_ts1755004213166 + inj_in_b_1755004213162_642;
        intermediate_arith_ts1755004213166 = intermediate_arith_ts1755004213166 - inj_in_c_1755004213162_885;
        intermediate_arith_ts1755004213166 = intermediate_arith_ts1755004213166 * inj_in_const1_1755004213162_767;
        if (inj_in_b_1755004213162_642 != CONST_ZERO) begin
            intermediate_arith_ts1755004213166 = intermediate_arith_ts1755004213166 / inj_in_b_1755004213162_642;
            intermediate_arith_ts1755004213166 = intermediate_arith_ts1755004213166 % inj_in_b_1755004213162_642;
        end else begin
            intermediate_arith_ts1755004213166 = 'x;
        end
        inj_out_arith_1755004213162_519 = intermediate_arith_ts1755004213166;
        intermediate_bitwise_ts1755004213166 = inj_in_a_1755004213162_427;
        intermediate_bitwise_ts1755004213166 = intermediate_bitwise_ts1755004213166 & inj_in_b_1755004213162_642;
        intermediate_bitwise_ts1755004213166 = intermediate_bitwise_ts1755004213166 | inj_in_c_1755004213162_885;
        intermediate_bitwise_ts1755004213166 = intermediate_bitwise_ts1755004213166 ^ inj_in_const1_1755004213162_767;
        inj_out_bitwise_1755004213162_246 = intermediate_bitwise_ts1755004213166;
        intermediate_logical_ts1755004213166 = (inj_in_a_1755004213162_427 != CONST_ZERO) && (inj_in_b_1755004213162_642 != CONST_ZERO);
        intermediate_logical_ts1755004213166 = intermediate_logical_ts1755004213166 || (inj_in_c_1755004213162_885 != CONST_ZERO);
        inj_out_logical_1755004213162_559 = !intermediate_logical_ts1755004213166;
        inj_out_unary_not_1755004213162_157 = ~inj_in_a_1755004213162_427;
        inj_out_negate_1755004213162_626 = -inj_in_a_1755004213162_427;
        intermediate_add_assoc_ts1755004213166 = (inj_in_a_1755004213162_427 + inj_in_b_1755004213162_642) + inj_in_c_1755004213162_885;
        inj_out_add_assoc_1755004213162_539 = intermediate_add_assoc_ts1755004213166;
        intermediate_mul_assoc_ts1755004213166 = (inj_in_a_1755004213162_427 * inj_in_b_1755004213162_642) * inj_in_c_1755004213162_885;
        inj_out_mul_assoc_1755004213162_295 = intermediate_mul_assoc_ts1755004213166;
        intermediate_and_assoc_ts1755004213166 = (inj_in_a_1755004213162_427 & inj_in_b_1755004213162_642) & inj_in_c_1755004213162_885;
        inj_out_and_assoc_1755004213162_528 = intermediate_and_assoc_ts1755004213166;
        intermediate_or_assoc_ts1755004213166 = (inj_in_a_1755004213162_427 | inj_in_b_1755004213162_642) | inj_in_c_1755004213162_885;
        inj_out_or_assoc_1755004213162_34 = intermediate_or_assoc_ts1755004213166;
        intermediate_xor_assoc_ts1755004213166 = (inj_in_a_1755004213162_427 ^ inj_in_b_1755004213162_642) ^ inj_in_c_1755004213162_885;
        inj_out_xor_assoc_1755004213162_585 = intermediate_xor_assoc_ts1755004213166;
        inj_out_and_swap_const_1755004213162_419 = inj_in_const1_1755004213162_767 & inj_in_a_1755004213162_427;
        inj_out_or_swap_not_1755004213162_72 = (~inj_in_a_1755004213162_427) | inj_in_b_1755004213162_642;
        inj_out_xor_swap_var_1755004213162_806 = inj_in_b_1755004213162_642 ^ inj_in_c_1755004213162_885;
    end
    // END: Mod_BasicOps_ts1755004213168

`endif
`ifdef SLANG_PRAGMA
`unknown_slang_pragma (arg1, arg2="value")
`endif
`ifdef SLANG_PRAGMA
`protect (1 + 2)
`endif
`ifdef SLANG_PRAGMA
`protect {3, 4}
`endif
`ifdef SLANG_PRAGMA
`protect unknown_action (arg=1)
`endif
`ifdef SLANG_PRAGMA
`protect encoding
`endif
`ifdef SLANG_PRAGMA
`protect encoding (enctype="raw", "string_arg_only")
`endif
`ifdef SLANG_PRAGMA
`protect encoding (enctype="raw", unknown_option=99)
`endif
`ifdef SLANG_PRAGMA
`protect encoding (bytes=-10)
`endif
`ifdef SLANG_PRAGMA
`protect license (match="not_an_integer")
`endif
`ifdef SLANG_PRAGMA
`protect license (match=42.5)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a", acc="b", extra=1)
`endif
`ifdef SLANG_PRAGMA
`protect begin (arg_present)
`endif
`ifdef SLANG_PRAGMA
`protect license ("license_string_only")
`endif
`ifdef SLANG_PRAGMA
`protect license (library=my_library_ident)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a", acc="b", c=3)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (obj="a", "access_string")
`endif
`ifdef SLANG_PRAGMA
`protect viewport ("object_string", acc="b")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="a", access=123)
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object=123, access="b")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (not_object="a", access="b")
`endif
`ifdef SLANG_PRAGMA
`protect viewport (object="a", not_access="b")
`endif
`ifdef SLANG_PRAGMA
`diagnostic (1 + 2)
`endif
`ifdef SLANG_PRAGMA
`diagnostic unknown_action_diag
`endif
`ifdef SLANG_PRAGMA
`diagnostic level=warn
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=(1+2))
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=(value=1))
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore (value=some_identifier)
`endif
`ifdef SLANG_PRAGMA
`diagnostic warn (value=12345)
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore simple_identifier_arg
`endif
`ifdef SLANG_PRAGMA
`protect "simple_string_argument"
`endif
`ifdef SLANG_PRAGMA
`diagnostic ignore "just_a_string_diag_code"
`endif
assign inj_test_case_result_1755004213160_392 = (inj_test_case_mode_1755004213160_3 == 2'b01) ? 4'h5 : 4'hA;
    // END: PragmaSyntaxVariety_ts1755004213161

    generate
        if (GEN) begin : g_true
            assign inj_sig_out_1755004213160_646 = inj_sig_in_1755004213160_419;
        end
        else begin : g_false
            assign inj_sig_out_1755004213160_646 = ~inj_sig_in_1755004213160_419;
        end
    endgenerate
    // END: GenerateIfParam_ts1755004213160
endmodule

