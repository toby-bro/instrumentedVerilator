module PragmaSyntaxVariety (
    input logic [1:0] test_case_mode,
    output logic [3:0] test_case_result
);
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
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
assign test_case_result = (test_case_mode == 2'b01) ? 4'h5 : 4'hA;
endmodule

module snippet (
    input wire clk,
    input logic inj_i_1755007790842_991,
    input logic [7:0] inj_in1_1755007790844_78,
    input logic [7:0] inj_in2_1755007790844_414,
    input logic [1:0] inj_test_case_mode_1755007790843_785,
    input logic [3:0] inj_val_a_1755007790842_146,
    input logic [3:0] inj_val_b_1755007790842_239,
    input wire reset,
    output logic [3:0] inj_data_out1_n_1755007790843_877,
    output logic [3:0] inj_data_out2_n_1755007790843_867,
    output logic inj_o_1755007790842_841,
    output logic [7:0] inj_out1_1755007790844_971,
    output logic [3:0] inj_result_1755007790842_124,
    output logic [3:0] inj_test_case_result_1755007790843_624
);
    // BEGIN: child_module_v2_config_dummy_ts1755007790842
    // BEGIN: CombinationalLogic_ts1755007790842
    // BEGIN: split_multiple_blocking_ts1755007790843
    logic [3:0] temp_n_ts1755007790843;
        // BEGIN: basic_comb_ts1755007790844
        ;
        logic [7:0] temp_wire_ts1755007790844;
        assign temp_wire_ts1755007790844 = inj_in1_1755007790844_78 + inj_in2_1755007790844_414;
        always_comb begin
            inj_out1_1755007790844_971 = temp_wire_ts1755007790844;
        end
        // END: basic_comb_ts1755007790844

        PragmaSyntaxVariety PragmaSyntaxVariety_inst_1755007790843_6075 (
            .test_case_result(inj_test_case_result_1755007790843_624),
            .test_case_mode(inj_test_case_mode_1755007790843_785)
        );
    always @(*) begin
        temp_n_ts1755007790843 = inj_val_b_1755007790842_239 + 1;
        inj_data_out1_n_1755007790843_877 = temp_n_ts1755007790843 * 2;
        inj_data_out2_n_1755007790843_867 = temp_n_ts1755007790843 + 3;
    end
    // END: split_multiple_blocking_ts1755007790843

    always_comb begin
        if (inj_i_1755007790842_991) begin
            inj_result_1755007790842_124 = inj_val_a_1755007790842_146 + inj_val_b_1755007790842_239;
        end else begin
            inj_result_1755007790842_124 = 4'h0;
        end
    end
    // END: CombinationalLogic_ts1755007790842

    assign inj_o_1755007790842_841 = inj_i_1755007790842_991 | inj_i_1755007790842_991; 
    // END: child_module_v2_config_dummy_ts1755007790842
endmodule

