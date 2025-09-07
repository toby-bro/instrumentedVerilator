module SimpleLoopExample (
    input logic [7:0] in_vec,
    output logic [7:0] out_vec
);
    always_comb begin
        for (int i = 0; i < 8; i++) begin
            out_vec[i] = in_vec[7 - i];
        end
    end
endmodule

module module_packed_logic (
    input logic data_in_in_pl,
    input logic [9:0] data_in_pl,
    output logic [4:0] data_out_pl
);
    logic [15:0] my_packed_logic ;
    always_comb begin
        my_packed_logic[9:0] = data_in_pl;
        my_packed_logic[15:10] = 6'h3F;
        my_packed_logic[0] = data_in_in_pl;
    end
    assign data_out_pl[4:1] = my_packed_logic[4:1];
    assign data_out_pl[0] = my_packed_logic[1];
endmodule

module snippet (
    input wire clk,
    input logic inj_data_in_in_pl_1755007823881_676,
    input logic [9:0] inj_data_in_pl_1755007823881_217,
    input logic [7:0] inj_in_vec_1755007823880_239,
    input logic [1:0] inj_test_case_mode_1755007823879_891,
    input wire reset,
    output logic [4:0] inj_data_out_pl_1755007823881_930,
    output logic [7:0] inj_out_vec_1755007823880_202,
    output logic [3:0] inj_test_case_result_1755007823879_247
);
    // BEGIN: PragmaSyntaxVariety_ts1755007823880
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
    module_packed_logic module_packed_logic_inst_1755007823881_3269 (
        .data_in_pl(inj_data_in_pl_1755007823881_217),
        .data_out_pl(inj_data_out_pl_1755007823881_930),
        .data_in_in_pl(inj_data_in_in_pl_1755007823881_676)
    );
    SimpleLoopExample SimpleLoopExample_inst_1755007823880_7550 (
        .out_vec(inj_out_vec_1755007823880_202),
        .in_vec(inj_in_vec_1755007823880_239)
    );
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
assign inj_test_case_result_1755007823879_247 = (inj_test_case_mode_1755007823879_891 == 2'b01) ? 4'h5 : 4'hA;
    // END: PragmaSyntaxVariety_ts1755007823880
endmodule

