module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module mod_err_event_constant (
    input wire clk,
    output logic dummy
);
    always @(posedge 1'b1) begin
        dummy = ~dummy;
    end
endmodule

module snippet (
    input wire clk,
    input bit inj_in_1755007848633_476,
    input logic [1:0] inj_test_case_mode_1755007848632_358,
    input wire reset,
    output logic inj_dummy_1755007848632_984,
    output bit inj_out_1755007848633_30,
    output logic [3:0] inj_test_case_result_1755007848632_805
);
    // BEGIN: PragmaSyntaxVariety_ts1755007848633
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
    BindSimpleModule BindSimpleModule_inst_1755007848633_2677 (
        .out(inj_out_1755007848633_30),
        .in(inj_in_1755007848633_476)
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
assign inj_test_case_result_1755007848632_805 = (inj_test_case_mode_1755007848632_358 == 2'b01) ? 4'h5 : 4'hA;
    // END: PragmaSyntaxVariety_ts1755007848633

    mod_err_event_constant mod_err_event_constant_inst_1755007848632_3720 (
        .clk(clk),
        .dummy(inj_dummy_1755007848632_984)
    );
endmodule

