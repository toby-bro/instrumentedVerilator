module mod_case_unique_priority (
    input bit [2:0] in_state_case,
    output bit out_priority_case,
    output bit out_unique_case
);
always_comb begin
    out_unique_case = 1'b0;
    unique case (in_state_case)
        3'd0: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        3'd2: out_unique_case = 1'b0;
        3'd1: out_unique_case = 1'b1;
        default: out_unique_case = 1'b1;
    endcase
end
always_comb begin
    out_priority_case = 1'b0;
    priority case (in_state_case)
        3'd0: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        3'd2: out_priority_case = 1'b0;
        3'd1: out_priority_case = 1'b1;
        default: out_priority_case = 1'b1;
    endcase
end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module split_complex_nb (
    input logic clk_s,
    input logic [7:0] i1_s,
    input logic [7:0] i2_s,
    input logic [7:0] i3_s,
    output logic [7:0] o1_s,
    output logic [7:0] o2_s,
    output logic [7:0] o3_s
);
    logic [7:0] t1_s, t2_s;
    always @(posedge clk_s) begin
        t1_s <= i1_s + i2_s;
        o1_s <= t1_s - i3_s;
        t2_s <= i2_s * i3_s;
        o2_s <= t1_s + t2_s;
        o3_s <= t2_s / 2;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007753554_508,
    input logic inj_b_1755007753554_532,
    input logic [3:0] inj_data_in_1755007753556_527,
    input logic [7:0] inj_i1_s_1755007753554_869,
    input logic [7:0] inj_i2_s_1755007753554_509,
    input logic [7:0] inj_i3_s_1755007753554_130,
    input bit [2:0] inj_in_state_case_1755007753557_816,
    input int inj_in_val_1755007753560_715,
    input logic [1:0] inj_test_case_mode_1755007753555_553,
    input wire reset,
    output logic inj_bind_out_1755007753555_324,
    output logic [3:0] inj_data_out_1755007753556_870,
    output logic inj_dummy_out_1755007753559_456,
    output logic [7:0] inj_o1_s_1755007753554_975,
    output logic [7:0] inj_o2_s_1755007753554_809,
    output logic [7:0] inj_o3_s_1755007753554_136,
    output bit inj_out_priority_case_1755007753557_75,
    output bit inj_out_unique_case_1755007753557_915,
    output int inj_out_val_1755007753560_332,
    output logic [7:0] inj_out_vec_1755007753558_422,
    output logic inj_sum_1755007753554_652,
    output logic [3:0] inj_test_case_result_1755007753555_900
);
    // BEGIN: bind_module_ts1755007753555
    // BEGIN: PragmaSyntaxVariety_ts1755007753555
`ifdef SLANG_PRAGMA
`unknown_pragma_real 1.23;
    // BEGIN: sequential_logic_ts1755007753556
    ;
    logic [3:0] internal_reg_ts1755007753556;
        // BEGIN: mixed_conn_child_ts1755007753559
        logic dummy_internal_ts1755007753559;
            // BEGIN: super_outside_class_diag_mod_ts1755007753560
            assign inj_out_val_1755007753560_332 = inj_in_val_1755007753560_715;
            // END: super_outside_class_diag_mod_ts1755007753560

        always_comb dummy_internal_ts1755007753559 = |inj_i3_s_1755007753554_130 | inj_b_1755007753554_532;
        assign inj_dummy_out_1755007753559_456 = dummy_internal_ts1755007753559;
        // END: mixed_conn_child_ts1755007753559

        // BEGIN: SimpleLoopExample_ts1755007753558
        always_comb begin
            for (int i = 0; i < 8; i++) begin
                inj_out_vec_1755007753558_422[i] = inj_i2_s_1755007753554_509[7 - i];
            end
        end
        // END: SimpleLoopExample_ts1755007753558

        mod_case_unique_priority mod_case_unique_priority_inst_1755007753557_7002 (
            .out_priority_case(inj_out_priority_case_1755007753557_75),
            .out_unique_case(inj_out_unique_case_1755007753557_915),
            .in_state_case(inj_in_state_case_1755007753557_816)
        );
    always_ff @(posedge clk or negedge reset) begin
        if (!reset) begin
            internal_reg_ts1755007753556 <= 4'h0;
        end else begin
            internal_reg_ts1755007753556 <= inj_data_in_1755007753556_527;
        end
    end
    assign inj_data_out_1755007753556_870 = internal_reg_ts1755007753556;
    // END: sequential_logic_ts1755007753556

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
assign inj_test_case_result_1755007753555_900 = (inj_test_case_mode_1755007753555_553 == 2'b01) ? 4'h5 : 4'hA;
    // END: PragmaSyntaxVariety_ts1755007753555

    assign inj_bind_out_1755007753555_324 = inj_b_1755007753554_532;
    // END: bind_module_ts1755007753555

    simple_adder simple_adder_inst_1755007753554_5812 (
        .sum(inj_sum_1755007753554_652),
        .a(inj_a_1755007753554_508),
        .b(inj_b_1755007753554_532)
    );
    split_complex_nb split_complex_nb_inst_1755007753554_5405 (
        .o1_s(inj_o1_s_1755007753554_975),
        .o2_s(inj_o2_s_1755007753554_809),
        .o3_s(inj_o3_s_1755007753554_136),
        .clk_s(clk),
        .i1_s(inj_i1_s_1755007753554_869),
        .i2_s(inj_i2_s_1755007753554_509),
        .i3_s(inj_i3_s_1755007753554_130)
    );
endmodule

