interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ModClockedResetReg (
    input logic clk,
    input logic d,
    input logic rst_n,
    output logic q
);
    always @(posedge clk or negedge rst_n) begin
    if (!rst_n) begin
        q <= 1'b0;
    end else begin
        q <= d;
    end
    end
endmodule

module mod_fixup_target (
    input logic fs_in_target,
    output logic fs_out_target
);
    assign fs_out_target = fs_in_target;
endmodule

module mod_fixup_syntax_user (
    input logic fs_in,
    output wire fs_out
);
    logic fixup_out_val;
    mod_fixup_target fixup_inst (
        .fs_in_target(fs_in),
        .fs_out_target(fixup_out_val)
    );
    assign fs_out = fixup_out_val;
endmodule

module simple_comb (
    input wire [7:0] in_data,
    output wire [7:0] out_data
);
    wire [7:0] intermediate_a;
    wire [7:0] intermediate_b;
    wire [7:0] intermediate_c;
    assign intermediate_a = in_data + 8'd1;
    assign intermediate_b = intermediate_a << 1;
    assign intermediate_c = intermediate_a >> 1;
    assign out_data = intermediate_b | intermediate_c;
endmodule

module snippet (
    input wire clk,
    input logic inj_fs_in_1755007895078_363,
    input wire [7:0] inj_in_data_1755007895079_309,
    input logic [7:0] inj_in_data_1755007895080_937,
    input logic [7:0] inj_in_true_d_1755007895080_737,
    input logic [3:0] inj_in_vector_1755007895079_818,
    input wire reset,
    output logic [7:0] inj_data_out_1755007895081_504,
    output wire inj_fs_out_1755007895078_50,
    output wire [7:0] inj_out_data_1755007895079_652,
    output logic [7:0] inj_out_reg_d_1755007895080_59,
    output logic inj_out_single_1755007895079_730,
    output logic inj_out_valid_status_1755007895080_908,
    output logic inj_protected_active_1755007895082_614,
    output logic inj_q_1755007895078_449,
    output logic inj_q_1755007895079_983
);
    // BEGIN: basic_d_flipflop_ts1755007895078
    // BEGIN: combinatorial_logic_ts1755007895079
    // BEGIN: module_assign_blocking_ts1755007895080
    // BEGIN: split_conditional_nb_ts1755007895080
    // BEGIN: sequential_register_en_ts1755007895081
    // BEGIN: PragmaProtectBoundaries_ts1755007895082
logic internal_state_ts1755007895082;
`ifdef SLANG_PRAGMA
`protect begin
`endif
assign internal_state_ts1755007895082 = inj_fs_in_1755007895078_363;
`ifdef SLANG_PRAGMA
`protect end
`endif
`ifdef SLANG_PRAGMA
`protect begin_protected
`endif
`ifdef SLANG_PRAGMA
`protect end_protected
`endif
assign inj_protected_active_1755007895082_614 = internal_state_ts1755007895082;
    // END: PragmaProtectBoundaries_ts1755007895082

    always_ff @(posedge clk) begin
        if (inj_fs_in_1755007895078_363) begin
            inj_data_out_1755007895081_504 <= inj_in_true_d_1755007895080_737;
        end
    end
    // END: sequential_register_en_ts1755007895081

    always @(posedge clk) begin
        if (inj_fs_in_1755007895078_363) begin
            inj_out_reg_d_1755007895080_59 <= inj_in_true_d_1755007895080_737;
        end else begin
            inj_out_reg_d_1755007895080_59 <= inj_in_data_1755007895080_937;
        end
    end
    // END: split_conditional_nb_ts1755007895080

    my_if vif_inst();
    always_comb begin
        vif_inst.data = inj_in_data_1755007895080_937;
        vif_inst.valid = 1'b1;
        vif_inst.ready = 1'b0;
        inj_out_valid_status_1755007895080_908 = vif_inst.valid;
    end
    // END: module_assign_blocking_ts1755007895080

    simple_comb simple_comb_inst_1755007895079_4409 (
        .in_data(inj_in_data_1755007895079_309),
        .out_data(inj_out_data_1755007895079_652)
    );
    ModClockedResetReg ModClockedResetReg_inst_1755007895079_6970 (
        .clk(clk),
        .d(inj_fs_in_1755007895078_363),
        .rst_n(reset),
        .q(inj_q_1755007895079_983)
    );
    always_comb begin
        if (inj_in_vector_1755007895079_818 > 4'd5) begin
            inj_out_single_1755007895079_730 = 1'b1;
        end else begin
            inj_out_single_1755007895079_730 = 1'b0;
        end
    end
    // END: combinatorial_logic_ts1755007895079

    always_ff @(posedge clk) begin
        inj_q_1755007895078_449 <= inj_fs_in_1755007895078_363;
    end
    // END: basic_d_flipflop_ts1755007895078

    mod_fixup_syntax_user mod_fixup_syntax_user_inst_1755007895078_2939 (
        .fs_in(inj_fs_in_1755007895078_363),
        .fs_out(inj_fs_out_1755007895078_50)
    );
endmodule

