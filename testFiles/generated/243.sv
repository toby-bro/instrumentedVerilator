module CaseEq (
    output wire match_x_neq,
    output wire match_z_eq,
    inout wire [3:0] data_io
);
    assign match_z_eq = (data_io === 4'b101z);
    assign match_x_neq = (data_io !== 4'b1x0x);
endmodule

module SimpleAssign (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data;
endmodule

module coalesced_assign (
    input logic [3:0] in_h,
    input logic [3:0] in_l,
    output logic [7:0] out
);
    wire [7:0] temp_wire;
    assign temp_wire[7:4] = in_h;
    assign temp_wire[3:0] = in_l;
    assign out = temp_wire;
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
    input int inj_b_1755007835432_993,
    input logic [7:0] inj_i1_s_1755007835429_552,
    input logic [7:0] inj_i2_s_1755007835429_809,
    input logic [7:0] inj_i3_s_1755007835429_184,
    input logic inj_i_data_sync_1755007835428_600,
    input logic inj_i_reg_data_1755007835428_12,
    input logic [3:0] inj_in_h_1755007835430_705,
    input logic [3:0] inj_in_l_1755007835430_295,
    input wire reset,
    output wire inj_match_x_neq_1755007835429_686,
    output wire inj_match_z_eq_1755007835429_38,
    output logic [7:0] inj_o1_s_1755007835429_313,
    output logic [7:0] inj_o2_s_1755007835429_649,
    output logic [7:0] inj_o3_s_1755007835429_854,
    output logic inj_o_reg_out_1755007835428_543,
    output wire inj_o_wire_out_1755007835428_609,
    output logic [7:0] inj_out_1755007835430_55,
    output wire inj_out_1755007835431_89,
    output logic inj_out_a_1755007835432_818,
    output int inj_out_b_1755007835432_501,
    output logic [7:0] inj_out_data_1755007835433_952,
    output logic inj_sub_out_1755007835429_438,
    output logic inj_y_1755007835431_349,
    inout wire [3:0] inj_data_io_1755007835429_155
);
    // BEGIN: nets_alias_clocking_ts1755007835429
    wire  w_internal_ts1755007835428;
    logic r_internal_ts1755007835428;
        // BEGIN: ModuleBasic_ts1755007835432
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755007835432;
        int   d_ts1755007835432;
        always_comb begin
            logic temp_v_ts1755007835432;
                SimpleAssign SimpleAssign_inst_1755007835433_6716 (
                    .out_data(inj_out_data_1755007835433_952),
                    .in_data(inj_i1_s_1755007835429_552)
                );
            temp_v_ts1755007835432 = d_ts1755007835432;
            c_ts1755007835432      = temp_v_ts1755007835432;
        end
        assign inj_out_a_1755007835432_818 = r_internal_ts1755007835428;
        assign d_ts1755007835432     = inj_b_1755007835432_993;
        assign inj_out_b_1755007835432_501 = d_ts1755007835432 + P1 + LP1;
        // END: ModuleBasic_ts1755007835432

        // BEGIN: ModSimpleLogic_ts1755007835431
        assign inj_y_1755007835431_349 = inj_i_reg_data_1755007835428_12 ^ r_internal_ts1755007835428;
        // END: ModSimpleLogic_ts1755007835431

        // BEGIN: Comb_Assign_ts1755007835431
        assign inj_out_1755007835431_89 = clk & reset;
        // END: Comb_Assign_ts1755007835431

        coalesced_assign coalesced_assign_inst_1755007835430_8841 (
            .in_h(inj_in_h_1755007835430_705),
            .in_l(inj_in_l_1755007835430_295),
            .out(inj_out_1755007835430_55)
        );
        // BEGIN: sub_module_ts1755007835429
        assign inj_sub_out_1755007835429_438 = !r_internal_ts1755007835428;
        // END: sub_module_ts1755007835429

        CaseEq CaseEq_inst_1755007835429_967 (
            .match_z_eq(inj_match_z_eq_1755007835429_38),
            .data_io(inj_data_io_1755007835429_155),
            .match_x_neq(inj_match_x_neq_1755007835429_686)
        );
        split_complex_nb split_complex_nb_inst_1755007835429_2532 (
            .i3_s(inj_i3_s_1755007835429_184),
            .o1_s(inj_o1_s_1755007835429_313),
            .o2_s(inj_o2_s_1755007835429_649),
            .o3_s(inj_o3_s_1755007835429_854),
            .clk_s(clk),
            .i1_s(inj_i1_s_1755007835429_552),
            .i2_s(inj_i2_s_1755007835429_809)
        );
    assign w_internal_ts1755007835428  = clk & inj_i_reg_data_1755007835428_12;
    assign inj_o_wire_out_1755007835428_609  = w_internal_ts1755007835428;
    always_ff @(posedge clk) r_internal_ts1755007835428 <= inj_i_data_sync_1755007835428_600;
    assign inj_o_reg_out_1755007835428_543 = r_internal_ts1755007835428;
    // END: nets_alias_clocking_ts1755007835429
endmodule

