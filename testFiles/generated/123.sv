module module_struct (
    input wire [15:0] i_packed_data,
    output logic [7:0] o_member_sum
);
    typedef struct packed {
        logic [3:0] part1;
        logic [7:0] part2;
        logic [3:0] part3;
    } my_packed_struct_t;
    my_packed_struct_t unpacked_data;
    assign unpacked_data = i_packed_data;
    always @* begin
        o_member_sum = unpacked_data.part1 + unpacked_data.part2 + unpacked_data.part3;
    end
endmodule

module recursive_param_diag_mod (
    input int dummy_in,
    output int out_val
);
    assign out_val = dummy_in;
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25
) (
    input wire clk,
    input logic [7:0] inj_a_1755007794137_825,
    input logic [7:0] inj_b_1755007794137_814,
    input logic [3:0] inj_b_1755007794138_469,
    input logic [7:0] inj_c_1755007794137_814,
    input logic [15:0] inj_data0_1755007794136_235,
    input logic [15:0] inj_data1_1755007794136_255,
    input logic [3:0] inj_data_in_1755007794134_791,
    input logic inj_din_1755007794134_480,
    input int inj_dummy_in_1755007794135_536,
    input bit inj_enable_in_1755007794140_584,
    input wire [15:0] inj_i_packed_data_1755007794135_209,
    input logic [2:0] inj_selector_1755007794134_85,
    input wire reset,
    output logic inj_anded_1755007794137_797,
    output logic [3:0] inj_data_out_1755007794134_536,
    output logic [15:0] inj_data_out_1755007794136_432,
    output logic inj_diff_1755007794137_294,
    output logic inj_dout_1755007794134_152,
    output logic [7:0] inj_field2_o_1755007794139_669,
    output logic [7:0] inj_o_member_sum_1755007794135_93,
    output logic [7:0] inj_o_sum_1755007794135_34,
    output logic inj_ored_1755007794137_503,
    output bit inj_out_1755007794140_923,
    output logic [15:0] inj_out_concat_1755007794138_792,
    output int inj_out_val_1755007794135_578,
    output logic [3:0] inj_result_out_1755007794134_496,
    output logic [7:0] inj_sum_1755007794137_989,
    output logic inj_xored_1755007794137_866
);
    // BEGIN: child_packed_scalar_port_ts1755007794134
    // BEGIN: rand_case_mod_ts1755007794134
    // BEGIN: ModRegister_ts1755007794134
    // BEGIN: param_local_port_ts1755007794135
    localparam int LP_BODY_VAL = 125;
    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
    // BEGIN: typedef_struct_mod_ts1755007794139
    typedef struct packed {
        logic [7:0] field1_ts1755007794139;
        logic [7:0] field2_ts1755007794139;
    } my_packed_struct_t;
    my_packed_struct_t my_struct_var;
    // BEGIN: mod_default_disable_ts1755007794140
    assign inj_out_1755007794140_923 = inj_enable_in_1755007794140_584;
    // END: mod_default_disable_ts1755007794140

    always_comb begin
        my_struct_var = inj_data0_1755007794136_235;
    end
    assign inj_field2_o_1755007794139_669 = my_struct_var.field2_ts1755007794139;
    // END: typedef_struct_mod_ts1755007794139

    // BEGIN: ConcatVectorOps_ts1755007794138
    assign inj_out_concat_1755007794138_792 = {inj_data_in_1755007794134_791, inj_b_1755007794138_469, inj_a_1755007794137_825};
    // END: ConcatVectorOps_ts1755007794138

    // BEGIN: more_ops_ts1755007794137
    assign inj_sum_1755007794137_989 = inj_a_1755007794137_825 + inj_b_1755007794137_814;
    assign inj_diff_1755007794137_294 = inj_a_1755007794137_825 > inj_c_1755007794137_814;
    assign inj_anded_1755007794137_797 = inj_a_1755007794137_825 & inj_b_1755007794137_814;
    assign inj_ored_1755007794137_503 = inj_a_1755007794137_825 | inj_c_1755007794137_814;
    assign inj_xored_1755007794137_866 = inj_a_1755007794137_825 ^ inj_b_1755007794137_814;
    // END: more_ops_ts1755007794137

    // BEGIN: CombinationalLogicExplicit_ts1755007794136
    always @(inj_din_1755007794134_480 or inj_data0_1755007794136_235 or inj_data1_1755007794136_255) begin
        if (inj_din_1755007794134_480) begin
            inj_data_out_1755007794136_432 = inj_data1_1755007794136_255;
        end else begin
            inj_data_out_1755007794136_432 = inj_data0_1755007794136_235;
        end
    end
    // END: CombinationalLogicExplicit_ts1755007794136

    recursive_param_diag_mod recursive_param_diag_mod_inst_1755007794135_7219 (
        .dummy_in(inj_dummy_in_1755007794135_536),
        .out_val(inj_out_val_1755007794135_578)
    );
    always_comb begin
        if (reset) begin
            inj_o_sum_1755007794135_34 = 0;
        end else begin
            inj_o_sum_1755007794135_34 = LP_CALCULATED;
        end
    end
    // END: param_local_port_ts1755007794135

    module_struct module_struct_inst_1755007794135_8791 (
        .o_member_sum(inj_o_member_sum_1755007794135_93),
        .i_packed_data(inj_i_packed_data_1755007794135_209)
    );
    always @* begin
        inj_dout_1755007794134_152 = inj_din_1755007794134_480;
    end
    // END: ModRegister_ts1755007794134

    always_comb begin
        case (inj_selector_1755007794134_85)
            0: inj_result_out_1755007794134_496 = 4'h0;
            1: inj_result_out_1755007794134_496 = 4'h1;
            2: inj_result_out_1755007794134_496 = 4'hA;
            default: inj_result_out_1755007794134_496 = 4'hF;
        endcase
    end
    // END: rand_case_mod_ts1755007794134

    assign inj_data_out_1755007794134_536 = inj_data_in_1755007794134_791;
    // END: child_packed_scalar_port_ts1755007794134
endmodule

