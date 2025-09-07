typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
typedef struct packed {
    logic [3:0] f1;
    logic f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;

interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
module assign_pattern_lvalue (
    input logic [38:0] in_packed_for_conv,
    input logic [7:0] in_vec,
    output logic out_bit_conv,
    output int out_int_conv,
    output logic [7:0] out_unpacked_struct_repacked,
    output logic [5:0] out_vec_conv
);
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked;
    int int_var;
    logic bit_var;
    logic [5:0] vec_var;
    always_comb begin
        unpacked_s.f1 = in_vec[3:0];
        unpacked_s.f2 = in_vec[4];
        unpacked_s.f3 = in_vec[7:5];
        reg_unpacked_struct_repacked = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var = in_packed_for_conv[31:0];
        bit_var = in_packed_for_conv[32];
        vec_var = in_packed_for_conv[38:33];
        out_unpacked_struct_repacked = reg_unpacked_struct_repacked;
        out_int_conv = int_var;
        out_bit_conv = bit_var;
        out_vec_conv = vec_var;
    end
endmodule

module explicit_non_ansi_decl_module (
    p_in,
    p_out
);
    input logic p_in;
    output wire p_out;
    assign p_out = p_in;
endmodule

module sequential_register (
    input logic clk,
    input logic data_in,
    input logic enable_in,
    input logic reset_n,
    output logic data_out
);
    always_ff @(posedge clk or negedge reset_n) begin
        if (!reset_n) begin
            data_out <= 1'b0; 
        end else if (enable_in) begin
            data_out <= data_in; 
        end
    end
endmodule

module snippet #(
    parameter int P_PORT_VAL = 25
) (
    input wire clk,
    input logic [15:0] inj_data_in_1755007853485_66,
    input logic inj_data_in_1755007853486_275,
    input logic [38:0] inj_in_packed_for_conv_1755007853485_238,
    input logic [7:0] inj_in_vec_1755007853485_582,
    input logic [31:0] inj_p_in1_1755007853485_721,
    input logic [31:0] inj_p_in2_1755007853485_176,
    input logic inj_p_in_1755007853485_557,
    input logic [1:0] inj_p_mode_1755007853485_801,
    input wire reset,
    output logic inj_control_status_1755007853485_616,
    output logic inj_data_out_1755007853486_102,
    output logic inj_nm_out_1755007853485_779,
    output logic inj_nm_out_1755007853487_912,
    output logic [7:0] inj_o_sum_1755007853486_224,
    output logic inj_out_bit_conv_1755007853485_323,
    output int inj_out_int_conv_1755007853485_345,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007853485_943,
    output logic [5:0] inj_out_vec_conv_1755007853485_702,
    output logic [31:0] inj_p_out_1755007853485_273,
    output wire inj_p_out_1755007853485_8
);
    // BEGIN: nested_module_ts1755007853485
    // BEGIN: module_conditional_write_ts1755007853485
    // BEGIN: more_procedural_ts1755007853486
    // BEGIN: param_local_port_ts1755007853486
    localparam int LP_BODY_VAL = 125;
    localparam int LP_CALCULATED = P_PORT_VAL + LP_BODY_VAL;
    // BEGIN: nested_module_ts1755007853487
    assign inj_nm_out_1755007853487_912 = inj_data_in_1755007853486_275;
    // END: nested_module_ts1755007853487

    always_comb begin
        if (reset) begin
            inj_o_sum_1755007853486_224 = 0;
        end else begin
            inj_o_sum_1755007853486_224 = LP_CALCULATED;
        end
    end
    // END: param_local_port_ts1755007853486

    sequential_register sequential_register_inst_1755007853486_3339 (
        .data_in(inj_data_in_1755007853486_275),
        .enable_in(inj_p_in_1755007853485_557),
        .reset_n(reset),
        .data_out(inj_data_out_1755007853486_102),
        .clk(clk)
    );
    always_comb begin
        case (inj_p_mode_1755007853485_801)
            2'b00: inj_p_out_1755007853485_273 = (inj_p_in1_1755007853485_721 + inj_p_in2_1755007853485_176) * 2;
            2'b01: inj_p_out_1755007853485_273 = (inj_p_in1_1755007853485_721 - inj_p_in2_1755007853485_176) / 3; 
            2'b10: inj_p_out_1755007853485_273 = (inj_p_in1_1755007853485_721 << 4) | (inj_p_in2_1755007853485_176 >> 2);
            default: inj_p_out_1755007853485_273 = ~(inj_p_in1_1755007853485_721 ^ inj_p_in2_1755007853485_176) + 1;
        endcase
    end
    // END: more_procedural_ts1755007853486

    cond_if cif_inst();
    always_comb begin
        if (inj_p_in_1755007853485_557) begin
            cif_inst.control_reg = inj_data_in_1755007853485_66;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        inj_control_status_1755007853485_616 = (cif_inst.control_reg != 16'h0);
    end
    // END: module_conditional_write_ts1755007853485

    assign_pattern_lvalue assign_pattern_lvalue_inst_1755007853485_4593 (
        .out_int_conv(inj_out_int_conv_1755007853485_345),
        .out_unpacked_struct_repacked(inj_out_unpacked_struct_repacked_1755007853485_943),
        .out_vec_conv(inj_out_vec_conv_1755007853485_702),
        .in_packed_for_conv(inj_in_packed_for_conv_1755007853485_238),
        .in_vec(inj_in_vec_1755007853485_582),
        .out_bit_conv(inj_out_bit_conv_1755007853485_323)
    );
    assign inj_nm_out_1755007853485_779 = inj_p_in_1755007853485_557;
    // END: nested_module_ts1755007853485

    explicit_non_ansi_decl_module explicit_non_ansi_decl_module_inst_1755007853485_9195 (
        .p_in(inj_p_in_1755007853485_557),
        .p_out(inj_p_out_1755007853485_8)
    );
endmodule

