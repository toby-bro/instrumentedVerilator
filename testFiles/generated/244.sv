interface cond_if;
    logic [15:0] control_reg;
    logic [15:0] status_reg;
    modport CtrlStat (output control_reg, input status_reg);
endinterface
interface my_if;
    logic [7:0] data;
    logic ready;
    logic valid;
    modport FullAccess (input data, output ready, output valid);
    modport AccessIn (output data, output valid, input ready);
    modport AccessOut (input data, input valid, output ready);
endinterface
module ConcatVectorOps (
    input logic [3:0] a,
    input logic [3:0] b,
    input logic [7:0] c,
    output logic [15:0] out_concat
);
    assign out_concat = {a, b, c};
endmodule

module GenerateIfParam #(
    parameter bit GEN = 1
) (
    input logic sig_in,
    output logic sig_out
);
    generate
        if (GEN) begin : g_true
            assign sig_out = sig_in;
        end
        else begin : g_false
            assign sig_out = ~sig_in;
        end
    endgenerate
endmodule

module cast_select_demo (
    input logic [7:0] in_data,
    output logic [1:0] out_bits
);
    logic [7:0] internal;
    always_comb begin
        internal = in_data;
        out_bits = internal[3 -: 2];
    end
endmodule

module mod_always_event (
    input logic clk,
    input logic in,
    input logic rst,
    output logic out
);
    always @(posedge clk or negedge rst) begin
        if (!rst) begin
            out <= 1'b0;
        end else begin
            out <= in;
        end
    end
endmodule

module module_sequential_writes (
    input logic [7:0] addr,
    input logic [7:0] wdata,
    output logic write_status
);
    my_if vif_bus();
    always_comb begin
        vif_bus.data = wdata;
        vif_bus.ready = 1'b1;
        vif_bus.valid = 1'b0;
        write_status = vif_bus.ready;
    end
endmodule

module range_select_simple_packed (
    input logic [15:0] in_vec,
    output logic [7:0] out_slice_be,
    output logic [7:0] out_slice_le
);
    assign out_slice_be = in_vec[7:0]; 
    assign out_slice_le = in_vec[7:0]; 
endmodule

module snippet #(
    parameter integer DATA_WIDTH = 8,
    parameter integer UNUSED_PARAM = 8
) (
    input wire clk,
    input logic [3:0] inj_a_1755007835788_949,
    input logic [3:0] inj_b_1755007835788_800,
    input logic inj_in2_1755007835797_835,
    input logic [7:0] inj_in_data_1755007835788_543,
    input logic inj_in_m_1755007835788_996,
    input logic [1:0] inj_in_val_1755007835788_661,
    input logic [15:0] inj_in_vec_1755007835790_423,
    input wire [7:0] inj_param_in_1755007835789_23,
    input logic [7:0] inj_wdata_1755007835789_168,
    input wire reset,
    output logic inj_control_status_1755007835793_978,
    output logic [7:0] inj_diff_v_1755007835791_244,
    output logic [7:0] inj_large_sum_out_1755007835795_221,
    output logic inj_out_1755007835794_543,
    output logic inj_out_1755007835797_193,
    output logic [1:0] inj_out_bits_1755007835788_510,
    output logic [15:0] inj_out_concat_1755007835788_483,
    output logic inj_out_n_1755007835788_222,
    output reg inj_out_res_1755007835788_333,
    output logic [7:0] inj_out_slice_be_1755007835790_859,
    output logic [7:0] inj_out_slice_le_1755007835790_561,
    output wire [7:0] inj_param_out_1755007835789_993,
    output logic [7:0] inj_prod_v_1755007835791_826,
    output logic inj_sig_out_1755007835790_17,
    output logic [7:0] inj_sum_v_1755007835791_331,
    output logic inj_write_status_1755007835789_482
);
    // BEGIN: case_default_ts1755007835788
    // BEGIN: LintParamUnused_ts1755007835788
    // BEGIN: module_with_params_ts1755007835789
    // BEGIN: split_arith_nb_ts1755007835792
    // BEGIN: module_conditional_write_ts1755007835793
    // BEGIN: loop_unroll_limit_test_ts1755007835796
    logic [7:0] current_large_sum_ts1755007835795;
        // BEGIN: simple_xor_gate_ts1755007835797
        assign inj_out_1755007835797_193 = inj_in_m_1755007835788_996 ^ inj_in2_1755007835797_835;
        // END: simple_xor_gate_ts1755007835797

    always_comb begin
        current_large_sum_ts1755007835795 = 8'h00;
        for (int m = 0; m < 40; m = m + 1) begin 
            current_large_sum_ts1755007835795 = current_large_sum_ts1755007835795 + inj_in_val_1755007835788_661[0];
            current_large_sum_ts1755007835795 = current_large_sum_ts1755007835795 + inj_in_val_1755007835788_661[1];
            current_large_sum_ts1755007835795 = current_large_sum_ts1755007835795 + 1;
        end
        inj_large_sum_out_1755007835795_221 = current_large_sum_ts1755007835795;
    end
    // END: loop_unroll_limit_test_ts1755007835796

    mod_always_event mod_always_event_inst_1755007835794_8779 (
        .in(inj_in_m_1755007835788_996),
        .out(inj_out_1755007835794_543),
        .clk(clk),
        .rst(reset)
    );
    cond_if cif_inst();
    always_comb begin
        if (inj_in_m_1755007835788_996) begin
            cif_inst.control_reg = inj_in_vec_1755007835790_423;
        end else begin
            cif_inst.control_reg = 16'h0;
        end
        inj_control_status_1755007835793_978 = (cif_inst.control_reg != 16'h0);
    end
    // END: module_conditional_write_ts1755007835793

    always @(posedge clk) begin
        inj_sum_v_1755007835791_331 <= inj_wdata_1755007835789_168 + inj_in_data_1755007835788_543;
        inj_diff_v_1755007835791_244 <= inj_wdata_1755007835789_168 - inj_in_data_1755007835788_543;
        inj_prod_v_1755007835791_826 <= inj_wdata_1755007835789_168 * inj_in_data_1755007835788_543;
    end
    // END: split_arith_nb_ts1755007835792

    range_select_simple_packed range_select_simple_packed_inst_1755007835790_555 (
        .in_vec(inj_in_vec_1755007835790_423),
        .out_slice_be(inj_out_slice_be_1755007835790_859),
        .out_slice_le(inj_out_slice_le_1755007835790_561)
    );
    GenerateIfParam GenerateIfParam_inst_1755007835790_8933 (
        .sig_in(inj_in_m_1755007835788_996),
        .sig_out(inj_sig_out_1755007835790_17)
    );
    assign inj_param_out_1755007835789_993 = inj_param_in_1755007835789_23;
    // END: module_with_params_ts1755007835789

    module_sequential_writes module_sequential_writes_inst_1755007835789_4739 (
        .addr(inj_in_data_1755007835788_543),
        .wdata(inj_wdata_1755007835789_168),
        .write_status(inj_write_status_1755007835789_482)
    );
    ConcatVectorOps ConcatVectorOps_inst_1755007835788_1017 (
        .c(inj_in_data_1755007835788_543),
        .out_concat(inj_out_concat_1755007835788_483),
        .a(inj_a_1755007835788_949),
        .b(inj_b_1755007835788_800)
    );
    cast_select_demo cast_select_demo_inst_1755007835788_6846 (
        .in_data(inj_in_data_1755007835788_543),
        .out_bits(inj_out_bits_1755007835788_510)
    );
    assign inj_out_n_1755007835788_222 = inj_in_m_1755007835788_996;
    // END: LintParamUnused_ts1755007835788

    always_comb begin
        inj_out_res_1755007835788_333 = 1'b0;
        case (inj_in_val_1755007835788_661)
            2'b01: inj_out_res_1755007835788_333 = 1'b1;
            2'b10: inj_out_res_1755007835788_333 = 1'b0;
            default: inj_out_res_1755007835788_333 = 1'b1;
        endcase
    end
    // END: case_default_ts1755007835788
endmodule

