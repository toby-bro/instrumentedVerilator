module ansi_implicit_inherit (
    input logic [2:0] in1,
    input logic in2,
    output logic extra_out,
    output logic out1,
    output logic out2
);
    always_comb begin
        out1 = |in1;
        out2 = |in2;
        extra_out = out1 ^ out2;
    end
endmodule

module child_scalar_port (
    input logic data_in,
    output logic data_out
);
    assign data_out = data_in;
endmodule

module mismatched_width_unhandled (
    input logic [7:0] in,
    output logic [3:0] out
);
    assign out = in;
endmodule

module mod_event_posedge (
    input wire clk,
    input wire data_in,
    output reg data_out
);
    always @(posedge clk) begin
        data_out <= data_in;
    end
endmodule

module mod_sub (
    input wire in_sub,
    output logic out_sub
);
    assign out_sub = in_sub;
endmodule

module module_packed_array (
    input logic enable_pa,
    input logic [31:0] input_pa,
    input logic [3:0] input_slice_pa,
    output logic [7:0] output_pa,
    output logic [7:0] output_pa_element1
);
    logic [7:0] my_packed_array[0:3] ;
    always_comb begin
        if (enable_pa) begin
            my_packed_array[0] = input_pa[7:0];
            my_packed_array[1] = input_pa[15:8];
            my_packed_array[2] = input_pa[23:16];
            my_packed_array[3] = my_packed_array[0] + my_packed_array[1];
        end else begin
            my_packed_array[0] = 8'h0;
            my_packed_array[1] = 8'h0;
            my_packed_array[2] = 8'h0;
            my_packed_array[3] = 8'h0;
        end
        my_packed_array[0][3:0] = input_slice_pa;
    end
    assign output_pa = my_packed_array[3];
    assign output_pa_element1 = my_packed_array[1];
endmodule

module split_conditional_blocking (
    input logic condition_o,
    input logic [7:0] in_false_o,
    input logic [7:0] in_true_o,
    output logic [7:0] out_val_o
);
    always @(*) begin
        if (condition_o) begin
            out_val_o = in_true_o;
        end else begin
            out_val_o = in_false_o;
        end
    end
endmodule

module unreferenced_module (
    input logic unused_in,
    output logic unused_out
);
    assign unused_out = ~unused_in;
endmodule

module snippet (
    input wire clk,
    input wire [7:0] inj_d_in_1755007820862_721,
    input logic [7:0] inj_in1_1755007820860_618,
    input logic [2:0] inj_in1_1755007820861_85,
    input logic [7:0] inj_in2_1755007820860_923,
    input logic inj_in2_1755007820861_480,
    input bit inj_in_h_1755007820861_44,
    input logic [31:0] inj_input_pa_1755007820861_955,
    input logic [3:0] inj_input_slice_pa_1755007820861_518,
    input wire reset,
    output logic inj_and_reduce_1755007820862_97,
    output logic inj_data_out_1755007820862_624,
    output reg inj_data_out_1755007820865_596,
    output logic inj_extra_out_1755007820861_750,
    output logic inj_or_reduce_1755007820862_614,
    output logic [7:0] inj_out1_1755007820860_572,
    output logic inj_out1_1755007820861_562,
    output logic [7:0] inj_out2_1755007820860_988,
    output logic inj_out2_1755007820861_222,
    output logic [3:0] inj_out_1755007820861_27,
    output logic [7:0] inj_out_1755007820863_989,
    output logic inj_out_h_1755007820861_690,
    output logic inj_out_sub_1755007820864_511,
    output logic [7:0] inj_out_val_o_1755007820863_567,
    output logic [7:0] inj_output_pa_1755007820861_278,
    output logic [7:0] inj_output_pa_element1_1755007820861_993,
    output reg [7:0] inj_q_out_1755007820862_979,
    output logic inj_unused_out_1755007820864_414,
    output logic inj_xor_reduce_1755007820862_502
);
    // BEGIN: ModuleComb_ts1755007820861
    logic [7:0] internal_wire_ts1755007820861;
        mod_event_posedge mod_event_posedge_inst_1755007820865_1156 (
            .data_in(reset),
            .data_out(inj_data_out_1755007820865_596),
            .clk(clk)
        );
        unreferenced_module unreferenced_module_inst_1755007820864_1854 (
            .unused_in(inj_in2_1755007820861_480),
            .unused_out(inj_unused_out_1755007820864_414)
        );
        mod_sub mod_sub_inst_1755007820864_1372 (
            .in_sub(clk),
            .out_sub(inj_out_sub_1755007820864_511)
        );
        // BEGIN: timed_assign_unhandled_ts1755007820863
        always @(posedge clk) begin
            inj_out_1755007820863_989 <= inj_in2_1755007820860_923;
        end
        // END: timed_assign_unhandled_ts1755007820863

        split_conditional_blocking split_conditional_blocking_inst_1755007820863_7340 (
            .out_val_o(inj_out_val_o_1755007820863_567),
            .condition_o(inj_in2_1755007820861_480),
            .in_false_o(internal_wire_ts1755007820861),
            .in_true_o(inj_in1_1755007820860_618)
        );
        // BEGIN: ReductionOperations_ts1755007820862
        assign inj_and_reduce_1755007820862_97 = &internal_wire_ts1755007820861;
        assign inj_or_reduce_1755007820862_614 = |internal_wire_ts1755007820861;
        assign inj_xor_reduce_1755007820862_502 = ^internal_wire_ts1755007820861;
        // END: ReductionOperations_ts1755007820862

        child_scalar_port child_scalar_port_inst_1755007820862_3234 (
            .data_out(inj_data_out_1755007820862_624),
            .data_in(inj_in2_1755007820861_480)
        );
        // BEGIN: Seq_DFF_ts1755007820862
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                inj_q_out_1755007820862_979 <= 8'b0;
            end else begin
                inj_q_out_1755007820862_979 <= inj_d_in_1755007820862_721;
            end
        end
        // END: Seq_DFF_ts1755007820862

        // BEGIN: CoverageHelper_ts1755007820861
        assign inj_out_h_1755007820861_690 = inj_in_h_1755007820861_44;
        // END: CoverageHelper_ts1755007820861

        module_packed_array module_packed_array_inst_1755007820861_7502 (
            .output_pa_element1(inj_output_pa_element1_1755007820861_993),
            .enable_pa(inj_in2_1755007820861_480),
            .input_pa(inj_input_pa_1755007820861_955),
            .input_slice_pa(inj_input_slice_pa_1755007820861_518),
            .output_pa(inj_output_pa_1755007820861_278)
        );
        mismatched_width_unhandled mismatched_width_unhandled_inst_1755007820861_5500 (
            .in(internal_wire_ts1755007820861),
            .out(inj_out_1755007820861_27)
        );
        ansi_implicit_inherit ansi_implicit_inherit_inst_1755007820861_4664 (
            .in1(inj_in1_1755007820861_85),
            .in2(inj_in2_1755007820861_480),
            .extra_out(inj_extra_out_1755007820861_750),
            .out1(inj_out1_1755007820861_562),
            .out2(inj_out2_1755007820861_222)
        );
    assign internal_wire_ts1755007820861 = inj_in1_1755007820860_618 + inj_in2_1755007820860_923;
    always_comb begin
        if (internal_wire_ts1755007820861 > 8'd128) begin
            inj_out1_1755007820860_572 = internal_wire_ts1755007820861 - 1;
        end else begin
            inj_out1_1755007820860_572 = internal_wire_ts1755007820861 + 1;
        end
        inj_out2_1755007820860_988 = internal_wire_ts1755007820861 / 2;
    end
    // END: ModuleComb_ts1755007820861
endmodule

