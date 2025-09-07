module case_empty_statement (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b1;
            2'b01: ;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module module_forceable_attr (
    input wire i_clk,
    input logic i_data_in,
    input wire i_rst_n,
    input logic i_write_en,
    output logic o_forceable_signal,
    output logic o_read_signal
);
    logic forceable_signal ;
    logic read_internal;
    assign o_forceable_signal = forceable_signal;
    always @(posedge i_clk or negedge i_rst_n) begin
        if (!i_rst_n) begin
            forceable_signal <= 1'b0;
            read_internal <= 1'b0;
        end else begin
            if (i_write_en) begin
                forceable_signal <= i_data_in;
            end
            read_internal <= forceable_signal;
        end
    end
    assign o_read_signal = read_internal;
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module split_complex_blocking (
    input logic [7:0] i1_r,
    input logic [7:0] i2_r,
    input logic [7:0] i3_r,
    output logic [7:0] o1_r,
    output logic [7:0] o2_r,
    output logic [7:0] o3_r
);
    logic [7:0] t1_r, t2_r;
    always @(*) begin
        t1_r = i1_r + i2_r;
        o1_r = t1_r - i3_r;
        t2_r = i2_r * i3_r;
        o2_r = t1_r + t2_r;
        o3_r = t2_r / 2;
    end
endmodule

module split_if_empty_then (
    input logic clk_p,
    input logic condition_p,
    input logic [7:0] in_val_p,
    output logic [7:0] out_reg_p
);
    always @(posedge clk_p) begin
        if (condition_p) begin
        end else begin
            out_reg_p <= in_val_p;
        end
    end
endmodule

module snippet (
    input wire clk,
    input wire [3:0] inj_data_in_1755007896074_240,
    input logic inj_i_write_en_1755007896073_368,
    input logic [31:0] inj_in_1755007896087_994,
    input logic [1:0] inj_in_val_1755007896083_333,
    input logic [4:0] inj_read_address_1755007896072_625,
    input logic inj_sub_in_1755007896072_367,
    input bit inj_trigger_input_1755007896072_639,
    input logic [4:0] inj_write_address_1755007896072_88,
    input logic [7:0] inj_write_data_1755007896072_565,
    input wire reset,
    output wire inj_data_b_1755007896081_827,
    output reg [3:0] inj_data_out_1755007896074_556,
    output logic [7:0] inj_o1_r_1755007896080_127,
    output logic [7:0] inj_o2_r_1755007896080_434,
    output logic [7:0] inj_o3_r_1755007896080_451,
    output logic inj_o_forceable_signal_1755007896073_758,
    output logic inj_o_out_1755007896085_514,
    output logic inj_o_read_signal_1755007896073_691,
    output logic [7:0] inj_out1_1755007896087_322,
    output logic inj_out2_1755007896087_525,
    output logic [7:0] inj_out_reg_p_1755007896076_892,
    output reg inj_out_res_1755007896083_182,
    output logic [7:0] inj_out_val_m10_1755007896078_158,
    output logic inj_q_1755007896077_33,
    output logic [7:0] inj_read_data_1755007896072_925,
    output logic [7:0] inj_read_data_1755007896074_716,
    output logic inj_sub_out_1755007896072_388,
    output bit inj_trigger_output_1755007896072_141
);
    // BEGIN: sub_module_ts1755007896072
    // BEGIN: PragmaOnceDirective_ts1755007896072
    // BEGIN: SynchronousMemory_ts1755007896073
    logic [7:0] mem_ts1755007896073 [0:31];
        // BEGIN: SynchronousMemory_ts1755007896075
        logic [7:0] mem_ts1755007896075 [0:31];
            // BEGIN: unsupported_cond_expr_ts1755007896078
            logic [7:0] var_m10_ts1755007896078;
                // BEGIN: attributes_on_expr_port_ts1755007896085
                logic internal_sig_ts1755007896085;
                    // BEGIN: constant_sel_ts1755007896087
                    assign inj_out1_1755007896087_322 = inj_in_1755007896087_994[15:8];
                    assign inj_out2_1755007896087_525 = inj_in_1755007896087_994[3];
                    // END: constant_sel_ts1755007896087

                assign internal_sig_ts1755007896085 = inj_i_write_en_1755007896073_368 & inj_sub_in_1755007896072_367;
                simple_adder sa_inst(
                    .a  (inj_i_write_en_1755007896073_368),
                    (* fanout_limit = 10 *) .b(inj_sub_in_1755007896072_367),
                    .sum(inj_o_out_1755007896085_514)
                );
                // END: attributes_on_expr_port_ts1755007896085

                case_empty_statement case_empty_statement_inst_1755007896083_9377 (
                    .in_val(inj_in_val_1755007896083_333),
                    .out_res(inj_out_res_1755007896083_182)
                );
                // BEGIN: simple_logic_a_ts1755007896081
                assign inj_data_b_1755007896081_827 = ~clk;
                // END: simple_logic_a_ts1755007896081

                split_complex_blocking split_complex_blocking_inst_1755007896080_7134 (
                    .i3_r(mem_ts1755007896075),
                    .o1_r(inj_o1_r_1755007896080_127),
                    .o2_r(inj_o2_r_1755007896080_434),
                    .o3_r(inj_o3_r_1755007896080_451),
                    .i1_r(var_m10_ts1755007896078),
                    .i2_r(mem_ts1755007896073)
                );
            always_comb begin
                var_m10_ts1755007896078 = inj_write_data_1755007896072_565;
                inj_out_val_m10_1755007896078_158 = inj_trigger_input_1755007896072_639 ? var_m10_ts1755007896078 : var_m10_ts1755007896078;
                var_m10_ts1755007896078++;
            end
            // END: unsupported_cond_expr_ts1755007896078

            // BEGIN: ModClockedResetReg_ts1755007896077
            always @(posedge clk or negedge reset) begin
            if (!reset) begin
                inj_q_1755007896077_33 <= 1'b0;
            end else begin
                inj_q_1755007896077_33 <= inj_sub_in_1755007896072_367;
            end
            end
            // END: ModClockedResetReg_ts1755007896077

            split_if_empty_then split_if_empty_then_inst_1755007896076_5625 (
                .in_val_p(mem_ts1755007896075),
                .out_reg_p(inj_out_reg_p_1755007896076_892),
                .clk_p(clk),
                .condition_p(inj_sub_in_1755007896072_367)
            );
        always_ff @(posedge clk or posedge reset) begin
            if (reset) begin
                inj_read_data_1755007896074_716 <= 8'h0;
            end else begin
                if (inj_sub_in_1755007896072_367) begin
                    mem_ts1755007896075[inj_write_address_1755007896072_88] <= mem_ts1755007896073;
                end
                inj_read_data_1755007896074_716 <= mem_ts1755007896075[inj_read_address_1755007896072_625];
            end
        end
        // END: SynchronousMemory_ts1755007896075

        // BEGIN: mod_event_implicit_ts1755007896074
        always @* begin
            inj_data_out_1755007896074_556 = inj_data_in_1755007896074_240;
        end
        // END: mod_event_implicit_ts1755007896074

        module_forceable_attr module_forceable_attr_inst_1755007896073_8485 (
            .o_forceable_signal(inj_o_forceable_signal_1755007896073_758),
            .o_read_signal(inj_o_read_signal_1755007896073_691),
            .i_clk(clk),
            .i_data_in(inj_sub_in_1755007896072_367),
            .i_rst_n(reset),
            .i_write_en(inj_i_write_en_1755007896073_368)
        );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            inj_read_data_1755007896072_925 <= 8'h0;
        end else begin
            if (inj_sub_in_1755007896072_367) begin
                mem_ts1755007896073[inj_write_address_1755007896072_88] <= inj_write_data_1755007896072_565;
            end
            inj_read_data_1755007896072_925 <= mem_ts1755007896073[inj_read_address_1755007896072_625];
        end
    end
    // END: SynchronousMemory_ts1755007896073

assign inj_trigger_output_1755007896072_141 = inj_trigger_input_1755007896072_639;
    // END: PragmaOnceDirective_ts1755007896072

    assign inj_sub_out_1755007896072_388 = !inj_sub_in_1755007896072_367;
    // END: sub_module_ts1755007896072
endmodule

