interface struct_if;
    logic [7:0] packet_field1;
    logic [7:0] packet_field2;
    logic tx_en;
    modport Access (output packet_field1, output packet_field2, output tx_en);
endinterface
module mod_split_ff (
    input logic clk,
    input logic [7:0] data_in,
    input logic reset,
    output logic [7:0] out_reg_a,
    output logic [7:0] out_reg_b
);
    logic [7:0]  split_reg_var;
    logic [7:0] other_reg_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var <= 8'b0;
            other_reg_var <= 8'b0;
            out_reg_a <= 8'b0;
            out_reg_b <= 8'b0;
        end else begin
            split_reg_var <= data_in;
            other_reg_var <= data_in + 2;
            out_reg_a <= split_reg_var;
            out_reg_b <= other_reg_var;
        end
    end
endmodule

module module_struct_write (
    input logic [7:0] in_field1,
    input logic [7:0] in_field2,
    output logic tx_status
);
    struct_if stif_inst();
    always_comb begin
        stif_inst.packet_field1 = in_field1;
        stif_inst.packet_field2 = in_field2;
        stif_inst.tx_en = 1'b1;
        tx_status = stif_inst.tx_en;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_din_1755007890753_941,
    input wire [7:0] inj_in1_1755007890752_835,
    input wire [7:0] inj_in2_1755007890752_561,
    input logic [63:0] inj_wide_a_1755007890754_858,
    input logic [63:0] inj_wide_b_1755007890754_484,
    input logic [63:0] inj_wide_c_1755007890754_873,
    input wire reset,
    output logic [7:0] inj_diff_u_1755007890755_675,
    output logic inj_dout_1755007890753_282,
    output logic inj_nm_out_1755007890753_684,
    output logic inj_o_sum_1755007890754_771,
    output logic [7:0] inj_o_target_result_1755007890753_475,
    output wire [7:0] inj_out1_1755007890752_618,
    output wire [7:0] inj_out2_1755007890752_801,
    output logic [7:0] inj_out_reg_a_1755007890753_538,
    output logic [7:0] inj_out_reg_b_1755007890753_825,
    output logic [7:0] inj_prod_u_1755007890755_969,
    output logic [7:0] inj_sum_u_1755007890755_244,
    output logic inj_tx_status_1755007890753_150,
    output logic [63:0] inj_wide_out_1755007890754_53,
    output logic [7:0] inj_wide_reg_1755007890754_457
);
    // BEGIN: multi_always_comb_ts1755007890752
    logic [7:0] intermediate1_ts1755007890752;
    logic [7:0] intermediate2_ts1755007890752;
        // BEGIN: mod_lint_target_ts1755007890754
        logic l_reg_ts1755007890754;
            // BEGIN: split_arith_blocking_ts1755007890755
            always @(*) begin
                inj_sum_u_1755007890755_244 = intermediate2_ts1755007890752 + intermediate1_ts1755007890752;
                inj_diff_u_1755007890755_675 = intermediate2_ts1755007890752 - intermediate1_ts1755007890752;
                inj_prod_u_1755007890755_969 = intermediate2_ts1755007890752 * intermediate1_ts1755007890752;
            end
            // END: split_arith_blocking_ts1755007890755

            // BEGIN: wide_ops_deep_ts1755007890754
            assign inj_wide_out_1755007890754_53 = (((inj_wide_a_1755007890754_858 + inj_wide_b_1755007890754_484) ^ inj_wide_c_1755007890754_873) & (~inj_wide_a_1755007890754_858 | inj_wide_b_1755007890754_484)) + (inj_wide_c_1755007890754_873 >>> 5);
            // END: wide_ops_deep_ts1755007890754

        always_comb begin
            l_reg_ts1755007890754 = 1;
            inj_wide_reg_1755007890754_457 = {clk, reset};
        end
        assign inj_o_sum_1755007890754_771 = clk + reset;
        // END: mod_lint_target_ts1755007890754

        // BEGIN: nested_module_ts1755007890753
        assign inj_nm_out_1755007890753_684 = inj_din_1755007890753_941;
        // END: nested_module_ts1755007890753

        // BEGIN: ModRegister_ts1755007890753
        always @* begin
            inj_dout_1755007890753_282 = inj_din_1755007890753_941;
        end
        // END: ModRegister_ts1755007890753

        mod_split_ff mod_split_ff_inst_1755007890753_1293 (
            .out_reg_b(inj_out_reg_b_1755007890753_825),
            .clk(clk),
            .data_in(intermediate1_ts1755007890752),
            .reset(reset),
            .out_reg_a(inj_out_reg_a_1755007890753_538)
        );
        module_struct_write module_struct_write_inst_1755007890753_130 (
            .in_field2(intermediate1_ts1755007890752),
            .tx_status(inj_tx_status_1755007890753_150),
            .in_field1(intermediate2_ts1755007890752)
        );
        // BEGIN: target_module_for_bind_ts1755007890753
        always_comb inj_o_target_result_1755007890753_475 = intermediate1_ts1755007890752 + 1;
        // END: target_module_for_bind_ts1755007890753

    always @(*) begin
        intermediate1_ts1755007890752 = inj_in1_1755007890752_835 & inj_in2_1755007890752_561;
    end
    always @(*) begin
        intermediate2_ts1755007890752 = inj_in1_1755007890752_835 | inj_in2_1755007890752_561;
    end
    assign inj_out1_1755007890752_618 = intermediate1_ts1755007890752 + 8'd1;
    assign inj_out2_1755007890752_801 = intermediate2_ts1755007890752 - 8'd1;
    // END: multi_always_comb_ts1755007890752
endmodule

