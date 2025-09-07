module constant_sel (
    input logic [31:0] in,
    output logic [7:0] out1,
    output logic out2
);
    assign out1 = in[15:8];
    assign out2 = in[3];
endmodule

module split_basic_nonblocking (
    input logic clk_b,
    input logic [7:0] in2_a,
    output logic [7:0] out2_a
);
    always @(posedge clk_b) begin
        out2_a <= in2_a;
    end
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007907009_894,
    input logic [31:0] inj_in_1755007907014_436,
    input logic [1:0] inj_selector_1755007907010_404,
    input wire reset,
    output logic inj_o_done_1755007907012_134,
    output logic [7:0] inj_out1_1755007907014_360,
    output logic inj_out2_1755007907014_95,
    output logic [7:0] inj_out2_a_1755007907011_813,
    output logic [7:0] inj_out_mv_a_1755007907009_135,
    output logic [7:0] inj_out_mv_b_1755007907009_256,
    output logic [7:0] inj_out_mv_c_1755007907009_610,
    output logic [7:0] inj_out_q_1755007907013_523,
    output wire inj_p_out_1755007907015_318,
    output logic [7:0] inj_selected_output_1755007907010_481,
    output logic inj_unused_out_1755007907016_420
);
    // BEGIN: mod_split_multiple_vars_ts1755007907010
    logic [7:0]  split_mv_var_ts1755007907010;
    logic [7:0] other_mv_var1_ts1755007907010;
    logic [7:0] other_mv_var2_ts1755007907010;
        // BEGIN: generate_for_block_ts1755007907011
        wire [7:0] data_ts1755007907011 [3:0]; 
            // BEGIN: mod_basic_ts1755007907012
            logic r_state_ts1755007907012;
                // BEGIN: explicit_non_ansi_decl_module_ts1755007907015
                input logic r_state_ts1755007907012_ts1755007907015;
                output wire inj_p_out_1755007907015_318_ts1755007907015;
                    // BEGIN: unreferenced_module_ts1755007907016
                    assign inj_unused_out_1755007907016_420 = ~r_state_ts1755007907012;
                    // END: unreferenced_module_ts1755007907016

                assign inj_p_out_1755007907015_318_ts1755007907015 = r_state_ts1755007907012_ts1755007907015;
                // END: explicit_non_ansi_decl_module_ts1755007907015

                constant_sel constant_sel_inst_1755007907014_9852 (
                    .in(inj_in_1755007907014_436),
                    .out1(inj_out1_1755007907014_360),
                    .out2(inj_out2_1755007907014_95)
                );
                // BEGIN: split_single_stmt_ts1755007907013
                always @(*) begin
                    inj_out_q_1755007907013_523 = inj_data_in_1755007907009_894 + 1;
                end
                // END: split_single_stmt_ts1755007907013

            parameter int PARAM_BASIC = 42;
            always_ff @(posedge clk) begin
                r_state_ts1755007907012 <= ~r_state_ts1755007907012;
            end
            always_comb begin
                inj_o_done_1755007907012_134 = r_state_ts1755007907012;
            end
            // END: mod_basic_ts1755007907012

            split_basic_nonblocking split_basic_nonblocking_inst_1755007907011_3313 (
                .out2_a(inj_out2_a_1755007907011_813),
                .clk_b(clk),
                .in2_a(inj_data_in_1755007907009_894)
            );
        genvar i;
        generate
            for (i = 0; i < 4; i = i + 1) begin : data_gen
                assign data_ts1755007907011[i] = 8'(i + 1) * 8'(i + 1);
            end
        endgenerate
        always_comb begin
            case (inj_selector_1755007907010_404)
                0: inj_selected_output_1755007907010_481 = data_ts1755007907011[0];
                1: inj_selected_output_1755007907010_481 = data_ts1755007907011[1];
                2: inj_selected_output_1755007907010_481 = data_ts1755007907011[2];
                3: inj_selected_output_1755007907010_481 = data_ts1755007907011[3];
                default: inj_selected_output_1755007907010_481 = 8'hXX;
            endcase
        end
        // END: generate_for_block_ts1755007907011

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_mv_var_ts1755007907010 <= 8'b0;
            other_mv_var1_ts1755007907010 <= 8'b0;
            other_mv_var2_ts1755007907010 <= 8'b0;
        end else begin
            split_mv_var_ts1755007907010 <= inj_data_in_1755007907009_894;
            other_mv_var1_ts1755007907010 <= inj_data_in_1755007907009_894 + 1;
            other_mv_var2_ts1755007907010 <= inj_data_in_1755007907009_894 + 2;
            if (inj_data_in_1755007907009_894 > 100) begin
                split_mv_var_ts1755007907010 <= 8'hFF;
            end
            inj_out_mv_a_1755007907009_135 <= split_mv_var_ts1755007907010;
            inj_out_mv_b_1755007907009_256 <= other_mv_var1_ts1755007907010;
            inj_out_mv_c_1755007907009_610 <= other_mv_var2_ts1755007907010;
        end
    end
    // END: mod_split_multiple_vars_ts1755007907010
endmodule

