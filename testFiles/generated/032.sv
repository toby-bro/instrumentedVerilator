module AlwaysCombInvert (
    input logic [3:0] a,
    output logic [3:0] y
);
    always_comb y = ~a;
endmodule

module child_concat_output (
    input logic dummy_in,
    output logic [7:0] data
);
    assign data = dummy_in ? 8'hAA : 8'h55;
endmodule

module mod_event_implicit (
    input wire [3:0] data_in,
    output reg [3:0] data_out
);
    always @* begin
        data_out = data_in;
    end
endmodule

module module_assignments_in_loops (
    input logic [2:0] in_shift,
    input logic [7:0] in_val,
    output logic [3:0] out_part,
    output logic [7:0] out_reg
);
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var;
    logic [3:0] part_var;
    always_comb begin
        reg_var  = in_val;
        part_var = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var  = reg_var + i;
            reg_var += (i * 2);
            reg_var <<= in_shift;
            reg_var[i % 8] = (reg_var[i % 8] == 1'b0);
            reg_var[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var = reg_var[7:4];
    end
    assign out_reg  = reg_var;
    assign out_part = part_var;
endmodule

module target_module_for_bind (
    input logic i_target_clk,
    input logic [7:0] i_target_data,
    output logic [7:0] o_target_result
);
    always_comb o_target_result = i_target_data + 1;
endmodule

module snippet (
    input wire clk,
    input logic inj_data_in_1755007761333_782,
    input logic [3:0] inj_data_in_1755007761335_753,
    input int inj_data_in_1755007761338_729,
    input logic inj_enable_1755007761333_116,
    input wire [15:0] inj_i_packed_data_1755007761334_590,
    input logic [7:0] inj_i_target_data_1755007761332_683,
    input wire [3:0] inj_in_a_1755007761333_196,
    input wire [3:0] inj_in_b_1755007761333_922,
    input wire [7:0] inj_in_c_1755007761333_568,
    input logic [2:0] inj_in_shift_1755007761333_114,
    input logic [1:0] inj_in_val_1755007761337_922,
    input wire reset,
    output logic inj_cond_out_1755007761334_457,
    output logic [7:0] inj_data_1755007761336_221,
    output logic [7:0] inj_data_out_1755007761333_443,
    output logic inj_data_out_1755007761333_565,
    output logic [3:0] inj_data_out_1755007761335_182,
    output reg [3:0] inj_data_out_1755007761335_366,
    output int inj_data_out_1755007761338_81,
    output logic inj_eq_1755007761339_349,
    output logic [7:0] inj_o_member_sum_1755007761334_368,
    output logic [7:0] inj_o_target_result_1755007761332_574,
    output logic [15:0] inj_out_concat_1755007761333_481,
    output logic [7:0] inj_out_if_else_1755007761333_610,
    output logic [3:0] inj_out_part_1755007761333_207,
    output logic [7:0] inj_out_reg_1755007761333_752,
    output reg inj_out_res_1755007761337_980,
    output logic [3:0] inj_y_1755007761337_608
);
    // BEGIN: module_concat_if_ts1755007761333
    // BEGIN: ModClockedConditional_ts1755007761333
    logic reg_data_ts1755007761333;
        // BEGIN: sequential_logic_ts1755007761335
        ;
        logic [3:0] internal_reg_ts1755007761335;
            // BEGIN: ModCompareVec_ts1755007761339
            assign inj_eq_1755007761339_349 = (inj_data_in_1755007761335_753 == internal_reg_ts1755007761335);
            // END: ModCompareVec_ts1755007761339

            // BEGIN: mod_named_begin_ts1755007761338
            always_comb begin : my_named_block
                inj_data_out_1755007761338_81 = inj_data_in_1755007761338_729;
            end
            // END: mod_named_begin_ts1755007761338

            AlwaysCombInvert AlwaysCombInvert_inst_1755007761337_789 (
                .a(inj_data_in_1755007761335_753),
                .y(inj_y_1755007761337_608)
            );
            // BEGIN: case_single_default_after_item_ts1755007761337
            always_comb begin
                inj_out_res_1755007761337_980 = 1'b0;
                case (inj_in_val_1755007761337_922)
                    2'b01: inj_out_res_1755007761337_980 = 1'b1;
                    default: inj_out_res_1755007761337_980 = 1'b0;
                    2'b10: inj_out_res_1755007761337_980 = 1'b1;
                endcase
            end
            // END: case_single_default_after_item_ts1755007761337

            child_concat_output child_concat_output_inst_1755007761336_6671 (
                .dummy_in(inj_data_in_1755007761333_782),
                .data(inj_data_1755007761336_221)
            );
        always_ff @(posedge clk or negedge reset) begin
            if (!reset) begin
                internal_reg_ts1755007761335 <= 4'h0;
            end else begin
                internal_reg_ts1755007761335 <= inj_data_in_1755007761335_753;
            end
        end
        assign inj_data_out_1755007761335_182 = internal_reg_ts1755007761335;
        // END: sequential_logic_ts1755007761335

        mod_event_implicit mod_event_implicit_inst_1755007761335_3347 (
            .data_in(inj_in_b_1755007761333_922),
            .data_out(inj_data_out_1755007761335_366)
        );
        // BEGIN: module_struct_ts1755007761334
        typedef struct packed {
            logic [3:0] part1_ts1755007761334;
            logic [7:0] part2_ts1755007761334;
            logic [3:0] part3_ts1755007761334;
        } my_packed_struct_t;
        my_packed_struct_t unpacked_data;
        assign unpacked_data = inj_i_packed_data_1755007761334_590;
        always @* begin
            inj_o_member_sum_1755007761334_368 = unpacked_data.part1_ts1755007761334 + unpacked_data.part2_ts1755007761334 + unpacked_data.part3_ts1755007761334;
        end
        // END: module_struct_ts1755007761334

        // BEGIN: mod_logical_not_ts1755007761334
        always_comb begin
            inj_cond_out_1755007761334_457 = !reg_data_ts1755007761333;
        end
        // END: mod_logical_not_ts1755007761334

        // BEGIN: sequential_register_en_ts1755007761333
        always_ff @(posedge clk) begin
            if (reg_data_ts1755007761333) begin
                inj_data_out_1755007761333_443 <= inj_i_target_data_1755007761332_683;
            end
        end
        // END: sequential_register_en_ts1755007761333

    always @(posedge clk) begin
    if (inj_enable_1755007761333_116) begin
        reg_data_ts1755007761333 <= inj_data_in_1755007761333_782;
    end
    end
    assign inj_data_out_1755007761333_565 = reg_data_ts1755007761333;
    // END: ModClockedConditional_ts1755007761333

    module_assignments_in_loops module_assignments_in_loops_inst_1755007761333_9758 (
        .in_shift(inj_in_shift_1755007761333_114),
        .in_val(inj_i_target_data_1755007761332_683),
        .out_part(inj_out_part_1755007761333_207),
        .out_reg(inj_out_reg_1755007761333_752)
    );
    always_comb begin
    inj_out_concat_1755007761333_481 = {inj_in_a_1755007761333_196, inj_in_b_1755007761333_922, inj_in_c_1755007761333_568};
    if (clk) begin
        inj_out_if_else_1755007761333_610 = inj_in_c_1755007761333_568;
    end else begin
        inj_out_if_else_1755007761333_610 = {inj_in_a_1755007761333_196, inj_in_b_1755007761333_922};
    end
    end
    // END: module_concat_if_ts1755007761333

    target_module_for_bind target_module_for_bind_inst_1755007761332_2047 (
        .i_target_clk(clk),
        .i_target_data(inj_i_target_data_1755007761332_683),
        .o_target_result(inj_o_target_result_1755007761332_574)
    );
endmodule

