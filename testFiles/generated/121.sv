module ModSimpleLogic (
    input logic a,
    input logic b,
    output logic y
);
    assign y = a ^ b;
endmodule

module SequentialLogicPlaceholder (
    input logic clk,
    input logic [15:0] data_in,
    input logic rst,
    output logic [15:0] data_out
);
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            data_out <= 16'h0;
        end else begin
            data_out <= data_in;
        end
    end
endmodule

module module_selection (
    input wire in_bit,
    input wire [2:0] in_index,
    input wire [1:0] in_part_lsb,
    input wire [7:0] in_vector,
    output logic out_bit_select,
    output logic [7:0] out_bitwise_ops,
    output logic [3:0] out_part_select,
    output logic [7:0] out_vector_assign
);
    always_comb begin
    out_vector_assign = in_vector;
    out_bit_select = in_vector[in_index];
    out_part_select = in_vector[in_part_lsb +: 4];
    out_bitwise_ops = in_vector & {8{in_bit}};
    end
endmodule

module simple_adder (
    input logic a,
    input logic b,
    output logic sum
);
    assign sum = a + b;
endmodule

module attributes_on_expr_port (
    input logic i_control,
    input logic i_in,
    output logic o_out
);
    logic internal_sig;
    assign internal_sig = i_in & i_control;
    simple_adder sa_inst(
        .a  (i_in),
        (* fanout_limit = 10 *) .b(i_control),
        .sum(o_out)
    );
endmodule

module simple_assign (
    input logic [7:0] in,
    output logic [7:0] out
);
    assign out = in;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007793426_22,
    input logic inj_b_1755007793426_578,
    input logic [7:0] inj_data_in_1755007793424_810,
    input logic [15:0] inj_data_in_1755007793427_449,
    input wire [3:0] inj_data_in_1755007793427_8,
    input wire [2:0] inj_in_index_1755007793425_196,
    input wire [1:0] inj_in_part_lsb_1755007793425_354,
    input int inj_in_val_1755007793424_29,
    input wire [7:0] inj_in_vector_1755007793425_745,
    input wire reset,
    output logic [15:0] inj_data_out_1755007793427_318,
    output reg [3:0] inj_data_out_1755007793427_445,
    output logic inj_o_out_1755007793429_96,
    output logic [7:0] inj_out1_z_1755007793430_357,
    output logic [7:0] inj_out2_z_1755007793430_192,
    output logic [7:0] inj_out_1755007793428_69,
    output logic inj_out_bit_select_1755007793425_36,
    output logic [7:0] inj_out_bitwise_ops_1755007793425_513,
    output logic [3:0] inj_out_part_select_1755007793425_264,
    output logic [7:0] inj_out_reg_a_1755007793424_89,
    output logic [7:0] inj_out_reg_b_1755007793424_561,
    output int inj_out_val_1755007793424_528,
    output logic [7:0] inj_out_vector_assign_1755007793425_750,
    output logic inj_y_1755007793426_792
);
    // BEGIN: undeclared_but_found_pkg_diag_mod_ts1755007793424
    // BEGIN: mod_split_ff_ts1755007793425
    logic [7:0]  split_reg_var_ts1755007793425;
    logic [7:0] other_reg_var_ts1755007793425;
        // BEGIN: split_diff_vars_branches_ts1755007793430
        always @(posedge clk) begin
            if (inj_b_1755007793426_578) begin
                inj_out1_z_1755007793430_357 <= split_reg_var_ts1755007793425;
            end else begin
                inj_out2_z_1755007793430_192 <= other_reg_var_ts1755007793425;
            end
        end
        // END: split_diff_vars_branches_ts1755007793430

        attributes_on_expr_port attributes_on_expr_port_inst_1755007793429_5939 (
            .o_out(inj_o_out_1755007793429_96),
            .i_control(inj_a_1755007793426_22),
            .i_in(inj_b_1755007793426_578)
        );
        simple_assign simple_assign_inst_1755007793428_9330 (
            .in(split_reg_var_ts1755007793425),
            .out(inj_out_1755007793428_69)
        );
        // BEGIN: mod_event_implicit_ts1755007793427
        always @* begin
            inj_data_out_1755007793427_445 = inj_data_in_1755007793427_8;
        end
        // END: mod_event_implicit_ts1755007793427

        SequentialLogicPlaceholder SequentialLogicPlaceholder_inst_1755007793427_3662 (
            .rst(reset),
            .data_out(inj_data_out_1755007793427_318),
            .clk(clk),
            .data_in(inj_data_in_1755007793427_449)
        );
        ModSimpleLogic ModSimpleLogic_inst_1755007793426_440 (
            .a(inj_a_1755007793426_22),
            .b(inj_b_1755007793426_578),
            .y(inj_y_1755007793426_792)
        );
        module_selection module_selection_inst_1755007793425_7779 (
            .in_vector(inj_in_vector_1755007793425_745),
            .out_bit_select(inj_out_bit_select_1755007793425_36),
            .out_bitwise_ops(inj_out_bitwise_ops_1755007793425_513),
            .out_part_select(inj_out_part_select_1755007793425_264),
            .out_vector_assign(inj_out_vector_assign_1755007793425_750),
            .in_bit(clk),
            .in_index(inj_in_index_1755007793425_196),
            .in_part_lsb(inj_in_part_lsb_1755007793425_354)
        );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_reg_var_ts1755007793425 <= 8'b0;
            other_reg_var_ts1755007793425 <= 8'b0;
            inj_out_reg_a_1755007793424_89 <= 8'b0;
            inj_out_reg_b_1755007793424_561 <= 8'b0;
        end else begin
            split_reg_var_ts1755007793425 <= inj_data_in_1755007793424_810;
            other_reg_var_ts1755007793425 <= inj_data_in_1755007793424_810 + 2;
            inj_out_reg_a_1755007793424_89 <= split_reg_var_ts1755007793425;
            inj_out_reg_b_1755007793424_561 <= other_reg_var_ts1755007793425;
        end
    end
    // END: mod_split_ff_ts1755007793425

    assign inj_out_val_1755007793424_528 = inj_in_val_1755007793424_29;
    // END: undeclared_but_found_pkg_diag_mod_ts1755007793424
endmodule

