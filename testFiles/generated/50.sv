module ModClockedWithSimpleAssign (
    input logic clk,
    input logic in_a,
    input logic in_b,
    output logic out_comb,
    output logic out_reg
);
    logic internal_reg;
    always @(posedge clk) begin 
    internal_reg <= in_a; 
    end
    assign out_comb = in_a ^ in_b; 
    always @(posedge clk) begin 
    out_reg <= internal_reg & in_b; 
    end
endmodule

module case_basic (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b00: out_res = 1'b0;
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            2'b11: out_res = 1'b1;
        endcase
    end
endmodule

module module_with_params #(
    parameter integer DATA_WIDTH = 8
) (
    input wire [7:0] param_in,
    output wire [7:0] param_out
);
    assign param_out = param_in;
endmodule

module recursive_macro_dummy (
    input logic in_bit,
    output logic out_bit
);
    `define RECURSIVE_TEST `RECURSIVE_TEST
    assign out_bit = in_bit;
endmodule

module variable_sel_mux (
    input logic [7:0] in,
    input logic [2:0] index,
    output logic out
);
    assign out = in[index];
endmodule

module snippet (
    input wire clk,
    input int inj_b_1755004220507_669,
    input logic inj_cond1_1755004220506_321,
    input logic [7:0] inj_data_in_1755004220506_856,
    input logic inj_in_bit_1755004220506_702,
    input logic [1:0] inj_in_val_1755004220508_73,
    input logic [2:0] inj_index_1755004220510_362,
    input wire [7:0] inj_param_in_1755004220514_414,
    input wire reset,
    output logic inj_out_1755004220510_913,
    output logic inj_out_1755004220511_454,
    output logic inj_out_a_1755004220507_37,
    output int inj_out_b_1755004220507_148,
    output logic inj_out_bit_1755004220506_891,
    output logic inj_out_comb_1755004220507_782,
    output logic [7:0] inj_out_nested_a_1755004220506_134,
    output logic [7:0] inj_out_nested_b_1755004220506_306,
    output logic inj_out_reg_1755004220507_696,
    output reg inj_out_res_1755004220508_304,
    output reg inj_out_res_1755004220509_867,
    output wire [7:0] inj_param_out_1755004220514_73,
    output logic inj_result_out_1755004220508_956,
    output logic inj_sum_1755004220512_56,
    output logic inj_unused_out_1755004220512_653
);
    // BEGIN: mod_split_nested_ts1755004220506
    logic [7:0]  split_nested_var_ts1755004220506;
    logic [7:0] other_nested_var_ts1755004220506;
        // BEGIN: ModuleBasic_ts1755004220507
        parameter int P1  = 10;
        localparam int LP1 = 20;
        logic c_ts1755004220507;
        int   d_ts1755004220507;
        always_comb begin
            logic temp_v_ts1755004220507;
                module_with_params module_with_params_inst_1755004220514_268 (
                    .param_in(inj_param_in_1755004220514_414),
                    .param_out(inj_param_out_1755004220514_73)
                );
                // BEGIN: simple_adder_ts1755004220512
                assign inj_sum_1755004220512_56 = inj_cond1_1755004220506_321 + temp_v_ts1755004220507;
                // END: simple_adder_ts1755004220512

                // BEGIN: unreferenced_module_ts1755004220512
                assign inj_unused_out_1755004220512_653 = ~temp_v_ts1755004220507;
                // END: unreferenced_module_ts1755004220512

                // BEGIN: variable_sel_mux_ts1755004220511
                assign inj_out_1755004220511_454 = split_nested_var_ts1755004220506[inj_index_1755004220510_362];
                // END: variable_sel_mux_ts1755004220511

                variable_sel_mux variable_sel_mux_inst_1755004220510_8433 (
                    .in(inj_data_in_1755004220506_856),
                    .index(inj_index_1755004220510_362),
                    .out(inj_out_1755004220510_913)
                );
                case_basic case_basic_inst_1755004220509_3363 (
                    .in_val(inj_in_val_1755004220508_73),
                    .out_res(inj_out_res_1755004220509_867)
                );
                // BEGIN: nested_blocks_ts1755004220508
                always_comb begin : main_block 
                    inj_result_out_1755004220508_956 = 1'b0; 
                    if (c_ts1755004220507) begin : inner_block1 
                        if (inj_in_bit_1755004220506_702) begin : inner_block2 
                            inj_result_out_1755004220508_956 = temp_v_ts1755004220507;
                        end 
                    end 
                end
                // END: nested_blocks_ts1755004220508

                // BEGIN: case_basic_ts1755004220508
                always_comb begin
                    inj_out_res_1755004220508_304 = 1'b0;
                    case (inj_in_val_1755004220508_73)
                        2'b00: inj_out_res_1755004220508_304 = 1'b0;
                        2'b01: inj_out_res_1755004220508_304 = 1'b1;
                        2'b10: inj_out_res_1755004220508_304 = 1'b0;
                        2'b11: inj_out_res_1755004220508_304 = 1'b1;
                    endcase
                end
                // END: case_basic_ts1755004220508

            temp_v_ts1755004220507 = d_ts1755004220507;
            c_ts1755004220507      = temp_v_ts1755004220507;
        end
        assign inj_out_a_1755004220507_37 = inj_in_bit_1755004220506_702;
        assign d_ts1755004220507     = inj_b_1755004220507_669;
        assign inj_out_b_1755004220507_148 = d_ts1755004220507 + P1 + LP1;
        // END: ModuleBasic_ts1755004220507

        ModClockedWithSimpleAssign ModClockedWithSimpleAssign_inst_1755004220507_6983 (
            .in_a(inj_cond1_1755004220506_321),
            .in_b(inj_in_bit_1755004220506_702),
            .out_comb(inj_out_comb_1755004220507_782),
            .out_reg(inj_out_reg_1755004220507_696),
            .clk(clk)
        );
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_nested_var_ts1755004220506 <= 8'b0;
            other_nested_var_ts1755004220506 <= 8'b0;
        end else begin
            split_nested_var_ts1755004220506 <= 8'h11; 
            other_nested_var_ts1755004220506 <= 8'h22; 
            if (inj_cond1_1755004220506_321) begin
                split_nested_var_ts1755004220506 <= inj_data_in_1755004220506_856 + 10;
                other_nested_var_ts1755004220506 <= inj_data_in_1755004220506_856 + 20;
                if (inj_in_bit_1755004220506_702) begin
                    split_nested_var_ts1755004220506 <= inj_data_in_1755004220506_856 + 100;
                    other_nested_var_ts1755004220506 <= inj_data_in_1755004220506_856 + 200;
                end
            end else begin
                split_nested_var_ts1755004220506 <= inj_data_in_1755004220506_856 - 10;
                other_nested_var_ts1755004220506 <= inj_data_in_1755004220506_856 - 20;
            end
        end
    end
    always_comb begin
        inj_out_nested_a_1755004220506_134 = split_nested_var_ts1755004220506;
        inj_out_nested_b_1755004220506_306 = other_nested_var_ts1755004220506;
    end
    // END: mod_split_nested_ts1755004220506

    recursive_macro_dummy recursive_macro_dummy_inst_1755004220506_2967 (
        .in_bit(inj_in_bit_1755004220506_702),
        .out_bit(inj_out_bit_1755004220506_891)
    );
endmodule

