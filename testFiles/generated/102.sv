module ModuleFF (
    input logic clk,
    input bit [3:0] in1,
    input bit [3:0] in2,
    input logic reset,
    output bit [3:0] out1,
    output bit [3:0] out2
);
    parameter int MAX_COUNT = 10;
    localparam int START_VAL = 5;
    logic [3:0] ff_reg;
    integer unused_int_var;
    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            ff_reg <= START_VAL;
            out1 <= '0;
            out2 <= '0;
            unused_int_var <= 0;
        end else begin
            case ({in1, in2})
                8'h00: ff_reg <= ff_reg;
                8'h01: ff_reg <= in1 + in2;
                default: ff_reg <= MAX_COUNT;
            endcase
            out1 <= ff_reg;
            out2 <= {in1[0], in1[0], in1[0], in1[0]} | {in2[3], in2[2], in2[1], in2[0]};
        end
    end
endmodule

module split_for_loop (
    input logic clk_i,
    input logic [7:0] start_val_i,
    output logic [15:0] sum_out_i
);
    always @(posedge clk_i) begin
        sum_out_i <= 0;
        for (int i = 0; i < 4; i = i + 1) begin
            sum_out_i <= sum_out_i + start_val_i + i;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_din_1755007786625_234,
    input wire [1:0] inj_i_sel_1755007786626_993,
    input wire [3:0] inj_i_val_1755007786626_369,
    input bit [3:0] inj_in1_1755007786627_262,
    input bit [3:0] inj_in2_1755007786627_341,
    input logic [7:0] inj_in_b_1755007786627_222,
    input logic [7:0] inj_in_val_h_1755007786625_959,
    input wire reset,
    output wire inj_dout_1755007786625_339,
    output logic inj_keyword_out_1755007786625_217,
    output logic [3:0] inj_o_out_1755007786626_145,
    output bit [3:0] inj_out1_1755007786627_827,
    output bit [3:0] inj_out2_1755007786627_324,
    output logic [15:0] inj_out_concat_1755007786627_630,
    output logic [7:0] inj_out_reg_h_1755007786625_982,
    output logic [7:0] inj_output_bf_1755007786629_792,
    output logic [3:0] inj_output_bf_slice_1755007786629_643,
    output logic [15:0] inj_sum_out_i_1755007786628_952
);
    // BEGIN: ContinuousWire_ts1755007786625
    wire internal_w_ts1755007786625;
        // BEGIN: mod_case_block_attrs_ts1755007786626
        logic [3:0] l_temp_ts1755007786626;
            // BEGIN: module_bitfield_concat_ts1755007786630
            logic [7:0] my_bitfield_ts1755007786630 ;
            always_comb begin
                if (inj_in_b_1755007786627_222[7]) begin
                    my_bitfield_ts1755007786630 = inj_in_b_1755007786627_222;
                end else begin
                    my_bitfield_ts1755007786630 = {inj_in_b_1755007786627_222[0], inj_in_b_1755007786627_222[7:1]};
                end
                my_bitfield_ts1755007786630[3:0] = l_temp_ts1755007786626;
            end
            assign inj_output_bf_1755007786629_792 = my_bitfield_ts1755007786630;
            assign inj_output_bf_slice_1755007786629_643 = my_bitfield_ts1755007786630[3:0];
            // END: module_bitfield_concat_ts1755007786630

            split_for_loop split_for_loop_inst_1755007786628_8490 (
                .start_val_i(inj_in_val_h_1755007786625_959),
                .sum_out_i(inj_sum_out_i_1755007786628_952),
                .clk_i(clk)
            );
            ModuleFF ModuleFF_inst_1755007786627_3996 (
                .clk(clk),
                .in1(inj_in1_1755007786627_262),
                .in2(inj_in2_1755007786627_341),
                .reset(reset),
                .out1(inj_out1_1755007786627_827),
                .out2(inj_out2_1755007786627_324)
            );
            // BEGIN: ComplexConversions_ts1755007786627
            always_comb begin
                inj_out_concat_1755007786627_630 = {inj_in_val_h_1755007786625_959, inj_in_b_1755007786627_222};
            end
            // END: ComplexConversions_ts1755007786627

        always_comb begin
            (* full_case *)
            (* parallel_case *)
            case (inj_i_sel_1755007786626_993)
                2'b00: l_temp_ts1755007786626 = inj_i_val_1755007786626_369;
                2'b01: l_temp_ts1755007786626 = inj_i_val_1755007786626_369 << 1;
                2'b10: l_temp_ts1755007786626 = inj_i_val_1755007786626_369 >> 1;
                default: l_temp_ts1755007786626 = 4'bxxxx;
            endcase
            (* coverage_off *)
            begin : my_named_block
                inj_o_out_1755007786626_145 = l_temp_ts1755007786626;
            end
        end
        // END: mod_case_block_attrs_ts1755007786626

        // BEGIN: keyword_import_export_ts1755007786625
        assign inj_keyword_out_1755007786625_217 = inj_din_1755007786625_234;
        // END: keyword_import_export_ts1755007786625

        // BEGIN: split_if_only_then_ts1755007786625
        always @(posedge clk) begin
            if (inj_din_1755007786625_234) begin
                inj_out_reg_h_1755007786625_982 <= inj_in_val_h_1755007786625_959;
            end
        end
        // END: split_if_only_then_ts1755007786625

    assign internal_w_ts1755007786625 = inj_din_1755007786625_234;
    assign inj_dout_1755007786625_339       = internal_w_ts1755007786625;
    // END: ContinuousWire_ts1755007786625
endmodule

