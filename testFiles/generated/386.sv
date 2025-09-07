module Comb_Case (
    input wire [3:0] in0,
    input wire [3:0] in1,
    input wire [3:0] in2,
    input wire [3:0] in3,
    input wire [1:0] sel,
    output reg [3:0] mux_out
);
    always_comb begin
        case (sel)
            2'b00: mux_out = in0;
            2'b01: mux_out = in1;
            2'b10: mux_out = in2;
            default: mux_out = in3;
        endcase
    end
endmodule

module mod_comb_logic (
    input logic a,
    input logic b,
    output logic y
);
    always_comb begin
        y = a & b;
    end
endmodule

module module_in_program_ref (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet (
    input wire clk,
    input logic inj_a_1755007883631_517,
    input logic inj_b_1755007883631_775,
    input logic [7:0] inj_data_in_1755007883634_279,
    input wire [3:0] inj_in0_1755007883632_289,
    input wire [3:0] inj_in1_1755007883632_231,
    input wire [3:0] inj_in2_1755007883632_209,
    input wire [3:0] inj_in3_1755007883632_297,
    input wire [7:0] inj_in_c_1755007883632_998,
    input int inj_in_val_1755007883632_66,
    input logic [3:0] inj_input_bf_slice_1755007883640_518,
    input logic [31:0] inj_p_in1_1755007883633_21,
    input logic [31:0] inj_p_in2_1755007883633_852,
    input logic [1:0] inj_p_mode_1755007883633_115,
    input wire [1:0] inj_sel_1755007883632_803,
    input logic inj_seq_in_1755007883636_638,
    input wire reset,
    output logic inj_comb_out_1755007883636_491,
    output reg [3:0] inj_mux_out_1755007883632_504,
    output logic [15:0] inj_out_concat_1755007883632_415,
    output logic [7:0] inj_out_if_a_1755007883634_892,
    output logic [7:0] inj_out_if_b_1755007883634_632,
    output logic [7:0] inj_out_if_else_1755007883632_76,
    output int inj_out_val_1755007883632_463,
    output logic [7:0] inj_out_vec_1755007883638_925,
    output logic [7:0] inj_output_bf_1755007883640_319,
    output logic [3:0] inj_output_bf_slice_1755007883640_616,
    output logic [31:0] inj_p_out_1755007883633_918,
    output wire inj_p_out_1755007883642_204,
    output logic inj_seq_out_1755007883636_224,
    output logic inj_y_1755007883631_178
);
    // BEGIN: module_concat_if_ts1755007883632
    // BEGIN: more_procedural_ts1755007883633
    // BEGIN: mod_split_if_ts1755007883635
    logic [7:0]  split_if_var_ts1755007883634;
    logic [7:0] other_if_var_ts1755007883634;
        // BEGIN: MixedLogic_ts1755007883636
        logic seq_reg_ts1755007883636;
        logic comb_intermediate_ts1755007883636;
            // BEGIN: module_bitfield_concat_ts1755007883640
            logic [7:0] my_bitfield_ts1755007883640 ;
                // BEGIN: explicit_non_ansi_decl_module_ts1755007883643
                input logic comb_intermediate_ts1755007883636_ts1755007883643;
                output wire inj_p_out_1755007883642_204_ts1755007883643;
                assign inj_p_out_1755007883642_204_ts1755007883643 = comb_intermediate_ts1755007883636_ts1755007883643;
                // END: explicit_non_ansi_decl_module_ts1755007883643

            always_comb begin
                if (split_if_var_ts1755007883634[7]) begin
                    my_bitfield_ts1755007883640 = split_if_var_ts1755007883634;
                end else begin
                    my_bitfield_ts1755007883640 = {split_if_var_ts1755007883634[0], split_if_var_ts1755007883634[7:1]};
                end
                my_bitfield_ts1755007883640[3:0] = inj_input_bf_slice_1755007883640_518;
            end
            assign inj_output_bf_1755007883640_319 = my_bitfield_ts1755007883640;
            assign inj_output_bf_slice_1755007883640_616 = my_bitfield_ts1755007883640[3:0];
            // END: module_bitfield_concat_ts1755007883640

            // BEGIN: SimpleLoopExample_ts1755007883638
            always_comb begin
                for (int i = 0; i < 8; i++) begin
                    inj_out_vec_1755007883638_925[i] = split_if_var_ts1755007883634[7 - i];
                end
            end
            // END: SimpleLoopExample_ts1755007883638

        always @(posedge clk or negedge reset) begin
            if (!reset) begin
                seq_reg_ts1755007883636 <= 1'b0;
            end else begin
                seq_reg_ts1755007883636 <= inj_seq_in_1755007883636_638;
            end
        end
        assign inj_seq_out_1755007883636_224 = seq_reg_ts1755007883636;
        always @(seq_reg_ts1755007883636 or inj_b_1755007883631_775 or inj_a_1755007883631_517) begin
            comb_intermediate_ts1755007883636 = (seq_reg_ts1755007883636 & inj_b_1755007883631_775) | (~seq_reg_ts1755007883636 & inj_a_1755007883631_517);
        end
        assign inj_comb_out_1755007883636_491 = comb_intermediate_ts1755007883636;
        // END: MixedLogic_ts1755007883636

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            split_if_var_ts1755007883634 <= 8'b0;
            other_if_var_ts1755007883634 <= 8'b0;
        end else begin
            if (inj_a_1755007883631_517) begin
                split_if_var_ts1755007883634 <= inj_data_in_1755007883634_279;
                other_if_var_ts1755007883634 <= inj_data_in_1755007883634_279 + 3;
            end else begin
                split_if_var_ts1755007883634 <= inj_data_in_1755007883634_279 - 1;
                other_if_var_ts1755007883634 <= inj_data_in_1755007883634_279 - 2;
            end
        end
    end
    always_comb begin
        inj_out_if_a_1755007883634_892 = split_if_var_ts1755007883634;
        inj_out_if_b_1755007883634_632 = other_if_var_ts1755007883634;
    end
    // END: mod_split_if_ts1755007883635

    always_comb begin
        case (inj_p_mode_1755007883633_115)
            2'b00: inj_p_out_1755007883633_918 = (inj_p_in1_1755007883633_21 + inj_p_in2_1755007883633_852) * 2;
            2'b01: inj_p_out_1755007883633_918 = (inj_p_in1_1755007883633_21 - inj_p_in2_1755007883633_852) / 3; 
            2'b10: inj_p_out_1755007883633_918 = (inj_p_in1_1755007883633_21 << 4) | (inj_p_in2_1755007883633_852 >> 2);
            default: inj_p_out_1755007883633_918 = ~(inj_p_in1_1755007883633_21 ^ inj_p_in2_1755007883633_852) + 1;
        endcase
    end
    // END: more_procedural_ts1755007883633

    always_comb begin
    inj_out_concat_1755007883632_415 = {inj_in2_1755007883632_209, inj_in3_1755007883632_297, inj_in_c_1755007883632_998};
    if (reset) begin
        inj_out_if_else_1755007883632_76 = inj_in_c_1755007883632_998;
    end else begin
        inj_out_if_else_1755007883632_76 = {inj_in2_1755007883632_209, inj_in3_1755007883632_297};
    end
    end
    // END: module_concat_if_ts1755007883632

    module_in_program_ref module_in_program_ref_inst_1755007883632_288 (
        .in_val(inj_in_val_1755007883632_66),
        .out_val(inj_out_val_1755007883632_463)
    );
    Comb_Case Comb_Case_inst_1755007883632_7069 (
        .in1(inj_in1_1755007883632_231),
        .in2(inj_in2_1755007883632_209),
        .in3(inj_in3_1755007883632_297),
        .sel(inj_sel_1755007883632_803),
        .mux_out(inj_mux_out_1755007883632_504),
        .in0(inj_in0_1755007883632_289)
    );
    mod_comb_logic mod_comb_logic_inst_1755007883631_6753 (
        .b(inj_b_1755007883631_775),
        .y(inj_y_1755007883631_178),
        .a(inj_a_1755007883631_517)
    );
endmodule

