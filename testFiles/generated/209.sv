module attributes_test (
    input logic i_attr_in,
    output logic o_attr_out
);
    (* synthesis_preserve *) logic internal_signal;
    always_comb begin : my_combinational_block
        internal_signal = i_attr_in ? 1'b1 : 1'b0;
        o_attr_out      = internal_signal;
    end
endmodule

module deep_ff_control_logic (
    input wire dffcl_clk,
    input wire [3:0] dffcl_ctrl_mode,
    input wire [15:0] dffcl_data_in1,
    input wire [15:0] dffcl_data_in2,
    input wire dffcl_rst_n,
    output logic [15:0] dffcl_data_out
);
    always_ff @(posedge dffcl_clk or negedge dffcl_rst_n) begin
    if (!dffcl_rst_n) begin
        dffcl_data_out <= 16'h0000;
    end else begin
        case (dffcl_ctrl_mode)
            4'd0: dffcl_data_out <= dffcl_data_in1 + dffcl_data_in2;
            4'd1: begin
                if (dffcl_data_in1 > dffcl_data_in2) begin
                    case (dffcl_ctrl_mode[1:0])
                        2'b00: dffcl_data_out <= dffcl_data_in1 - dffcl_data_in2;
                        2'b01: dffcl_data_out <= dffcl_data_in1 & dffcl_data_in2;
                        default: dffcl_data_out <= dffcl_data_in1 | dffcl_data_in2;
                    endcase
                end else begin
                    case (dffcl_ctrl_mode[1:0])
                        2'b00: dffcl_data_out <= dffcl_data_in2 - dffcl_data_in1;
                        2'b01: dffcl_data_out <= dffcl_data_in1 ^ dffcl_data_in2;
                        default: dffcl_data_out <= ~dffcl_data_in1;
                    endcase
                end
            end
            4'd2: begin
                casez (dffcl_data_in1[15:13])
                    3'b000: dffcl_data_out <= dffcl_data_in2;
                    3'b001: dffcl_data_out <= ~dffcl_data_in2;
                    3'b01?: begin
                        if (dffcl_data_in2[0]) dffcl_data_out <= dffcl_data_in1 << 1;
                        else dffcl_data_out <= dffcl_data_in1 >> 1;
                    end
                    3'b1??: begin
                        if (dffcl_ctrl_mode[0]) dffcl_data_out <= dffcl_data_in1 + 1;
                        else dffcl_data_out <= dffcl_data_in1 - 1;
                    end
                    default: dffcl_data_out <= 16'hAAAA;
                endcase
            end
            default: begin
                if (dffcl_ctrl_mode[2]) dffcl_data_out <= dffcl_data_in1;
                else dffcl_data_out <= dffcl_data_in2;
            end
        endcase
    end
    end
endmodule

module explicit_non_ansi_decl_module (
    p_in,
    p_out
);
    input logic p_in;
    output wire p_out;
    assign p_out = p_in;
endmodule

module macro_line_continuation_user (
    input logic lc_en,
    output logic [15:0] lc_val
);
    `define MULTI_VAL                \
        16'hABCD
    `define ADD_FIVE(v)              \
        ((v) +                         \
            5)
    logic [15:0] value_reg;
    always_comb begin
        if (lc_en)
            value_reg = `MULTI_VAL;
        else
            value_reg = `ADD_FIVE(16'h0010);
    end
    assign lc_val = value_reg;
endmodule

module snippet (
    input wire clk,
    input wire [3:0] inj_dffcl_ctrl_mode_1755007823146_934,
    input wire [15:0] inj_dffcl_data_in1_1755007823146_256,
    input wire [15:0] inj_dffcl_data_in2_1755007823146_952,
    input logic inj_i_attr_in_1755007823144_573,
    input logic [2:0] inj_in_shift_1755007823144_368,
    input logic [7:0] inj_in_val_1755007823144_333,
    input int inj_in_val_1755007823144_760,
    input wire reset,
    output logic [7:0] inj_data_out_1755007823145_579,
    output logic [15:0] inj_dffcl_data_out_1755007823146_415,
    output logic [15:0] inj_lc_val_1755007823150_104,
    output logic inj_o_attr_out_1755007823144_602,
    output logic inj_out_bit_1755007823148_517,
    output logic [3:0] inj_out_part_1755007823144_786,
    output logic [7:0] inj_out_reg_1755007823144_196,
    output logic [3:0] inj_out_slice_1755007823148_259,
    output int inj_out_val_1755007823144_303,
    output logic [7:0] inj_out_vec_y_1755007823147_704,
    output wire inj_p_out_1755007823151_114
);
    // BEGIN: invalid_this_diag_mod_ts1755007823144
    // BEGIN: module_assignments_in_loops_ts1755007823145
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var_ts1755007823145;
    logic [3:0] part_var_ts1755007823145;
        // BEGIN: SequentialLogic_ts1755007823145
        logic [7:0] internal_reg_ts1755007823145;
            explicit_non_ansi_decl_module explicit_non_ansi_decl_module_inst_1755007823151_830 (
                .p_in(inj_i_attr_in_1755007823144_573),
                .p_out(inj_p_out_1755007823151_114)
            );
            macro_line_continuation_user macro_line_continuation_user_inst_1755007823150_4346 (
                .lc_val(inj_lc_val_1755007823150_104),
                .lc_en(inj_i_attr_in_1755007823144_573)
            );
            // BEGIN: element_select_packed_ts1755007823148
            always_comb begin
                if (inj_in_val_1755007823144_760 >= 0 && inj_in_val_1755007823144_760 < 8)
                    inj_out_bit_1755007823148_517 = reg_var_ts1755007823145[inj_in_val_1755007823144_760];
                else
                    inj_out_bit_1755007823148_517 = 'x; 
            end
            assign inj_out_slice_1755007823148_259 = reg_var_ts1755007823145[6:3];
            // END: element_select_packed_ts1755007823148

            // BEGIN: split_vector_assign_ts1755007823147
            always @(posedge clk) begin
                if (inj_i_attr_in_1755007823144_573) begin
                    inj_out_vec_y_1755007823147_704[3:0] <= inj_in_val_1755007823144_333[3:0];
                    inj_out_vec_y_1755007823147_704[7:4] <= inj_in_val_1755007823144_333[7:4] + 1;
                end else begin
                    inj_out_vec_y_1755007823147_704 <= 8'hFF;
                end
            end
            // END: split_vector_assign_ts1755007823147

            deep_ff_control_logic deep_ff_control_logic_inst_1755007823146_402 (
                .dffcl_clk(clk),
                .dffcl_ctrl_mode(inj_dffcl_ctrl_mode_1755007823146_934),
                .dffcl_data_in1(inj_dffcl_data_in1_1755007823146_256),
                .dffcl_data_in2(inj_dffcl_data_in2_1755007823146_952),
                .dffcl_rst_n(reset),
                .dffcl_data_out(inj_dffcl_data_out_1755007823146_415)
            );
        always @(posedge clk or negedge reset) begin
            if (~reset) begin
                internal_reg_ts1755007823145 <= 8'h00;
            end else begin
                internal_reg_ts1755007823145 <= inj_in_val_1755007823144_333;
            end
        end
        assign inj_data_out_1755007823145_579 = internal_reg_ts1755007823145;
        // END: SequentialLogic_ts1755007823145

    always_comb begin
        reg_var_ts1755007823145  = inj_in_val_1755007823144_333;
        part_var_ts1755007823145 = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var_ts1755007823145  = reg_var_ts1755007823145 + i;
            reg_var_ts1755007823145 += (i * 2);
            reg_var_ts1755007823145 <<= inj_in_shift_1755007823144_368;
            reg_var_ts1755007823145[i % 8] = (reg_var_ts1755007823145[i % 8] == 1'b0);
            reg_var_ts1755007823145[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var_ts1755007823145 = reg_var_ts1755007823145[7:4];
    end
    assign inj_out_reg_1755007823144_196  = reg_var_ts1755007823145;
    assign inj_out_part_1755007823144_786 = part_var_ts1755007823145;
    // END: module_assignments_in_loops_ts1755007823145

    assign inj_out_val_1755007823144_303 = inj_in_val_1755007823144_760;
    // END: invalid_this_diag_mod_ts1755007823144

    attributes_test attributes_test_inst_1755007823144_5807 (
        .o_attr_out(inj_o_attr_out_1755007823144_602),
        .i_attr_in(inj_i_attr_in_1755007823144_573)
    );
endmodule

