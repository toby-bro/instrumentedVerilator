module ModRegister (
    input logic din,
    output logic dout
);
    always @* begin
        dout = din;
    end
endmodule

module split_if_only_then (
    input logic clk_h,
    input logic condition_h,
    input logic [7:0] in_val_h,
    output logic [7:0] out_reg_h
);
    always @(posedge clk_h) begin
        if (condition_h) begin
            out_reg_h <= in_val_h;
        end
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_din_1755007903264_100,
    input logic [2:0] inj_in_shift_1755007903265_77,
    input logic [7:0] inj_in_val_1755007903265_917,
    input logic [15:0] inj_packed_in_1755007903266_488,
    input bit inj_trigger_input_1755007903264_495,
    input logic [3:0] inj_v1_1755007903264_930,
    input logic [3:0] inj_v2_1755007903264_52,
    input logic [9:0] inj_val_in_1755007903267_920,
    input wire reset,
    output logic inj_dout_1755007903264_25,
    output logic inj_eq_1755007903264_934,
    output logic [7:0] inj_field2_o_1755007903266_864,
    output logic [3:0] inj_out_part_1755007903265_978,
    output logic [7:0] inj_out_reg_1755007903265_133,
    output logic [7:0] inj_out_reg_h_1755007903268_209,
    output bit inj_system_status_clear_1755007903264_592,
    output bit inj_trigger_output_1755007903264_305,
    output logic [9:0] inj_val_out_1755007903267_581
);
    // BEGIN: PragmaOnceDirective_ts1755007903264
    // BEGIN: PragmaResetDirectives_ts1755007903264
`ifdef SLANG_PRAGMA
`reset protect diagnostic
`endif
    // BEGIN: ModCompareVec_ts1755007903264
    // BEGIN: module_assignments_in_loops_ts1755007903265
    localparam int PART_START = 4;
    localparam int PART_WIDTH = 4;
    logic [7:0] reg_var_ts1755007903265;
    logic [3:0] part_var_ts1755007903265;
        split_if_only_then split_if_only_then_inst_1755007903268_6305 (
            .condition_h(inj_din_1755007903264_100),
            .in_val_h(reg_var_ts1755007903265),
            .out_reg_h(inj_out_reg_h_1755007903268_209),
            .clk_h(clk)
        );
        // BEGIN: SimpleAssign_ts1755007903267
        assign inj_val_out_1755007903267_581 = inj_val_in_1755007903267_920;
        // END: SimpleAssign_ts1755007903267

        // BEGIN: typedef_struct_mod_ts1755007903266
        typedef struct packed {
            logic [7:0] field1_ts1755007903266;
            logic [7:0] field2_ts1755007903266;
        } my_packed_struct_t;
        my_packed_struct_t my_struct_var;
        always_comb begin
            my_struct_var = inj_packed_in_1755007903266_488;
        end
        assign inj_field2_o_1755007903266_864 = my_struct_var.field2_ts1755007903266;
        // END: typedef_struct_mod_ts1755007903266

    always_comb begin
        reg_var_ts1755007903265  = inj_in_val_1755007903265_917;
        part_var_ts1755007903265 = 4'h0;
        for (int i = 0; i < 4; i++) begin
            reg_var_ts1755007903265  = reg_var_ts1755007903265 + i;
            reg_var_ts1755007903265 += (i * 2);
            reg_var_ts1755007903265 <<= inj_in_shift_1755007903265_77;
            reg_var_ts1755007903265[i % 8] = (reg_var_ts1755007903265[i % 8] == 1'b0);
            reg_var_ts1755007903265[PART_START +: PART_WIDTH] = i[3:0];
        end
        part_var_ts1755007903265 = reg_var_ts1755007903265[7:4];
    end
    assign inj_out_reg_1755007903265_133  = reg_var_ts1755007903265;
    assign inj_out_part_1755007903265_978 = part_var_ts1755007903265;
    // END: module_assignments_in_loops_ts1755007903265

    assign inj_eq_1755007903264_934 = (inj_v1_1755007903264_930 == inj_v2_1755007903264_52);
    // END: ModCompareVec_ts1755007903264

assign inj_system_status_clear_1755007903264_592 = reset;
    // END: PragmaResetDirectives_ts1755007903264

    ModRegister ModRegister_inst_1755007903264_1666 (
        .din(inj_din_1755007903264_100),
        .dout(inj_dout_1755007903264_25)
    );
assign inj_trigger_output_1755007903264_305 = inj_trigger_input_1755007903264_495;
    // END: PragmaOnceDirective_ts1755007903264
endmodule

