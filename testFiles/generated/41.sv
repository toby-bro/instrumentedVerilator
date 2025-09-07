typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
typedef struct packed {
    logic [3:0] f1;
    logic f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;

module BindSimpleModule (
    input bit in,
    output bit out
);
    assign out = in;
endmodule

module ModClockedConditional (
    input logic clk,
    input logic data_in,
    input logic enable,
    output logic data_out
);
    logic reg_data;
    always @(posedge clk) begin
    if (enable) begin
        reg_data <= data_in;
    end
    end
    assign data_out = reg_data;
endmodule

module ModuleBasic (
    input logic a,
    input int b,
    output logic out_a,
    output int out_b
);
    parameter int P1  = 10;
    localparam int LP1 = 20;
    logic c;
    int   d;
    always_comb begin
        logic temp_v;
        temp_v = d;
        c      = temp_v;
    end
    assign out_a = a;
    assign d     = b;
    assign out_b = d + P1 + LP1;
endmodule

module Module_ConfigKeywords (
    input bit cfg_in,
    output bit cfg_out
);
    assign cfg_out = cfg_in;
endmodule

module always_multi_stmt_unhandled (
    input logic [7:0] in1,
    input logic [7:0] in2,
    output logic [7:0] out1,
    output logic [7:0] out2
);
    always_comb begin
        out1 = in1;
        out2 = in2;
    end
endmodule

module case_priority_overlapping_mod (
    input logic [1:0] case_expr,
    output logic [4:0] internal_out
);
    always @* begin
        priority casez (case_expr)
            2'b1?: internal_out = 5;
            2'b?1: internal_out = 6;  
            2'b0?: internal_out = 7;
            2'b?0: internal_out = 8;  
            default: internal_out = 9;
        endcase
    end
endmodule

module formatting_stress (
    input logic [1:0] case_sel_fmt,
    input logic [7:0] data_in_fmt,
    input logic enable_block_fmt,
    input logic sel_fmt,
    output logic [7:0] data_out_fmt
);
    logic [7:0] temp_reg_fmt; 
    always_comb begin : stress_comb_block_label 
        data_out_fmt = 8'hXX; 
        if (enable_block_fmt) begin
            if (sel_fmt) begin
                case (case_sel_fmt) 
                    2'b00: data_out_fmt = data_in_fmt;
                    2'b01: begin 
                        data_out_fmt = ~data_in_fmt; 
                        end 
                    2'b10: begin 
                        logic [7:0] added_val; 
                        added_val = data_in_fmt + 8'h01; 
                        data_out_fmt = added_val; 
                        end 
                    default: data_out_fmt = 8'hFF; 
                endcase 
            end else begin
                data_out_fmt = data_in_fmt - 8'h01; 
            end 
        end else begin
            data_out_fmt = 8'h00; 
        end 
    end
endmodule

module mod_internal_if_test (
    input wire in_i,
    output logic out_o
);
    assign out_o = !in_i;
endmodule

module snippet (
    input wire clk,
    input logic [1:0] inj_case_sel_fmt_1755004217192_590,
    input logic inj_data_in_1755004217187_951,
    input logic [7:0] inj_in1_1755004217185_654,
    input wire [7:0] inj_in1_1755004217188_588,
    input logic [7:0] inj_in2_1755004217185_373,
    input wire [7:0] inj_in2_1755004217188_330,
    input logic inj_in_1755004217185_559,
    input logic [3:0] inj_in_h_1755004217191_774,
    input logic [3:0] inj_in_l_1755004217191_923,
    input logic [38:0] inj_in_packed_for_conv_1755004217195_601,
    input bit inj_trigger_input_1755004217189_722,
    input wire reset,
    output bit inj_d_out_1755004217189_77,
    output logic inj_data_out_1755004217187_303,
    output logic [7:0] inj_data_out_fmt_1755004217192_188,
    output logic [4:0] inj_internal_out_1755004217193_186,
    output wire inj_o_1755004217185_810,
    output logic [7:0] inj_out1_1755004217185_713,
    output wire [7:0] inj_out1_1755004217188_875,
    output logic [7:0] inj_out2_1755004217185_168,
    output wire [7:0] inj_out2_1755004217188_413,
    output logic inj_out_1755004217185_388,
    output wire inj_out_1755004217194_684,
    output logic inj_out_a_1755004217202_687,
    output int inj_out_b_1755004217202_870,
    output logic inj_out_bit_conv_1755004217195_313,
    output logic [1:0] inj_out_bits_1755004217200_29,
    output logic [7:0] inj_out_c_1755004217191_95,
    output logic inj_out_cmp_1755004217198_208,
    output int inj_out_int_conv_1755004217195_557,
    output logic inj_out_o_1755004217186_807,
    output logic [7:0] inj_out_ops_1755004217198_990,
    output bit inj_out_tc_1755004217190_920,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755004217195_432,
    output logic [5:0] inj_out_vec_conv_1755004217195_25,
    output logic inj_sub_out_1755004217186_667,
    output bit inj_trigger_output_1755004217189_357
);
    // BEGIN: mod_always_event_ts1755004217185
    // BEGIN: buf_primitive_ts1755004217185
    // BEGIN: sub_module_ts1755004217186
    // BEGIN: multi_always_comb_ts1755004217188
    logic [7:0] intermediate1_ts1755004217188;
    logic [7:0] intermediate2_ts1755004217188;
        // BEGIN: assign_pattern_lvalue_ts1755004217196
        eight_bit_unpacked_struct_t unpacked_s;
        logic [7:0] reg_unpacked_struct_repacked_ts1755004217196;
        int int_var_ts1755004217196;
        logic bit_var_ts1755004217196;
        logic [5:0] vec_var_ts1755004217196;
            // BEGIN: Module_BasicSyntax_ts1755004217198
            logic [7:0] temp_ts1755004217198;
                // BEGIN: cast_select_demo_ts1755004217200
                logic [7:0] internal_ts1755004217200;
                    ModuleBasic ModuleBasic_inst_1755004217202_5784 (
                        .b(int_var_ts1755004217196),
                        .out_a(inj_out_a_1755004217202_687),
                        .out_b(inj_out_b_1755004217202_870),
                        .a(bit_var_ts1755004217196)
                    );
                always_comb begin
                    internal_ts1755004217200 = temp_ts1755004217198;
                    inj_out_bits_1755004217200_29 = internal_ts1755004217200[3 -: 2];
                end
                // END: cast_select_demo_ts1755004217200

            always_comb begin
                temp_ts1755004217198 = intermediate1_ts1755004217188 + inj_in1_1755004217185_654;
            end
            assign inj_out_ops_1755004217198_990 = (intermediate1_ts1755004217188 & inj_in1_1755004217185_654) | (intermediate1_ts1755004217188 ^ inj_in1_1755004217185_654);
            assign inj_out_cmp_1755004217198_208 = (intermediate1_ts1755004217188 == inj_in1_1755004217185_654);
            // END: Module_BasicSyntax_ts1755004217198

        always_comb begin
            unpacked_s.f1 = inj_in1_1755004217185_654[3:0];
            unpacked_s.f2 = inj_in1_1755004217185_654[4];
            unpacked_s.f3 = inj_in1_1755004217185_654[7:5];
            reg_unpacked_struct_repacked_ts1755004217196 = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
            int_var_ts1755004217196 = inj_in_packed_for_conv_1755004217195_601[31:0];
            bit_var_ts1755004217196 = inj_in_packed_for_conv_1755004217195_601[32];
            vec_var_ts1755004217196 = inj_in_packed_for_conv_1755004217195_601[38:33];
            inj_out_unpacked_struct_repacked_1755004217195_432 = reg_unpacked_struct_repacked_ts1755004217196;
            inj_out_int_conv_1755004217195_557 = int_var_ts1755004217196;
            inj_out_bit_conv_1755004217195_313 = bit_var_ts1755004217196;
            inj_out_vec_conv_1755004217195_25 = vec_var_ts1755004217196;
        end
        // END: assign_pattern_lvalue_ts1755004217196

        // BEGIN: Comb_Assign_ts1755004217194
        assign inj_out_1755004217194_684 = clk & reset;
        // END: Comb_Assign_ts1755004217194

        case_priority_overlapping_mod case_priority_overlapping_mod_inst_1755004217193_6827 (
            .case_expr(inj_case_sel_fmt_1755004217192_590),
            .internal_out(inj_internal_out_1755004217193_186)
        );
        formatting_stress formatting_stress_inst_1755004217192_2226 (
            .sel_fmt(inj_in_1755004217185_559),
            .data_out_fmt(inj_data_out_fmt_1755004217192_188),
            .case_sel_fmt(inj_case_sel_fmt_1755004217192_590),
            .data_in_fmt(inj_in1_1755004217185_654),
            .enable_block_fmt(inj_data_in_1755004217187_951)
        );
        // BEGIN: concat_op_ts1755004217191
        assign inj_out_c_1755004217191_95 = {inj_in_h_1755004217191_774, inj_in_l_1755004217191_923};
        // END: concat_op_ts1755004217191

        // BEGIN: TopConfigExample_ts1755004217190
        Module_ConfigKeywords i_cfg (.cfg_in(inj_trigger_input_1755004217189_722), .cfg_out(inj_out_tc_1755004217190_920));
        // END: TopConfigExample_ts1755004217190

        // BEGIN: DummyBindTarget_ts1755004217189
        assign inj_d_out_1755004217189_77 = inj_trigger_input_1755004217189_722;
        BindSimpleModule u_bind (.in(inj_trigger_input_1755004217189_722), .out());
        // END: DummyBindTarget_ts1755004217189

        // BEGIN: PragmaOnceDirective_ts1755004217189
    assign inj_trigger_output_1755004217189_357 = inj_trigger_input_1755004217189_722;
        // END: PragmaOnceDirective_ts1755004217189

    always @(*) begin
        intermediate1_ts1755004217188 = inj_in1_1755004217188_588 & inj_in2_1755004217188_330;
    end
    always @(*) begin
        intermediate2_ts1755004217188 = inj_in1_1755004217188_588 | inj_in2_1755004217188_330;
    end
    assign inj_out1_1755004217188_875 = intermediate1_ts1755004217188 + 8'd1;
    assign inj_out2_1755004217188_413 = intermediate2_ts1755004217188 - 8'd1;
    // END: multi_always_comb_ts1755004217188

    ModClockedConditional ModClockedConditional_inst_1755004217187_7785 (
        .clk(clk),
        .data_in(inj_data_in_1755004217187_951),
        .enable(inj_in_1755004217185_559),
        .data_out(inj_data_out_1755004217187_303)
    );
    assign inj_sub_out_1755004217186_667 = !inj_in_1755004217185_559;
    // END: sub_module_ts1755004217186

    mod_internal_if_test mod_internal_if_test_inst_1755004217186_669 (
        .in_i(clk),
        .out_o(inj_out_o_1755004217186_807)
    );
    buf b1 (inj_o_1755004217185_810, clk);
    // END: buf_primitive_ts1755004217185

    always @(posedge clk or negedge reset) begin
        if (!reset) begin
            inj_out_1755004217185_388 <= 1'b0;
        end else begin
            inj_out_1755004217185_388 <= inj_in_1755004217185_559;
        end
    end
    // END: mod_always_event_ts1755004217185

    always_multi_stmt_unhandled always_multi_stmt_unhandled_inst_1755004217185_436 (
        .in1(inj_in1_1755004217185_654),
        .in2(inj_in2_1755004217185_373),
        .out1(inj_out1_1755004217185_713),
        .out2(inj_out2_1755004217185_168)
    );
endmodule

