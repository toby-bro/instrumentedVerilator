module ModuleLineDirective (
    input logic in1,
    output logic out1
);
    logic internal_sig_a;
    logic internal_sig_b;
    logic unused_line_var;
    `line 100 "virtual_file_A.sv" 1
    assign internal_sig_a = in1;
    `line 20 "virtual_file_B.sv" 1
    assign internal_sig_b = ~internal_sig_a;
    assign unused_line_var = 1'b1;
    `line 150 "virtual_file_A.sv" 2
    assign out1 = internal_sig_b;
    `line 1 "original_file.sv" 0
endmodule

module SimpleAssign (
    input logic [7:0] in_data,
    output logic [7:0] out_data
);
    assign out_data = in_data;
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

module snippet (
    input wire clk,
    input logic [7:0] inj_in_data_1755007902931_532,
    input logic [2:0] inj_in_val_1755007902931_129,
    input logic [1:0] inj_in_val_1755007902932_147,
    input logic [31:0] inj_p_in1_1755007902932_558,
    input logic [31:0] inj_p_in2_1755007902932_173,
    input int inj_val_false_1755007902931_531,
    input int inj_val_true_1755007902931_141,
    input wire reset,
    output logic inj_o_sum_1755007902930_31,
    output logic inj_out1_1755007902932_749,
    output logic [7:0] inj_out_data_1755007902931_807,
    output reg inj_out_res_1755007902931_166,
    output reg inj_out_res_1755007902932_143,
    output int inj_out_val_1755007902931_991,
    output logic [31:0] inj_p_out_1755007902933_626,
    output logic inj_unused_out_1755007902931_649,
    output logic [7:0] inj_wide_reg_1755007902930_270
);
    // BEGIN: mod_lint_target_ts1755007902931
    logic l_reg_ts1755007902931;
        // BEGIN: more_procedural_ts1755007902933
        always_comb begin
            case (inj_in_val_1755007902932_147)
                2'b00: inj_p_out_1755007902933_626 = (inj_p_in1_1755007902932_558 + inj_p_in2_1755007902932_173) * 2;
                2'b01: inj_p_out_1755007902933_626 = (inj_p_in1_1755007902932_558 - inj_p_in2_1755007902932_173) / 3; 
                2'b10: inj_p_out_1755007902933_626 = (inj_p_in1_1755007902932_558 << 4) | (inj_p_in2_1755007902932_173 >> 2);
                default: inj_p_out_1755007902933_626 = ~(inj_p_in1_1755007902932_558 ^ inj_p_in2_1755007902932_173) + 1;
            endcase
        end
        // END: more_procedural_ts1755007902933

        ModuleLineDirective ModuleLineDirective_inst_1755007902932_9736 (
            .in1(l_reg_ts1755007902931),
            .out1(inj_out1_1755007902932_749)
        );
        case_basic case_basic_inst_1755007902932_5477 (
            .out_res(inj_out_res_1755007902932_143),
            .in_val(inj_in_val_1755007902932_147)
        );
        SimpleAssign SimpleAssign_inst_1755007902931_1660 (
            .in_data(inj_in_data_1755007902931_532),
            .out_data(inj_out_data_1755007902931_807)
        );
        // BEGIN: mod_unused_ports_ts1755007902931
        assign inj_unused_out_1755007902931_649 = reset;
        // END: mod_unused_ports_ts1755007902931

        // BEGIN: casez_xz_ts1755007902931
        always_comb begin
            inj_out_res_1755007902931_166 = 1'b0;
            casez (inj_in_val_1755007902931_129)
                3'b1??: inj_out_res_1755007902931_166 = 1'b1;
                3'b0z?: inj_out_res_1755007902931_166 = 1'b0;
                default: inj_out_res_1755007902931_166 = 1'b1;
            endcase
        end
        // END: casez_xz_ts1755007902931

        // BEGIN: ConditionalOps_ts1755007902931
        assign inj_out_val_1755007902931_991 = l_reg_ts1755007902931 ? inj_val_true_1755007902931_141 : inj_val_false_1755007902931_531;
        // END: ConditionalOps_ts1755007902931

    always_comb begin
        l_reg_ts1755007902931 = 1;
        inj_wide_reg_1755007902930_270 = {clk, reset};
    end
    assign inj_o_sum_1755007902930_31 = clk + reset;
    // END: mod_lint_target_ts1755007902931
endmodule

