typedef struct packed {
    logic [3:0] f1;
    logic       f2;
    logic [2:0] f3;
} eight_bit_unpacked_struct_t;
typedef struct packed {
    logic f2;
    logic [2:0] f3;
    logic [3:0] f1;
} eight_bit_unpacked_struct_t;

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

module case_default (
    input logic [1:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        case (in_val)
            2'b01: out_res = 1'b1;
            2'b10: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module module_function (
    input wire [7:0] in_func_a,
    input wire [7:0] in_func_b,
    output logic [7:0] out_func_result
);
    function automatic [7:0] add_and_subtract;
    input [7:0] val1;
    input [7:0] val2;
    reg [7:0] temp;
    begin
    temp = val1 + val2;
    add_and_subtract = temp - 1;
    end
    endfunction
    always_comb begin
    out_func_result = add_and_subtract(in_func_a, in_func_b);
    end
endmodule

module timed_assign_unhandled (
    input logic clk,
    input logic [7:0] in,
    output logic [7:0] out
);
    always @(posedge clk) begin
        out <= in;
    end
endmodule

module snippet (
    input wire clk,
    input logic inj_in1_1755007851152_409,
    input logic [7:0] inj_in_1755007851153_972,
    input wire [7:0] inj_in_func_a_1755007851152_779,
    input wire [7:0] inj_in_func_b_1755007851152_370,
    input bit inj_in_h_1755007851152_22,
    input logic [38:0] inj_in_packed_for_conv_1755007851154_188,
    input logic [1:0] inj_in_val_1755007851153_743,
    input wire reset,
    output logic [7:0] inj_default_out_1755007851156_107,
    output logic inj_out1_1755007851152_663,
    output bit inj_out_1755007851153_253,
    output logic [7:0] inj_out_1755007851153_936,
    output logic inj_out_bit_conv_1755007851154_775,
    output logic [7:0] inj_out_func_result_1755007851152_453,
    output logic inj_out_h_1755007851152_286,
    output logic inj_out_h_1755007851152_694,
    output int inj_out_int_conv_1755007851154_380,
    output reg inj_out_res_1755007851153_920,
    output reg inj_out_res_1755007851157_853,
    output logic [7:0] inj_out_unpacked_struct_repacked_1755007851154_570,
    output logic [5:0] inj_out_vec_conv_1755007851154_226
);
    // BEGIN: CoverageHelper_ts1755007851152
    // BEGIN: CoverageHelper_ts1755007851152
    // BEGIN: BindSimpleModule_ts1755007851153
    // BEGIN: assign_pattern_lvalue_ts1755007851156
    eight_bit_unpacked_struct_t unpacked_s;
    logic [7:0] reg_unpacked_struct_repacked_ts1755007851155;
    int int_var_ts1755007851155;
    logic bit_var_ts1755007851155;
    logic [5:0] vec_var_ts1755007851155;
        // BEGIN: case_empty_statement_ts1755007851158
        always_comb begin
            inj_out_res_1755007851157_853 = 1'b0;
            case (inj_in_val_1755007851153_743)
                2'b00: inj_out_res_1755007851157_853 = 1'b1;
                2'b01: ;
                2'b10: inj_out_res_1755007851157_853 = 1'b0;
                default: inj_out_res_1755007851157_853 = 1'b1;
            endcase
        end
        // END: case_empty_statement_ts1755007851158

        // BEGIN: func_macro_defaults_ts1755007851157
        `define DEFAULT_CONST       8'hAA
        `define CALC(val, def=`DEFAULT_CONST) ((val) | (def))
        localparam logic [7:0] P_WITH_DEF     = `CALC(8'h0F);
        localparam logic [7:0] P_OVERRIDE_DEF = `CALC(8'hF0, 8'h11);
        assign inj_default_out_1755007851156_107 = bit_var_ts1755007851155 ? P_WITH_DEF : P_OVERRIDE_DEF;
        // END: func_macro_defaults_ts1755007851157

    always_comb begin
        unpacked_s.f1 = inj_in_1755007851153_972[3:0];
        unpacked_s.f2 = inj_in_1755007851153_972[4];
        unpacked_s.f3 = inj_in_1755007851153_972[7:5];
        reg_unpacked_struct_repacked_ts1755007851155 = { unpacked_s.f3, unpacked_s.f2, unpacked_s.f1 };
        int_var_ts1755007851155 = inj_in_packed_for_conv_1755007851154_188[31:0];
        bit_var_ts1755007851155 = inj_in_packed_for_conv_1755007851154_188[32];
        vec_var_ts1755007851155 = inj_in_packed_for_conv_1755007851154_188[38:33];
        inj_out_unpacked_struct_repacked_1755007851154_570 = reg_unpacked_struct_repacked_ts1755007851155;
        inj_out_int_conv_1755007851154_380 = int_var_ts1755007851155;
        inj_out_bit_conv_1755007851154_775 = bit_var_ts1755007851155;
        inj_out_vec_conv_1755007851154_226 = vec_var_ts1755007851155;
    end
    // END: assign_pattern_lvalue_ts1755007851156

    case_default case_default_inst_1755007851153_327 (
        .in_val(inj_in_val_1755007851153_743),
        .out_res(inj_out_res_1755007851153_920)
    );
    timed_assign_unhandled timed_assign_unhandled_inst_1755007851153_2966 (
        .out(inj_out_1755007851153_936),
        .clk(clk),
        .in(inj_in_1755007851153_972)
    );
    assign inj_out_1755007851153_253 = inj_in_h_1755007851152_22;
    // END: BindSimpleModule_ts1755007851153

    assign inj_out_h_1755007851152_694 = inj_in_h_1755007851152_22;
    // END: CoverageHelper_ts1755007851152

    ModuleLineDirective ModuleLineDirective_inst_1755007851152_4907 (
        .in1(inj_in1_1755007851152_409),
        .out1(inj_out1_1755007851152_663)
    );
    module_function module_function_inst_1755007851152_4396 (
        .in_func_a(inj_in_func_a_1755007851152_779),
        .in_func_b(inj_in_func_b_1755007851152_370),
        .out_func_result(inj_out_func_result_1755007851152_453)
    );
    assign inj_out_h_1755007851152_286 = inj_in_h_1755007851152_22;
    // END: CoverageHelper_ts1755007851152
endmodule

