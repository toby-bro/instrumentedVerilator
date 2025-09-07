module BitwiseOperations (
    input logic [7:0] a,
    input logic [7:0] b,
    input logic [7:0] c,
    output logic [7:0] result_and,
    output logic [7:0] result_or,
    output logic [7:0] result_xor
);
    assign result_and = a & b;
    assign result_or = a | c;
    assign result_xor = b ^ c;
endmodule

module CaseStatementConditions (
    input wire [3:0] data_c,
    input wire [1:0] selector,
    output logic [3:0] out_case_case,
    output logic [3:0] out_case_casex,
    output logic [3:0] out_case_casez
);
    always_comb begin
        case (selector)
            2'b00: out_case_case = data_c;
            2'b01: out_case_case = data_c + 1;
            2'b10: out_case_case = data_c + 2;
            default: out_case_case = 4'bxxxx;
        endcase
        casez (selector)
            2'b0?: out_case_casez = data_c + 10;
            2'b1?: out_case_casez = data_c + 20;
            default: out_case_casez = 4'bzzzz;
        endcase
        casex (selector)
            2'b0?: out_case_casex = data_c - 1;
            2'b1?: out_case_casex = data_c - 2;
            default: out_case_casex = 4'bxxxx;
        endcase
    end
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

module mod_split_case (
    input logic [7:0] data_in,
    input logic [1:0] sel,
    output logic [7:0] out_case_a,
    output logic [7:0] out_case_b
);
    logic [7:0]  split_case_var;
    logic [7:0] other_case_var;
    always_comb begin
        split_case_var = 8'hFF;
        other_case_var = 8'hAA;
        case (sel)
            2'b00: begin
                split_case_var = data_in + 5;
                other_case_var = data_in + 6;
            end
            2'b01: begin
                split_case_var = data_in - 5;
                other_case_var = data_in - 6;
            end
            default: begin
                split_case_var = data_in;
                other_case_var = data_in;
            end
        endcase
        out_case_a = split_case_var;
        out_case_b = other_case_var;
    end
endmodule

module undeclared_but_found_pkg_diag_mod (
    input int in_val,
    output int out_val
);
    assign out_val = in_val;
endmodule

module snippet #(
    parameter int SEL_PARAM = 6
) (
    input wire clk,
    input logic [7:0] inj_a_1755007776390_842,
    input logic [7:0] inj_b_1755007776390_914,
    input wire [3:0] inj_data_c_1755007776388_907,
    input logic [3:0] inj_data_in_1755007776382_893,
    input logic [7:0] inj_data_in_1755007776385_889,
    input wire [15:0] inj_in_packed_data_1755007776387_396,
    input int inj_sel_in_1755007776382_234,
    input wire [1:0] inj_selector_1755007776388_126,
    input wire reset,
    output logic [7:0] inj_data_out_1755007776382_235,
    output logic [4:0] inj_internal_out_1755007776384_660,
    output logic inj_is_even_1755007776385_735,
    output logic [7:0] inj_out1_1755007776397_218,
    output logic [7:0] inj_out2_1755007776397_907,
    output wire [7:0] inj_out_byte_1755007776387_199,
    output logic [7:0] inj_out_case_a_1755007776395_296,
    output logic [7:0] inj_out_case_b_1755007776395_390,
    output logic [3:0] inj_out_case_case_1755007776388_722,
    output logic [3:0] inj_out_case_casex_1755007776388_535,
    output logic [3:0] inj_out_case_casez_1755007776388_121,
    output logic [7:0] inj_out_reg_a_1755007776393_705,
    output logic [7:0] inj_out_reg_b_1755007776393_831,
    output int inj_out_val_1755007776386_676,
    output logic [7:0] inj_result_and_1755007776390_351,
    output logic [7:0] inj_result_or_1755007776390_570,
    output logic [7:0] inj_result_xor_1755007776390_418
);
    // BEGIN: ModuleHierarchy_High_ts1755007776383
    ModuleBasic m1 (
        .a      (1'b1),
        .b      (inj_sel_in_1755007776382_234),
        .out_a  (),
        .out_b  ( )
    );
    if (SEL_PARAM > 5) begin : gen_high
        int high_data_ts1755007776383;
        ModuleBasic m_high (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (high_data_ts1755007776383)
        );
    end else begin : gen_low
        int low_data_ts1755007776383;
        ModuleBasic m_low (
            .a      (1'b0),
            .b      (SEL_PARAM),
            .out_a  (),
            .out_b  (low_data_ts1755007776383)
        );
    end
    for (genvar i = 0; i < 2; ++i) begin : gen_loop
        logic [1:0] sub_in_ts1755007776383;
        assign sub_in_ts1755007776383 = inj_data_in_1755007776382_893[i*2 +: 2];
        int temp_int_ts1755007776383;
            // BEGIN: mod_split_ff_ts1755007776393
            logic [7:0]  split_reg_var_ts1755007776393;
            logic [7:0] other_reg_var_ts1755007776393;
                always_multi_stmt_unhandled always_multi_stmt_unhandled_inst_1755007776397_905 (
                    .in1(split_reg_var_ts1755007776393),
                    .in2(other_reg_var_ts1755007776393),
                    .out1(inj_out1_1755007776397_218),
                    .out2(inj_out2_1755007776397_907)
                );
                mod_split_case mod_split_case_inst_1755007776395_9900 (
                    .sel(sub_in_ts1755007776383),
                    .out_case_a(inj_out_case_a_1755007776395_296),
                    .out_case_b(inj_out_case_b_1755007776395_390),
                    .data_in(other_reg_var_ts1755007776393)
                );
            always_ff @(posedge clk or posedge reset) begin
                if (reset) begin
                    split_reg_var_ts1755007776393 <= 8'b0;
                    other_reg_var_ts1755007776393 <= 8'b0;
                    inj_out_reg_a_1755007776393_705 <= 8'b0;
                    inj_out_reg_b_1755007776393_831 <= 8'b0;
                end else begin
                    split_reg_var_ts1755007776393 <= inj_a_1755007776390_842;
                    other_reg_var_ts1755007776393 <= inj_a_1755007776390_842 + 2;
                    inj_out_reg_a_1755007776393_705 <= split_reg_var_ts1755007776393;
                    inj_out_reg_b_1755007776393_831 <= other_reg_var_ts1755007776393;
                end
            end
            // END: mod_split_ff_ts1755007776393

            BitwiseOperations BitwiseOperations_inst_1755007776390_4968 (
                .c(inj_data_in_1755007776385_889),
                .result_and(inj_result_and_1755007776390_351),
                .result_or(inj_result_or_1755007776390_570),
                .result_xor(inj_result_xor_1755007776390_418),
                .a(inj_a_1755007776390_842),
                .b(inj_b_1755007776390_914)
            );
            CaseStatementConditions CaseStatementConditions_inst_1755007776388_4254 (
                .data_c(inj_data_c_1755007776388_907),
                .selector(inj_selector_1755007776388_126),
                .out_case_case(inj_out_case_case_1755007776388_722),
                .out_case_casez(inj_out_case_casez_1755007776388_121),
                .out_case_casex(inj_out_case_casex_1755007776388_535)
            );
            // BEGIN: packed_struct_module_ts1755007776387
            typedef struct packed {
                logic [7:0] byte1_ts1755007776387;
                logic [7:0] byte2_ts1755007776387;
            } my_packed_struct_t;
            my_packed_struct_t data_struct;
            assign data_struct = inj_in_packed_data_1755007776387_396;
            assign inj_out_byte_1755007776387_199 = data_struct.byte1_ts1755007776387;
            // END: packed_struct_module_ts1755007776387

            undeclared_but_found_pkg_diag_mod undeclared_but_found_pkg_diag_mod_inst_1755007776386_9739 (
                .in_val(temp_int_ts1755007776383),
                .out_val(inj_out_val_1755007776386_676)
            );
            // BEGIN: FunctionTaskMod_ts1755007776385
            function automatic bit check_even(input logic [7:0] v);
                check_even = ~v[0];
            endfunction
            task automatic dummy_task(input logic [7:0] v);
                int tmp_ts1755007776385;
                tmp_ts1755007776385 = v;
            endtask
            assign inj_is_even_1755007776385_735 = check_even(inj_data_in_1755007776385_889);
            // END: FunctionTaskMod_ts1755007776385

            // BEGIN: case_full_parallel_mod_ts1755007776384
            always @* begin
                (* full, parallel *)
                case (sub_in_ts1755007776383)
                    2'b00: inj_internal_out_1755007776384_660 = 1;
                    2'b01: inj_internal_out_1755007776384_660 = 2;
                    2'b10: inj_internal_out_1755007776384_660 = 3;
                    default: inj_internal_out_1755007776384_660 = 4;
                endcase
            end
            // END: case_full_parallel_mod_ts1755007776384

        ModuleBasic m_inst (
            .a      (1'b0),
            .b      (int'(sub_in_ts1755007776383)),
            .out_a  (),
            .out_b  (temp_int_ts1755007776383)
        );
        assign inj_data_out_1755007776382_235[i*4 +: 4] = temp_int_ts1755007776383[3:0];
    end
    // END: ModuleHierarchy_High_ts1755007776383
endmodule

