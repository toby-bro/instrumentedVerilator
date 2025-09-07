module casez_xz (
    input logic [2:0] in_val,
    output reg out_res
);
    always_comb begin
        out_res = 1'b0;
        casez (in_val)
            3'b1??: out_res = 1'b1;
            3'b0z?: out_res = 1'b0;
            default: out_res = 1'b1;
        endcase
    end
endmodule

module recursive_macro_dummy (
    input logic in_bit,
    output logic out_bit
);
    `define RECURSIVE_TEST `RECURSIVE_TEST
    assign out_bit = in_bit;
endmodule

module snippet (
    input wire clk,
    input logic [7:0] inj_data_in_1755007811407_177,
    input logic inj_in_bit_1755007811407_699,
    input logic [2:0] inj_in_val_1755007811406_995,
    input logic [31:0] inj_p_in1_1755007811406_857,
    input logic [31:0] inj_p_in2_1755007811406_183,
    input logic [1:0] inj_p_mode_1755007811406_999,
    input wire reset,
    output logic inj_is_even_1755007811407_200,
    output logic inj_out_bit_1755007811407_583,
    output reg inj_out_res_1755007811406_266,
    output reg inj_out_res_1755007811406_462,
    output logic [31:0] inj_p_out_1755007811406_758
);
    // BEGIN: more_procedural_ts1755007811406
    // BEGIN: case_empty_statement_ts1755007811406
    // BEGIN: FunctionTaskMod_ts1755007811407
    function automatic bit check_even(input logic [7:0] v);
        check_even = ~v[0];
    endfunction
    task automatic dummy_task(input logic [7:0] v);
        int tmp_ts1755007811407;
        tmp_ts1755007811407 = v;
    recursive_macro_dummy recursive_macro_dummy_inst_1755007811407_2388 (
        .out_bit(inj_out_bit_1755007811407_583),
        .in_bit(inj_in_bit_1755007811407_699)
    );
    endtask
    assign inj_is_even_1755007811407_200 = check_even(inj_data_in_1755007811407_177);
    // END: FunctionTaskMod_ts1755007811407

    always_comb begin
        inj_out_res_1755007811406_462 = 1'b0;
        case (inj_p_mode_1755007811406_999)
            2'b00: inj_out_res_1755007811406_462 = 1'b1;
            2'b01: ;
            2'b10: inj_out_res_1755007811406_462 = 1'b0;
            default: inj_out_res_1755007811406_462 = 1'b1;
        endcase
    end
    // END: case_empty_statement_ts1755007811406

    casez_xz casez_xz_inst_1755007811406_1534 (
        .out_res(inj_out_res_1755007811406_266),
        .in_val(inj_in_val_1755007811406_995)
    );
    always_comb begin
        case (inj_p_mode_1755007811406_999)
            2'b00: inj_p_out_1755007811406_758 = (inj_p_in1_1755007811406_857 + inj_p_in2_1755007811406_183) * 2;
            2'b01: inj_p_out_1755007811406_758 = (inj_p_in1_1755007811406_857 - inj_p_in2_1755007811406_183) / 3; 
            2'b10: inj_p_out_1755007811406_758 = (inj_p_in1_1755007811406_857 << 4) | (inj_p_in2_1755007811406_183 >> 2);
            default: inj_p_out_1755007811406_758 = ~(inj_p_in1_1755007811406_857 ^ inj_p_in2_1755007811406_183) + 1;
        endcase
    end
    // END: more_procedural_ts1755007811406
endmodule

