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

module snippet (
    input wire clk,
    input logic [3:0] inj_in_a_1755007889550_856,
    input logic [3:0] inj_in_b_1755007889550_373,
    input logic [7:0] inj_in_vec_1755007889550_389,
    input int inj_index_in_1755007889550_682,
    input logic inj_p_in_1755007889550_465,
    input logic [1:0] inj_sel_1755007889550_742,
    input wire reset,
    output logic inj_out_bit_1755007889550_473,
    output logic [7:0] inj_out_case_a_1755007889550_172,
    output logic [7:0] inj_out_case_b_1755007889550_504,
    output logic [3:0] inj_out_slice_1755007889550_978,
    output logic [3:0] inj_out_y_1755007889550_719,
    output wire inj_p_out_1755007889550_289
);
    // BEGIN: element_select_packed_ts1755007889550
    // BEGIN: explicit_non_ansi_decl_module_ts1755007889550
    input logic inj_p_in_1755007889550_465_ts1755007889550;
    output wire inj_p_out_1755007889550_289_ts1755007889550;
        // BEGIN: BitwiseAssign_ts1755007889550
        assign inj_out_y_1755007889550_719 = inj_in_a_1755007889550_856 ^ inj_in_b_1755007889550_373;
        // END: BitwiseAssign_ts1755007889550

        mod_split_case mod_split_case_inst_1755007889550_3883 (
            .out_case_a(inj_out_case_a_1755007889550_172),
            .out_case_b(inj_out_case_b_1755007889550_504),
            .data_in(inj_in_vec_1755007889550_389),
            .sel(inj_sel_1755007889550_742)
        );
    assign inj_p_out_1755007889550_289_ts1755007889550 = inj_p_in_1755007889550_465_ts1755007889550;
    // END: explicit_non_ansi_decl_module_ts1755007889550

    always_comb begin
        if (inj_index_in_1755007889550_682 >= 0 && inj_index_in_1755007889550_682 < 8)
            inj_out_bit_1755007889550_473 = inj_in_vec_1755007889550_389[inj_index_in_1755007889550_682];
        else
            inj_out_bit_1755007889550_473 = 'x; 
    end
    assign inj_out_slice_1755007889550_978 = inj_in_vec_1755007889550_389[6:3];
    // END: element_select_packed_ts1755007889550
endmodule

